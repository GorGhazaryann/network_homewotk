#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <signal.h>
#include <pthread.h>
#include <stdatomic.h>
#include <time.h>
#include <poll.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <linux/netfilter.h>
#include <libnetfilter_queue/libnetfilter_queue.h>

#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/rand.h>
#include <openssl/crypto.h>
#include <openssl/bn.h>
#include <openssl/param_build.h>
#include <openssl/core_names.h>

#define LOG(...) do { fprintf(stderr, "[secchan] " __VA_ARGS__); fputc('\n', stderr); } while (0)

#define DH_GROUP        "ffdhe2048"
#define DH_PUB_LEN      256
#define NONCE_LEN       32
#define MAC_LEN         32
#define MSG_BODY        (4 + NONCE_LEN + DH_PUB_LEN)
#define MSG_LEN         (MSG_BODY + MAC_LEN)
#define OFF_NONCE       4
#define OFF_PUB         (4 + NONCE_LEN)

#define KEY_LEN         32
#define SALT_LEN        4
#define IV_LEN          12
#define CTR_LEN         8
#define TAG_LEN         16
#define TRAILER_LEN     (CTR_LEN + TAG_LEN)
#define AAD_LEN         17
#define MAX_IP_PKT      65535

#define REKEY_SECS      3600
#define REKEY_PKTS      (1ULL << 32)
#define HARD_LIMIT_PKTS (1ULL << 48)

static uint8_t g_psk[256];
static size_t  g_psk_len;

typedef struct {
    uint8_t  tx_key[KEY_LEN], rx_key[KEY_LEN];
    uint8_t  tx_salt[SALT_LEN], rx_salt[SALT_LEN];
    _Atomic uint64_t tx_ctr;
    uint64_t rx_max, rx_bitmap;
    int      rx_any;
} session_t;

static pthread_rwlock_t g_lock = PTHREAD_RWLOCK_INITIALIZER;
static session_t *g_cur, *g_prev;

static void session_free(session_t *s)
{
    if (!s) return;
    OPENSSL_cleanse(s, sizeof *s);
    free(s);
}

static void session_install(session_t *s)
{
    pthread_rwlock_wrlock(&g_lock);
    session_free(g_prev);
    g_prev = g_cur;
    g_cur  = s;
    pthread_rwlock_unlock(&g_lock);
}

static void drop_log(const char *why)
{
    static _Atomic time_t last;
    time_t now = time(NULL);
    if (atomic_exchange(&last, now) != now) LOG("drop: %s", why);
}

static void hmac_sha256(const uint8_t *data, size_t len, uint8_t out[32])
{
    unsigned int n = 32;
    HMAC(EVP_sha256(), g_psk, (int)g_psk_len, data, len, out, &n);
}

static void mac3(const char *label, const uint8_t *a, size_t al,
                 const uint8_t *b, size_t bl, uint8_t out[32])
{
    uint8_t buf[1024];
    size_t l = strlen(label);
    memcpy(buf, label, l);
    if (al) memcpy(buf + l, a, al);
    if (bl) memcpy(buf + l + al, b, bl);
    hmac_sha256(buf, l + al + bl, out);
    OPENSSL_cleanse(buf, sizeof buf);
}

static void hkdf(const uint8_t *salt, size_t sl, const uint8_t *ikm, size_t il,
                 const char *info, uint8_t *out, size_t olen)
{
    uint8_t prk[32], t[32], buf[32 + 64 + 1];
    unsigned int n;
    size_t tl = 0, pos = 0, infol = strlen(info);
    uint8_t c = 1;

    HMAC(EVP_sha256(), salt, (int)sl, ikm, il, prk, &n);
    while (pos < olen) {
        memcpy(buf, t, tl);
        memcpy(buf + tl, info, infol);
        buf[tl + infol] = c++;
        HMAC(EVP_sha256(), prk, 32, buf, tl + infol + 1, t, &n);
        tl = 32;
        size_t k = (olen - pos < 32) ? olen - pos : 32;
        memcpy(out + pos, t, k);
        pos += k;
    }
    OPENSSL_cleanse(prk, sizeof prk);
    OPENSSL_cleanse(t, sizeof t);
}

static EVP_PKEY *dh_generate(void)
{
    EVP_PKEY *k = NULL;
    EVP_PKEY_CTX *c = EVP_PKEY_CTX_new_from_name(NULL, "DH", NULL);
    OSSL_PARAM p[2] = {
        OSSL_PARAM_construct_utf8_string(OSSL_PKEY_PARAM_GROUP_NAME, (char *)DH_GROUP, 0),
        OSSL_PARAM_construct_end()
    };
    if (!c || EVP_PKEY_keygen_init(c) <= 0 || EVP_PKEY_CTX_set_params(c, p) <= 0 ||
        EVP_PKEY_generate(c, &k) <= 0)
        k = NULL;
    EVP_PKEY_CTX_free(c);
    return k;
}

static int dh_pub_bytes(EVP_PKEY *k, uint8_t out[DH_PUB_LEN])
{
    BIGNUM *bn = NULL;
    if (!EVP_PKEY_get_bn_param(k, OSSL_PKEY_PARAM_PUB_KEY, &bn)) return -1;
    int r = BN_bn2binpad(bn, out, DH_PUB_LEN);
    BN_free(bn);
    return r == DH_PUB_LEN ? 0 : -1;
}

static EVP_PKEY *dh_import_peer(const uint8_t pub[DH_PUB_LEN])
{
    EVP_PKEY *pk = NULL;
    BIGNUM *bn = BN_bin2bn(pub, DH_PUB_LEN, NULL);
    OSSL_PARAM_BLD *bld = OSSL_PARAM_BLD_new();
    OSSL_PARAM *params = NULL;
    EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_from_name(NULL, "DH", NULL);

    if (bn && bld && ctx &&
        OSSL_PARAM_BLD_push_utf8_string(bld, OSSL_PKEY_PARAM_GROUP_NAME, DH_GROUP, 0) &&
        OSSL_PARAM_BLD_push_BN(bld, OSSL_PKEY_PARAM_PUB_KEY, bn) &&
        (params = OSSL_PARAM_BLD_to_param(bld)) &&
        EVP_PKEY_fromdata_init(ctx) > 0 &&
        EVP_PKEY_fromdata(ctx, &pk, EVP_PKEY_PUBLIC_KEY, params) > 0) {
        EVP_PKEY_CTX *chk = EVP_PKEY_CTX_new_from_pkey(NULL, pk, NULL);
        if (!chk || EVP_PKEY_public_check(chk) != 1) {
            EVP_PKEY_free(pk);
            pk = NULL;
        }
        EVP_PKEY_CTX_free(chk);
    } else {
        pk = NULL;
    }
    OSSL_PARAM_free(params);
    OSSL_PARAM_BLD_free(bld);
    EVP_PKEY_CTX_free(ctx);
    BN_free(bn);
    return pk;
}

static int dh_derive(EVP_PKEY *priv, EVP_PKEY *peer, uint8_t *out, size_t *len)
{
    EVP_PKEY_CTX *c = EVP_PKEY_CTX_new_from_pkey(NULL, priv, NULL);
    int ok = c && EVP_PKEY_derive_init(c) > 0 &&
             EVP_PKEY_derive_set_peer(c, peer) > 0 &&
             EVP_PKEY_derive(c, out, len) > 0;
    EVP_PKEY_CTX_free(c);
    return ok ? 0 : -1;
}

static session_t *derive_session(int is_init, const uint8_t *secret, size_t sl,
                                 const uint8_t th[32])
{
    session_t *s = calloc(1, sizeof *s);
    uint8_t ik[KEY_LEN], rk[KEY_LEN], is[SALT_LEN], rs[SALT_LEN];
    if (!s) return NULL;

    hkdf(th, 32, secret, sl, "SCH i2r key",  ik, KEY_LEN);
    hkdf(th, 32, secret, sl, "SCH i2r salt", is, SALT_LEN);
    hkdf(th, 32, secret, sl, "SCH r2i key",  rk, KEY_LEN);
    hkdf(th, 32, secret, sl, "SCH r2i salt", rs, SALT_LEN);

    memcpy(s->tx_key,  is_init ? ik : rk, KEY_LEN);
    memcpy(s->rx_key,  is_init ? rk : ik, KEY_LEN);
    memcpy(s->tx_salt, is_init ? is : rs, SALT_LEN);
    memcpy(s->rx_salt, is_init ? rs : is, SALT_LEN);
    atomic_init(&s->tx_ctr, 0);

    OPENSSL_cleanse(ik, sizeof ik); OPENSSL_cleanse(rk, sizeof rk);
    return s;
}

static int gcm_encrypt(const uint8_t *key, const uint8_t *iv,
                       const uint8_t *aad, size_t aadl,
                       uint8_t *buf, size_t len, uint8_t *tag)
{
    EVP_CIPHER_CTX *c = EVP_CIPHER_CTX_new();
    int ol = 0, fl = 0, ok = 0;
    uint8_t fin[16];
    if (!c) return 0;
    ok = EVP_EncryptInit_ex(c, EVP_aes_256_gcm(), NULL, NULL, NULL) == 1 &&
         EVP_CIPHER_CTX_ctrl(c, EVP_CTRL_GCM_SET_IVLEN, IV_LEN, NULL) == 1 &&
         EVP_EncryptInit_ex(c, NULL, NULL, key, iv) == 1 &&
         EVP_EncryptUpdate(c, NULL, &ol, aad, (int)aadl) == 1 &&
         EVP_EncryptUpdate(c, buf, &ol, buf, (int)len) == 1 && (size_t)ol == len &&
         EVP_EncryptFinal_ex(c, fin, &fl) == 1 &&
         EVP_CIPHER_CTX_ctrl(c, EVP_CTRL_GCM_GET_TAG, TAG_LEN, tag) == 1;
    EVP_CIPHER_CTX_free(c);
    return ok;
}

static int gcm_decrypt(const uint8_t *key, const uint8_t *iv,
                       const uint8_t *aad, size_t aadl,
                       const uint8_t *in, size_t len, const uint8_t *tag,
                       uint8_t *out)
{
    EVP_CIPHER_CTX *c = EVP_CIPHER_CTX_new();
    int ol = 0, fl = 0, ok = 0;
    uint8_t fin[16];
    if (!c) return 0;
    ok = EVP_DecryptInit_ex(c, EVP_aes_256_gcm(), NULL, NULL, NULL) == 1 &&
         EVP_CIPHER_CTX_ctrl(c, EVP_CTRL_GCM_SET_IVLEN, IV_LEN, NULL) == 1 &&
         EVP_DecryptInit_ex(c, NULL, NULL, key, iv) == 1 &&
         EVP_DecryptUpdate(c, NULL, &ol, aad, (int)aadl) == 1 &&
         EVP_DecryptUpdate(c, out, &ol, in, (int)len) == 1 && (size_t)ol == len &&
         EVP_CIPHER_CTX_ctrl(c, EVP_CTRL_GCM_SET_TAG, TAG_LEN, (void *)tag) == 1 &&
         EVP_DecryptFinal_ex(c, fin, &fl) == 1;
    EVP_CIPHER_CTX_free(c);
    return ok;
}

static void put_be64(uint8_t *p, uint64_t v) { for (int i = 7; i >= 0; i--) { p[i] = (uint8_t)v; v >>= 8; } }
static uint64_t get_be64(const uint8_t *p)   { uint64_t v = 0; for (int i = 0; i < 8; i++) v = (v << 8) | p[i]; return v; }

static void make_iv(uint8_t iv[IV_LEN], const uint8_t salt[SALT_LEN], uint64_t ctr)
{
    memcpy(iv, salt, SALT_LEN);
    put_be64(iv + SALT_LEN, ctr);
}

static int replay_ok(const session_t *s, uint64_t c)
{
    if (!s->rx_any || c > s->rx_max) return 1;
    uint64_t d = s->rx_max - c;
    return d < 64 && !((s->rx_bitmap >> d) & 1);
}

static void replay_update(session_t *s, uint64_t c)
{
    if (!s->rx_any || c > s->rx_max) {
        uint64_t sh = s->rx_any ? c - s->rx_max : 0;
        s->rx_bitmap = (sh >= 64) ? 0 : (s->rx_bitmap << sh);
        s->rx_bitmap |= 1;
        s->rx_max = c;
        s->rx_any = 1;
    } else {
        s->rx_bitmap |= 1ULL << (s->rx_max - c);
    }
}

static uint32_t csum_add(uint32_t sum, const void *data, size_t len)
{
    const uint8_t *p = data;
    while (len > 1) { sum += (uint32_t)((p[0] << 8) | p[1]); p += 2; len -= 2; }
    if (len) sum += (uint32_t)(p[0] << 8);
    return sum;
}
static uint16_t csum_fold(uint32_t sum)
{
    while (sum >> 16) sum = (sum & 0xffff) + (sum >> 16);
    return (uint16_t)~sum;
}

static void fix_checksums(struct iphdr *ip, struct tcphdr *tcp, unsigned ihl, unsigned tot)
{
    unsigned tcplen = tot - ihl;
    uint32_t sum;

    ip->check = 0;
    ip->check = htons(csum_fold(csum_add(0, ip, ihl)));

    tcp->check = 0;
    sum = csum_add(0, &ip->saddr, 8);
    sum += IPPROTO_TCP;
    sum += tcplen;
    sum = csum_add(sum, tcp, tcplen);
    tcp->check = htons(csum_fold(sum));
}

typedef enum { MODE_ENC, MODE_DEC } pmode_t;

static void build_aad(const struct iphdr *ip, const struct tcphdr *tcp, uint8_t aad[AAD_LEN])
{
    memcpy(aad,      &ip->saddr, 4);
    memcpy(aad + 4,  &ip->daddr, 4);
    aad[8] = ip->protocol;
    memcpy(aad + 9,  &tcp->source, 2);
    memcpy(aad + 11, &tcp->dest,   2);
    memcpy(aad + 13, &tcp->seq,    4);
}

static int process(pmode_t mode, uint8_t *pkt, int len, int *newlen)
{
    *newlen = 0;
    if (len < (int)sizeof(struct iphdr)) { drop_log("short packet"); return NF_DROP; }

    struct iphdr *ip = (struct iphdr *)pkt;
    if (ip->version != 4 || ip->protocol != IPPROTO_TCP) { drop_log("not TCP/IPv4"); return NF_DROP; }

    unsigned ihl = ip->ihl * 4u, tot = ntohs(ip->tot_len);
    if (ihl < 20 || tot > (unsigned)len || tot < ihl + sizeof(struct tcphdr)) {
        drop_log("bad IP header"); return NF_DROP;
    }
    if (ip->frag_off & htons(IP_MF | IP_OFFMASK)) { drop_log("fragment"); return NF_DROP; }

    struct tcphdr *tcp = (struct tcphdr *)(pkt + ihl);
    unsigned thl = tcp->doff * 4u;
    if (thl < 20 || tot < ihl + thl) { drop_log("bad TCP header"); return NF_DROP; }

    unsigned plen = tot - ihl - thl;
    uint8_t *payload = pkt + ihl + thl;
    if (plen == 0) return NF_ACCEPT;

    uint8_t aad[AAD_LEN], iv[IV_LEN];
    build_aad(ip, tcp, aad);
    unsigned newtot;

    if (mode == MODE_ENC) {
        if (tot + TRAILER_LEN > MAX_IP_PKT) { drop_log("packet too large (clamp MSS)"); return NF_DROP; }

        pthread_rwlock_rdlock(&g_lock);
        session_t *s = g_cur;
        if (!s) { pthread_rwlock_unlock(&g_lock); drop_log("no session established"); return NF_DROP; }

        uint64_t c = atomic_fetch_add(&s->tx_ctr, 1);
        if (c >= HARD_LIMIT_PKTS) { pthread_rwlock_unlock(&g_lock); drop_log("nonce space exhausted"); return NF_DROP; }
        make_iv(iv, s->tx_salt, c);
        int ok = gcm_encrypt(s->tx_key, iv, aad, AAD_LEN, payload, plen,
                             payload + plen + CTR_LEN);
        pthread_rwlock_unlock(&g_lock);
        if (!ok) { drop_log("encrypt failed"); return NF_DROP; }

        put_be64(payload + plen, c);
        newtot = tot + TRAILER_LEN;
    } else {
        if (plen <= TRAILER_LEN) { drop_log("payload too short for trailer"); return NF_DROP; }
        size_t ctl = plen - TRAILER_LEN;
        uint64_t c = get_be64(payload + ctl);
        const uint8_t *tag = payload + ctl + CTR_LEN;
        uint8_t plain[MAX_IP_PKT];
        int ok = 0;

        pthread_rwlock_rdlock(&g_lock);
        session_t *cand[2] = { g_cur, g_prev };
        for (int i = 0; i < 2 && !ok; i++) {
            session_t *s = cand[i];
            if (!s || !replay_ok(s, c)) continue;
            make_iv(iv, s->rx_salt, c);
            if (gcm_decrypt(s->rx_key, iv, aad, AAD_LEN, payload, ctl, tag, plain)) {
                replay_update(s, c);
                ok = 1;
            }
        }
        pthread_rwlock_unlock(&g_lock);
        if (!ok) { drop_log("auth failed / replay / no session"); return NF_DROP; }

        memcpy(payload, plain, ctl);
        OPENSSL_cleanse(plain, ctl);
        newtot = tot - TRAILER_LEN;
    }

    ip->tot_len = htons((uint16_t)newtot);
    fix_checksums(ip, tcp, ihl, newtot);
    *newlen = (int)newtot;
    return NF_ACCEPT;
}

typedef struct { pmode_t mode; int qnum; } qctx_t;

static int qcb(struct nfq_q_handle *qh, struct nfgenmsg *nfmsg, struct nfq_data *nfa, void *data)
{
    (void)nfmsg;
    qctx_t *q = data;
    struct nfqnl_msg_packet_hdr *ph = nfq_get_msg_packet_hdr(nfa);
    if (!ph) return 0;
    uint32_t id = ntohl(ph->packet_id);

    unsigned char *p = NULL;
    int len = nfq_get_payload(nfa, &p);
    uint8_t work[MAX_IP_PKT + TRAILER_LEN + 16];
    if (len < 0 || len > MAX_IP_PKT) return nfq_set_verdict(qh, id, NF_DROP, 0, NULL);

    memcpy(work, p, (size_t)len);
    int newlen = 0;
    int v = process(q->mode, work, len, &newlen);
    if (v == NF_ACCEPT && newlen > 0)
        return nfq_set_verdict(qh, id, NF_ACCEPT, (uint32_t)newlen, work);
    return nfq_set_verdict(qh, id, v, 0, NULL);
}

static void *queue_thread(void *arg)
{
    qctx_t *q = arg;
    struct nfq_handle *h = nfq_open();
    if (!h) { LOG("nfq_open failed"); exit(1); }
    struct nfq_q_handle *qh = nfq_create_queue(h, (uint16_t)q->qnum, qcb, q);
    if (!qh) { LOG("cannot bind queue %d (already in use? root?)", q->qnum); exit(1); }
    nfq_set_mode(qh, NFQNL_COPY_PACKET, 0xffff);
    nfq_set_queue_maxlen(qh, 4096);

    int fd = nfq_fd(h);
    static __thread char buf[MAX_IP_PKT + 4096] __attribute__((aligned(8)));
    for (;;) {
        ssize_t n = recv(fd, buf, sizeof buf, 0);
        if (n < 0) {
            if (errno == EINTR || errno == ENOBUFS) continue;
            LOG("queue %d recv: %s", q->qnum, strerror(errno));
            exit(1);
        }
        nfq_handle_packet(h, buf, (int)n);
    }
    return NULL;
}

static int read_full(int fd, void *buf, size_t n)
{
    uint8_t *p = buf;
    while (n) {
        ssize_t r = recv(fd, p, n, 0);
        if (r <= 0) { if (r < 0 && errno == EINTR) continue; return -1; }
        p += r; n -= (size_t)r;
    }
    return 0;
}
static int write_full(int fd, const void *buf, size_t n)
{
    const uint8_t *p = buf;
    while (n) {
        ssize_t r = send(fd, p, n, MSG_NOSIGNAL);
        if (r <= 0) { if (r < 0 && errno == EINTR) continue; return -1; }
        p += r; n -= (size_t)r;
    }
    return 0;
}

static void sock_setup(int fd, int rcv_timeout_s)
{
    int on = 1, idle = 10, intvl = 5, cnt = 3;
    struct timeval tv = { rcv_timeout_s, 0 };
    setsockopt(fd, SOL_SOCKET, SO_KEEPALIVE, &on, sizeof on);
    setsockopt(fd, IPPROTO_TCP, TCP_KEEPIDLE, &idle, sizeof idle);
    setsockopt(fd, IPPROTO_TCP, TCP_KEEPINTVL, &intvl, sizeof intvl);
    setsockopt(fd, IPPROTO_TCP, TCP_KEEPCNT, &cnt, sizeof cnt);
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv);
}

static void transcript_hash(const uint8_t *m1, const uint8_t *m2, uint8_t th[32])
{
    uint8_t buf[2 * MSG_LEN];
    unsigned int n = 32;
    memcpy(buf, m1, MSG_LEN);
    memcpy(buf + MSG_LEN, m2, MSG_LEN);
    EVP_Digest(buf, sizeof buf, th, &n, EVP_sha256(), NULL);
}

static session_t *handshake_initiator(int fd)
{
    uint8_t m1[MSG_LEN], m2[MSG_LEN], m3[4 + MAC_LEN], m[32], th[32], secret[DH_PUB_LEN];
    size_t sl = sizeof secret;
    EVP_PKEY *k = NULL, *peer = NULL;
    session_t *s = NULL;

    if (!(k = dh_generate())) goto out;
    memcpy(m1, "SCH1", 4);
    if (RAND_bytes(m1 + OFF_NONCE, NONCE_LEN) != 1 || dh_pub_bytes(k, m1 + OFF_PUB)) goto out;
    mac3("init", m1, MSG_BODY, NULL, 0, m1 + MSG_BODY);
    if (write_full(fd, m1, MSG_LEN) || read_full(fd, m2, MSG_LEN)) goto out;

    if (memcmp(m2, "SCH2", 4)) goto out;
    mac3("resp", m1, MSG_LEN, m2, MSG_BODY, m);
    if (CRYPTO_memcmp(m, m2 + MSG_BODY, MAC_LEN)) { LOG("peer authentication failed"); goto out; }
    if (!(peer = dh_import_peer(m2 + OFF_PUB)) || dh_derive(k, peer, secret, &sl)) goto out;

    memcpy(m3, "SCH3", 4);
    mac3("conf", m1, MSG_LEN, m2, MSG_LEN, m3 + 4);
    if (write_full(fd, m3, sizeof m3)) goto out;

    transcript_hash(m1, m2, th);
    s = derive_session(1, secret, sl, th);
out:
    OPENSSL_cleanse(secret, sizeof secret);
    EVP_PKEY_free(k); EVP_PKEY_free(peer);
    return s;
}

static session_t *handshake_responder(int fd)
{
    uint8_t m1[MSG_LEN], m2[MSG_LEN], m3[4 + MAC_LEN], m[32], th[32], secret[DH_PUB_LEN];
    size_t sl = sizeof secret;
    EVP_PKEY *k = NULL, *peer = NULL;
    session_t *s = NULL;

    if (read_full(fd, m1, MSG_LEN) || memcmp(m1, "SCH1", 4)) goto out;
    mac3("init", m1, MSG_BODY, NULL, 0, m);
    if (CRYPTO_memcmp(m, m1 + MSG_BODY, MAC_LEN)) { LOG("peer authentication failed"); goto out; }
    if (!(peer = dh_import_peer(m1 + OFF_PUB))) goto out;

    if (!(k = dh_generate())) goto out;
    memcpy(m2, "SCH2", 4);
    if (RAND_bytes(m2 + OFF_NONCE, NONCE_LEN) != 1 || dh_pub_bytes(k, m2 + OFF_PUB)) goto out;
    mac3("resp", m1, MSG_LEN, m2, MSG_BODY, m2 + MSG_BODY);
    if (write_full(fd, m2, MSG_LEN)) goto out;
    if (dh_derive(k, peer, secret, &sl)) goto out;

    if (read_full(fd, m3, sizeof m3) || memcmp(m3, "SCH3", 4)) goto out;
    mac3("conf", m1, MSG_LEN, m2, MSG_LEN, m);
    if (CRYPTO_memcmp(m, m3 + 4, MAC_LEN)) { LOG("key confirmation failed"); goto out; }

    transcript_hash(m1, m2, th);
    s = derive_session(0, secret, sl, th);
out:
    OPENSSL_cleanse(secret, sizeof secret);
    EVP_PKEY_free(k); EVP_PKEY_free(peer);
    return s;
}

static struct sockaddr_in g_peer;

static void *initiator_thread(void *arg)
{
    (void)arg;
    for (;;) {
        int fd = socket(AF_INET, SOCK_STREAM, 0);
        sock_setup(fd, 5);
        if (connect(fd, (struct sockaddr *)&g_peer, sizeof g_peer) < 0) {
            close(fd); sleep(2); continue;
        }
        session_t *s = handshake_initiator(fd);
        if (!s) { LOG("handshake failed, retrying"); close(fd); sleep(2); continue; }
        session_install(s);
        LOG("session established (initiator)");

        time_t t0 = time(NULL);
        for (;;) {
            struct pollfd pf = { fd, POLLIN, 0 };
            int r = poll(&pf, 1, 1000);
            if (r > 0) {
                char b;
                ssize_t n = recv(fd, &b, 1, MSG_DONTWAIT);
                if (n == 0 || (n < 0 && errno != EAGAIN && errno != EINTR)) { LOG("control link lost"); break; }
            } else if (r < 0 && errno != EINTR) break;
            if (time(NULL) - t0 >= REKEY_SECS || atomic_load(&s->tx_ctr) >= REKEY_PKTS) {
                LOG("rekeying"); break;
            }
        }
        close(fd);
    }
    return NULL;
}

static void *responder_conn(void *arg)
{
    int fd = (int)(intptr_t)arg;
    sock_setup(fd, 5);
    session_t *s = handshake_responder(fd);
    if (s) {
        session_install(s);
        LOG("session established (responder)");
        struct timeval tv = { 0, 0 };
        setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
        char b;
        while (recv(fd, &b, 1, 0) > 0) { }
    } else {
        LOG("handshake failed");
    }
    close(fd);
    return NULL;
}

static void responder_loop(const char *bind_ip, int port)
{
    int ls = socket(AF_INET, SOCK_STREAM, 0), on = 1;
    struct sockaddr_in a = { .sin_family = AF_INET, .sin_port = htons((uint16_t)port) };
    setsockopt(ls, SOL_SOCKET, SO_REUSEADDR, &on, sizeof on);
    if (inet_pton(AF_INET, bind_ip, &a.sin_addr) != 1 ||
        bind(ls, (struct sockaddr *)&a, sizeof a) < 0 || listen(ls, 8) < 0) {
        LOG("listen failed: %s", strerror(errno)); exit(1);
    }
    for (;;) {
        int fd = accept(ls, NULL, NULL);
        if (fd < 0) { if (errno == EINTR) continue; sleep(1); continue; }
        pthread_t t;
        if (pthread_create(&t, NULL, responder_conn, (void *)(intptr_t)fd) == 0) pthread_detach(t);
        else close(fd);
    }
}

static void usage(const char *p)
{
    fprintf(stderr, "usage: %s -m init|resp -k pskfile [-a peer_ip|bind_ip] [-p port] [-E encq] [-D decq]\n", p);
    exit(2);
}

int main(int argc, char **argv)
{
    int init = -1, port = 9000, encq = 0, decq = 1, opt;
    const char *addr = NULL, *pskfile = NULL;

    while ((opt = getopt(argc, argv, "m:a:p:k:E:D:")) != -1) {
        switch (opt) {
        case 'm': init = !strcmp(optarg, "init") ? 1 : !strcmp(optarg, "resp") ? 0 : -1; break;
        case 'a': addr = optarg; break;
        case 'p': port = atoi(optarg); break;
        case 'k': pskfile = optarg; break;
        case 'E': encq = atoi(optarg); break;
        case 'D': decq = atoi(optarg); break;
        default: usage(argv[0]);
        }
    }
    if (init < 0 || !pskfile || (init && !addr)) usage(argv[0]);

    FILE *f = fopen(pskfile, "rb");
    if (!f) { perror("psk"); return 1; }
    g_psk_len = fread(g_psk, 1, sizeof g_psk, f);
    fclose(f);
    if (g_psk_len < 16) { LOG("PSK must be at least 16 bytes"); return 1; }

    signal(SIGPIPE, SIG_IGN);

    static qctx_t qe, qd;
    qe = (qctx_t){ MODE_ENC, encq };
    qd = (qctx_t){ MODE_DEC, decq };
    pthread_t t1, t2, t3;
    pthread_create(&t1, NULL, queue_thread, &qe);
    pthread_create(&t2, NULL, queue_thread, &qd);

    if (init) {
        g_peer.sin_family = AF_INET;
        g_peer.sin_port = htons((uint16_t)port);
        if (inet_pton(AF_INET, addr, &g_peer.sin_addr) != 1) usage(argv[0]);
        pthread_create(&t3, NULL, initiator_thread, NULL);
        pthread_join(t3, NULL);
    } else {
        responder_loop(addr ? addr : "0.0.0.0", port);
    }
    return 0;
}
