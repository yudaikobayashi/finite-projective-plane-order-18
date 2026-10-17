// Independent reproduction (from the paper alone). Parametrised in p (runtime), p<=17.
// Usage:
//   indep2 P fam
//   indep2 P classes OUTFILE
//   indep2 P run CLASSFILE OUTFILE [from to]      (resumable; one line per class)
//   indep2 P allnets CLASSFILE                    (all p*|Orth0| orthomorphisms: counts cliques; for small p)
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
#include <array>
#include <algorithm>
#include <string>
#include <set>
#include <map>
#include <chrono>
#include <immintrin.h>
#include <omp.h>
using namespace std;
typedef uint32_t u32;
typedef uint64_t u64;

static int P, NN, NCLS;
static u32 FULL;

static inline u32 rotm(u32 B, int s) { return (u32)((((u64)B >> s) | ((u64)B << (P - s))) & FULL); }
static inline int cls(int d) { d %= P; if (d < 0) d += P; return d <= P - d ? d : P - d; }  // 1..(P-1)/2

// ---------------------------------------------------------------- families
// Families are stored as a trie of blocks (blocks listed by increasing minimal element; block 0 contains 1).
struct TNode {
    u32 bm;
    uint16_t blk;       // id of the block (as a subset)
    uint8_t depth;      // index of this block in the family
    uint8_t bs;
    uint8_t el[4];
    int firstChild, nextSib;
    int dpos;           // offset into DPOOL: D(j, depth) for j<depth, D = {y-x : x in B_j, y in B_depth}
};
static vector<TNode> TR;
static vector<u32> DPOOL;
static map<pair<int, u32>, int> TCH;
static map<u32, int> BLKID;
static vector<u32> BLKMASK;
static long long famLeaves = 0;
static size_t FAMS_size_dummy = 0;
struct FamsStub { size_t size() const { return famLeaves; } } FAMS;
static long long famTotal = 0;
static long long famTypeCnt[4] = {0, 0, 0, 0};   // by type (n4,n3,n2,n1) index
static long long famViableType[4] = {0, 0, 0, 0};

static int ORDERMODE = 0;
static void finishFamily(const vector<vector<int>>& blocks0) {
    vector<vector<int>> blocks = blocks0;
    // order: block containing 1 first, then by size desc, then min element
    sort(blocks.begin(), blocks.end(), [](const vector<int>& a, const vector<int>& b) {
        bool a1 = (a[0] == 1), b1 = (b[0] == 1);
        if (a1 != b1) return a1;
        if (a.size() != b.size()) return a.size() > b.size();
        return a[0] < b[0];
    });
    // classify type
    int n[5] = {0, 0, 0, 0, 0};
    for (auto& b : blocks) n[b.size()]++;
    int ty = -1;
    if (n[4] == 0 && n[3] == 0) ty = 0;            // (0,0,8,0)
    else if (n[4] == 0 && n[3] == 1) ty = 1;
    else if (n[4] == 0 && n[3] == 2) ty = 2;
    else if (n[4] == 1) ty = 3;
    // For p != 17 types are just counted in 4 buckets by (n4>0, n3) - informational.
    famTotal++;
    if (ty >= 0) famTypeCnt[ty]++;
    // viability: for every two blocks the cross differences y-x must be pairwise distinct (R4, column independent)
    size_t nb = blocks.size();
    if (nb > 12) { fprintf(stderr, "too many blocks\n"); exit(1); }
    vector<u32> Dm;
    for (size_t k = 0; k < nb; k++) {
        if (blocks[k].size() > 4) { fprintf(stderr, "block too big\n"); exit(1); }
        for (size_t j = 0; j < k; j++) {
            u32 m = 0;
            for (int x : blocks[j])
                for (int y : blocks[k]) {
                    int d = ((y - x) % P + P) % P;
                    if (m >> d & 1) return;
                    m |= 1u << d;
                }
            Dm.push_back(m);
        }
    }
    if (ty >= 0) famViableType[ty]++;
    famLeaves++;
    // insert into trie
    int cur = 0;
    size_t dp = 0;
    for (size_t k = 0; k < nb; k++) {
        u32 bm = 0;
        for (int x : blocks[k]) bm |= 1u << x;
        auto key = make_pair(cur, bm);
        auto it = TCH.find(key);
        if (it != TCH.end()) { cur = it->second; dp += k; continue; }
        TNode nd;
        memset(&nd, 0, sizeof nd);
        nd.bm = bm;
        auto bi = BLKID.find(bm);
        if (bi == BLKID.end()) { int id = BLKMASK.size(); BLKID[bm] = id; BLKMASK.push_back(bm); nd.blk = id; }
        else nd.blk = bi->second;
        nd.depth = k;
        nd.bs = blocks[k].size();
        for (size_t t = 0; t < blocks[k].size(); t++) nd.el[t] = blocks[k][t];
        nd.firstChild = -1;
        nd.nextSib = TR[cur].firstChild;
        nd.dpos = DPOOL.size();
        for (size_t j = 0; j < k; j++) DPOOL.push_back(Dm[dp + j]);
        int id = TR.size();
        TR.push_back(nd);
        TR[cur].firstChild = id;
        TCH[key] = id;
        cur = id;
        dp += k;
    }
}

static void famDfs(u32 uncovered, u32 usedCls, vector<vector<int>>& blocks);

static void blockExtend(u32 uncovered, u32 usedCls, vector<int>& blk, int last, vector<vector<int>>& blocks) {
    // blk currently valid (classes already accounted in usedCls); try to close or extend
    u32 rest = uncovered;
    for (int b : blk) rest &= ~(1u << b);
    blocks.push_back(blk);
    famDfs(rest, usedCls, blocks);
    blocks.pop_back();
    for (int e = last + 1; e < P; e++) {
        if (!(uncovered >> e & 1)) continue;
        u32 nc = usedCls;
        bool ok = true;
        for (int z : blk) {
            int c = cls(e - z);
            if (nc >> c & 1) { ok = false; break; }
            nc |= 1u << c;
        }
        if (!ok) continue;
        blk.push_back(e);
        blockExtend(uncovered, nc, blk, e, blocks);
        blk.pop_back();
    }
}
static void famDfs(u32 uncovered, u32 usedCls, vector<vector<int>>& blocks) {
    if (uncovered == 0) {
        // all classes must be used
        u32 all = 0;
        for (int c = 1; c <= NCLS; c++) all |= 1u << c;
        if (usedCls == all) finishFamily(blocks);
        return;
    }
    int m = __builtin_ctz(uncovered);
    vector<int> blk = {m};
    blockExtend(uncovered, usedCls, blk, m, blocks);
}
static void buildFamilies() {
    TR.clear(); DPOOL.clear(); TCH.clear(); BLKID.clear(); BLKMASK.clear();
    famLeaves = 0;
    { TNode r; memset(&r, 0, sizeof r); r.firstChild = -1; r.nextSib = -1; TR.push_back(r); }
    famTotal = 0;
    for (int i = 0; i < 4; i++) famTypeCnt[i] = famViableType[i] = 0;
    vector<vector<int>> blocks;
    u32 unc = 0;
    for (int x = 1; x < P; x++) unc |= 1u << x;
    famDfs(unc, 0, blocks);
}

// ---------------------------------------------------------------- rows
struct alignas(32) Row {
    uint8_t sz[32];
    uint8_t g[16];
    uint8_t u1, u2;
    uint8_t pad[14];
};

struct Gen {
    int th[17];
    int c;
    vector<Row>* out;
    int colOf[12];
    int path[12];
    int dm[17][17];     // (a-b) mod P
    int dth[17][17];    // (th[a]-th[b]) mod P
    vector<array<u32, 24>> rotA, rotB;
    void init() {
        for (int a = 0; a < P; a++)
            for (int b = 0; b < P; b++) {
                dm[a][b] = ((a - b) % P + P) % P;
                dth[a][b] = ((th[a] - th[b]) % P + P) % P;
            }
        rotA.assign(BLKMASK.size(), array<u32, 24>());
        rotB.assign(BLKMASK.size(), array<u32, 24>());
        for (size_t i = 0; i < BLKMASK.size(); i++)
            for (int a = 0; a < P; a++) { rotA[i][a] = rotm(BLKMASK[i], a); rotB[i][a] = rotm(BLKMASK[i], th[a]); }
    }
    void emit(int depthLast, u32 A, u32 B) {
        Row r;
        memset(&r, 0, sizeof(r));
        for (int i = 0; i < 16; i++) r.g[i] = 0xF0 + i;
        for (int kk = 0; kk <= depthLast; kk++) {
            const TNode& nd = TR[path[kk]];
            r.sz[colOf[kk]] = nd.bs;
            for (int t = 0; t < nd.bs; t++) r.g[nd.el[t] - 1] = colOf[kk];
        }
        r.u1 = __builtin_ctz(~A & FULL);
        r.u2 = __builtin_ctz(~B & FULL);
        out->push_back(r);
    }
    // children of 'node' are blocks with index k
    void rec(int node, int k, u32 usedCols, u32 A, u32 B) {
        for (int ch = TR[node].firstChild; ch >= 0; ch = TR[ch].nextSib) {
            const TNode& nd = TR[ch];
            const u32* Dp = &DPOOL[nd.dpos];
            const array<u32, 24>& RA = rotA[nd.blk];
            const array<u32, 24>& RB = rotB[nd.blk];
            u32 feas = 0;
            {
                __m256i vA = _mm256_set1_epi32((int)A), vB = _mm256_set1_epi32((int)B), z = _mm256_setzero_si256();
                for (int q = 0; q < 3; q++) {
                    __m256i ra = _mm256_loadu_si256((const __m256i*)(RA.data() + 8 * q));
                    __m256i rb = _mm256_loadu_si256((const __m256i*)(RB.data() + 8 * q));
                    __m256i okv = _mm256_and_si256(_mm256_cmpeq_epi32(_mm256_and_si256(ra, vA), z),
                                                   _mm256_cmpeq_epi32(_mm256_and_si256(rb, vB), z));
                    feas |= (u32)_mm256_movemask_ps(_mm256_castsi256_ps(okv)) << (8 * q);
                }
                feas &= FULL & ~usedCols;
                if (k == 0) feas &= (1u << c);
            }
            while (feas) {
                int a = __builtin_ctz(feas);
                feas &= feas - 1;
                u32 ra = RA[a];
                u32 rb = RB[a];
                bool ok = true;
                for (int j = 0; j < k; j++) {
                    int be = colOf[j];
                    u32 D = Dp[j];
                    if ((D >> dm[a][be] & 1) || (D >> dth[a][be] & 1)) { ok = false; break; }
                }
                if (!ok) continue;
                colOf[k] = a;
                path[k] = ch;
                if (nd.firstChild < 0) emit(k, A | ra, B | rb);
                else rec(ch, k + 1, usedCols | (1u << a), A | ra, B | rb);
            }
        }
    }
};

static void genBucket(const int* th, int c, vector<Row>& out) {
    out.clear();
    Gen* G = new Gen();
    memcpy(G->th, th, sizeof(int) * P);
    G->c = c;
    G->out = &out;
    G->init();
    G->rec(0, 0, 0, 0, 0);
    delete G;
}

// ---------------------------------------------------------------- compatibility
static inline int dotsz(const Row& a, const Row& b) {
    __m256i x = _mm256_load_si256((const __m256i*)a.sz), y = _mm256_load_si256((const __m256i*)b.sz);
    __m256i m = _mm256_maddubs_epi16(x, y);
    __m256i s = _mm256_madd_epi16(m, _mm256_set1_epi16(1));
    __m128i l = _mm_add_epi32(_mm256_castsi256_si128(s), _mm256_extracti128_si256(s, 1));
    l = _mm_hadd_epi32(l, l);
    l = _mm_hadd_epi32(l, l);
    return _mm_cvtsi128_si32(l);
}
static inline bool quickOK(const Row& a, const Row& b, int need, int lanemask) {
    if (dotsz(a, b) != need) return false;
    __m128i x = _mm_load_si128((const __m128i*)a.g), y = _mm_load_si128((const __m128i*)b.g);
    int m = _mm_movemask_epi8(_mm_cmpeq_epi8(x, y)) & lanemask;
    return m == 0;
}
static bool compatFull(const Row& a, const Row& b) {
    int d1 = (a.u1 - b.u1 + P) % P, d2 = (a.u2 - b.u2 + P) % P;
    if (d1 == 0 || d2 == 0 || d1 == d2) return false;
    // (C1)
    u32 seen = 0;
    int cnt = 0;
    for (int x = 1; x < P; x++)
        for (int x2 = 1; x2 < P; x2++)
            if (a.g[x - 1] == b.g[x2 - 1]) {
                int d = (x - x2 + P) % P;
                if (seen >> d & 1) return false;
                seen |= 1u << d;
                cnt++;
            }
    u32 forb = 1u | (1u << d1) | (1u << d2);
    if (seen & forb) return false;
    if (cnt != P - 3) return false;
    // (C2)
    static thread_local u32 Ma[17][17], Mb[17][17];
    memset(Ma, 0, sizeof(Ma));
    memset(Mb, 0, sizeof(Mb));
    for (int x = 1; x < P; x++)
        for (int y = 1; y < P; y++) {
            int ga = a.g[x - 1], gb = a.g[y - 1];
            if (ga != gb) Ma[ga][gb] |= 1u << ((y - x + P) % P);
            ga = b.g[x - 1]; gb = b.g[y - 1];
            if (ga != gb) Mb[ga][gb] |= 1u << ((y - x + P) % P);
        }
    for (int al = 0; al < P; al++)
        for (int be = 0; be < P; be++)
            if (al != be && (Ma[al][be] & Mb[al][be])) return false;
    return true;
}

static long long cliqueCount(vector<vector<const Row*>>& lists, vector<char>& active, int need, int lanemask) {
    int best = -1;
    size_t bs = 1u << 30;
    for (size_t i = 0; i < lists.size(); i++)
        if (active[i] && lists[i].size() < bs) { bs = lists[i].size(); best = i; }
    if (best < 0) return 1;
    long long total = 0;
    active[best] = 0;
    for (const Row* h : lists[best]) {
        vector<vector<const Row*>> nl(lists.size());
        bool ok = true;
        for (size_t i = 0; i < lists.size() && ok; i++) {
            if (!active[i]) continue;
            for (const Row* r : lists[i])
                if (quickOK(*h, *r, need, lanemask) && compatFull(*h, *r)) nl[i].push_back(r);
            if (nl[i].empty()) ok = false;
        }
        if (ok) total += cliqueCount(nl, active, need, lanemask);
    }
    active[best] = 1;
    return total;
}

// structure-of-arrays copy of the cell-size vectors of a bucket, to test sum_alpha |C||C'| = P-3 for 32 rows at once
struct SoA {
    size_t n = 0, nblk = 0;
    uint8_t* T[17];
    void build(const vector<Row>& H) {
        n = H.size();
        nblk = (n + 31) / 32;
        for (int a = 0; a < P; a++) {
            T[a] = (uint8_t*)_mm_malloc(nblk * 32 + 32, 32);
            memset(T[a], 0, nblk * 32 + 32);
        }
        for (size_t i = 0; i < n; i++)
            for (int a = 0; a < P; a++) T[a][i] = H[i].sz[a];
    }
    void release() { for (int a = 0; a < P; a++) _mm_free(T[a]); }
};
static bool existsCompat(const Row& g, const SoA& S, const vector<Row>& H, int need, int lanemask) {
    int L[5][17], nl[5] = {0, 0, 0, 0, 0};
    for (int a = 0; a < P; a++) {
        int s = g.sz[a];
        if (s) L[s][nl[s]++] = a;
    }
    __m256i vneed = _mm256_set1_epi8((char)need);
    for (size_t b = 0; b < S.nblk; b++) {
        __m256i s1 = _mm256_setzero_si256(), s2 = s1, s3 = s1, s4 = s1;
        for (int i = 0; i < nl[1]; i++) s1 = _mm256_add_epi8(s1, _mm256_load_si256((const __m256i*)(S.T[L[1][i]] + 32 * b)));
        for (int i = 0; i < nl[2]; i++) s2 = _mm256_add_epi8(s2, _mm256_load_si256((const __m256i*)(S.T[L[2][i]] + 32 * b)));
        for (int i = 0; i < nl[3]; i++) s3 = _mm256_add_epi8(s3, _mm256_load_si256((const __m256i*)(S.T[L[3][i]] + 32 * b)));
        for (int i = 0; i < nl[4]; i++) s4 = _mm256_add_epi8(s4, _mm256_load_si256((const __m256i*)(S.T[L[4][i]] + 32 * b)));
        __m256i acc = _mm256_add_epi8(_mm256_add_epi8(s1, _mm256_add_epi8(s2, s2)),
                                      _mm256_add_epi8(_mm256_add_epi8(s3, _mm256_add_epi8(s3, s3)), _mm256_slli_epi16(_mm256_and_si256(s4, _mm256_set1_epi8(0x3F)), 2)));
        u32 m = (u32)_mm256_movemask_epi8(_mm256_cmpeq_epi8(acc, vneed));
        while (m) {
            int bit = __builtin_ctz(m);
            m &= m - 1;
            size_t idx = b * 32 + bit;
            if (idx >= S.n) break;
            const Row& h = H[idx];
            __m128i x = _mm_load_si128((const __m128i*)g.g), y = _mm_load_si128((const __m128i*)h.g);
            if (_mm_movemask_epi8(_mm_cmpeq_epi8(x, y)) & lanemask) continue;
            if (compatFull(g, h)) return true;
        }
    }
    return false;
}

struct NetResult {
    long long nb[4];
    long long a[4];
    long long cliques;
    int rowsTotalGenerated;
};

static NetResult runNet(const int* th, bool fullCount) {
    NetResult R;
    for (int i = 0; i < 4; i++) { R.nb[i] = -1; R.a[i] = 0; }
    R.cliques = 0;
    int need = P - 3;
    int lanemask = (1 << (P - 1)) - 1;
    vector<vector<Row>> B(P);
    genBucket(th, 0, B[0]);
    R.nb[0] = B[0].size();
    vector<const Row*> cand;
    for (auto& r : B[0]) cand.push_back(&r);
    int lastc = 0;
    for (int c = 1; c < P && !cand.empty(); c++) {
        auto tg0 = chrono::steady_clock::now();
        genBucket(th, c, B[c]);
        if (getenv("INDEP2_PROF")) fprintf(stderr, "gen c=%d %.2fs cand=%zu\n", c, chrono::duration<double>(chrono::steady_clock::now() - tg0).count(), cand.size());
        if (c < 4) R.nb[c] = B[c].size();
        vector<const Row*> nc;
        {
            SoA S;
            S.build(B[c]);
            for (const Row* g : cand)
                if (existsCompat(*g, S, B[c], need, lanemask)) nc.push_back(g);
            S.release();
        }
        cand.swap(nc);
        if (c < 4) R.a[c] = cand.size();
        lastc = c;
    }
    if (!cand.empty() || fullCount) {
        // all buckets generated if cand survived to the end
        for (int c = 1; c < P; c++)
            if (B[c].empty() && lastc < c) genBucket(th, c, B[c]);
        vector<const Row*> c0;
        if (fullCount) for (auto& r : B[0]) c0.push_back(&r); else c0 = cand;
        for (const Row* g0 : c0) {
            vector<vector<const Row*>> lists(P);
            vector<char> active(P, 0);
            bool ok = true;
            for (int c = 1; c < P && ok; c++) {
                active[c] = 1;
                for (const Row& h : B[c])
                    if (quickOK(*g0, h, need, lanemask) && compatFull(*g0, h)) lists[c].push_back(&h);
                if (lists[c].empty()) ok = false;
            }
            if (ok) R.cliques += cliqueCount(lists, active, need, lanemask);
        }
    }
    return R;
}

// ---------------------------------------------------------------- orthomorphisms and classes
static vector<array<int, 4>> LM;  // (a,b,c,d): (x,y)->(a x+b y, c x+d y)
static void buildLinear() {
    set<array<int, 4>> S;
    vector<array<int, 4>> gens;
    for (int m = 1; m < P; m++) gens.push_back({m, 0, 0, m});
    gens.push_back({0, 1, 1, 0});
    gens.push_back({(P - 1) % P, 0, (P - 1) % P, 1});   // (x,y)->(-x, y-x)
    vector<array<int, 4>> q = {{1, 0, 0, 1}};
    S.insert(q[0]);
    for (size_t i = 0; i < q.size(); i++)
        for (auto& g : gens) {
            auto a = q[i];
            // new = g * a
            array<int, 4> r = {(g[0] * a[0] + g[1] * a[2]) % P, (g[0] * a[1] + g[1] * a[3]) % P,
                               (g[2] * a[0] + g[3] * a[2]) % P, (g[2] * a[1] + g[3] * a[3]) % P};
            if (!S.count(r)) { S.insert(r); q.push_back(r); }
        }
    LM = q;
}
// returns true if theta is lexicographically minimal in its class
static bool isCanonical(const int* th) {
    int X[17], Y[17];
    for (auto& L : LM) {
        for (int j = 0; j < P; j++) {
            X[j] = (L[0] * j + L[1] * th[j]) % P;
            Y[j] = (L[2] * j + L[3] * th[j]) % P;
        }
        for (int i = 0; i < P; i++) {
            int T[17];
            for (int j = 0; j < P; j++) T[((X[j] - X[i]) % P + P) % P] = ((Y[j] - Y[i]) % P + P) % P;
            for (int x = 1; x < P; x++) {
                if (T[x] < th[x]) return false;
                if (T[x] > th[x]) break;
            }
        }
    }
    return true;
}
static int orbitSize(const int* th) {
    set<array<uint8_t, 16>> S;
    int X[17], Y[17];
    for (auto& L : LM) {
        for (int j = 0; j < P; j++) {
            X[j] = (L[0] * j + L[1] * th[j]) % P;
            Y[j] = (L[2] * j + L[3] * th[j]) % P;
        }
        for (int i = 0; i < P; i++) {
            int T[17];
            for (int j = 0; j < P; j++) T[((X[j] - X[i]) % P + P) % P] = ((Y[j] - Y[i]) % P + P) % P;
            array<uint8_t, 16> v;
            v.fill(0);
            for (int x = 1; x < P; x++) v[x - 1] = T[x];
            S.insert(v);
        }
    }
    return S.size();
}
struct Prefix { int v[3]; };
static void orthDfs(int x, int* th, u32 usedV, u32 usedD, int maxx, long long& cnt, vector<array<int, 17>>& reps) {
    if (x == P) {
        cnt++;
        if (isCanonical(th)) { array<int, 17> a; for (int i = 0; i < P; i++) a[i] = th[i]; for (int i = P; i < 17; i++) a[i] = 0; reps.push_back(a); }
        return;
    }
    for (int v = 1; v < P; v++) {
        if (usedV >> v & 1) continue;
        int d = ((v - x) % P + P) % P;
        if (usedD >> d & 1) continue;
        th[x] = v;
        orthDfs(x + 1, th, usedV | (1u << v), usedD | (1u << d), maxx, cnt, reps);
    }
}
static void doClasses(const char* outfile) {
    buildLinear();
    fprintf(stderr, "linear group size %zu (expect %d)\n", LM.size(), 6 * (P - 1));
    // prefixes th[1], th[2]
    vector<array<int, 2>> pre;
    for (int a = 1; a < P; a++) {
        if (((a - 1) % P + P) % P == 0) continue;  // theta(1)-1 != 0 (diff 0 used by x=0)
        for (int b = 1; b < P; b++) {
            if (b == a) continue;
            int d1 = ((a - 1) % P + P) % P, d2 = ((b - 2) % P + P) % P;
            if (d2 == 0 || d2 == d1) continue;
            pre.push_back({a, b});
        }
    }
    if (P == 3) { pre.clear(); }
    long long total = 0;
    vector<array<int, 17>> allreps;
    if (P == 3) {
        int th[17] = {0};
        long long cnt = 0;
        vector<array<int, 17>> reps;
        orthDfs(1, th, 1u, 1u, P, cnt, reps);
        total = cnt;
        allreps = reps;
    } else {
#pragma omp parallel for schedule(dynamic, 1) num_threads(12)
        for (int pi = 0; pi < (int)pre.size(); pi++) {
            int th[17] = {0};
            th[1] = pre[pi][0];
            th[2] = pre[pi][1];
            u32 uv = 1u | (1u << th[1]) | (1u << th[2]);
            u32 ud = 1u | (1u << ((th[1] - 1 + P) % P)) | (1u << ((th[2] - 2 + P) % P));
            long long cnt = 0;
            vector<array<int, 17>> reps;
            orthDfs(3, th, uv, ud, P, cnt, reps);
#pragma omp critical
            {
                total += cnt;
                allreps.insert(allreps.end(), reps.begin(), reps.end());
            }
        }
    }
    fprintf(stderr, "dfs done %zu\n", allreps.size());
    {
        long long cs = 0;
        for (auto& a : allreps)
            for (int i = 0; i < 17; i++) {
                if (a[i] < 0 || a[i] >= 17) fprintf(stderr, "bad entry\n");
                cs += a[i];
            }
        fprintf(stderr, "checksum %lld\n", cs);
    }
    {
        vector<string> ks;
        for (auto& a : allreps) {
            string s;
            for (int i = 0; i < 17; i++) s.push_back((char)(a[i] + 1));
            ks.push_back(s);
        }
        fprintf(stderr, "keys\n");
        sort(ks.begin(), ks.end());
        for (size_t i = 0; i < ks.size(); i++)
            for (int j = 0; j < 17; j++) allreps[i][j] = ks[i][j] - 1;
    }
    fprintf(stderr, "sorted\n");
    printf("p=%d |Orth0|=%lld  classes=%zu\n", P, total, allreps.size());
    FILE* f = fopen(outfile, "w");
    long long sum = 0;
    map<int, pair<int, long long>> hist;
    vector<int> osz(allreps.size());
#pragma omp parallel for schedule(dynamic, 64) num_threads(12)
    for (int i = 0; i < (int)allreps.size(); i++) osz[i] = orbitSize(allreps[i].data());
    for (size_t i = 0; i < allreps.size(); i++) {
        fprintf(f, "%zu", i);
        for (int x = 1; x < P; x++) fprintf(f, " %d", allreps[i][x]);
        fprintf(f, " %d\n", osz[i]);
        sum += osz[i];
        hist[osz[i]].first++;
        hist[osz[i]].second += osz[i];
    }
    fclose(f);
    printf("orbit-size sum=%lld (should equal |Orth0|)\n", sum);
    for (auto& kv : hist) printf("  size %d : %d classes, total %lld\n", kv.first, kv.second.first, kv.second.second);
}

struct NetDef { int id; int th[17]; int orbit; };
static vector<NetDef> loadClasses(const char* fn) {
    vector<NetDef> v;
    FILE* f = fopen(fn, "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    while (true) {
        NetDef n;
        memset(&n, 0, sizeof(n));
        if (fscanf(f, "%d", &n.id) != 1) break;
        n.th[0] = 0;
        for (int x = 1; x < P; x++) fscanf(f, "%d", &n.th[x]);
        fscanf(f, "%d", &n.orbit);
        v.push_back(n);
    }
    fclose(f);
    return v;
}

int main(int argc, char** argv) {
    if (argc < 3) { fprintf(stderr, "usage\n"); return 1; }
    P = atoi(argv[1]);
    NN = P - 1;
    NCLS = (P - 1) / 2;
    FULL = (1u << P) - 1;
    string mode = argv[2];
    if (mode == "classes") { doClasses(argv[3]); return 0; }
    buildFamilies();
    printf("p=%d families=%lld  by type (0,0,..)/(.,1,..)/(.,2,..)/(n4=1): %lld %lld %lld %lld ; viable(pairwise-distinct block diffs)=%zu (by type %lld %lld %lld %lld)\n",
           P, famTotal, famTypeCnt[0], famTypeCnt[1], famTypeCnt[2], famTypeCnt[3], FAMS.size(),
           famViableType[0], famViableType[1], famViableType[2], famViableType[3]);
    fflush(stdout);
    if (mode == "fam") return 0;
    vector<NetDef> nets;
    if (string(argv[3]) == "ALL") {
        // all normalised orthomorphisms (small p only)
        buildLinear();
        vector<array<int, 17>> reps;
        long long cnt = 0;
        int th[17] = {0};
        // reuse orthDfs but collect everything: temporarily treat all as canonical via direct enumeration
        struct Rec {
            static void go(int x, int* th, u32 uv, u32 ud, vector<array<int, 17>>& out) {
                if (x == P) { array<int, 17> a; a.fill(0); for (int i = 0; i < P; i++) a[i] = th[i]; out.push_back(a); return; }
                for (int v = 1; v < P; v++) {
                    if (uv >> v & 1) continue;
                    int d = ((v - x) % P + P) % P;
                    if (ud >> d & 1) continue;
                    th[x] = v;
                    go(x + 1, th, uv | (1u << v), ud | (1u << d), out);
                }
            }
        };
        Rec::go(1, th, 1u, 1u, reps);
        (void)cnt;
        for (size_t i = 0; i < reps.size(); i++) { NetDef n; memset(&n, 0, sizeof n); n.id = i; for (int x = 0; x < P; x++) n.th[x] = reps[i][x]; nets.push_back(n); }
        printf("ALL normalised orthomorphisms: %zu\n", nets.size());
    } else nets = loadClasses(argv[3]);
    if (mode == "allnets") {
        // all p*|Orth0| orthomorphisms theta0+b, with full clique counting
        long long totalSol = 0, netsWith = 0, nnets = 0;
        for (auto& n : nets)
            for (int b = 0; b < P; b++) {
                int th[17];
                for (int x = 0; x < P; x++) th[x] = (n.th[x] + b) % P;
                // note: the list "classes" only has representatives; for p<=7 call with the full normalised list
                NetResult r = runNet(th, true);
                nnets++;
                totalSol += r.cliques;
                if (r.cliques) netsWith++;
            }
        printf("allnets over given list x shifts: nets=%lld nets_with_solutions=%lld solutions=%lld\n", nnets, netsWith, totalSol);
        return 0;
    }
    if (mode == "run") {
        const char* outfn = argv[4];
        int from = 0, to = (int)nets.size();
        if (argc > 6) { from = atoi(argv[5]); to = atoi(argv[6]); }
        set<int> done;
        {
            FILE* f = fopen(outfn, "r");
            if (f) {
                char line[512];
                while (fgets(line, sizeof line, f)) { int id; if (sscanf(line, "%d", &id) == 1) done.insert(id); }
                fclose(f);
            }
        }
        printf("already done: %zu\n", done.size());
        FILE* out = fopen(outfn, "a");
        vector<int> todo;
        for (int i = from; i < to && i < (int)nets.size(); i++) if (!done.count(nets[i].id)) todo.push_back(i);
        auto t0 = chrono::steady_clock::now();
        int nd = 0;
        bool fullCount = (P <= 13);
#pragma omp parallel for schedule(dynamic, 1) num_threads(12)
        for (int ti = 0; ti < (int)todo.size(); ti++) {
            const NetDef& n = nets[todo[ti]];
            auto s = chrono::steady_clock::now();
            NetResult r = runNet(n.th, fullCount);
            double sec = chrono::duration<double>(chrono::steady_clock::now() - s).count();
#pragma omp critical
            {
                fprintf(out, "%d %lld %lld %lld %lld %lld %lld %lld %lld %.2f\n", n.id, r.nb[0], r.nb[1], r.nb[2], r.nb[3], r.a[1], r.a[2], r.a[3], r.cliques, sec);
                fflush(out);
                nd++;
                if (nd % 200 == 0) {
                    double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
                    printf("done %d/%zu elapsed %.0fs\n", nd, todo.size(), el);
                    fflush(stdout);
                }
            }
        }
        fclose(out);
        printf("finished\n");
    }
    return 0;
}
