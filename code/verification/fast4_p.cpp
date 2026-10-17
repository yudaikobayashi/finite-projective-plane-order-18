// PARAMETRISED COPY of fast4.cpp (64-bit masks; SIMD widths derived from P; P<=63). Original untouched.
// Added: mode "ctl" (single net + explicit family list, prints cliques) and FAMFILE-free production paths otherwise.
// Fast exact-cover search per net (order p+1 triangle reduction).  -DP=7 or 17
// usage: fast netsfile start end outfile [mode]  (mode: run|norowfilter)
#include <bits/stdc++.h>
#include <omp.h>
#include <immintrin.h>
#include <mutex>
using namespace std; typedef unsigned long long u64; typedef u64 u32; typedef u64 M; // NOTE: u32 is kept as a name but is 64-bit here (masks)
#ifndef P
#define P 17
#endif
const u32 FULL=(1ull<<P)-1; static_assert(P<=63,"64-bit masks");
const int NX=P-1, NCL=(P-1)/2; const int NCLW=(P*NCL+63)/64; const int CW=((P+31)/32)*32; const int GW=((NX+15)/16)*16; const int NQ=(P+1)/2; const u32 XALL=FULL&~1ull;
static inline u32 rot(u32 m,int a){ return a? (((m>>a)|(m<<(P-a)))&FULL):m; }
static inline int md(int v){ v%=P; return v<0?v+P:v; }
static bool NOROWFILTER=false;
static thread_local long C1=0,C2=0,C3=0; static thread_local long FIN=0,DN=0,TN_=0,KC=0;
struct Fam{ vector<u32> nb; u32 sing; };
vector<Fam> fams;
void genfam(){
  vector<u32> bl;
  function<void(u32,u32)> rec=[&](u32 placed,u32 usedc){
    if(placed==XALL){ if(usedc==(1ull<<(NCL+1))-2){ Fam f; u32 s=0; for(u32 b:bl){ if(__builtin_popcountll(b)>=2) f.nb.push_back(b); else s|=b; } f.sing=s; fams.push_back(f);} return; }
    int x=__builtin_ctzll(XALL&~placed);
    bl.push_back(1ull<<x); rec(placed|(1ull<<x),usedc); bl.pop_back();
    u32 fa=XALL&~placed&~((2ull<<x)-1); vector<int> el; for(u32 m=fa;m;m&=m-1) el.push_back(__builtin_ctzll(m)); int n=el.size();
    auto tb=[&](int* B,int k){ u32 uc=usedc,mask=0; for(int i=0;i<k;i++){ mask|=1ull<<B[i]; for(int j=i+1;j<k;j++){ int d=(B[j]-B[i]+P)%P; d=min(d,P-d); if(uc&(1ull<<d)) return; uc|=1ull<<d; } } bl.push_back(mask); rec(placed|mask,uc); bl.pop_back(); };
    for(int i=0;i<n;i++){ int B[5]={x,el[i]}; tb(B,2); for(int j=i+1;j<n;j++){ B[2]=el[j]; tb(B,3); for(int k=j+1;k<n;k++){ B[3]=el[k]; tb(B,4); for(int l=k+1;l<n;l++){ B[4]=el[l]; tb(B,5);} } } }
  };
  rec(0,0);
}
static bool bsz(u32 a,u32 b){ int pa=__builtin_popcountll(a),pb=__builtin_popcountll(b); return pa!=pb?pa>pb:a<b; }
static inline u32 negm(u32 m){ u32 r=m&1; for(int i=1;i<P;i++) if(m>>i&1) r|=1ull<<(P-i); return r; }
struct Node{ u32 blk; vector<int> kids; vector<int> fl; u32 nb=0; };
struct Trie{ vector<Node> n; map<pair<int,u64>,int> idx; Trie(){ n.push_back({0,{},{}}); }
  int child(int v,u32 b){ auto k=make_pair(v,(u64)b); auto it=idx.find(k); if(it!=idx.end()) return it->second; n.push_back({b,{},{}}); int id=n.size()-1; n[v].kids.push_back(id); idx[k]=id; return id; } };
Trie TN[P], TS[P]; // TN[x]: x in nonsingleton block (placed first); TS[x]: x singleton
void buildTries(){
  for(int x=1;x<P;x++){
    for(size_t fi=0;fi<fams.size();fi++){ const Fam& f=fams[fi]; vector<u32> b=f.nb; int node=0;
      if(f.sing>>x&1){ sort(b.begin(),b.end(),bsz); for(u32 m:b) node=TS[x].child(node,m); TS[x].n[node].fl.push_back(fi); }
      else { u32 bx=0; for(u32 m:b) if(m>>x&1) bx=m; vector<u32> r; for(u32 m:b) if(m!=bx) r.push_back(m); sort(r.begin(),r.end(),bsz); node=TN[x].child(0,bx); for(u32 m:r) node=TN[x].child(node,m); TN[x].n[node].fl.push_back(fi); }
    }
  }
}

struct FNode{ u32 blk,nb,kb,fb; unsigned short nk,nf; };
struct FlatTrie{ vector<FNode> n; vector<u32> sing; };
FlatTrie FTN[P],FTS[P]; static bool flatDone[P]={0};
static FlatTrie flatten(const Trie& T){
  FlatTrie F; size_t N=T.n.size(); F.n.resize(N); vector<int> order; order.reserve(N); order.push_back(0); 
  vector<int> newid(N,-1); newid[0]=0; size_t head=0;
  while(head<order.size()){ int o=order[head]; int id=head; head++; const Node& nd=T.n[o];
    FNode& fn=F.n[id]; fn.blk=nd.blk; fn.nb=negm(nd.blk); fn.kb=order.size(); fn.nk=nd.kids.size();
    for(int k:nd.kids){ newid[k]=order.size(); order.push_back(k); }
    fn.fb=F.sing.size(); fn.nf=nd.fl.size(); for(int f:nd.fl) F.sing.push_back(fams[f].sing); }
  F.n.resize(order.size()); return F; }
void initNeg(){ for(int x=0;x<P;x++){ for(auto&n:TN[x].n) n.nb=negm(n.blk); for(auto&n:TS[x].n) n.nb=negm(n.blk);} }
// ---------- rows ----------
const int NCC=(P*(P-1)/2*P+63)/64;
int pairidx[P][P];
struct alignas(32) RowX{ unsigned char cn[CW]; unsigned char g[GW]; int u1,u2; u64 cls[NCLW]; u32 cellm[P]; u32 cellneg[P]; u64 cc[NCC]; };
struct Hot{ alignas(32) unsigned char cn[CW]; unsigned char g[GW]; };
// generic helpers replacing the fixed 16/32-byte SIMD loads
static inline int dotcn(const unsigned char* a,const unsigned char* b){ int cnt=0; for(int h=0;h<CW;h+=16){ __m128i x=_mm_loadu_si128((const __m128i*)(a+h)),y=_mm_loadu_si128((const __m128i*)(b+h)); __m128i m=_mm_maddubs_epi16(x,y); __m128i z=_mm_setzero_si128(); __m128i t=_mm_sad_epu8(_mm_packus_epi16(m,z),z); cnt+=_mm_cvtsi128_si32(t)+_mm_extract_epi16(t,4);} return cnt; }
static inline bool gEqAny(const unsigned char* a,const unsigned char* b){ for(int h=0;h<GW;h+=16){ unsigned mk=_mm_movemask_epi8(_mm_cmpeq_epi8(_mm_loadu_si128((const __m128i*)(a+h)),_mm_loadu_si128((const __m128i*)(b+h)))); int lim=NX-h; unsigned vm= lim>=16?0xFFFFu:(lim<=0?0u:((1u<<lim)-1)); if(mk&vm) return true; } return false; }
struct NetCtx{ int th[P]; u64 forbid[NCC]; };
bool prepRow(const unsigned char* g,int u1,int u2,const NetCtx& N,RowX& x){
  memset(&x,0,sizeof x); x.u1=u1; x.u2=u2; for(int t=0;t<NX;t++){ x.g[t]=g[t]; x.cellm[g[t]]|=1ull<<(t+1); x.cn[g[t]]++; x.cellneg[g[t]]|=1ull<<md(-(t+1)); }
  for(int c=0;c<P;c++){ u32 m=x.cellm[c]; for(u32 a=m;a;a&=a-1) for(u32 b=a&(a-1);b;b&=b-1){ int xa=__builtin_ctzll(a),xb=__builtin_ctzll(b); int d=md(xb-xa); d=min(d,P-d); int id=c*NCL+(d-1); x.cls[id>>6]|=1ull<<(id&63);} }
  for(int a=0;a<P;a++) for(int b=a+1;b<P;b++) for(u32 ma=x.cellm[a];ma;ma&=ma-1) for(u32 mb=x.cellm[b];mb;mb&=mb-1){ int d=md(__builtin_ctzll(mb)-__builtin_ctzll(ma)); int id=pairidx[a][b]*P+d; u64 bit=1ull<<(id&63); if(!NOROWFILTER){ if(x.cc[id>>6]&bit) return false; if(N.forbid[id>>6]&bit) return false; } x.cc[id>>6]|=bit; }
  return true;
}
static inline bool compat(const RowX& r,const RowX& s){
  if(dotcn(r.cn,s.cn)!=P-3) return false;
  if(gEqAny(r.g,s.g)) return false;
  for(int w=0;w<NCLW;w++) if(r.cls[w]&s.cls[w]) return false;
  u32 D=0; int cnt=0;
  for(int c=0;c<P;c++){ u32 a=r.cellm[c],b=s.cellm[c]; if(!a||!b) continue; for(u32 ma=a;ma;ma&=ma-1){ int xa=__builtin_ctzll(ma); for(u32 mb=b;mb;mb&=mb-1){ int d=md(xa-__builtin_ctzll(mb)); if((D>>d)&1) return false; D|=1ull<<d; cnt++; } } }
  if(cnt!=P-3||(D&1)) return false;
  u32 miss=XALL&~D; u32 want=(1ull<<md(r.u1-s.u1))|(1ull<<md(r.u2-s.u2));
  if(miss!=want||__builtin_popcountll(want)!=2) return false;
  for(int w=0;w<NCC;w++) if(r.cc[w]&s.cc[w]) return false;
  return true;
}

static inline u32 rotlm(u32 m,int a){ return a? (((m<<a)|(m>>(P-a)))&FULL):m; }
// tail of compat (after cn, g, cls tests): difference-distinctness, missing differences, cc disjointness
static inline bool compatTail(const RowX& r,const RowX& s){
  u32 D=0;
  for(int c=0;c<P;c++){ u32 a=r.cellm[c],bn=s.cellneg[c]; if(!a||!bn) continue; for(u32 ma=a;ma;ma&=ma-1){ u32 m=rotlm(bn,__builtin_ctzll(ma)); if(D&m) return false; D|=m; } }
  if(D&1) return false;
  u32 miss=XALL&~D; int d1=r.u1-s.u1; if(d1<0) d1+=P; int d2=r.u2-s.u2; if(d2<0) d2+=P; u32 want=(1ull<<d1)|(1ull<<d2);
  if(miss!=want||__builtin_popcountll(want)!=2) return false;
  for(int w=0;w<NCC;w++) if(r.cc[w]&s.cc[w]) return false;
  return true; }
static inline bool compatFull2(const RowX& r,const RowX& s){
  { int cnt=0; for(int c=0;c<P;c++) cnt+=r.cn[c]*s.cn[c]; if(cnt!=P-3) return false; }
  for(int t=0;t<NX;t++) if(r.g[t]==s.g[t]) return false;
  for(int w=0;w<NCLW;w++) if(r.cls[w]&s.cls[w]) return false;
  return compatTail(r,s); }
// ---------- bucket generation: rows with g(x)=c0 ----------
void genBucketOld(const NetCtx& N,int x,int c0,vector<RowX>& out){
  out.clear();
  unsigned char g[NX];
  const int* th=N.th;
  auto finish=[&](u32 i1,u32 i2){ FIN++; u32 m1=FULL&~i1,m2=FULL&~i2; RowX r; if(prepRow(g,__builtin_ctzll(m1),__builtin_ctzll(m2),N,r)) out.push_back(r); };
  vector<int> pts;
  function<void(int,u32,u32,u32)> tail=[&](int k,u32 used,u32 i1,u32 i2){
    if(k==(int)pts.size()){ finish(i1,i2); return; }
    int px=pts[k]; u32 fc=~used&FULL;
    for(;fc;fc&=fc-1){ int col=__builtin_ctzll(fc); int a=md(px-col),b=md(px-th[col]); if((i1>>a)&1||(i2>>b)&1) continue; g[px-1]=col; tail(k+1,used|(1ull<<col),i1|(1ull<<a),i2|(1ull<<b)); }
  };
  auto runTrie=[&](Trie& T,bool isN){
    function<void(int,u32,u32,u32)> dfs=[&](int nd,u32 used,u32 i1,u32 i2){
      for(int f:T.n[nd].fl){ u32 sg=fams[f].sing; if(!isN) sg&=~(1ull<<x); pts.clear(); for(u32 m=sg;m;m&=m-1) pts.push_back(__builtin_ctzll(m)); tail(0,used,i1,i2); }
      for(int k:T.n[nd].kids){ u32 b=T.n[k].blk; u32 fc= (isN&&nd==0)? (1ull<<c0) : (~used&FULL);
        for(;fc;fc&=fc-1){ int col=__builtin_ctzll(fc); u32 s1=rot(b,col); if(s1&i1) continue; u32 s2=rot(b,th[col]); if(s2&i2) continue;
          for(u32 m=b;m;m&=m-1) g[__builtin_ctzll(m)-1]=col;
          dfs(k,used|(1ull<<col),i1|s1,i2|s2); }
      }
    };
    if(isN) dfs(0,0,0,0);
    else { int a=md(x-c0),b=md(x-th[c0]); g[x-1]=c0; dfs(0,1ull<<c0,1ull<<a,1ull<<b); }
  };
  runTrie(TN[x],true); runTrie(TS[x],false);
}
void genBucketNew(const NetCtx& N,int x,int c0,vector<RowX>& out){
  out.clear();
  unsigned char g[NX];
  const int* th=N.th;
  auto finish=[&](u32 i1,u32 i2){ FIN++; u32 m1=FULL&~i1,m2=FULL&~i2; RowX r; if(prepRow(g,__builtin_ctzll(m1),__builtin_ctzll(m2),N,r)) out.push_back(r); };
  u32 T1[P][P],T2[P][P]; { int thi[P]; for(int c=0;c<P;c++) thi[th[c]]=c; for(int y=0;y<P;y++) for(int a=0;a<P;a++){ T1[y][a]=1ull<<md(y-a); T2[y][a]=1ull<<thi[md(y-a)]; } }
  function<void(u32,u32,u32,u32,const u32*)> tailm=[&](u32 rem,u32 used,u32 i1,u32 i2,const u32* F){
    TN_++; if(!rem){ finish(i1,i2); return; }
    int bx=-1,bc=99; u32 bav=0;
    for(u32 m=rem;m;m&=m-1){ int y=__builtin_ctzll(m); u32 av=FULL&~used&~F[y]; int pc=__builtin_popcountll(av); if(pc<bc){bc=pc;bx=y;bav=av; if(pc==0) return;} }
    u32 rem2=rem&~(1ull<<bx);
    for(u32 fc=bav;fc;fc&=fc-1){ int col=__builtin_ctzll(fc); int a=md(bx-col),b=md(bx-th[col]); g[bx-1]=col;
      u32 F2[P]; for(u32 m=rem2;m;m&=m-1){ int y=__builtin_ctzll(m); F2[y]=F[y]|T1[y][a]|T2[y][b]; }
      tailm(rem2,used|(1ull<<col),i1|(1ull<<a),i2|(1ull<<b),F2); }
  };
  auto tailStart=[&](u32 rem,u32 used,u32 i1,u32 i2){ u32 F[P]; for(u32 m=rem;m;m&=m-1){ int y=__builtin_ctzll(m); u32 f=0; for(u32 q=i1;q;q&=q-1) f|=T1[y][__builtin_ctzll(q)]; for(u32 q=i2;q;q&=q-1) f|=T2[y][__builtin_ctzll(q)]; F[y]=f; } tailm(rem,used,i1,i2,F); };
  auto runTrie=[&](Trie& T,bool isN){
    function<void(int,u32,u32,u32,u32,const u32*)> dfs=[&](int nd,u32 used,u32 i1,u32 i2,u32 placed,const u32* F){ DN++; KC+=T.n[nd].kids.size();
      for(int f:T.n[nd].fl){ u32 sg=fams[f].sing; if(!isN) sg&=~(1ull<<x); tailm(sg,used,i1,i2,F); }
      u32 R=XALL&~placed;
      for(int k:T.n[nd].kids){ u32 b=T.n[k].blk; u32 fc= (isN&&nd==0)? (1ull<<c0) : (~used&FULL);
        u32 R2=R&~b;
        for(;fc;fc&=fc-1){ int col=__builtin_ctzll(fc); u32 s1=rot(b,col); if(s1&i1) continue; u32 s2=rot(b,th[col]); if(s2&i2) continue;
          u32 F2[P]; for(u32 m=R2;m;m&=m-1){ int y=__builtin_ctzll(m); u32 f=F[y]; for(u32 q=s1;q;q&=q-1) f|=T1[y][__builtin_ctzll(q)]; for(u32 q=s2;q;q&=q-1) f|=T2[y][__builtin_ctzll(q)]; F2[y]=f; }
          u32 used2=used|(1ull<<col); bool ok=true; for(u32 m=R2;m;m&=m-1){ int y=__builtin_ctzll(m); if(!(FULL&~used2&~F2[y])){ ok=false; break; } }
          if(!ok) continue;
          for(u32 m=b;m;m&=m-1) g[__builtin_ctzll(m)-1]=col;
          dfs(k,used2,i1|s1,i2|s2,placed|b,F2); }
      }
    };
    u32 F0[P]; for(int y=0;y<P;y++) F0[y]=0;
    if(isN) dfs(0,0,0,0,0,F0);
    else { int a=md(x-c0),b=md(x-th[c0]); g[x-1]=c0; for(int y=0;y<P;y++) F0[y]=T1[y][a]|T2[y][b]; dfs(0,1ull<<c0,1ull<<a,1ull<<b,1ull<<x,F0); }
  };
  runTrie(TN[x],true); runTrie(TS[x],false);
}

static inline u32 rotl(u32 m,int a){ return a? (((m<<a)|(m>>(P-a)))&FULL):m; }

static std::mutex flatMu;
static void ensureFlat(int x){ if(__atomic_load_n(&flatDone[x],__ATOMIC_ACQUIRE)) return; std::lock_guard<std::mutex> lk(flatMu); if(flatDone[x]) return; FTN[x]=flatten(TN[x]); FTS[x]=flatten(TS[x]); __atomic_store_n(&flatDone[x],true,__ATOMIC_RELEASE); }
void genBucketFlat(const NetCtx& N,int x,int c0,vector<RowX>& out){
  out.clear(); unsigned char g[NX]; const int* th=N.th;
  M pullT[8][256]; u32 T1[P][P],T2[P][P];
  { int thi[P]; for(int c=0;c<P;c++) thi[th[c]]=c;
    for(int ch=0;ch<8;ch++) for(int m=0;m<256;m++){ M r=0; for(int v=0;v<8;v++) if(m>>v&1){ int val=ch*8+v; if(val<P) r|=1ull<<thi[val]; } pullT[ch][m]=r; }
    for(int y=0;y<P;y++) for(int a=0;a<P;a++){ T1[y][a]=1ull<<md(y-a); T2[y][a]=1ull<<thi[md(y-a)]; }
  }
  auto pull=[&](u32 m){ M r=0; for(int ch=0;ch<(P+7)/8;ch++) r|=pullT[ch][(m>>(8*ch))&255]; return r; };
  auto finish=[&](u32 i1,u32 i2){ u32 m1=FULL&~i1,m2=FULL&~i2; RowX r; if(prepRow(g,__builtin_ctzll(m1),__builtin_ctzll(m2),N,r)) out.push_back(r); };
  function<void(u32,u32,u32,u32,const u32*)> tailm=[&](u32 rem,u32 used,u32 i1,u32 i2,const u32* F){
    if(!rem){ finish(i1,i2); return; }
    int bx=-1,bc=99; u32 bav=0;
    for(u32 m=rem;m;m&=m-1){ int y=__builtin_ctzll(m); u32 av=FULL&~used&~F[y]; int pc=__builtin_popcountll(av); if(pc<bc){bc=pc;bx=y;bav=av; if(pc==0) return;} }
    u32 rem2=rem&~(1ull<<bx);
    for(u32 fc=bav;fc;fc&=fc-1){ int col=__builtin_ctzll(fc); int a=md(bx-col),b=md(bx-th[col]); g[bx-1]=col;
      u32 F2[P]; for(u32 m=rem2;m;m&=m-1){ int y=__builtin_ctzll(m); F2[y]=F[y]|T1[y][a]|T2[y][b]; }
      tailm(rem2,used|(1ull<<col),i1|(1ull<<a),i2|(1ull<<b),F2); }
  };
  auto tailStart=[&](u32 rem,u32 used,u32 i1,u32 i2){ u32 F[P]; for(u32 m=rem;m;m&=m-1){ int y=__builtin_ctzll(m); u32 f=0; for(u32 q=i1;q;q&=q-1) f|=T1[y][__builtin_ctzll(q)]; for(u32 q=i2;q;q&=q-1) f|=T2[y][__builtin_ctzll(q)]; F[y]=f; } tailm(rem,used,i1,i2,F); };
  auto runTrie=[&](const FlatTrie& T,bool isN){
    function<void(int,u32,u32,u32,u32,u32)> dfs=[&](int nd,u32 used,u32 i1,u32 i2,u32 n1,u32 n2){
      const FNode& cur=T.n[nd];
      for(int q=0;q<cur.nf;q++){ u32 sg=T.sing[cur.fb+q]; if(!isN) sg&=~(1ull<<x); tailStart(sg,used,i1,i2); }
      for(int k=cur.kb;k<(int)cur.kb+cur.nk;k++){ const FNode& kn=T.n[k]; u32 b=kn.blk; u32 fc= (isN&&nd==0)? (1ull<<c0) : (~used&FULL);
        u32 f1=0,f2v=0; for(u32 m=b;m;m&=m-1){ int xx=__builtin_ctzll(m); f1|=rotl(n1,xx); f2v|=rotl(n2,xx); }
        fc&=~f1; fc&=~pull(f2v);
        for(;fc;fc&=fc-1){ int col=__builtin_ctzll(fc); u32 s1=rot(b,col); u32 s2=rot(b,th[col]);
          for(u32 m=b;m;m&=m-1) g[__builtin_ctzll(m)-1]=col;
          dfs(k,used|(1ull<<col),i1|s1,i2|s2,n1|rotl(kn.nb,col),n2|rotl(kn.nb,th[col])); }
      }
    };
    if(isN) dfs(0,0,0,0,0,0);
    else { int a=md(x-c0),b=md(x-th[c0]); g[x-1]=c0; dfs(0,1ull<<c0,1ull<<a,1ull<<b,1ull<<md(-a),1ull<<md(-b)); }
  };
  ensureFlat(x);
  runTrie(FTN[x],true); runTrie(FTS[x],false);
}
void genBucketLUT(const NetCtx& N,int x,int c0,vector<RowX>& out){
  out.clear(); unsigned char g[NX]; const int* th=N.th;
  static thread_local M pullT[8][256]; static thread_local int lastth[P]; static thread_local bool init=false; static thread_local u32 T1[P][P],T2[P][P];
  bool same=init; if(same) for(int i=0;i<P;i++) if(lastth[i]!=th[i]){ same=false; break; }
  if(!same){ int thi[P]; for(int c=0;c<P;c++) thi[th[c]]=c;
    for(int ch=0;ch<8;ch++) for(int m=0;m<256;m++){ M r=0; for(int v=0;v<8;v++) if(m>>v&1){ int val=ch*8+v; if(val<P) r|=1ull<<thi[val]; } pullT[ch][m]=r; }
    for(int y=0;y<P;y++) for(int a=0;a<P;a++){ T1[y][a]=1ull<<md(y-a); T2[y][a]=1ull<<thi[md(y-a)]; }
    for(int i=0;i<P;i++) lastth[i]=th[i]; init=true; }
  auto pull=[&](u32 m){ M r=0; for(int ch=0;ch<(P+7)/8;ch++) r|=pullT[ch][(m>>(8*ch))&255]; return r; };
  auto finish=[&](u32 i1,u32 i2){ u32 m1=FULL&~i1,m2=FULL&~i2; RowX r; if(prepRow(g,__builtin_ctzll(m1),__builtin_ctzll(m2),N,r)) out.push_back(r); };
  function<void(u32,u32,u32,u32,const u32*)> tailm=[&](u32 rem,u32 used,u32 i1,u32 i2,const u32* F){
    TN_++; if(!rem){ finish(i1,i2); return; }
    int bx=-1,bc=99; u32 bav=0;
    for(u32 m=rem;m;m&=m-1){ int y=__builtin_ctzll(m); u32 av=FULL&~used&~F[y]; int pc=__builtin_popcountll(av); if(pc<bc){bc=pc;bx=y;bav=av; if(pc==0) return;} }
    u32 rem2=rem&~(1ull<<bx);
    for(u32 fc=bav;fc;fc&=fc-1){ int col=__builtin_ctzll(fc); int a=md(bx-col),b=md(bx-th[col]); g[bx-1]=col;
      u32 F2[P]; for(u32 m=rem2;m;m&=m-1){ int y=__builtin_ctzll(m); F2[y]=F[y]|T1[y][a]|T2[y][b]; }
      tailm(rem2,used|(1ull<<col),i1|(1ull<<a),i2|(1ull<<b),F2); }
  };
  auto tailStart=[&](u32 rem,u32 used,u32 i1,u32 i2){ u32 F[P]; for(u32 m=rem;m;m&=m-1){ int y=__builtin_ctzll(m); u32 f=0; for(u32 q=i1;q;q&=q-1) f|=T1[y][__builtin_ctzll(q)]; for(u32 q=i2;q;q&=q-1) f|=T2[y][__builtin_ctzll(q)]; F[y]=f; } tailm(rem,used,i1,i2,F); };
  auto runTrie=[&](Trie& T,bool isN){
    function<void(int,u32,u32,u32,u32,u32)> dfs=[&](int nd,u32 used,u32 i1,u32 i2,u32 n1,u32 n2){ DN++;
      for(int f:T.n[nd].fl){ u32 sg=fams[f].sing; if(!isN) sg&=~(1ull<<x); tailStart(sg,used,i1,i2); }
      for(int k:T.n[nd].kids){ KC++; const Node& kn=T.n[k]; u32 b=kn.blk; u32 fc= (isN&&nd==0)? (1ull<<c0) : (~used&FULL);
        u32 f1=0,f2v=0; for(u32 m=b;m;m&=m-1){ int xx=__builtin_ctzll(m); f1|=rotl(n1,xx); f2v|=rotl(n2,xx); }
        fc&=~f1; fc&=~pull(f2v); 
        for(;fc;fc&=fc-1){ int col=__builtin_ctzll(fc); u32 s1=rot(b,col); u32 s2=rot(b,th[col]);
          for(u32 m=b;m;m&=m-1) g[__builtin_ctzll(m)-1]=col;
          dfs(k,used|(1ull<<col),i1|s1,i2|s2,n1|rotl(kn.nb,col),n2|rotl(kn.nb,th[col])); }
      }
    };
    if(isN) dfs(0,0,0,0,0,0);
    else { int a=md(x-c0),b=md(x-th[c0]); g[x-1]=c0; dfs(0,1ull<<c0,1ull<<a,1ull<<b,1ull<<md(-a),1ull<<md(-b)); }
  };
  runTrie(TN[x],true); runTrie(TS[x],false);
}
static int GENMODE=3; static bool NEWGEN=true; 
void genBucket(const NetCtx& N,int x,int c0,vector<RowX>& out){ if(GENMODE==3) genBucketFlat(N,x,c0,out); else if(GENMODE==2) genBucketLUT(N,x,c0,out); else if(NEWGEN) genBucketNew(N,x,c0,out); else genBucketOld(N,x,c0,out); }
// ---------- search ----------
struct Hot2{ unsigned char g[GW]; u64 cls[NCLW]; u32 cellneg[P]; int u1,u2; };
struct Bucket{ bool have=false; vector<RowX> rows; vector<Hot> hot; vector<Hot2> h2; vector<unsigned char> T; size_t nb=0; };

static inline bool dMiss(const RowX& r,const Hot2& s){
  u32 D=0;
  for(int c=0;c<P;c++){ u32 a=r.cellm[c],bn=s.cellneg[c]; if(!a||!bn) continue; for(u32 ma=a;ma;ma&=ma-1){ u32 m=rotlm(bn,__builtin_ctzll(ma)); if(D&m) return false; D|=m; } }
  if(D&1) return false;
  u32 miss=XALL&~D; int d1=r.u1-s.u1; if(d1<0) d1+=P; int d2=r.u2-s.u2; if(d2<0) d2+=P; u32 want=(1ull<<d1)|(1ull<<d2);
  return miss==want&&__builtin_popcountll(want)==2; }
static bool VERIFY=false; static bool CTLMODE=false; struct RawRow{ unsigned char g[64]; int u1,u2; }; static vector<RawRow> INJRAW; static vector<string> CLQ;
struct Stats{ int maxdepth=0; u64 cliques=0,finals=0,nodes=0; size_t b1=0,surv=0; u64 vE=0; int vmax=0,vge=0; size_t after[4]={0,0,0}; double tgen=0,tb2=0; };

// number of rows s in bucket b compatible with r (if firstOnly: 1 as soon as one is found, else the exact count)
static int scanRow(const RowX& r,Bucket& b,bool firstOnly){
  size_t m=b.rows.size(); int cnt=0;
  __m256i rv[NQ]; for(int q=0;q<NQ;q++){ int lo=r.cn[2*q],hi=(2*q+1<P)?r.cn[2*q+1]:0; rv[q]=_mm256_set1_epi16((short)(lo|(hi<<8))); }
  const __m256i k14=_mm256_set1_epi16(P-3); 
  for(size_t blk=0;blk<b.nb;blk++){
    const unsigned char* tp=&b.T[blk*NQ*32]; __m256i acc=_mm256_maddubs_epi16(_mm256_loadu_si256((const __m256i*)tp),rv[0]);
    for(int q=1;q<NQ;q++) acc=_mm256_add_epi16(acc,_mm256_maddubs_epi16(_mm256_loadu_si256((const __m256i*)(tp+q*32)),rv[q]));
    unsigned mk=(unsigned)_mm256_movemask_epi8(_mm256_cmpeq_epi16(acc,k14)); mk&=0x55555555u;
    while(mk){ int l=__builtin_ctzll(mk)>>1; mk&=mk-1; size_t i=blk*16+l; if(i>=m) break; const Hot2& h=b.h2[i];
      if(gEqAny(r.g,h.g)) continue;
      { u64 cl=0; for(int w=0;w<NCLW;w++) cl|=r.cls[w]&h.cls[w]; if(cl) continue; }
      if(dMiss(r,h)&&compatTail(r,b.rows[i])){ cnt++; if(firstOnly) return 1; } } }
  return cnt; }
struct Searcher{
  NetCtx N; Bucket bk[P][P]; // [x][c]
  Stats st;
  vector<const RowX*> ch; u32 cov[P];
  Bucket& get(int x,int c){ Bucket& b=bk[x][c]; if(!b.have){ if(INJRAW.empty()) genBucket(N,x,c,b.rows); else { b.rows.clear(); for(const RawRow& w:INJRAW) if(w.g[x-1]==c){ RowX r; if(prepRow(w.g,w.u1,w.u2,N,r)) b.rows.push_back(r); } } if(getenv("DUMP")){ vector<string> v; for(auto&r:b.rows){ string s; for(int t=0;t<NX;t++) s+=char('A'+r.g[t]); s+=' '+to_string(r.u1)+' '+to_string(r.u2); v.push_back(s);} sort(v.begin(),v.end()); FILE* fo=fopen((string(getenv("DUMP"))+"_"+to_string(x)+"_"+to_string(c)).c_str(),"w"); for(auto&s:v) fprintf(fo,"%s\n",s.c_str()); fclose(fo);}  b.hot.resize(b.rows.size()); for(size_t i=0;i<b.rows.size();i++){ memcpy(b.hot[i].cn,b.rows[i].cn,CW); memcpy(b.hot[i].g,b.rows[i].g,GW);} b.have=true;
    { size_t m=b.rows.size(); b.nb=(m+15)/16; b.T.assign(b.nb*NQ*32,0); b.h2.resize(m); for(size_t i=0;i<m;i++){ memcpy(b.h2[i].g,b.rows[i].g,GW); memcpy(b.h2[i].cls,b.rows[i].cls,sizeof b.h2[i].cls); memcpy(b.h2[i].cellneg,b.rows[i].cellneg,sizeof b.h2[i].cellneg); b.h2[i].u1=b.rows[i].u1; b.h2[i].u2=b.rows[i].u2; }
      for(size_t i=0;i<m;i++){ size_t blk=i/16,l=i%16; for(int c=0;c<P;c++) b.T[(blk*NQ+c/2)*32+2*l+(c&1)]=b.rows[i].cn[c]; } } } return b; }
  bool finalOk(){
    for(int col=0;col<P;col++) for(int k=1;k<=2;k++){ u32 seen=0; int n=0; int sk= k==1? col: N.th[col];
      for(const RowX* r:ch){ int u= k==1? r->u1:r->u2; for(u32 m=r->cellm[col];m;m&=m-1){ int v=md(__builtin_ctzll(m)-u); if((seen>>v)&1) return false; seen|=1ull<<v; n++; } }
      if(n!=P-1|| (FULL&~seen)!=(1ull<<sk)) return false; }
    return true; }
  void dfs(){
    int d=ch.size(); st.nodes++; if(d>st.maxdepth) st.maxdepth=d;
    if(d==P){ st.cliques++; bool fo=finalOk(); if(fo){ st.finals++; } if(CTLMODE){ string o=fo?"CLQ final":"CLQ nofinal"; for(const RowX* r:ch){ o+=" |"; for(int t=0;t<NX;t++) o+=" "+to_string((int)r->g[t]); o+=" "+to_string(r->u1)+" "+to_string(r->u2);} CLQ.push_back(o);} return; }
    int c=-1,x=0; for(int cc=0;cc<P;cc++) if((cov[cc]&XALL)!=XALL){ c=cc; x=__builtin_ctzll(XALL&~cov[cc]); break; }
    if(c<0) return; // all columns covered with fewer than P rows: impossible (cells P*(P-1) total, but is allowed only if rows hold >P-1 cells each on average; handled by pigeonhole: cannot extend)
    Bucket& b=get(x,c);
    size_t n=b.rows.size();
    for(size_t i=0;i<n;i++){
      const RowX& s=b.rows[i];
      if(d){ if(dotcn(ch[0]->cn,b.hot[i].cn)!=P-3) continue; }
      bool ok=true; for(int k=d-1;k>=0;k--) if(!compat(*ch[k],s)){ ok=false; break; }
      if(!ok) continue;
      u32 sv[P]; memcpy(sv,cov,sizeof cov); for(int cc=0;cc<P;cc++) cov[cc]|=s.cellm[cc];
      ch.push_back(&s); dfs(); ch.pop_back(); memcpy(cov,sv,sizeof cov);
    }
  }
  void run(const int* th){
    memcpy(N.th,th,sizeof N.th); memset(N.forbid,0,sizeof N.forbid);
    for(int a=0;a<P;a++) for(int b=a+1;b<P;b++) for(int k=1;k<=2;k++){ int s_a= k==1? a: th[a], s_b= k==1? b: th[b]; int d=md(s_b-s_a); int id=pairidx[a][b]*P+d; N.forbid[id>>6]|=1ull<<(id&63); }
    for(int x=0;x<P;x++) for(int c=0;c<P;c++){ bk[x][c].have=false; }
    st=Stats(); ch.clear(); memset(cov,0,sizeof cov);
    double tg=omp_get_wtime(); Bucket& b1=get(1,0); st.b1=b1.rows.size(); st.tgen=omp_get_wtime()-tg;
    size_t n1=b1.rows.size();
    if(VERIFY){ // legacy-equivalent edge counts: all edges from rows with g(1)=0 to all rows (union of buckets (1,c), c>=1)
      vector<int> deg(n1,0); u64 E=0;
      for(int c=1;c<P;c++){ Bucket& b=get(1,c); for(size_t i=0;i<n1;i++){ int k=scanRow(b1.rows[i],b,false); deg[i]+=k; E+=k; } }
      int mx=0,ge=0; for(int d:deg){ mx=max(mx,d); if(d>=P-1) ge++; }
      st.vE=E; st.vmax=mx; st.vge=ge; return; }
    // exact necessary filter: in a solution the P rows have pairwise distinct columns at x=1 (bijection),
    // so a row r (g(1)=0) needs, for every column c != 0, a compatible row s with g_s(1)=c.
    vector<int> cand(n1); iota(cand.begin(),cand.end(),0);
    for(int c=1;c<P&&!cand.empty();c++){
      Bucket& b=get(1,c); vector<int> keep;
      for(int ri:cand) if(scanRow(b1.rows[ri],b,true)) keep.push_back(ri);
      cand.swap(keep); if(c<=4) st.after[c-1]=cand.size(); }
    st.surv=cand.size();
    for(int ri:cand){ const RowX& r=b1.rows[ri]; for(int cc=0;cc<P;cc++) cov[cc]=r.cellm[cc]; ch.assign(1,&r); dfs(); }
  }
};
void initIdx(){ int k=0; for(int a=0;a<P;a++) for(int b=a+1;b<P;b++) pairidx[a][b]=k++; }
static int ctlMain(const char* inf,const char* outf){
  ifstream in(inf); int pp; in>>pp; if(pp!=P){ fprintf(stderr,"P mismatch %d vs %d\n",pp,P); return 1; }
  int th[P]; for(int i=0;i<P;i++) in>>th[i];
  int nt; in>>nt; vector<RawRow> trueraw(nt); for(int i=0;i<nt;i++){ memset(&trueraw[i],0,sizeof(RawRow)); for(int t=0;t<NX;t++){ int v; in>>v; trueraw[i].g[t]=v; } in>>trueraw[i].u1>>trueraw[i].u2; }
  int nf; in>>nf; fams.resize(nf);
  for(int i=0;i<nf;i++){ int k; in>>k; u64 all=0; for(int j=0;j<k;j++){ u64 b; in>>b; fams[i].nb.push_back(b); all|=b; } fams[i].sing=XALL&~all; }
  if(getenv("INJECT")){ // rows-injected mode: buckets := true rows + random single mutations (generator bypassed; prepRow/scanRow/compat/dfs/finalOk are the production code)
    INJRAW=trueraw; mt19937_64 rng(777); int nm=atoi(getenv("INJECT")); for(int i=0;i<nt;i++) for(int rep=0;rep<nm;rep++){ RawRow w=trueraw[i]; int kind=rng()%3;
      if(kind==0){ int a=rng()%NX,b=rng()%NX; if(w.g[a]==w.g[b]) continue; swap(w.g[a],w.g[b]); }
      else if(kind==1){ int a=rng()%NX; int c=rng()%P; if(c==w.g[a]) continue; w.g[a]=c; }
      else { w.u1=(w.u1+1+rng()%(P-1))%P; }
      INJRAW.push_back(w); } fprintf(stderr,"inject: %zu raw rows\n",INJRAW.size()); }
  CTLMODE=true; initIdx(); buildTries(); initNeg();
  Searcher* S=new Searcher(); double t=omp_get_wtime(); S->run(th); t=omp_get_wtime()-t;
  FILE* fo=fopen(outf,"w");
  fprintf(fo,"P %d fams %d truerows %d b1 %zu a1 %zu a2 %zu a3 %zu a4 %zu surv %zu depth %d cliques %llu finals %llu nodes %llu t %.2f\n",P,nf,nt,S->st.b1,S->st.after[0],S->st.after[1],S->st.after[2],S->st.after[3],S->st.surv,S->st.maxdepth,S->st.cliques,S->st.finals,S->st.nodes,t);
  for(auto&l:CLQ) fprintf(fo,"%s\n",l.c_str());
  fclose(fo); return 0; }
int main(int argc,char**argv){
  if(argc>5 && string(argv[5])=="ctl") return ctlMain(argv[1],argv[4]);
  string netsf=argv[1]; int st=atoi(argv[2]),en=atoi(argv[3]); string outf=argv[4]; string mode=argc>5?argv[5]:"run";
  if(mode=="norowfilter") NOROWFILTER=true; if(mode=="verify") VERIFY=true; if(getenv("OLDGEN")) {NEWGEN=false;GENMODE=0;} if(getenv("NEWGEN1")) GENMODE=1; if(getenv("LUTGEN")) GENMODE=2;
  initIdx(); double t0=omp_get_wtime(); genfam(); fprintf(stderr,"fams %zu (%.1fs)\n",fams.size(),omp_get_wtime()-t0); buildTries(); initNeg(); { size_t a=0; for(int x=0;x<P;x++) a+=TN[x].n.size()+TS[x].n.size(); fprintf(stderr,"trie nodes total %zu x1: %zu %zu\n",a,TN[1].n.size(),TS[1].n.size()); } fprintf(stderr,"tries built %.1fs\n",omp_get_wtime()-t0);
  vector<array<int,P>> nets; { ifstream f(netsf); array<int,P> a; while(true){ bool ok=true; for(int i=0;i<P;i++) if(!(f>>a[i])) ok=false; if(!ok) break; nets.push_back(a);} }

  if(mode=="pairdump"){
    int id=st; Searcher* S=new Searcher(); const int* th=nets[id].data();
    memcpy(S->N.th,th,sizeof S->N.th); memset(S->N.forbid,0,sizeof S->N.forbid);
    for(int a=0;a<P;a++) for(int b=a+1;b<P;b++) for(int k=1;k<=2;k++){ int s_a= k==1? a: th[a], s_b= k==1? b: th[b]; int d=md(s_b-s_a); int q=pairidx[a][b]*P+d; S->N.forbid[q>>6]|=1ull<<(q&63); }
    Bucket& A=S->get(1,0); Bucket& B=S->get(1,atoi(getenv("PDC")?getenv("PDC"):"1"));
    mt19937_64 rng(12345+id); const int K=60; vector<vector<pair<int,int>>> res(6); long seen[6]={0,0,0,0,0,0};
    for(size_t i=0;i<A.rows.size();i++){ const RowX& r=A.rows[i];
      for(size_t j=0;j<B.rows.size();j++){ const RowX& s=B.rows[j];
        int stg; int cnt=0; for(int c=0;c<P;c++) cnt+=r.cn[c]*s.cn[c];
        if(cnt!=P-3) stg=0; else { bool geq=gEqAny(r.g,s.g); if(geq) stg=1; else { bool cl=false; for(int w=0;w<NCLW;w++) if(r.cls[w]&s.cls[w]) cl=true; if(cl) stg=2; else { Hot2 h; memcpy(h.cellneg,s.cellneg,sizeof h.cellneg); h.u1=s.u1; h.u2=s.u2; if(!dMiss(r,h)) stg=3; else if(!compatTail(r,s)) stg=4; else stg=5; } } }
        seen[stg]++; size_t cap= stg==5? 100000: K;
        if(res[stg].size()<cap) res[stg].push_back({(int)i,(int)j}); else if(stg!=5){ long q=rng()%seen[stg]; if(q<K) res[stg][q]={(int)i,(int)j}; } } }
    FILE* fo=fopen(outf.c_str(),"w"); fprintf(fo,"NET"); for(int i=0;i<P;i++) fprintf(fo," %d",th[i]); fprintf(fo,"\n");
    for(int stg=0;stg<6;stg++) for(auto pr:res[stg]){ const RowX& r=A.rows[pr.first]; const RowX& s=B.rows[pr.second]; bool c1=compat(r,s), c2=compatFull2(r,s);
      fprintf(fo,"PAIR %d %d %d",stg,(int)c1,(int)c2); for(int t=0;t<NX;t++) fprintf(fo," %d",r.g[t]); fprintf(fo," %d %d",r.u1,r.u2); for(int t=0;t<NX;t++) fprintf(fo," %d",s.g[t]); fprintf(fo," %d %d\n",s.u1,s.u2); }
    fprintf(fo,"SEEN %ld %ld %ld %ld %ld %ld\n",seen[0],seen[1],seen[2],seen[3],seen[4],seen[5]); fclose(fo); return 0; }
  en=min<int>(en,nets.size());
  set<int> done; { ifstream f(outf); string line; while(getline(f,line)){ int id; if(sscanf(line.c_str(),"%d",&id)==1) done.insert(id);} }
  vector<int> todo; for(int i=st;i<en;i++) if(!done.count(i)) todo.push_back(i);
  fprintf(stderr,"nets %zu todo %zu\n",nets.size(),todo.size());
  FILE* out=fopen(outf.c_str(),"a"); double lastlog=omp_get_wtime(); int cntdone=0; double tstart=lastlog;
  #pragma omp parallel
  { Searcher* S=new Searcher();
    #pragma omp for schedule(dynamic,1)
    for(int q=0;q<(int)todo.size();q++){ int id=todo[q]; double t=omp_get_wtime(); S->run(nets[id].data()); t=omp_get_wtime()-t;
      #pragma omp critical
      { if(VERIFY) fprintf(out,"%d cand %zu edges %llu maxdeg %d ge16 %d time %.2f\n",id,S->st.b1,S->st.vE,S->st.vmax,S->st.vge,t); else fprintf(out,"%d b1 %zu a1 %zu a2 %zu a3 %zu a4 %zu surv %zu depth %d cliques %llu finals %llu nodes %llu t %.2f\n",id,S->st.b1,S->st.after[0],S->st.after[1],S->st.after[2],S->st.after[3],S->st.surv,S->st.maxdepth,S->st.cliques,S->st.finals,S->st.nodes,t); fflush(out); cntdone++;
        if(S->st.cliques){ printf("CLIQUE net %d cliques %llu finals %llu\n",id,S->st.cliques,S->st.finals); fflush(stdout);}
        double now=omp_get_wtime(); if(now-lastlog>600){ lastlog=now; fprintf(stderr,"[%.0fs] done %d/%zu\n",now-tstart,cntdone,todo.size()); } }
    }
    delete S; }
  fprintf(stderr,"finished %d nets in %.1fs\n",cntdone,omp_get_wtime()-tstart);
  fclose(out);
}
