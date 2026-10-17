// Positive control: production-style predicates / generators of fast4.cpp, re-written with 64-bit masks, generic in P (P<=32 prime-or-not).
// Ported by hand from fast4.cpp (prepRow, compat, compatTail, compatFull2, genBucketNew, genBucketFlat, trie building, bucket pruning).
// build: g++ -O2 -std=c++17 -DP=31 ctrl_p.cpp -o ctrl_p31
// usage: ctrl_p input.txt
//   input: P ; th[0..P-1] ; ntrue ; ntrue lines "g[1..P-1] u1 u2" ; nfam ; nfam lines "nb b1 b2 ... bnb" (block masks, nonsingleton only; singles = rest of Z_P^*)
#include <bits/stdc++.h>
using namespace std; typedef unsigned long long u64; typedef u64 M;
#ifndef P
#define P 31
#endif
static_assert(P<=63,"mask width");
const M FULL=(1ull<<P)-1; const int NX=P-1, NCL=(P-1)/2; const M XALL=FULL&~1ull;
const int NCLW=(P*NCL+63)/64; const int NCC=(P*(P-1)/2*P+63)/64;
static inline M rot(M m,int a){ return a? (((m>>a)|(m<<(P-a)))&FULL):m; }
static inline M rotl(M m,int a){ return a? (((m<<a)|(m>>(P-a)))&FULL):m; }
static inline int md(int v){ v%=P; return v<0?v+P:v; }
static inline int ctz(M m){ return __builtin_ctzll(m);} static inline int pc(M m){ return __builtin_popcountll(m);}
static inline M negm(M m){ M r=m&1; for(int i=1;i<P;i++) if(m>>i&1) r|=1ull<<(P-i); return r; }
struct Fam{ vector<M> nb; M sing; }; vector<Fam> fams;
static bool bsz(M a,M b){ int pa=pc(a),pb=pc(b); return pa!=pb?pa>pb:a<b; }
struct Node{ M blk; vector<int> kids; vector<int> fl; };
struct Trie{ vector<Node> n; map<pair<int,M>,int> idx; Trie(){ n.push_back({0,{},{}}); }
  int child(int v,M b){ auto k=make_pair(v,b); auto it=idx.find(k); if(it!=idx.end()) return it->second; n.push_back({b,{},{}}); int id=n.size()-1; n[v].kids.push_back(id); idx[k]=id; return id; } };
Trie TN[P], TS[P];
void buildTries(){
  for(int x=1;x<P;x++) for(size_t fi=0;fi<fams.size();fi++){ const Fam& f=fams[fi]; vector<M> b=f.nb; int node=0;
    if(f.sing>>x&1){ sort(b.begin(),b.end(),bsz); for(M m:b) node=TS[x].child(node,m); TS[x].n[node].fl.push_back(fi); }
    else { M bx=0; for(M m:b) if(m>>x&1) bx=m; vector<M> r; for(M m:b) if(m!=bx) r.push_back(m); sort(r.begin(),r.end(),bsz); node=TN[x].child(0,bx); for(M m:r) node=TN[x].child(node,m); TN[x].n[node].fl.push_back(fi); } }
}
int pairidx[P][P];
struct RowX{ unsigned char cn[64]; unsigned char g[64]; int u1,u2; u64 cls[NCLW]; M cellm[P]; M cellneg[P]; u64 cc[NCC]; };
struct NetCtx{ int th[P]; u64 forbid[NCC]; };
bool NOROWFILTER=false;
bool prepRow(const unsigned char* g,int u1,int u2,const NetCtx& N,RowX& x){
  memset(&x,0,sizeof x); x.u1=u1; x.u2=u2; for(int t=0;t<NX;t++){ x.g[t]=g[t]; x.cellm[g[t]]|=1ull<<(t+1); x.cn[g[t]]++; x.cellneg[g[t]]|=1ull<<md(-(t+1)); }
  for(int c=0;c<P;c++){ M m=x.cellm[c]; for(M a=m;a;a&=a-1) for(M b=a&(a-1);b;b&=b-1){ int xa=ctz(a),xb=ctz(b); int d=md(xb-xa); d=min(d,P-d); int id=c*NCL+(d-1); x.cls[id>>6]|=1ull<<(id&63);} }
  for(int a=0;a<P;a++) for(int b=a+1;b<P;b++) for(M ma=x.cellm[a];ma;ma&=ma-1) for(M mb=x.cellm[b];mb;mb&=mb-1){ int d=md(ctz(mb)-ctz(ma)); int id=pairidx[a][b]*P+d; u64 bit=1ull<<(id&63); if(!NOROWFILTER){ if(x.cc[id>>6]&bit) return false; if(N.forbid[id>>6]&bit) return false; } x.cc[id>>6]|=bit; }
  return true;
}
// original `compat` (difference list x-y)
static bool compatA(const RowX& r,const RowX& s){
  { int cnt=0; for(int c=0;c<P;c++) cnt+=r.cn[c]*s.cn[c]; if(cnt!=P-3) return false; }
  for(int t=0;t<NX;t++) if(r.g[t]==s.g[t]) return false;
  for(int w=0;w<NCLW;w++) if(r.cls[w]&s.cls[w]) return false;
  M D=0; int cnt=0;
  for(int c=0;c<P;c++){ M a=r.cellm[c],b=s.cellm[c]; if(!a||!b) continue; for(M ma=a;ma;ma&=ma-1){ int xa=ctz(ma); for(M mb=b;mb;mb&=mb-1){ int d=md(xa-ctz(mb)); if((D>>d)&1) return false; D|=1ull<<d; cnt++; } } }
  if(cnt!=P-3||(D&1)) return false;
  M miss=XALL&~D; M want=(1ull<<md(r.u1-s.u1))|(1ull<<md(r.u2-s.u2));
  if(miss!=want||pc(want)!=2) return false;
  for(int w=0;w<NCC;w++) if(r.cc[w]&s.cc[w]) return false;
  return true;
}
// compatTail / compatFull2 version (rotated negated masks)
static inline bool compatTail(const RowX& r,const RowX& s){
  M D=0;
  for(int c=0;c<P;c++){ M a=r.cellm[c],bn=s.cellneg[c]; if(!a||!bn) continue; for(M ma=a;ma;ma&=ma-1){ M m=rotl(bn,ctz(ma)); if(D&m) return false; D|=m; } }
  if(D&1) return false;
  M miss=XALL&~D; int d1=md(r.u1-s.u1),d2=md(r.u2-s.u2); M want=(1ull<<d1)|(1ull<<d2);
  if(miss!=want||pc(want)!=2) return false;
  for(int w=0;w<NCC;w++) if(r.cc[w]&s.cc[w]) return false;
  return true; }
static inline bool compatB(const RowX& r,const RowX& s){
  { int cnt=0; for(int c=0;c<P;c++) cnt+=r.cn[c]*s.cn[c]; if(cnt!=P-3) return false; }
  for(int t=0;t<NX;t++) if(r.g[t]==s.g[t]) return false;
  for(int w=0;w<NCLW;w++) if(r.cls[w]&s.cls[w]) return false;
  return compatTail(r,s); }
static inline bool compat(const RowX& r,const RowX& s){ bool a=compatA(r,s),b=compatB(r,s); if(a!=b){ fprintf(stderr,"compatA/compatB DISAGREE\n"); exit(3);} return a; }
// ---- bucket generation (genBucketNew, forward-checking over trie) ----
void genBucketNew(const NetCtx& N,int x,int c0,vector<RowX>& out){
  out.clear(); unsigned char g[NX]; const int* th=N.th;
  auto finish=[&](M i1,M i2){ M m1=FULL&~i1,m2=FULL&~i2; RowX r; if(prepRow(g,ctz(m1),ctz(m2),N,r)) out.push_back(r); };
  M T1[P][P],T2[P][P]; { int thi[P]; for(int c=0;c<P;c++) thi[th[c]]=c; for(int y=0;y<P;y++) for(int a=0;a<P;a++){ T1[y][a]=1ull<<md(y-a); T2[y][a]=1ull<<thi[md(y-a)]; } }
  function<void(M,M,M,M,const M*)> tailm=[&](M rem,M used,M i1,M i2,const M* F){
    if(!rem){ finish(i1,i2); return; }
    int bx=-1,bc=99; M bav=0;
    for(M m=rem;m;m&=m-1){ int y=ctz(m); M av=FULL&~used&~F[y]; int p_=pc(av); if(p_<bc){bc=p_;bx=y;bav=av; if(p_==0) return;} }
    M rem2=rem&~(1ull<<bx);
    for(M fc=bav;fc;fc&=fc-1){ int col=ctz(fc); int a=md(bx-col),b=md(bx-th[col]); g[bx-1]=col;
      M F2[P]; for(M m=rem2;m;m&=m-1){ int y=ctz(m); F2[y]=F[y]|T1[y][a]|T2[y][b]; }
      tailm(rem2,used|(1ull<<col),i1|(1ull<<a),i2|(1ull<<b),F2); }
  };
  auto runTrie=[&](Trie& T,bool isN){
    function<void(int,M,M,M,M,const M*)> dfs=[&](int nd,M used,M i1,M i2,M placed,const M* F){
      for(int f:T.n[nd].fl){ M sg=fams[f].sing; if(!isN) sg&=~(1ull<<x); tailm(sg,used,i1,i2,F); }
      M R=XALL&~placed;
      for(int k:T.n[nd].kids){ M b=T.n[k].blk; M fc= (isN&&nd==0)? (1ull<<c0) : (~used&FULL);
        M R2=R&~b;
        for(;fc;fc&=fc-1){ int col=ctz(fc); M s1=rot(b,col); if(s1&i1) continue; M s2=rot(b,th[col]); if(s2&i2) continue;
          M F2[P]; for(M m=R2;m;m&=m-1){ int y=ctz(m); M f=F[y]; for(M q=s1;q;q&=q-1) f|=T1[y][ctz(q)]; for(M q=s2;q;q&=q-1) f|=T2[y][ctz(q)]; F2[y]=f; }
          M used2=used|(1ull<<col); bool ok=true; for(M m=R2;m;m&=m-1){ int y=ctz(m); if(!(FULL&~used2&~F2[y])){ ok=false; break; } }
          if(!ok) continue;
          for(M m=b;m;m&=m-1) g[ctz(m)-1]=col;
          dfs(k,used2,i1|s1,i2|s2,placed|b,F2); }
      }
    };
    M F0[P]; for(int y=0;y<P;y++) F0[y]=0;
    if(isN) dfs(0,0,0,0,0,F0);
    else { int a=md(x-c0),b=md(x-th[c0]); g[x-1]=c0; for(int y=0;y<P;y++) F0[y]=T1[y][a]|T2[y][b]; dfs(0,1ull<<c0,1ull<<a,1ull<<b,1ull<<x,F0); }
  };
  runTrie(TN[x],true); runTrie(TS[x],false);
}
// ---- genBucketFlat-style (neighbour masks n1,n2 + pull via inverse theta; no forward checking in the trie part) ----
void genBucketFlat(const NetCtx& N,int x,int c0,vector<RowX>& out){
  out.clear(); unsigned char g[NX]; const int* th=N.th;
  int thi[P]; for(int c=0;c<P;c++) thi[th[c]]=c;
  static M pullT[8][256]; for(int ch=0;ch<8;ch++) for(int m=0;m<256;m++){ M r=0; for(int v=0;v<8;v++) if(m>>v&1){ int val=ch*8+v; if(val<P) r|=1ull<<thi[val]; } pullT[ch][m]=r; }
  M T1[P][P],T2[P][P]; for(int y=0;y<P;y++) for(int a=0;a<P;a++){ T1[y][a]=1ull<<md(y-a); T2[y][a]=1ull<<thi[md(y-a)]; }
  auto pull=[&](M m){ M r=0; for(int ch=0;ch<8;ch++) r|=pullT[ch][(m>>(8*ch))&255]; return r; };
  auto finish=[&](M i1,M i2){ M m1=FULL&~i1,m2=FULL&~i2; RowX r; if(prepRow(g,ctz(m1),ctz(m2),N,r)) out.push_back(r); };
  function<void(M,M,M,M,const M*)> tailm=[&](M rem,M used,M i1,M i2,const M* F){
    if(!rem){ finish(i1,i2); return; }
    int bx=-1,bc=99; M bav=0;
    for(M m=rem;m;m&=m-1){ int y=ctz(m); M av=FULL&~used&~F[y]; int p_=pc(av); if(p_<bc){bc=p_;bx=y;bav=av; if(p_==0) return;} }
    M rem2=rem&~(1ull<<bx);
    for(M fc=bav;fc;fc&=fc-1){ int col=ctz(fc); int a=md(bx-col),b=md(bx-th[col]); g[bx-1]=col;
      M F2[P]; for(M m=rem2;m;m&=m-1){ int y=ctz(m); F2[y]=F[y]|T1[y][a]|T2[y][b]; }
      tailm(rem2,used|(1ull<<col),i1|(1ull<<a),i2|(1ull<<b),F2); }
  };
  auto tailStart=[&](M rem,M used,M i1,M i2){ M F[P]; for(M m=rem;m;m&=m-1){ int y=ctz(m); M f=0; for(M q=i1;q;q&=q-1) f|=T1[y][ctz(q)]; for(M q=i2;q;q&=q-1) f|=T2[y][ctz(q)]; F[y]=f; } tailm(rem,used,i1,i2,F); };
  auto runTrie=[&](Trie& T,bool isN){
    function<void(int,M,M,M,M,M)> dfs=[&](int nd,M used,M i1,M i2,M n1,M n2){
      for(int f:T.n[nd].fl){ M sg=fams[f].sing; if(!isN) sg&=~(1ull<<x); tailStart(sg,used,i1,i2); }
      for(int k:T.n[nd].kids){ M b=T.n[k].blk; M nbk=negm(b); M fc= (isN&&nd==0)? (1ull<<c0) : (~used&FULL);
        M f1=0,f2v=0; for(M m=b;m;m&=m-1){ int xx=ctz(m); f1|=rotl(n1,xx); f2v|=rotl(n2,xx); }
        fc&=~f1; fc&=~pull(f2v);
        for(;fc;fc&=fc-1){ int col=ctz(fc); M s1=rot(b,col); M s2=rot(b,th[col]);
          for(M m=b;m;m&=m-1) g[ctz(m)-1]=col;
          dfs(k,used|(1ull<<col),i1|s1,i2|s2,n1|rotl(nbk,col),n2|rotl(nbk,th[col])); }
      }
    };
    if(isN) dfs(0,0,0,0,0,0);
    else { int a=md(x-c0),b=md(x-th[c0]); g[x-1]=c0; dfs(0,1ull<<c0,1ull<<a,1ull<<b,1ull<<md(-a),1ull<<md(-b)); }
  };
  runTrie(TN[x],true); runTrie(TS[x],false);
}
static bool finalOK(const NetCtx& N,const vector<const RowX*>& rr){
  for(int col=0;col<P;col++) for(int k=1;k<=2;k++){ int sk= k==1? col: N.th[col]; M un=0; int cnt=0;
    for(auto r:rr){ int u= k==1? r->u1: r->u2; for(M m=r->cellm[col];m;m&=m-1){ int v=md(ctz(m)-u); if(un>>v&1) return false; un|=1ull<<v; cnt++; } }
    if(cnt!=P-1|| (FULL&~un)!=(1ull<<sk)) return false; }
  return true; }
static bool sameRow(const RowX& a,const RowX& b){ return a.u1==b.u1&&a.u2==b.u2&&memcmp(a.g,b.g,NX)==0; }
static vector<vector<int>> readMat; // unused
int main(int argc,char**argv){
  ifstream in(argv[1]); int pp; in>>pp; if(pp!=P){ fprintf(stderr,"P mismatch %d vs %d\n",pp,P); return 1; }
  NetCtx N; for(int i=0;i<P;i++) in>>N.th[i];
  int nt; in>>nt; vector<array<int,P+1>> tr(nt); // g[0..P-2],u1,u2 -> store g (P-1) then u1,u2: need P+1 ints
  vector<vector<int>> trg(nt); vector<int> tu1(nt),tu2(nt);
  for(int i=0;i<nt;i++){ trg[i].resize(NX); for(int t=0;t<NX;t++) in>>trg[i][t]; in>>tu1[i]>>tu2[i]; }
  int nf; in>>nf; fams.resize(nf);
  for(int i=0;i<nf;i++){ int k; in>>k; M all=0; for(int j=0;j<k;j++){ u64 b; in>>b; fams[i].nb.push_back(b); all|=b; } fams[i].sing=XALL&~all; }
  buildTries();
  { int q=0; for(int a=0;a<P;a++) for(int b=a+1;b<P;b++) pairidx[a][b]=q++; }
  memset(N.forbid,0,sizeof N.forbid);
  for(int a=0;a<P;a++) for(int b=a+1;b<P;b++) for(int k=1;k<=2;k++){ int s_a= k==1? a: N.th[a], s_b= k==1? b: N.th[b]; int d=md(s_b-s_a); int id=pairidx[a][b]*P+d; N.forbid[id>>6]|=1ull<<(id&63); }
  printf("P=%d families=%d true rows=%d\n",P,nf,nt);
  // (A) row-level filter + pairwise compat on true rows
  vector<RowX> TR(nt); int rowok=0;
  for(int i=0;i<nt;i++){ unsigned char g[NX]; for(int t=0;t<NX;t++) g[t]=trg[i][t]; if(prepRow(g,tu1[i],tu2[i],N,TR[i])) rowok++; }
  printf("[A1] prepRow (row-level cc & forbid filter) accepts %d/%d true rows\n",rowok,nt);
  int pok=0,ptot=0; for(int i=0;i<nt;i++) for(int j=i+1;j<nt;j++){ ptot++; if(compat(TR[i],TR[j])) pok++; }
  printf("[A2] compat accepts %d/%d pairs of true rows (compatA == compatB on all)\n",pok,ptot);
  // (B) mutations
  mt19937_64 rng(777); long mrows=0,mpass_row=0,mrej=0,macc=0; long tot_mut=0; map<string,long> kinds;
  for(int i=0;i<nt;i++) for(int rep=0;rep<200;rep++){
    unsigned char g[NX]; for(int t=0;t<NX;t++) g[t]=trg[i][t]; int u1=tu1[i],u2=tu2[i]; int kind=rng()%4; string kn;
    if(kind==0){ u1=md(u1+1+rng()%(P-1)); kn="u1 shift"; }
    else if(kind==1){ int a=rng()%NX,b=rng()%NX; if(g[a]==g[b]) continue; swap(g[a],g[b]); kn="swap two x"; }
    else if(kind==2){ int a=rng()%NX; int c=rng()%P; if(c==g[a]) continue; g[a]=c; kn="reassign one x"; }
    else { int c1=g[rng()%NX],c2=rng()%P; if(c1==c2) continue; bool used=false; for(int t=0;t<NX;t++) if(g[t]==c2) used=true; if(used) continue; for(int t=0;t<NX;t++) if(g[t]==c1) g[t]=c2; kn="move block to free column"; }
    tot_mut++;
    // is the mutated object a legitimate row (T1-T3, u consistent)? test via brute force
    bool legit=true; { set<int> a1,a2; for(int x=1;x<P;x++){ a1.insert(md(x-g[x-1])); a2.insert(md(x-N.th[g[x-1]])); } if((int)a1.size()!=P-1||(int)a2.size()!=P-1) legit=false; else { int m1=-1,m2=-1; for(int v=0;v<P;v++){ if(!a1.count(v)) m1=v; if(!a2.count(v)) m2=v; } if(m1!=u1||m2!=u2) legit=false; }
      if(legit){ map<int,vector<int>> cl; for(int x=1;x<P;x++) cl[g[x-1]].push_back(x); set<int> seen; for(auto&kv:cl) for(size_t a=0;a<kv.second.size();a++) for(size_t b=a+1;b<kv.second.size();b++){ int d=md(kv.second[b]-kv.second[a]); d=min(d,P-d); if(seen.count(d)) legit=false; seen.insert(d);} if((int)seen.size()!=NCL) legit=false; } }
    RowX m; string tag= legit? " [legit row T1-T3]":" [not a row]"; if(legit) mpass_row++;
    if(!prepRow(g,u1,u2,N,m)){ kinds[kn+tag+" rejected by prepRow"]++; if(legit) mrej++; continue; }
    bool any=false; for(int j=0;j<nt;j++) if(j!=i && !compat(m,TR[j])){ any=true; break; }
    if(any){ kinds[kn+tag+" rejected by compat"]++; if(legit) mrej++; } else { if(legit) macc++; kinds[kn+tag+" ACCEPTED by all other true rows (!)"]++; }
  }
  printf("[B] mutations: %ld tried, %ld are legitimate rows (T1-T3); of those %ld rejected (prepRow or incompatible with >=1 other true row), %ld accepted by all\n",tot_mut,mpass_row,mrej,macc);
  for(auto&kv:kinds) printf("    %-60s %ld\n",kv.first.c_str(),kv.second);
  if(argc>2 && string(argv[2])=="nogen"){ printf("[C-E] skipped (nogen)\n"); return 0; }
  // (C) generator: buckets
  vector<vector<RowX>> BN(P),BF(P); size_t tot=0;
  for(int c=0;c<P;c++){ genBucketNew(N,1,c,BN[c]); genBucketFlat(N,1,c,BF[c]); tot+=BN[c].size(); }
  int found=0; for(int i=0;i<nt;i++){ int c=trg[i][0]; bool f1=false,f2=false; for(auto&r:BN[c]) if(sameRow(r,TR[i])){f1=true;break;} for(auto&r:BF[c]) if(sameRow(r,TR[i])){f2=true;break;} if(f1&&f2) found++; else printf("   true row %d (g(1)=%d) MISSING from New=%d Flat=%d\n",i,c,f1,f2); }
  printf("[C1] bucket generators (New / Flat): true rows found in B(1,g(1)) by both: %d/%d ; total bucket rows %zu\n",found,nt,tot);
  int same=0; for(int c=0;c<P;c++){ auto key=[&](const RowX&r){ string s((char*)r.g,NX); s+=char(r.u1); s+=char(r.u2); return s; }; set<string> a,b; for(auto&r:BN[c]) a.insert(key(r)); for(auto&r:BF[c]) b.insert(key(r)); if(a==b) same++; else printf("   bucket %d: New=%zu Flat=%zu differ\n",c,a.size(),b.size()); }
  { size_t dup=0; for(int c=0;c<P;c++){ set<string> a; for(auto&r:BN[c]){ string k((char*)r.g,NX); k+=char(r.u1); k+=char(r.u2); if(!a.insert(k).second) dup++; } } printf("[C1b] duplicate rows inside buckets (New): %zu\n",dup); }
  printf("[C2] New vs Flat generate identical row sets in %d/%d buckets; bucket sizes:",same,P); for(int c=0;c<P;c++) printf(" %zu",BN[c].size()); printf("\n");
  // (D) bucket pruning pipeline: B(1,0) rows filtered through B(1,1),B(1,2),...
  vector<int> cand(BN[0].size()); iota(cand.begin(),cand.end(),0);
  int r0=-1; for(int i=0;i<nt;i++) if(trg[i][0]==0) r0=i; size_t r0idx=SIZE_MAX; for(size_t q=0;q<BN[0].size();q++) if(sameRow(BN[0][q],TR[r0])) r0idx=q;
  printf("[D] stages (true row index in B(1,0): %zu): survivors after each c:",r0idx);
  bool truealive=true; for(int c=1;c<P;c++){ vector<int> keep; for(int qi:cand){ bool has=false; for(auto&s:BN[c]) if(compat(BN[0][qi],s)){has=true;break;} if(has) keep.push_back(qi);} cand.swap(keep); printf(" %zu",cand.size()); if(find(cand.begin(),cand.end(),(int)r0idx)==cand.end()) truealive=false; }
  printf("\n[D] true row r0 (g(1)=0) survives all stages: %s\n",truealive?"YES":"NO");
  // (E) exact clique search for a P-clique with one row per bucket, seeded from survivors of B(1,0), using all bucket rows
  // restrict each bucket to rows compatible with some survivor? just do a plain DFS with candidate lists
  long cliques=0; long finals=0; long nodes=0; bool trueFound=false;
  for(int qi:cand){
    vector<vector<int>> cl(P); for(int c=1;c<P;c++) for(size_t k=0;k<BN[c].size();k++) if(compat(BN[0][qi],BN[c][k])) cl[c].push_back(k);
    vector<int> chosen(P,-1); chosen[0]=qi;
    // simple fixed-order DFS
    function<void(int)> go=[&](int c){ nodes++; if(c==P){ cliques++; { vector<const RowX*> rr; for(int t=0;t<P;t++) rr.push_back(t==0?&BN[0][qi]:&BN[t][chosen[t]]); if(finalOK(N,rr)){ finals++; if(finals<=3){ for(auto r:rr){ for(int t=0;t<NX;t++) fprintf(stderr,"%d ",r->g[t]); fprintf(stderr,"%d %d\n",r->u1,r->u2);} fprintf(stderr,"--\n"); } } } bool isTrue=true; for(int t=0;t<P;t++){ int tr_=-1; for(int i=0;i<nt;i++) if(trg[i][0]==t) tr_=i; const RowX& rr=(t==0?BN[0][qi]:BN[t][chosen[t]]); if(!sameRow(rr,TR[tr_])) isTrue=false; } if(isTrue) trueFound=true; return; }
      for(int k:cl[c]){ bool ok=true; for(int t=1;t<c&&ok;t++) if(!compat(BN[t][chosen[t]],BN[c][k])) ok=false; if(!ok) continue; chosen[c]=k; go(c+1); chosen[c]=-1; } };
    go(1);
  }
  printf("[E] exact search over generated rows (from survivors of stage D): %ld %d-cliques found, %ld pass the final side-point check, true plane among them: %s (dfs nodes %ld)\n",cliques,P,finals,trueFound?"YES":"NO",nodes);
  return 0;
}
