// Independent re-implementation (written from the specification, not from fast*.cpp) of the per-net decision for p=17.
//   Rows(theta, g(1)=c): g:{1..16}->columns, (T1) same-column difference classes +-d (d=1..8) used exactly once overall,
//   (T2) x-g(x) injective, (T3) x-theta(g(x)) injective;  u1,u2 = the value missing from the image of T2, T3.
//   Pair compatibility (derived from the geometry): cov(d)=1 for all d in Z_17, where cov counts
//   same-column cell pairs (x in r, y in s, x-y=d) plus the three V-line differences 0, u1r-u1s, u2r-u2s.
//   Decision: B(1,0) rows r survive stage c if some s in B(1,c) is compatible; a 17-clique needs survivors for all c=1..16.
// usage: indep netsfile id [maxc] [dumpprefix]
#include <bits/stdc++.h>
using namespace std; typedef unsigned int u32;
const int P=17; const u32 FULL=(1u<<P)-1;
static inline int md(int v){ v%=P; if(v<0) v+=P; return v; }
vector<vector<u32>> fams; // each: list of block masks (including singletons) covering {1..16}
void genfams(){
  vector<u32> cur;
  function<void(u32,u32)> rec=[&](u32 placed,u32 usedcls){
    if(placed==((1u<<P)-2)){ if(usedcls==0x1FE) fams.push_back(cur); return; }
    int x=1; while(placed>>x&1) x++;
    // block containing x: x plus subset (size 0..4) of unplaced elements > x
    vector<int> el; for(int y=x+1;y<P;y++) if(!(placed>>y&1)) el.push_back(y);
    vector<int> B={x};
    function<void(int,u32)> ext=[&](int from,u32 uc){
      u32 m=0; for(int b:B) m|=1u<<b; cur.push_back(m); rec(placed|m,uc); cur.pop_back();
      if(B.size()==4) return;
      for(int i=from;i<(int)el.size();i++){
        u32 uc2=uc; bool ok=true; for(int b:B){ int d=abs(el[i]-b); d=min(d,P-d); if(uc2>>d&1){ ok=false; break; } uc2|=1u<<d; }
        if(!ok) continue; B.push_back(el[i]); ext(i+1,uc2); B.pop_back(); }
    };
    ext(0,usedcls);
  };
  rec(0,0);
}
struct Row{ unsigned char g[16]; int u1,u2; u32 cell[P]; };
int th[P];
void genrows(int c,vector<Row>& out){
  out.clear();
  for(auto& F:fams){
    // order: block containing 1 first (fixed column c), then others by decreasing size
    vector<u32> bl=F; int i1=-1; for(int i=0;i<(int)bl.size();i++) if(bl[i]&2) i1=i; swap(bl[0],bl[i1]);
    sort(bl.begin()+1,bl.end(),[](u32 a,u32 b){ return __builtin_popcount(a)>__builtin_popcount(b); });
    int n=bl.size(); vector<int> col(n,-1);
    function<void(int,u32,u32,u32)> go=[&](int k,u32 usedc,u32 im1,u32 im2){
      if(k==n){ Row r; memset(&r,0,sizeof r); for(int t=0;t<n;t++) for(int x=1;x<P;x++) if(bl[t]>>x&1){ r.g[x-1]=col[t]; r.cell[col[t]]|=1u<<x; }
        r.u1=__builtin_ctz(FULL&~im1); r.u2=__builtin_ctz(FULL&~im2); out.push_back(r); return; }
      for(int cc=(k==0?c:0);cc<=(k==0?c:P-1);cc++){ if(usedc>>cc&1) continue;
        u32 a1=im1,a2=im2; bool ok=true;
        for(int x=1;x<P&&ok;x++) if(bl[k]>>x&1){ int v1=md(x-cc),v2=md(x-th[cc]); if((a1>>v1&1)||(a2>>v2&1)) ok=false; else { a1|=1u<<v1; a2|=1u<<v2; } }
        if(!ok) continue; col[k]=cc; go(k+1,usedc|(1u<<cc),a1,a2); }
    };
    go(0,0,0,0);
  }
}
static inline bool compatI(const Row& r,const Row& s){
  u32 D=0;
  for(int j=0;j<P;j++){ u32 a=r.cell[j],b=s.cell[j]; if(!a||!b) continue;
    for(u32 ma=a;ma;ma&=ma-1){ int x=__builtin_ctz(ma); for(u32 mb=b;mb;mb&=mb-1){ int y=__builtin_ctz(mb); int d=md(x-y); if(D>>d&1) return false; D|=1u<<d; } } }
  int ds[3]={0,md(r.u1-s.u1),md(r.u2-s.u2)};
  for(int q=0;q<3;q++){ if(D>>ds[q]&1) return false; D|=1u<<ds[q]; }
  return D==FULL;
}
int main(int argc,char** argv){
  ifstream f(argv[1]); int id=atoi(argv[2]); int maxc=argc>3?atoi(argv[3]):16; string dump=argc>4?argv[4]:"";
  vector<array<int,P>> nets; array<int,P> a; while(true){ bool ok=true; for(int i=0;i<P;i++) if(!(f>>a[i])) ok=false; if(!ok) break; nets.push_back(a); }
  for(int i=0;i<P;i++) th[i]=nets[id][i];
  genfams(); { map<int,int> t; for(auto&F:fams){ int c4=0,c3=0,c2=0; for(u32 b:F){ int p=__builtin_popcount(b); c4+=p==4; c3+=p==3; c2+=p==2; } t[c4*100+c3*10+c2]++; } fprintf(stderr,"families %zu by (n4,n3,n2):",fams.size()); for(auto&kv:t) fprintf(stderr," %d:%d",kv.first,kv.second); fprintf(stderr,"\n"); }
  vector<Row> B0; genrows(0,B0); printf("NET %d rows(g(1)=0) %zu\n",id,B0.size());
  if(!dump.empty()){ vector<string> v; for(auto&r:B0){ string s; for(int t=0;t<16;t++) s+=char('A'+r.g[t]); s+=' '+to_string(r.u1)+' '+to_string(r.u2); v.push_back(s);} sort(v.begin(),v.end()); FILE* fo=fopen((dump+"_1_0").c_str(),"w"); for(auto&s:v) fprintf(fo,"%s\n",s.c_str()); fclose(fo); }
  vector<int> cand(B0.size()); iota(cand.begin(),cand.end(),0);
  for(int c=1;c<=maxc&&!cand.empty();c++){
    vector<Row> Bc; genrows(c,Bc);
    vector<int> keep; vector<char> has(cand.size(),0);
    #pragma omp parallel for schedule(dynamic,64)
    for(int q=0;q<(int)cand.size();q++){ const Row& r=B0[cand[q]]; for(const Row& s:Bc) if(compatI(r,s)){ has[q]=1; break; } }
    for(size_t q=0;q<cand.size();q++) if(has[q]) keep.push_back(cand[q]);
    printf("stage c=%d: |B(1,c)|=%zu survivors %zu\n",c,Bc.size(),keep.size()); fflush(stdout);
    if(!dump.empty()){ vector<string> v; for(auto&r:Bc){ string s; for(int t=0;t<16;t++) s+=char('A'+r.g[t]); s+=' '+to_string(r.u1)+' '+to_string(r.u2); v.push_back(s);} sort(v.begin(),v.end()); FILE* fo=fopen((dump+"_1_"+to_string(c)).c_str(),"w"); for(auto&s:v) fprintf(fo,"%s\n",s.c_str()); fclose(fo); }
    cand.swap(keep);
  }
  printf("FINAL survivors %zu (a 17-clique needs survivors after all c=1..16)\n",cand.size());
}
