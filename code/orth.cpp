// enumerate normalised orthomorphisms of Z_17 (theta(0)=0), count, and canonical classes under
// translations (289), multipliers (16), S3 on sides. usage: orth [count|classes [OUTFILE]]  (P is compile-time, default 17: g++ -O3 -march=native -fopenmp orth.cpp -o orth).
// 'classes' writes the class representatives to OUTFILE only if OUTFILE is given (it never overwrites classes17.txt by itself).
// To regenerate the shipped list: ./orth classes classes17_regen.txt ; then compare, e.g. sort both files and diff / sha256sum.

#include <bits/stdc++.h>
#include <omp.h>
using namespace std; typedef unsigned long long u64; typedef unsigned int u32;
#ifndef P
#define P 17
#endif
struct Lin{ int a,b,c,d; }; // (x,y)->(a x+b y, c x+d y)
vector<Lin> grp; // multipliers x S3
static inline int md(int v){ v%=P; return v<0?v+P:v; }
bool isCanon(const int* th){
  // net points (a,th[a]); images under all lin maps and all 17 choices of origin; canonical if th is lexicographically minimal among normalised thetas
  int ax[P],bx[P];
  for(const Lin& L:grp){
    for(int a=0;a<P;a++){ ax[a]=md(L.a*a+L.b*th[a]); bx[a]=md(L.c*a+L.d*th[a]); }
    for(int o=0;o<P;o++){
      int t[P];
      for(int a=0;a<P;a++) t[md(ax[a]-ax[o])]=md(bx[a]-bx[o]);
      for(int i=1;i<P;i++){ if(t[i]<th[i]) return false; if(t[i]>th[i]) break; }
    }
  }
  return true;
}
int main(int argc,char**argv){
  string mode=argc>1?argv[1]:"count";
  // S3 generators on (x,y): swap12: (y,x); swap01: (-x, y-x)
  vector<array<int,4>> s3={{1,0,0,1}}; set<array<int,4>> S(s3.begin(),s3.end());
  auto mul=[&](array<int,4> A,array<int,4> B){ // A after B
    return array<int,4>{md(A[0]*B[0]+A[1]*B[2]),md(A[0]*B[1]+A[1]*B[3]),md(A[2]*B[0]+A[3]*B[2]),md(A[2]*B[1]+A[3]*B[3])}; };
  array<int,4> g1={0,1,1,0}, g2={P-1,0,P-1,1};
  bool ch=true; while(ch){ ch=false; vector<array<int,4>> cur(S.begin(),S.end()); for(auto A:cur) for(auto g:{g1,g2}){ auto C=mul(g,A); if(!S.count(C)){S.insert(C);ch=true;} } }
  fprintf(stderr,"S3 size %zu\n",S.size());
  for(int m=1;m<P;m++) for(auto A:S) grp.push_back({md(m*A[0]),md(m*A[1]),md(m*A[2]),md(m*A[3])});
  fprintf(stderr,"group (lin part) %zu\n",grp.size());
  // distinct as matrices?
  { set<array<int,4>> d; for(auto&L:grp) d.insert({L.a,L.b,L.c,L.d}); fprintf(stderr,"distinct %zu\n",d.size()); }
  // prefixes: theta(1),theta(2),theta(3)
  vector<array<int,3>> pre;
  for(int a=1;a<P;a++) for(int b=1;b<P;b++) if(b!=a) for(int c=1;c<P;c++) if(c!=a&&c!=b){
    // diffs th-i distinct and nonzero?? th(0)=0 so diff 0 used by index 0: others nonzero.
    int d1=md(a-1),d2=md(b-2),d3=md(c-3); if(!d1||!d2||!d3||d1==d2||d1==d3||d2==d3) continue; pre.push_back({a,b,c}); }
  fprintf(stderr,"prefixes %zu\n",pre.size());
  u64 total=0, ncanon=0; 
  vector<vector<array<int,P>>> found(omp_get_max_threads());
  double t0=omp_get_wtime();
  #pragma omp parallel for schedule(dynamic,1) reduction(+:total,ncanon)
  for(int pi=0;pi<(int)pre.size();pi++){
    int th[P]; th[0]=0; th[1]=pre[pi][0]; th[2]=pre[pi][1]; th[3]=pre[pi][2];
    u32 ua=1|(1u<<th[1])|(1u<<th[2])|(1u<<th[3]);
    u32 ub=1|(1u<<md(th[1]-1))|(1u<<md(th[2]-2))|(1u<<md(th[3]-3));
    int tid=omp_get_thread_num();
    function<void(int,u32,u32)> rec=[&](int a,u32 ua,u32 ub){
      if(a==P){ total++; if(mode=="classes" && isCanon(th)){ ncanon++; array<int,P> arr; for(int i=0;i<P;i++) arr[i]=th[i]; found[tid].push_back(arr);} return; }
      u32 fa=~ua&((1u<<P)-1);
      for(;fa;fa&=fa-1){ int v=__builtin_ctz(fa); int d=md(v-a); if((ub>>d)&1) continue; th[a]=v; rec(a+1,ua|(1u<<v),ub|(1u<<d)); }
    };
    rec(4,ua,ub);
  }
  printf("normalised orthomorphisms %llu  total %llu  canonical classes %llu  time %.1f\n",total,total*P,ncanon,omp_get_wtime()-t0);
  if(mode=="classes"){ if(argc<3){ fprintf(stderr,"classes: give OUTFILE as 2nd argument (nothing written)\n"); return 1; } FILE*f=fopen(argv[2],"w"); for(auto&v:found) for(auto&a:v){ for(int i=0;i<P;i++) fprintf(f,"%d ",a[i]); fprintf(f,"\n"); } fclose(f); }
}
