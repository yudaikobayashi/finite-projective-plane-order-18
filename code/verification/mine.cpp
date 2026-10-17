// Independent re-implementation (audit). nets -> rows (T1-T3) -> pair compat -> exact bucket clique.
// usage: mine P mode [args]   mode "all": all orthomorphisms (theta(0)=0 if norm=1)
#include <bits/stdc++.h>
#include <omp.h>
using namespace std;
#ifndef P
#define P 7
#endif
typedef unsigned int u32;
struct Row{ unsigned char g[P]; unsigned char cnt[32]; unsigned char st[P+1]; unsigned char mem[P]; int u1,u2; };
static inline int md(int a){a%=P; if(a<0)a+=P; return a;}
// enumerate rows for net th
static void genRows(const int*th, vector<Row>&rows){
  int al[P],be[P]; for(int j=0;j<P;j++){al[j]=j;be[j]=th[j];}
  int g[P]; int cnt[P]; int blk[P][P]; // block members
  u32 used1=0, used2=0, cls=0; const int NC=(P-1)/2; const u32 full=(1u<<NC)-1;
  memset(cnt,0,sizeof cnt);
  function<void(int)> rec=[&](int x){
    if(x==P){ if(cls!=full) return;
      Row r; memset(&r,0,sizeof r); for(int y=1;y<P;y++) r.g[y]=g[y];
      for(int j=0;j<P;j++) r.cnt[j]=cnt[j];
      { int q=0; for(int j=0;j<P;j++){ r.st[j]=q; for(int y=1;y<P;y++) if(g[y]==j) r.mem[q++]=y; } r.st[P]=q; }
      u32 m1=(~used1)&((1u<<P)-1), m2=(~used2)&((1u<<P)-1);
      r.u1=__builtin_ctz(m1); r.u2=__builtin_ctz(m2); rows.push_back(r); return;}
    for(int c=0;c<P;c++){
      int v1=md(x-al[c]), v2=md(x-be[c]);
      if(used1>>v1&1) continue; if(used2>>v2&1) continue;
      u32 add=0; bool ok=true;
      for(int k=0;k<cnt[c];k++){ int d=md(x-blk[c][k]); int cl=min(d,P-d)-1; if((cls|add)>>cl&1){ok=false;break;} add|=1u<<cl; }
      if(!ok) continue;
      used1|=1u<<v1; used2|=1u<<v2; cls|=add; g[x]=c; blk[c][cnt[c]++]=x;
      rec(x+1);
      cnt[c]--; used1&=~(1u<<v1); used2&=~(1u<<v2); cls&=~add;
    }
  };
  rec(1);
}
static bool compat(const Row&r,const Row&s){
  // same column cross differences
  u32 m=0; int tot=0;
  for(int j=0;j<P;j++) for(int a=r.st[j];a<r.st[j+1];a++) for(int b=s.st[j];b<s.st[j+1];b++){
    int d=r.mem[a]-s.mem[b]; if(d<0)d+=P; if(d==0) return false; if(m>>d&1) return false; m|=1u<<d; tot++; }
  if(tot!=P-3) return false;
  int d1=md(r.u1-s.u1), d2=md(r.u2-s.u2);
  if(d1==0||d2==0||d1==d2) return false; if(m>>d1&1||m>>d2&1) return false;
  // column pair differences disjoint between rows
  static thread_local u32 Dr[P][P],Ds[P][P];
  memset(Dr,0,sizeof Dr); memset(Ds,0,sizeof Ds);
  for(int x=1;x<P;x++) for(int y=1;y<P;y++){ if(x==y) continue;
    if(r.g[x]!=r.g[y]) Dr[r.g[x]][r.g[y]]|=1u<<md(y-x);
    if(s.g[x]!=s.g[y]) Ds[s.g[x]][s.g[y]]|=1u<<md(y-x); }
  for(int j=0;j<P;j++)for(int k=0;k<P;k++) if(Dr[j][k]&Ds[j][k]) return false;
  return true;
}
static inline bool fastdot(const Row&r,const Row&s){ int t=0; for(int j=0;j<P;j++) t+=r.cnt[j]*s.cnt[j]; return t==P-3; }

// full plane verification of a row set (rows indexes into R)
static bool verifyPlane(const int*th,const vector<Row>&R,const vector<int>&sel){
  const int np=3+3*P+P*P; vector<vector<char>> inc; // lines x points
  auto pidx=[&](int k){return k;}; auto sidx=[&](int k,int z){return 3+k*P+md(z);}; auto gidx=[&](int i,int X){return 3+3*P+i*P+md(X);};
  int be[P]; for(int j=0;j<P;j++) be[j]=th[j];
  int s[3][P]; for(int j=0;j<P;j++){s[0][j]=0;s[1][j]=j;s[2][j]=be[j];}
  // L_k
  for(int k=0;k<3;k++){ vector<char> l(np,0); l[pidx((k+1)%3)]=l[pidx((k+2)%3)]=1; for(int z=0;z<P;z++) l[sidx(k,z)]=1; inc.push_back(l);}
  // V_{k,w}
  for(int k=0;k<3;k++) for(int w=0;w<P;w++){ vector<char> l(np,0); l[pidx(k)]=1; l[sidx(k,w)]=1;
    for(int i=0;i<P;i++){ const Row&r=R[sel[i]]; int u=(k==0?0:(k==1?r.u1:r.u2)); l[gidx(i,w-u)]=1;} inc.push_back(l);}
  // H_{j,y}
  for(int j=0;j<P;j++) for(int y=0;y<P;y++){ vector<char> l(np,0);
    for(int k=0;k<3;k++) l[sidx(k,y-s[k][j])]=1;
    for(int i=0;i<P;i++){ const Row&r=R[sel[i]]; for(int x=1;x<P;x++) if(r.g[x]==j) l[gidx(i,y-x)]=1;} inc.push_back(l);}
  for(auto&l:inc){ int c=0; for(char v:l)c+=v; if(c!=P+2) return false; }
  for(int a=0;a<np;a++)for(int b=a+1;b<np;b++){ int c=0; for(auto&l:inc) c+=(l[a]&&l[b]); if(c!=1) return false; }
  return true;
}
struct Res{ long rows=0,b1=0,a1=0,sols=0,verok=0,verfail=0; vector<vector<int>> solrows; };
// exact DFS: choose one per bucket
static void dfsPick(const vector<vector<int>>&L,vector<int>&chosen,vector<char>&done,const vector<Row>&R,long&sols,vector<vector<int>>*out,int r0){
  int best=-1; size_t bs=1e18; for(int c=0;c<(int)L.size();c++) if(!done[c]&&L[c].size()<bs){bs=L[c].size();best=c;}
  if(best<0){ sols++; if(out){ vector<int> v=chosen; v.push_back(r0); out->push_back(v);} return; }
  done[best]=1;
  for(int s:L[best]){
    vector<vector<int>> L2(L.size());
    bool ok=true;
    for(int c=0;c<(int)L.size();c++){ if(done[c]) continue; for(int t:L[c]) if(compat(R[s],R[t])) L2[c].push_back(t); if(L2[c].empty()){ok=false;break;} }
    if(!ok) continue;
    chosen.push_back(s); dfsPick(L2,chosen,done,R,sols,out,r0); chosen.pop_back();
  }
  done[best]=0;
}
static Res runNet(const int*th,bool keep,bool par=false){
  Res res; vector<Row> rows; genRows(th,rows); res.rows=rows.size();
  vector<vector<int>> B(P); for(int i=0;i<(int)rows.size();i++) B[rows[i].g[1]].push_back(i);
  res.b1=B[0].size();
  vector<char> surv(B[0].size(),0);
  long a1c=0,solc=0;
  #pragma omp parallel for schedule(dynamic,8) if(par) reduction(+:a1c,solc)
  for(long a=0;a<(long)B[0].size();a++){
    const Row&r=rows[B[0][a]];
    vector<vector<int>> L(P-1); bool ok=true;
    for(int c=1;c<P&&ok;c++){ for(int t:B[c]) if(fastdot(r,rows[t])&&compat(r,rows[t])) L[c-1].push_back(t); if(L[c-1].empty()) ok=false; if(c==1&&ok) a1c++; if(c==1&&!ok) {} }
    if(!ok) continue;
    vector<int> ch; vector<char> done(P-1,0); long s=0;
    vector<vector<int>> loc; dfsPick(L,ch,done,rows,s,&loc,B[0][a]); solc+=s;
    for(auto&q:loc){
      bool v=(P<=13)?verifyPlane(th,rows,q):true;
      #pragma omp critical
      { res.solrows.push_back(q); if(v) res.verok++; else {res.verfail++; puts("PLANE-VERIFY-FAIL");} }
    }
  }
  res.a1=a1c; res.sols=solc;
  return res;
}
// orthomorphisms
static void enumOrth(bool norm,vector<array<int,P>>&out){
  array<int,P> th; vector<char> u1(P,0),u2(P,0);
  function<void(int)> rec=[&](int a){
    if(a==P){out.push_back(th);return;}
    for(int v=0;v<P;v++){ if(norm&&a==0&&v!=0) continue; int w=md(v-a); if(u1[v]||u2[w])continue; u1[v]=u2[w]=1; th[a]=v; rec(a+1); u1[v]=u2[w]=0; }
  };
  rec(0);
}

static bool isCanon(const array<int,P>&th){
  int perms[6][3]={{0,1,2},{1,0,2},{2,1,0},{0,2,1},{1,2,0},{2,0,1}};
  for(int sw=0;sw<6;sw++) for(int m=1;m<P;m++){ int X[P],Y[P];
    for(int a=0;a<P;a++){ int t[3]={0,a,th[a]}; int u0=t[perms[sw][0]],u1=t[perms[sw][1]],u2=t[perms[sw][2]]; X[a]=md(u1-u0)*m%P; Y[a]=md(u2-u0)*m%P; }
    for(int k=0;k<P;k++){ array<int,P> q; for(int a=0;a<P;a++) q[md(X[a]-X[k])]=md(Y[a]-Y[k]); if(q<th) return false; } }
  return true;
}
int main(int argc,char**argv){
  string mode=argv[1];
  if(mode=="all"){ int norm=atoi(argv[2]); vector<array<int,P>> nets; enumOrth(norm>0,nets); if(norm==2){ vector<array<int,P>> k; for(auto&t:nets) if(isCanon(t)) k.push_back(t); nets=k; }
    fprintf(stderr,"P=%d nets=%zu\n",P,nets.size());
    long totsol=0,netsol=0,totrows=0; vector<Res> R(nets.size());
    #pragma omp parallel for schedule(dynamic,1)
    for(int i=0;i<(int)nets.size();i++){ R[i]=runNet(nets[i].data(),true); if(i%2000==0) fprintf(stderr,"done %d rows %ld\n",i,R[i].rows); }
    for(size_t i=0;i<nets.size();i++){ totsol+=R[i].sols; if(R[i].sols) netsol++; totrows+=R[i].rows;
      if(argc>3){ printf("net"); for(int v:nets[i]) printf(" %d",v); printf(" rows %ld b1 %ld a1 %ld sols %ld\n",R[i].rows,R[i].b1,R[i].a1,R[i].sols);
        for(auto&v:R[i].solrows){ printf("  SOL"); for(int ri:v) printf(" %d",ri); printf("\n"); } } }
    long vo=0,vf=0; for(auto&r:R){vo+=r.verok;vf+=r.verfail;} printf("P=%d nets=%zu nets_with_sol=%ld total_sols=%ld totrows=%ld plane_ok=%ld plane_fail=%ld\n",P,nets.size(),netsol,totsol,totrows,vo,vf);
  } else if(mode=="list"){ // read thetas from file lines: id theta...; args: file id0 id1 (line index)
    ifstream f(argv[2]); int a0=atoi(argv[3]),a1=atoi(argv[4]); string line; int idx=0;
    vector<array<int,P>> nets; vector<int> ids;
    while(getline(f,line)){ if(idx>=a0&&idx<a1){ istringstream is(line); array<int,P> t; for(int j=0;j<P;j++) is>>t[j]; nets.push_back(t); ids.push_back(idx);} idx++; }
    for(size_t i=0;i<nets.size();i++){ double t0=omp_get_wtime(); Res r=runNet(nets[i].data(),false,true);
      printf("%d rows %ld b1 %ld a1 %ld sols %ld t %.1f\n",ids[i],r.rows,r.b1,r.a1,r.sols,omp_get_wtime()-t0); fflush(stdout);} 
  }
}
