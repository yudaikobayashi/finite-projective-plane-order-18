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

vector<vector<u32>> fams;
static void genFams(){
  vector<u32> cur;
  function<void(u32,u32)> rec=[&](u32 placed,u32 usedcls){
    if(placed==((1u<<P)-2)){ if(usedcls==((1u<<((P-1)/2))-1)) fams.push_back(cur); return; }
    int x=1; while(placed>>x&1) x++;
    vector<int> el; for(int y=x+1;y<P;y++) if(!(placed>>y&1)) el.push_back(y);
    vector<int> B={x};
    function<void(int,u32)> ext=[&](int from,u32 uc){
      u32 m=0; for(int b:B) m|=1u<<b; cur.push_back(m); rec(placed|m,uc); cur.pop_back();
      if(B.size()==4) return;
      for(int i=from;i<(int)el.size();i++){ u32 uc2=uc; bool ok=true;
        for(int b:B){ int d=abs(el[i]-b); d=min(d,P-d)-1; if(uc2>>d&1){ok=false;break;} uc2|=1u<<d; }
        if(!ok) continue; B.push_back(el[i]); ext(i+1,uc2); B.pop_back(); }
    };
    ext(0,usedcls);
  };
  rec(0,0);
}
static void genBucket(const int*th,int c0,vector<Row>&out){
  out.clear(); const u32 FULLP=(1u<<P)-1;
  for(auto&F:fams){
    vector<u32> bl=F; int i1=-1; for(int i=0;i<(int)bl.size();i++) if(bl[i]&2) i1=i; swap(bl[0],bl[i1]);
    sort(bl.begin()+1,bl.end(),[](u32 a,u32 b){return __builtin_popcount(a)>__builtin_popcount(b);});
    int n=bl.size(); int col[P];
    function<void(int,u32,u32,u32)> go=[&](int k,u32 usedc,u32 im1,u32 im2){
      if(k==n){ Row r; memset(&r,0,sizeof r);
        for(int t=0;t<n;t++) for(int x=1;x<P;x++) if(bl[t]>>x&1) r.g[x]=col[t];
        for(int x=1;x<P;x++) r.cnt[r.g[x]]++;
        {int q=0; for(int j=0;j<P;j++){ r.st[j]=q; for(int y=1;y<P;y++) if(r.g[y]==j) r.mem[q++]=y; } r.st[P]=q;}
        r.u1=__builtin_ctz(FULLP&~im1); r.u2=__builtin_ctz(FULLP&~im2); out.push_back(r); return; }
      for(int cc=(k==0?c0:0);cc<=(k==0?c0:P-1);cc++){ if(usedc>>cc&1) continue;
        u32 a1=im1,a2=im2; bool ok=true;
        for(int x=1;x<P&&ok;x++) if(bl[k]>>x&1){ int v1=md(x-cc),v2=md(x-th[cc]); if((a1>>v1&1)||(a2>>v2&1)) ok=false; else {a1|=1u<<v1;a2|=1u<<v2;} }
        if(!ok) continue; col[k]=cc; go(k+1,usedc|(1u<<cc),a1,a2); }
    };
    go(0,0,0,0);
  }
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

int main(int argc,char**argv){
  // usage: mine17b classesfile id0 id1 [maxc]
  ifstream f(argv[1]); int a0=atoi(argv[2]),a1=atoi(argv[3]); int maxc=argc>4?atoi(argv[4]):P-1;
  vector<array<int,P>> nets; string line; while(getline(f,line)){ istringstream is(line); array<int,P> t; for(int j=0;j<P;j++) is>>t[j]; nets.push_back(t);} 
  genFams(); fprintf(stderr,"families %zu\n",fams.size());
  for(int id=a0;id<a1;id++){
    double t0=omp_get_wtime(); const int*th=nets[id].data();
    vector<Row> B0; genBucket(th,0,B0); vector<int> cand(B0.size()); iota(cand.begin(),cand.end(),0);
    string st="";
    int c=1;
    for(;c<=maxc&&!cand.empty();c++){
      vector<Row> Bc; genBucket(th,c,Bc); vector<char> has(cand.size(),0);
      #pragma omp parallel for schedule(dynamic,32)
      for(int q=0;q<(int)cand.size();q++){ const Row&r=B0[cand[q]]; for(const Row&s:Bc) if(fastdot(r,s)&&compat(r,s)){has[q]=1;break;} }
      vector<int> keep; for(size_t q=0;q<cand.size();q++) if(has[q]) keep.push_back(cand[q]);
      st+=" a"+to_string(c)+" "+to_string(keep.size()); cand.swap(keep);
    }
    printf("%d b1 %zu%s surv %zu t %.1f\n",id,B0.size(),st.c_str(),cand.size(),omp_get_wtime()-t0); fflush(stdout);
    if(!cand.empty()&&c>maxc) printf("SURVIVORS_AFTER_ALL_STAGES %d\n",id);
  }
}
