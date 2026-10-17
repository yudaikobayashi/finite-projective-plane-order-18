#include <bits/stdc++.h>
using namespace std; const int p=17; typedef array<int8_t,p> T;
int main(){ ifstream f("../t17h/classes17.txt"); string line; long total=0,n=0,bad=0; map<int,long> dist;
 int perms[6][3]={{0,1,2},{1,0,2},{2,1,0},{0,2,1},{1,2,0},{2,0,1}};
 while(getline(f,line)){ istringstream is(line); T th; for(int j=0;j<p;j++){int v;is>>v;th[j]=v;}
  set<T> orb; 
  for(int sw=0;sw<6;sw++) for(int m=1;m<p;m++){ int X[p],Y[p];
    for(int a=0;a<p;a++){ int t[3]={0,a,th[a]}; int u0=t[perms[sw][0]],u1=t[perms[sw][1]],u2=t[perms[sw][2]];
      X[a]=((u1-u0+p)%p)*m%p; Y[a]=((u2-u0+p)%p)*m%p; }
    for(int k=0;k<p;k++){ T q; for(int a=0;a<p;a++) q[((X[a]-X[k])%p+p)%p]=((Y[a]-Y[k])%p+p)%p; orb.insert(q);} }
  if(*orb.begin()!=th) bad++;
  total+=orb.size(); dist[orb.size()]++; n++; }
 printf("classes %ld total %ld notmin %ld\n",n,total,bad); for(auto&kv:dist) printf("size %d: %ld\n",kv.first,kv.second);
}
