#include <bits/stdc++.h>
const int p=17; long cnt=0; long bytype[5][5]; 
int sz[10]; 
void rec(unsigned assigned,unsigned cls,int nb,int*bs){
  int x=1; while(x<p&&(assigned>>x&1)) x++;
  if(x==p){ if(cls==(1u<<8)-1){cnt++;} return; }
  // block containing x: choose subset of larger unassigned elements, size 0..3
  std::vector<int> cand; for(int y=x+1;y<p;y++) if(!(assigned>>y&1)) cand.push_back(y);
  int n=cand.size();
  std::vector<int> blk={x};
  std::function<void(int,unsigned,unsigned)> pick=[&](int s,unsigned asg,unsigned cl){
    // option: close block here
    { bs[blk.size()]++; rec(asg,cl,nb+1,bs); bs[blk.size()]--; }
    if(blk.size()==4) return;
    for(int k=s;k<n;k++){ int y=cand[k]; unsigned add=0; bool ok=true;
      for(int z:blk){ int d=y-z; int c=std::min(d,p-d)-1; if(((cl|add)>>c)&1){ok=false;break;} add|=1u<<c; }
      if(!ok) continue; blk.push_back(y); pick(k+1,asg|1u<<y,cl|add); blk.pop_back(); }
  };
  pick(0,assigned|1u<<x,cls);
}
int main(){ int bs[6]={0}; rec(0,0,0,bs); printf("families %ld\n",cnt); }
