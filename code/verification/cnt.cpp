#include <bits/stdc++.h>
const int p=17; long cnt=0; unsigned u1=0,u2=0;
void rec(int a){ if(a==p){cnt++;return;} for(int v=0;v<p;v++){ if(a==0&&v) continue; int w=((v-a)%p+p)%p; if((u1>>v&1)||(u2>>w&1))continue; u1|=1u<<v;u2|=1u<<w; rec(a+1); u1&=~(1u<<v);u2&=~(1u<<w);} }
int main(){rec(0);printf("%ld %ld\n",cnt,cnt*17);}
