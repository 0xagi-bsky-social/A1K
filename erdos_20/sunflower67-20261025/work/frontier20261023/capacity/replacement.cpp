#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Choices{int x=-1,y=-1;}; // x=-1 all; x=-2 none; y=-1 no second
inline void intersect(Choices&c,int a,int b=-1){
 if(c.x==-2)return;
 if(c.x==-1){c.x=a;c.y=b;return;}
 int u=(c.x==a||c.x==b)?c.x:-1;
 int v=c.y>=0&&(c.y==a||c.y==b)?c.y:-1;
 if(u<0){u=v;v=-1;} c.x=u>=0?u:-2;c.y=v;
}
int main(int argc,char**argv){
 int n=stoi(argv[1]);uint32_t full=(1u<<n)-1;
 vector<uint32_t> f;uint32_t a;ifstream in(argv[2]);while(in>>a)f.push_back(a);
 sort(f.begin(),f.end());vector<Choices> rem(1u<<n);vector<bool> member(1u<<n,false);
 for(auto a:f)member[a]=true;
 for(int i=0;i<(int)f.size();i++){
  uint32_t a=f[i];
  for(uint32_t s=a;;s=(s-1)&a){intersect(rem[s],i);if(!s)break;}
  uint32_t free=full^a;
  for(uint32_t s=free;;s=(s-1)&free){intersect(rem[a|s],i);if(!s)break;}
 }
 for(int i=0;i<(int)f.size();i++)for(int j=i+1;j<(int)f.size();j++){
  uint32_t core=f[i]&f[j],free=full^(f[i]|f[j]);
  for(uint32_t s=free;;s=(s-1)&free){intersect(rem[core|s],i,j);if(!s)break;}
 }
 ofstream out(argv[3]);int num=0;
 for(uint32_t a=0;a<=full;a++)if(!member[a]&&rem[a].x>=0){out<<a<<" "<<rem[a].x<<" "<<rem[a].y<<"\n";num++;}
 cout<<"one-removal candidates "<<num<<"\n";
}

