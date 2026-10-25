#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <map>
#include <vector>
using U=uint32_t;
struct Trace{U mask, containing; std::vector<U> blockers;};
std::vector<U>A;
std::vector<Trace>T;
int d,max_weight;
uint64_t cases;
U bestmask;
std::map<int,uint64_t> hist;
bool sf(U a,U b,U c){return (a&b)==(a&c)&&(a&b)==(b&c);}
int pc(U x){return __builtin_popcount(x);}
int weight(U omitted, bool print=false){
  int sum=0;
  for(const auto&t:T){
    bool good=true;
    for(U b:t.blockers) if(!(b&omitted)){good=false;break;}
    if(!good)continue;
    int rank=4-pc(t.mask),cap;
    bool contained=t.containing&~omitted;
    if(rank==0) cap=1;
    else if(rank==1) cap=contained?1:2;
    else if(rank==2) cap=contained?3:6;
    else cap=contained?10:20;
    sum+=cap;
    if(print) std::cout<<" "<<t.mask<<":"<<cap;
  }
  return sum;
}
void enumerate(int next,int need,U omitted){
  if(need==0){
    int w=weight(omitted);cases++;hist[w]++;
    if(w>max_weight){max_weight=w;bestmask=omitted;}
    return;
  }
  for(int i=next;i<=27-need;i++) enumerate(i+1,need-1,omitted|(U(1)<<i));
}
int main(){
  const auto begin=std::chrono::steady_clock::now();
  for(U a=0;a<512;a++){
    if(pc(a)!=4)continue;
    int s[3]={pc(a&7),pc((a>>3)&7),pc((a>>6)&7)};
    std::sort(s,s+3);
    if(s[0]==0&&s[1]==2&&s[2]==2)A.push_back(a);
  }
  assert(A.size()==27);
  for(U t=1;t<512;t++){
    if(pc(t)>4||std::find(A.begin(),A.end(),t)!=A.end())continue;
    Trace tr{t,0,{}};
    for(int i=0;i<27;i++){
      if((A[i]&t)==t)tr.containing|=U(1)<<i;
      for(int j=i+1;j<27;j++)if(sf(A[i],A[j],t))tr.blockers.push_back((U(1)<<i)|(U(1)<<j));
    }
    assert(!tr.blockers.empty());T.push_back(tr);
  }
  assert(T.size()==228);
  std::cout<<"AHS blocks:";
  for(U a:A)std::cout<<" "<<a;
  std::cout<<"\n";
  for(d=0;d<=7;d++){
    cases=0;hist.clear();max_weight=-1;bestmask=0;
    enumerate(0,d,0);
    std::cout<<"d="<<d<<" cases="<<cases<<" max_weight="<<max_weight
      <<" total_bound="<<54-d+max_weight<<" omitted="<<bestmask<<" traces:";
    weight(bestmask,true);std::cout<<" histogram:";
    for(auto [w,n]:hist)std::cout<<" "<<w<<":"<<n;
    std::cout<<"\n"<<std::flush;
  }
  std::cout<<"runtime_seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()<<"\n";
}
