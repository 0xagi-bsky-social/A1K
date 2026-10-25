#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <map>
#include <vector>
using namespace std;
int lift(int s, int supp) {
  int out=0,k=0;
  for(int i=0;i<24;i++) if(supp>>i&1) {
    if(s>>k&1) out|=1<<i;
    k++;
  }
  return out;
}
int main(int argc,char**argv) {
  if(argc!=3) return 2;
  ifstream in(argv[1]);ofstream out(argv[2]);
  int np;in>>np; vector<pair<int,int>> ps(np);
  for(auto&[a,b]:ps)in>>a>>b;
  int d[12][10];for(auto&row:d)for(int&x:row)in>>x;
  int ten[]={7,11,21,41,49,38,26,50,28,44};
  vector<int>T,triples,rows;map<int,int>tid;
  for(int x:ten){T.push_back(x);T.push_back(x<<6);}
  for(int i=0;i<24;i++)for(int j=i+1;j<24;j++)for(int k=j+1;k<24;k++){
    int s=(1<<i)|(1<<j)|(1<<k);tid[s]=triples.size();triples.push_back(s);
  }
  for(int i=0;i<28;i++)for(int j=i+1;j<28;j++)for(int k=j+1;k<28;k++)
    for(int l=k+1;l<28;l++)rows.push_back((1<<i)|(1<<j)|(1<<k)|(1<<l));
  vector<vector<unsigned char>> ok(triples.size(),vector<unsigned char>(rows.size()));
  for(int s=0;s<(int)triples.size();s++)for(int r=0;r<(int)rows.size();r++){
    bool a=true;int S=triples[s],R=rows[r];
    for(int t:T)if((t&S)==(t&R)&&(t&S)==(S&R)){a=false;break;}
    ok[s][r]=a;
  }
  int total=0,maxn=0;bool inside=true;map<int,int>hist;
  for(int p=0;p<np;p++){
    auto[A,B]=ps[p];
    for(int a=0;a<12;a++)for(int b=0;b<12;b++){
      total++;vector<int>S,cand;
      for(int t:d[a])S.push_back(tid.at(lift(t,A)));
      for(int t:d[b])S.push_back(tid.at(lift(t,B)));
      for(int r=0;r<(int)rows.size();r++){
        bool good=true;for(int t:S)if(!ok[t][r]){good=false;break;}
        if(good){cand.push_back(rows[r]);if(rows[r]&~(4095|A|B))inside=false;}
      }
      int n=cand.size();hist[n]++;maxn=max(n,maxn);
      if(n){out<<p<<' '<<a<<' '<<b<<' '<<A<<' '<<B<<' '<<n;
        for(int R:cand)out<<' '<<R;out<<'\n';}
    }
  }
  cout<<"{\"geometries\":"<<total<<",\"candidate_R\":"<<rows.size()
      <<",\"max_compatible_R\":"<<maxn<<",\"all_inside_actual_link_union\":"
      <<(inside?"true":"false")<<",\"histogram\":{";
  bool first=true;for(auto[n,c]:hist){if(!first)cout<<',';first=false;cout<<'"'<<n<<"\":"<<c;}cout<<"}}\n";
}
