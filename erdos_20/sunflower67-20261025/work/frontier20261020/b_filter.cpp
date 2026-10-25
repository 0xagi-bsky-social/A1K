#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <map>
#include <vector>
using namespace std;
int lift(int s, int supp) {
  int out=0,k=0;
  for(int i=0;i<15;i++) if(supp>>i&1) {
    if(s>>k&1) out|=1<<i;
    k++;
  }
  return out;
}
int main(int argc,char**argv) {
  if(argc!=3) return 2;
  ifstream in(argv[1]); ofstream out(argv[2]);
  int np;in>>np;
  vector<pair<int,int>> ps(np);
  for(auto&[a,b]:ps) in>>a>>b;
  int d[12][10];for(auto&row:d)for(int&x:row)in>>x;
  vector<int> T, triples, rows;
  // Same labelled canonical design as Python TEN.
  int ten[]={7,11,21,41,49,38,26,50,28,44};
  for(int x:ten){T.push_back(x);T.push_back(x<<6);}
  vector<int> tid(1<<15,-1);
  for(int s=0;s<(1<<15);s++){
    int k=__builtin_popcount((unsigned)s);
    if(k==3){tid[s]=triples.size();triples.push_back(s);}
    if(k==4) rows.push_back(s);
  }
  vector<vector<int>> allowed(triples.size(),vector<int>(rows.size()));
  for(int j=0;j<(int)triples.size();j++)
    for(int r=0;r<(int)rows.size();r++){
      int S=triples[j],R=rows[r]; bool ok=true;
      for(int t:T) if((t&S)==(t&R) && (t&S)==(S&R)){ok=false;break;}
      allowed[j][r]=ok;
    }
  int total=0,survive=0,minn=2000,maxn=0;
  map<int,int> hist;
  for(int p=0;p<np;p++){
    auto[A,B]=ps[p];
    for(int a=0;a<12;a++) for(int b=0;b<12;b++){
      total++;vector<int>S;for(int t:d[a])S.push_back(tid[lift(t,A)]);
      for(int t:d[b])S.push_back(tid[lift(t,B)]);
      vector<int>cand;int deg[15]={};
      for(int r=0;r<(int)rows.size();r++){
        bool ok=true;
        for(int t:S) if(!allowed[t][r]){ok=false;break;}
        if(ok){cand.push_back(rows[r]);for(int i=0;i<15;i++)deg[i]+=rows[r]>>i&1;}
      }
      int n=cand.size();minn=min(minn,n);maxn=max(maxn,n);hist[n]++;
      vector<int>exceptions;
      if(n>=41)for(int ex=0;ex<15;ex++){
        bool ok=true;
        for(int i=0;i<15;i++){
          int k=(i<12)+((A|B)>>i&1);
          if(deg[i]<19-5*k-(ex==i)){ok=false;break;}
        }
        if(ok) exceptions.push_back(ex);
      }
      if(!exceptions.empty()) survive++;
      if(n>0){
        out<<p<<' '<<a<<' '<<b<<' '<<A<<' '<<B<<' '<<exceptions.size();
        for(int e:exceptions)out<<' '<<e;
        out<<' '<<n;for(int r:cand)out<<' '<<r;out<<'\n';
      }
    }
  }
  cout<<"{\"geometries\":"<<total<<",\"survivors\":"<<survive
      <<",\"candidate_min\":"<<minn<<",\"candidate_max\":"<<maxn<<",\"histogram\":{";
  bool first=true;for(auto[n,c]:hist){if(!first)cout<<',';first=false;cout<<'"'<<n<<"\":"<<c;}cout<<"}}\n";
}
