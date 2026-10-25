#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <map>
#include <algorithm>
using namespace std;
int main(int argc,char**argv){
 ifstream in(argv[1]);int nDesign;in>>nDesign;vector<array<int,10>>ds(nDesign);for(auto &d:ds)for(int&x:d)in>>x;
 vector<int>rs;int x;while(in>>x)rs.push_back(x);
 int ten[]={7,11,21,41,49,38,26,50,28,44};vector<int>T;for(int t:ten){T.push_back(t);T.push_back(t<<6);}
 const int N=22;vector<int>tripid(1<<N,-1);vector<int>ts;for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)for(int c=b+1;c<N;c++){int s=(1<<a)|(1<<b)|(1<<c);tripid[s]=ts.size();ts.push_back(s);}
 for(int R:rs){vector<bool>allowed(ts.size());for(int j=0;j<(int)ts.size();j++){int s=ts[j];bool ok=true;for(int t:T)if((s&t)==(s&R)&&(s&t)==(t&R)){ok=false;break;}allowed[j]=ok;}
 vector<pair<int,int>>good;int pts[6];
 for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)for(int c=b+1;c<N;c++)for(int d=c+1;d<N;d++)for(int e=d+1;e<N;e++)for(int f=e+1;f<N;f++){
 int ps[]={a,b,c,d,e,f};int sup=0;for(int p:ps)sup|=1<<p;
 for(int k=0;k<nDesign;k++){bool ok=true;for(int t:ds[k]){int s=0;for(int i=0;i<6;i++)if(t>>i&1)s|=1<<ps[i];if(!allowed[tripid[s]]){ok=false;break;}}if(ok)good.emplace_back(sup,k);}}
 map<int,int>supportCounts;int common=(1<<N)-1;for(auto[p,k]:good){supportCounts[p]++;common&=p;}
 vector<pair<int,int>>pairs;for(auto a=supportCounts.begin();a!=supportCounts.end();a++)for(auto b=supportCounts.begin();b!=a;b++)if(!(a->first&b->first))pairs.emplace_back(a->first,b->first);
 cout<<"{\"R\":"<<R<<",\"good_components\":"<<good.size()<<",\"common_support\":"<<common<<",\"supports\":[";bool first=true;for(auto[p,n]:supportCounts){if(!first)cout<<',';first=false;cout<<'['<<p<<','<<n<<']';}cout<<"],\"disjoint_support_pairs\":[";first=true;for(auto[a,b]:pairs){if(!first)cout<<',';first=false;cout<<'['<<a<<','<<b<<']';}cout<<"]}"<<endl;
 }
}
