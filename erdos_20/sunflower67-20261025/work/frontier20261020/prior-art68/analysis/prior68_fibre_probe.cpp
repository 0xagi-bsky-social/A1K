#include <algorithm>
#include <array>
#include <cstdint>
#include <functional>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>
using namespace std;
// Diagnostic only: exact integer reconstruction of the F68 / min-degree 24
// necessary fibre and point-star conditions. Not a theorem certificate.
using V=vector<int>;
V canon(const V &v) {
  int n=v.size(); V best=v,w(n);
  for(int s: {-1,1}) for(int o=0;o<n;o++){
    for(int i=0;i<n;i++)w[i]=v[(s*i+o+n)%n];
    best=min(best,w);
  }
  return best;
}
void show(const V &v){cout<<"[";for(int i=0;i<(int)v.size();i++)cout<<(i?",":"")<<v[i];cout<<"]";}
int main(){
  for(int k=3;k<=6;k++){
    int n=3*k-1;vector<V> adj(n);for(int i=0;i<n;i++)for(int j=0;j<n;j++)if(k<=(j-i+n)%n&&(j-i+n)%n<=2*k-1)adj[i].push_back(j);
    vector<int> independent;
    for(int mask=0;mask<(1<<n);mask++){
      bool ok=true;
      for(int i=0;i<n;i++)if(mask>>i&1)for(int j:adj[i])if(mask>>j&1)ok=false;
      if(ok){
        independent.push_back(mask);
        bool inwindow=false;
        for(int s=0;s<n;s++){
          int window=0;for(int h=0;h<k;h++)window|=1<<((s+h)%n);
          if(!(mask&~window))inwindow=true;
        }
        if(!inwindow){cerr<<"independent support outside a cyclic window";return 2;}
      }
    }
    set<V> reps;V r(n);
    function<void(int,int)> gen=[&](int i,int left){
      if(i==n){if(!left)reps.insert(canon(r));return;}
      for(int z=max(0,left-3*(n-i-1));z<=min(3,left);z++){r[i]=z;gen(i+1,left-z);}
    };gen(0,24-4*k);
    uint64_t stars=0,fail=0,alphaFail=0,coverFail=0;int minB=100000,minBadB=100000;
    for(auto R:reps){
      V a(n);for(int i=0;i<n;i++)a[i]=4+R[i]+R[(i+k)%n]+R[(i+2*k-1)%n];
      if(accumulate(a.begin(),a.end(),0)!=68){cerr<<"sum error";return 2;}
      for(int i=0;i<n;i++){int b=0;for(int j:adj[i])b+=a[j];if(b!=24+R[i]){cerr<<"inverse error";return 2;}}
      for(int mask=1;mask<(1<<n);mask++){
        V I,cap(n),t(n);bool ok=true,nonind=false;
        for(int i=0;i<n;i++)if(mask>>i&1){
          I.push_back(i);cap[i]=a[i];int d=0;for(int j:adj[i])if(mask>>j&1){d++;cap[i]=min(cap[i],R[j]);}
          if(d>R[i]||cap[i]==0){ok=false;break;}if(d)nonind=true;
        }
        if(!ok||!nonind)continue;
        int totalcap=0;for(int i:I)totalcap+=cap[i];if(totalcap<16)continue;
        function<void(int,int)> visit=[&](int pos,int left){
          if(pos==(int)I.size()){
            if(left)return;
            V q(n);for(int i=0;i<n;i++)for(int j:adj[i])q[i]+=t[j];
            for(int i:I)if(q[i]>R[i])return;
            stars++;int B=0;for(int i=0;i<n;i++)if(!q[i])B+=a[i]-t[i];
            minB=min(minB,B);if(B>=2)return;
            V near(n);
            for(int i=0;i<n;i++)if(q[i]==1){
              int jstar=-1;for(int j:adj[i])if(t[j])jstar=j;
              near[jstar]+=a[i]-t[i];
            }
            if(*max_element(near.begin(),near.end())+B>2)return;
            int alpha=16;
            for(int W:independent){
              int weight=0;
              for(int i=0;i<n;i++){
                if(W>>i&1)weight+=a[i]-t[i];
                bool meets=false;for(int j:adj[i])if(W>>j&1)meets=true;
                if(!meets)weight+=t[i];
              }
              alpha=max(alpha,weight);
            }
            if(alpha>27){alphaFail++;return;}
            V missing(n);
            for(int i=0;i<n;i++)for(int j:adj[i])if(t[j])missing[i]|=1<<j;
            const int coverCap[4]={1,2,4,10};
            for(int i=0;i<n;i++)if(q[i]<=3){
              int covered=0;
              for(int j=0;j<n;j++)if(!(missing[j]&~missing[i]))covered+=a[j]-t[j];
              if(covered>coverCap[q[i]]){coverFail++;return;}
            }
            fail++;minBadB=min(minBadB,B);
            if(fail<=8){cout<<"unresolved k="<<k<<" B="<<B<<" alpha="<<alpha<<" r=";show(R);cout<<" a=";show(a);cout<<" t=";show(t);cout<<" q=";show(q);cout<<" near=";show(near);cout<<"\n";}
            return;
          }
          int i=I[pos],futurecap=0;for(int p=pos+1;p<(int)I.size();p++)futurecap+=cap[I[p]];
          for(int z=max(1,left-futurecap);z<=min(cap[i],left-(int)I.size()+pos+1);z++){
            t[i]=z;bool feasible=true;
            for(int j:I){int used=0;for(int h:adj[j])used+=t[h];if(used>R[j]){feasible=false;break;}}
            if(feasible)visit(pos+1,left-z);
          }t[i]=0;
        };visit(0,16);
      }
    }
    cout<<"SUMMARY k="<<k<<" profiles="<<reps.size()<<" stars="<<stars<<" alpha-excluded="<<alphaFail<<" cover-excluded="<<coverFail<<" unresolved="<<fail<<" minB="<<minB<<" minUnresolvedB="<<minBadB<<endl;
    const int expectedProfiles[4]={543,1541,103,1};
    const int expectedStars[4]={33912,87790,2621,0};
    if(reps.size()!=expectedProfiles[k-3]||stars!=expectedStars[k-3]||fail){cerr<<"census mismatch or unresolved vector";return 3;}
  }
}
