// Independent integer reconstruction of the order68 fibre/star domain.
// No solver and no import or execution of the Oct20 producer.
// Stars are partitioned by their first occupied graph edge, then generated
// directly as integer vectors with conditional neighbour-budget propagation.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <functional>
#include <iostream>
#include <numeric>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
#include <utility>
using Vec = std::vector<int>;
using Clock = std::chrono::steady_clock;

struct Search {
  int k, n;
  double seconds;
  Clock::time_point start;
  std::vector<uint32_t> adj;
  std::vector<std::pair<int,int>> edges;
  std::vector<Vec> edge_id;
  uint64_t nodes=0, independent_supports=0;
  void tick() {
    ++nodes;
    if ((nodes & 2047)==0 && std::chrono::duration<double>(Clock::now()-start).count()>seconds)
      throw std::runtime_error("bounded reconstruction deadline expired");
  }
  Search(int kk,double limit):k(kk),n(3*kk-1),seconds(limit),start(Clock::now()),adj(n,0),edge_id(n,Vec(n,-1)) {
    for(int u=0;u<n;++u) for(int v=u+1;v<n;++v)
      if(k<=v-u && v-u<=2*k-1) {
        edge_id[u][v]=edge_id[v][u]=int(edges.size()); edges.emplace_back(u,v);
        adj[u]|=uint32_t(1)<<v; adj[v]|=uint32_t(1)<<u;
      }
    for(uint32_t s=0;s<(uint32_t(1)<<n);++s) {
      bool independent=true;
      for(int i=0;i<n;++i) if((s>>i&1) && (s&adj[i])) {independent=false;break;}
      if(!independent) continue;
      ++independent_supports;
      bool window=false;
      for(int offset=0;offset<n;++offset) {
        uint32_t w=0;
        for(int j=0;j<k;++j) w|=uint32_t(1)<<((offset+j)%n);
        if((s&~w)==0) {window=true;break;}
      }
      if(!window) throw std::runtime_error("independent image support lacks a k-window");
    }
  }
  Vec canonical(const Vec &r) const {
    Vec best=r, candidate(n);
    for(int offset=0;offset<n;++offset) for(int sign:{1,-1}) {
      for(int i=0;i<n;++i) candidate[i]=r[(offset+sign*i+n)%n];
      if(candidate<best) best=candidate;
    }
    return best;
  }
  std::vector<Vec> profiles() {
    std::set<Vec> orbit;
    Vec r(n,0);
    std::function<void(int,int)> compose=[&](int pos,int left) {
      tick();
      if(pos==n) {if(left==0) orbit.insert(canonical(r));return;}
      for(int value=0;value<=3;++value) {
        if(value>left || left-value>3*(n-pos-1)) continue;
        r[pos]=value; compose(pos+1,left-value);
      }
    };
    compose(0,24-4*k);
    return {orbit.begin(),orbit.end()};
  }
  struct Result {
    Vec r,a,first_unresolved;
    uint64_t stars=0, unresolved=0;
    std::array<uint64_t,4> excluded{{0,0,0,0}};
  };
  Result profile(const Vec &r) {
    Result out; out.r=r; out.a.resize(n);
    for(int i=0;i<n;++i) out.a[i]=4+r[i]+r[(i+k)%n]+r[(i+2*k-1)%n];
    if(std::accumulate(out.a.begin(),out.a.end(),0)!=68) throw std::runtime_error("fibre total differs from68");
    for(int i=0;i<n;++i) {
      int b=0;for(int j=0;j<n;++j) if(adj[i]>>j&1) b+=out.a[j];
      if(b!=24+r[i] || out.a[i]<=0) throw std::runtime_error("inverse fibre identity failed");
    }
    const int caps[4]={1,2,4,10};
    for(int seed=0;seed<int(edges.size());++seed) {
      auto [u,v]=edges[seed];
      if(r[u]==0 || r[v]==0) continue;
      Vec order{u,v};
      for(int j=0;j<n;++j) if(j!=u && j!=v) order.push_back(j);
      // A fixed, seed-dependent order is different from support-first loops.
      std::stable_sort(order.begin()+2,order.end(),[&](int a,int b) {
        int da=((adj[a]>>u)&1)+((adj[a]>>v)&1);
        int db=((adj[b]>>u)&1)+((adj[b]>>v)&1);
        return da>db;
      });
      Vec t(n,0), q(n,0);
      uint32_t occupied=0;
      auto ceiling=[&](int vertex) {
        if(q[vertex]>r[vertex]) return 0;
        int upper=out.a[vertex];
        for(int w=0;w<n;++w) if((occupied>>w&1) && (adj[vertex]>>w&1)) {
          if(edge_id[vertex][w]<seed) return 0;
          upper=std::min(upper,r[w]-q[w]);
        }
        return std::max(upper,0);
      };
      std::function<void(int,int)> dfs=[&](int pos,int remaining) {
        tick();
        if(pos==n) {
          if(remaining) return;
          int first=-1,total=0;
          for(int e=0;e<int(edges.size());++e) if(t[edges[e].first] && t[edges[e].second]) {first=e;break;}
          if(first!=seed) throw std::runtime_error("first-occupied-edge partition failed");
          for(int i=0;i<n;++i) {
            total+=t[i];int recomputed=0;
            for(int j=0;j<n;++j) if(adj[i]>>j&1) recomputed+=t[j];
            if(recomputed!=q[i] || (t[i]>0 && q[i]>r[i]) || t[i]<0 || t[i]>out.a[i])
              throw std::runtime_error("generated star violates an exact domain condition");
          }
          if(total!=16) throw std::runtime_error("star total differs from16");
          ++out.stars;
          std::vector<uint32_t> missing(n);
          for(int i=0;i<n;++i) missing[i]=adj[i]&occupied;
          for(int i=0;i<n;++i) if(q[i]<=3) {
            int actual_covers=0;
            for(int j=0;j<n;++j) if((missing[j]&~missing[i])==0) actual_covers+=out.a[j]-t[j];
            if(actual_covers>caps[q[i]]) {++out.excluded[q[i]];return;}
          }
          ++out.unresolved;
          if(out.first_unresolved.empty()) out.first_unresolved=t;
          return;
        }
        int vertex=order[pos], upper=std::min(remaining,ceiling(vertex));
        int lower=(pos<2 ? 1 : 0);
        if(upper<lower) return;
        for(int value=lower;value<=upper;++value) {
          t[vertex]=value;
          if(value) {
            occupied|=uint32_t(1)<<vertex;
            for(int j=0;j<n;++j) if(adj[vertex]>>j&1) q[j]+=value;
          }
          int left=remaining-value, possible=0, mandatory=0;
          bool possible_seed=true;
          for(int next=pos+1;next<n;++next) {
            int cap=ceiling(order[next]);possible+=cap;
            if(next<2) {++mandatory;if(cap==0) possible_seed=false;}
          }
          if(possible_seed && mandatory<=left && left<=possible) dfs(pos+1,left);
          if(value) {
            for(int j=0;j<n;++j) if(adj[vertex]>>j&1) q[j]-=value;
            occupied&=~(uint32_t(1)<<vertex);
          }
          t[vertex]=0;
        }
      };
      dfs(0,16);
    }
    return out;
  }
};
void json_vec(const Vec &v) {std::cout<<'[';for(size_t i=0;i<v.size();++i){if(i)std::cout<<',';std::cout<<v[i];}std::cout<<']';}
int main(int argc,char **argv) {
  try {
    if(argc!=5) throw std::runtime_error("arguments: k seconds first_profile profile_count(0=all)");
    int k=std::stoi(argv[1]), first=std::stoi(argv[3]), count=std::stoi(argv[4]);
    double seconds=std::stod(argv[2]);
    if(k<3 || k>6 || seconds<=0 || seconds>60 || first<0 || count<0) throw std::runtime_error("invalid bounded request");
    Search search(k,seconds);auto profiles=search.profiles();
    const int expected_profiles[4]={543,1541,103,1};
    const uint64_t expected_stars[4]={33912,87790,2621,0};
    if(profiles.size()!=size_t(expected_profiles[k-3])) throw std::runtime_error("dihedral profile count mismatch");
    if(first>=int(profiles.size())) throw std::runtime_error("first_profile outside complete domain");
    int last=count==0 ? int(profiles.size()) : std::min(int(profiles.size()),first+count);
    std::vector<Search::Result> results;
    uint64_t stars=0,unresolved=0;std::array<uint64_t,4> excluded{{0,0,0,0}};
    for(int i=first;i<last;++i) {
      auto result=search.profile(profiles[i]);stars+=result.stars;unresolved+=result.unresolved;
      for(int j=0;j<4;++j) excluded[j]+=result.excluded[j];results.push_back(std::move(result));
    }
    bool complete=first==0 && last==int(profiles.size());
    if(complete && stars!=expected_stars[k-3]) throw std::runtime_error("full star count differs from expected independent reconstruction target");
    std::cout<<"{\"schema\":\"d16-fibre-edge-partition-census-v1\",\"k\":"<<k
             <<",\"profile_total\":"<<profiles.size()<<",\"first_profile\":"<<first<<",\"stop_profile\":"<<last
             <<",\"complete_k_domain\":"<<(complete?"true":"false")<<",\"stars\":"<<stars<<",\"unresolved\":"<<unresolved
             <<",\"independent_supports_window_checked\":"<<search.independent_supports<<",\"search_nodes\":"<<search.nodes
             <<",\"excluded_by_cap\":["<<excluded[0]<<','<<excluded[1]<<','<<excluded[2]<<','<<excluded[3]<<"],\"profiles\":[";
    for(size_t i=0;i<results.size();++i) {
      if(i)std::cout<<',';const auto &r=results[i];
      std::cout<<"{\"index\":"<<first+int(i)<<",\"r\":";json_vec(r.r);std::cout<<",\"a\":";json_vec(r.a);
      std::cout<<",\"stars\":"<<r.stars<<",\"unresolved\":"<<r.unresolved<<",\"first_unresolved\":";json_vec(r.first_unresolved);std::cout<<'}';
    }
    std::cout<<"],\"seconds\":"<<std::chrono::duration<double>(Clock::now()-search.start).count()<<"}\n";
    return unresolved ? 3 : 0;
  } catch(const std::exception &e) {std::cerr<<e.what()<<'\n';return 2;}
}
