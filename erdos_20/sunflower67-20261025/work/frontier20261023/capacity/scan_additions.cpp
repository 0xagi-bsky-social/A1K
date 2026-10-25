#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 if(argc!=4){cerr<<"usage: scan_additions n family_masks output_candidates\n";return 2;}
 int n=stoi(argv[1]);uint32_t full=(1u<<n)-1;
 vector<uint32_t> fam;uint32_t a;ifstream in(argv[2]);while(in>>a)fam.push_back(a);
 if(!in.eof()){cerr<<"parse error\n";return 2;}
 sort(fam.begin(),fam.end());
 if(adjacent_find(fam.begin(),fam.end())!=fam.end()){cerr<<"duplicate input\n";return 2;}
 vector<uint8_t> forbidden(1u<<n,0),member(1u<<n,0);
 for(auto a:fam){if(a>full){cerr<<"range error\n";return 2;}member[a]=1;}
 uint64_t pair_completions=0,sunflowers=0,containments=0;
 // Single candidate antichain requirement: comparable to an existing member is forbidden.
 for(auto a:fam){
  for(uint32_t s=a;;s=(s-1)&a){forbidden[s]=1;if(s!=a&&member[s])containments++;if(!s)break;}
  uint32_t free=full^a;
  for(uint32_t s=free;;s=(s-1)&free){forbidden[a|s]=1;if(!s)break;}
 }
 // Exact all-candidate theorem: C forms sunflower with A,B iff
 // (A&B) subset C and C avoids A xor B; all outside A|B arbitrary.
 for(size_t i=0;i<fam.size();i++)for(size_t j=i+1;j<fam.size();j++){
  uint32_t core=fam[i]&fam[j],free=full^(fam[i]|fam[j]);
  for(uint32_t s=free;;s=(s-1)&free){
   uint32_t c=core|s;forbidden[c]=1;pair_completions++;
   if(c!=fam[i]&&c!=fam[j]&&member[c])sunflowers++;
   if(!s)break;
  }
 }
 ofstream out(argv[3]);size_t count=0;
 for(uint32_t s=0;s<=full;s++)if(!forbidden[s]){out<<s<<"\n";count++;}
 cout<<"{\"n\":"<<n<<",\"family_size\":"<<fam.size()<<",\"containments\":"<<containments
 <<",\"sunflower_triples\":"<<sunflowers/3<<",\"pair_completions\":"<<pair_completions
 <<",\"admissible_single_additions\":"<<count<<"}\n";
 return containments||sunflowers?1:0;
}

