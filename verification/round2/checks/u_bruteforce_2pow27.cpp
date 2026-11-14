// Independent 2^27 definition-based subset audit, including centre split.
#include <array>
#include <cstdint>
#include <cstdio>
#include <vector>
using u64=uint64_t;
int main(){
  std::vector<uint32_t> nb;
  auto add=[&](int parent)->int{
    int id=(int)nb.size(); nb.push_back(1u<<id);
    if(parent>=0){nb[id]|=1u<<parent;nb[parent]|=1u<<id;}
    return id;
  };
  add(-1);  // v0 = 0
  for(int k: {2,2,3}){
    int hub=add(0);
    for(int arm=0;arm<k;arm++){
      int a=add(hub);int b=add(a);add(b);
    }
  }
  int a=add(0);add(a);
  const int n=(int)nb.size();
  if(n!=27)return 3;
  const uint32_t total=1u<<n,full=total-1;
  std::vector<uint32_t> covered(total);
  std::array<u64,28> all{},with0{},without0{};
  for(uint32_t s=1;s<total;s++){
    uint32_t low=s&-s;
    int v=__builtin_ctz(low);
    covered[s]=covered[s^low]|nb[v];
    if(covered[s]==full){
      int sz=__builtin_popcount(s);
      all[sz]++;
      (s&1?with0:without0)[sz]++;
    }
  }
  int gamma=0;while(gamma<=n&&!all[gamma])gamma++;
  int lcFails=0,nonUnimodal=0,idx=0;
  for(int j=1;j<n;j++)if((__uint128_t)all[j]*all[j] < (__uint128_t)all[j-1]*all[j+1]){lcFails++;idx=j;}
  bool descending=false;
  for(int j=1;j<=n;j++){
    if(all[j]<all[j-1])descending=true;
    if(descending&&all[j]>all[j-1])nonUnimodal++;
  }
  printf("{\"n\":27,\"subsets\":%u,\"gamma\":%d,\"lc_violations\":%d,\"lc_index\":%d,\"unimodal_violations\":%d,",total,gamma,lcFails,idx,nonUnimodal);
  printf("\"coefficients\":[");
  for(int j=0;j<=n;j++)printf("%s%llu",j?",":"",(unsigned long long)all[j]);
  printf("],\"with_centre\":[");
  for(int j=gamma;j<=gamma+2;j++)printf("%s%llu",j==gamma?"":",",(unsigned long long)with0[j]);
  printf("],\"without_centre\":[");
  for(int j=gamma;j<=gamma+2;j++)printf("%s%llu",j==gamma?"":",",(unsigned long long)without0[j]);
  printf("],\"d10_squared\":%llu,\"d9_times_d11\":%llu}\n",
    (unsigned long long)(all[10]*all[10]),(unsigned long long)(all[9]*all[11]));
  return (gamma!=9 || lcFails!=1 || idx!=10 || nonUnimodal!=0 || all[10]*all[10]!=5625 || all[9]*all[11]!=5674);
}
