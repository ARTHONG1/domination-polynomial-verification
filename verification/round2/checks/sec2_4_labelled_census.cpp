// Independent definition-based labelled-graph census, n=0..7.
// No domination-polynomial package or submitted C++ recurrence is used.
#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdint>
#include <numeric>
#include <queue>
#include <vector>

struct Totals {
  uint64_t graphs=0, forests=0, bipartite=0, assertions=0, violations=0;
  std::array<uint64_t,8> forests_by_n{}, bipartite_by_n{};
} out;

void test(bool ok, const char* name, int n, unsigned e) {
  ++out.assertions;
  if(!ok) {
    ++out.violations;
    if(out.violations<=15) fprintf(stderr,"FAIL %s n=%d edges=%u\n",name,n,e);
  }
}

void check(int n, unsigned edges) {
  std::array<unsigned,8> nb{};
  for(int i=0;i<n;i++) nb[i]=1u<<i;
  std::array<int,8> par{};
  std::iota(par.begin(),par.end(),0);
  auto find=[&](int v) {while(par[v]!=v)v=par[v]=par[par[v]]; return v;};
  bool forest=true;
  unsigned bit=0;
  for(int i=0;i<n;i++)for(int j=i+1;j<n;j++,bit++)if((edges>>bit)&1u){
    nb[i]|=1u<<j; nb[j]|=1u<<i;
    int a=find(i),b=find(j); if(a==b)forest=false; else par[a]=b;
  }
  std::array<int,8> col{};
  col.fill(-1);
  bool bip=true;
  for(int i=0;i<n;i++)if(col[i]<0){
    std::queue<int> q; q.push(i);col[i]=0;
    while(!q.empty()){
      int u=q.front();q.pop();
      for(int v=0;v<n;v++)if(v!=u && ((nb[u]>>v)&1u)){
        if(col[v]<0){col[v]=col[u]^1;q.push(v);}
        else if(col[v]==col[u])bip=false;
      }
    }
  }
  if(!bip&&!forest) return;
  ++out.graphs;
  if(forest){++out.forests;++out.forests_by_n[n];}
  if(bip){++out.bipartite;++out.bipartite_by_n[n];}
  unsigned m=1u<<n;
  std::array<unsigned char,128> dom{}, critical{};
  std::array<unsigned,8> d{},s1{},s2{};
  int gamma=n+1,Gamma=0,alpha=0;
  for(unsigned s=0;s<m;s++){
    bool dominates=true;
    for(int v=0;v<n;v++)if(!(nb[v]&s)){dominates=false;break;}
    dom[s]=dominates;
    bool ind=true;
    for(int v=0;v<n;v++)if((s>>v)&1u){
      if((nb[v] & s)!=(1u<<v)){ind=false;break;}
    }
    if(ind)alpha=std::max(alpha,__builtin_popcount(s));
  }
  for(unsigned s=0;s<m;s++)if(dom[s]){
    int j=__builtin_popcount(s),a=0;
    for(int v=0;v<n;v++)if(s>>v&1u){
      bool crit=!dom[s &~(1u<<v)];
      critical[s]|=unsigned(crit)<<v;
      a+=crit;
      bool witness=false;
      for(int w=0;w<n;w++)if((nb[w]&s)==(1u<<v))witness=true;
      test(crit==witness,"private_witness",n,edges);
    }
    d[j]++;s1[j]+=a;s2[j]+=a*a;
    gamma=std::min(gamma,j);
    if(a==j)Gamma=std::max(Gamma,j);
    test((a==j)==([&](){for(int v=0;v<n;v++)if(s>>v&1u)if(dom[s &~(1u<<v)])return false;return true;})(),"minimal",n,edges);
  }
  for(unsigned s=0;s<m;s++)if(dom[s])for(unsigned u=s;u<m;u=(u+1u)|s){
    if(dom[u])test((critical[u]&~critical[s])==0,"critical_monotonicity",n,edges);
    if(u==(m-1))break;
  }
  for(int j=0;j<=n;j++)test((d[j]>0)==(gamma<=j),"rank_nonzero",n,edges);
  for(int j=1;j<=n;j++){
    test((n-j+1)*d[j-1]==j*d[j]-s1[j],"incidence",n,edges);
    if(bip && 3*j>=n+2*alpha+1) test(d[j-1]>=d[j],"bip_segment",n,edges);
    if(forest && 3*j<=n+2*gamma+1) test(d[j-1]<=d[j],"forest_segment",n,edges);
  }
  unsigned total=std::accumulate(d.begin(),d.end(),0u),degree=0;
  for(int j=0;j<=n;j++)degree+=j*d[j];
  if(bip)test(3*degree<=(n+2*alpha)*total,"bip_avd",n,edges);
  if(forest)test(3*degree>=(n+2*gamma)*total,"forest_avd",n,edges);
  for(unsigned s=0;s<m;s++)if(dom[s]){
    int a=__builtin_popcount(critical[s]),j=__builtin_popcount(s);
    if(forest)test(j+a>=2*gamma,"forest_critical",n,edges);
    if(bip)test(j+a<=2*alpha,"bip_critical",n,edges);
  }
  for(int j=gamma+1;j<=n;j++){
    long long lhs=(long long)(j*d[j]-s1[j])*((long long)s1[j]*d[j-1]-(long long)s1[j-1]*d[j]);
    long long rhs=((long long)s2[j]*d[j]-(long long)s1[j]*s1[j])*d[j-1];
    test(lhs<=rhs,"covariance",n,edges);
  }
  for(int j=gamma+1;j<n;j++)if(d[j-1]>=d[j]&&d[j]<d[j+1]){
    test((long long)s1[j+1]*d[j]-(long long)s1[j]*d[j+1]>2LL*d[j]*d[j+1],"valley",n,edges);
  }
  if(forest){
    int h=Gamma-gamma,K=((h+1)*(h+1)+3)/4;
    for(int j=gamma+K;j<=n;j++)if(j>gamma){
      test((long long)s1[j]*d[j-1]-(long long)s1[j-1]*d[j]<=2LL*d[j]*d[j-1],"jump_Hh",n,edges);
    }
  }
}

int main(){
  for(int n=0;n<=7;n++){
    int m=n*(n-1)/2;
    for(unsigned e=0;e<(1u<<m);e++)check(n,e);
    fprintf(stderr,"n=%d bipartite=%llu forests=%llu violations=%llu\n",n,
       (unsigned long long)out.bipartite_by_n[n], (unsigned long long)out.forests_by_n[n], (unsigned long long)out.violations);
  }
  printf("{\"labelled_n\":\"0..7\",\"forests\":%llu,\"bipartite\":%llu,\"graph_cases\":%llu,\"assertions\":%llu,\"violations\":%llu}\n",
       (unsigned long long)out.forests,(unsigned long long)out.bipartite,(unsigned long long)out.graphs,
       (unsigned long long)out.assertions,(unsigned long long)out.violations);
  return out.violations ? 1:0;
}
