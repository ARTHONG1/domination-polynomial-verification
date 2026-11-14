// Third, independent exhaustive check (audit 2026-11-13).
// Generator: free trees as centroid-rooted multisets of rooted subtrees (no level sequences).
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <thread>
#include <atomic>
#include <mutex>
#include <map>
#include <array>
#include <algorithm>
#include <string>
#include <cstdint>
typedef unsigned long long u64; typedef __uint128_t u128;
static int NMAX;
struct Poly { u64 c[28]; };
static inline void mul(const Poly&a,const Poly&b,Poly&r){ u64 t[28]; for(int i=0;i<=NMAX;i++)t[i]=0; for(int i=0;i<=NMAX;i++){u64 x=a.c[i]; if(!x)continue; for(int j=0;i+j<=NMAX;j++) t[i+j]+=x*b.c[j];} memcpy(r.c,t,sizeof(u64)*28);} 
struct Node{ std::vector<int> ch; int size; Poly P1,P2,P3,S,AB,Bv; int in,out; };
static std::vector<Node> nodes; static std::vector<int> firstId, lastId; // by size
static Poly ONE;
static void finalize(Node&nd){ // from P1,P2,P3
  for(int i=0;i<28;i++){nd.S.c[i]=nd.AB.c[i]=nd.Bv.c[i]=0;}
  for(int i=0;i<=NMAX;i++){ u64 a=(i>=1?nd.P1.c[i-1]:0); u64 b=nd.P2.c[i]-nd.P3.c[i]; nd.S.c[i]=a+nd.P2.c[i]; nd.AB.c[i]=a+b; nd.Bv.c[i]=b; }
}
static void genRooted(int s,int rem,int maxId,std::vector<int>&cur){
  if(rem==0){ Node nd; nd.ch=cur; nd.size=s; nd.P1=nd.P2=nd.P3=ONE; int in=1,out=0; for(int w:cur){ mul(nd.P1,nodes[w].S,nd.P1); mul(nd.P2,nodes[w].AB,nd.P2); mul(nd.P3,nodes[w].Bv,nd.P3); in+=nodes[w].out; out+=std::max(nodes[w].in,nodes[w].out);} nd.in=in; nd.out=out; finalize(nd); nodes.push_back(nd); return; }
  int cap=std::min(rem,s-1); int hi=std::min(maxId,lastId[cap]);
  for(int id=hi;id>=0;id--){ if(nodes[id].size>rem)continue; cur.push_back(id); genRooted(s,rem-nodes[id].size,id,cur); cur.pop_back(); }
}

// Unique exact AHU free-tree encoding. For n<=22, length <= 46 bits.
// Each rooted subtree is reconstructed *by shape*, children re-sorted
// by their rooted AHU parentheses strings rather than by generator IDs.
static std::vector<std::string> ahu;
static const std::string& rooted_code(int idx){
  if(!ahu[idx].empty()) return ahu[idx];
  std::vector<std::string> child;
  for(int c:nodes[idx].ch) child.push_back(rooted_code(c));
  std::sort(child.begin(),child.end());
  std::string s="(";
  for(auto &x:child) s+=x;
  s+=")";
  ahu[idx]=s;
  return ahu[idx];
}
static uint64_t tree_code(int n,const std::vector<int>&desc){
  std::vector<std::string> child;
  bool bicenter=desc.size()==3 && desc[0]==-1;
  for(size_t i=bicenter?1:0;i<desc.size();i++) child.push_back(rooted_code(desc[i]));
  std::sort(child.begin(),child.end());
  std::string c="(";
  for(auto &x:child)c+=x;
  c+=")";
  if(c.size()!=(size_t)(2*n+(bicenter?2:0)) || c.size()>63){
    fprintf(stderr,"AHU code construction length mismatch n=%d len=%zu\n",n,c.size());
    exit(8);
  }
  uint64_t bits=0;
  for(char ch:c){bits=(bits<<1)+(ch=='(' ? 1u : 0u);}
  return bits;
}

struct Jump { long long num=0; u64 den=1; int j=-1; bool valid=false; };
static void offer(Jump& best,long long num,u64 den,int j){
  if(!best.valid || (__int128)num*best.den > (__int128)best.num*den){
    best.num=num; best.den=den; best.j=j; best.valid=true;
  }
}
struct Acc{ u64 count=0,lcFail=0,uniFail=0; std::map<std::array<int,2>,u64> hist; std::vector<std::vector<int>> wit; std::vector<Poly> witPoly; std::vector<uint64_t> codes; Jump maxJump,maxRestricted; };
static void evalTree(int n,const Poly&P1,const Poly&P2,const Poly&P3,int in,int out,Acc&acc,const std::vector<int>&desc){
  u64 d[30]; for(int i=0;i<=n;i++){ d[i]=(i>=1?P1.c[i-1]:0)+P2.c[i]-P3.c[i]; } d[n+1]=0;
  acc.count++; acc.codes.push_back(tree_code(n,desc)); int g=0; while(d[g]==0)g++;
  bool lc=true; for(int j=1;j<n;j++) if((u128)d[j]*d[j] < (u128)d[j-1]*d[j+1]) {lc=false;break;}
  bool uni=true; { int j=0; while(j<n && d[j]<=d[j+1]) j++; while(j<n && d[j]>=d[j+1]) j++; uni=(j==n); }
  if(d[n]!=1||d[n-1]!=(u64)n){ fprintf(stderr,"sanity fail\n"); exit(3);} 
  for(int j=g+1;j<n;j++){
    u64 den=d[j]*d[j+1];
    long long num=(long long)den+(long long)((n-j+1)*d[j-1]*d[j+1])-(long long)((n-j)*d[j]*d[j]);
    offer(acc.maxJump,num,den,j);
    if(3*j>n+2*g+1) offer(acc.maxRestricted,num,den,j);
  }
  if(!lc){ acc.lcFail++; acc.wit.push_back(desc); Poly p; memset(&p,0,sizeof p); for(int i=0;i<=n;i++)p.c[i]=d[i]; acc.witPoly.push_back(p);} if(!uni)acc.uniFail++;
  int Gam=std::max(in,out); acc.hist[{n-g,Gam-g}]++;
}
static void dfs(int n,int rem,int maxId,int cap,const Poly&P1,const Poly&P2,const Poly&P3,int in,int out,Acc&acc,std::vector<int>&cur){
  if(rem==0){ evalTree(n,P1,P2,P3,in,out,acc,cur); return; }
  int c=std::min(rem,cap); int hi=std::min(maxId,lastId[c]);
  for(int id=hi;id>=0;id--){ const Node&w=nodes[id]; Poly a,b,cc; mul(P1,w.S,a); mul(P2,w.AB,b); mul(P3,w.Bv,cc); cur.push_back(id); dfs(n,rem-w.size,id,cap,a,b,cc,in+w.out,out+std::max(w.in,w.out),acc,cur); cur.pop_back(); }
}
// explicit structure for brute force
static void build(int id,int par,std::vector<std::vector<int>>&adj){ int v=adj.size(); adj.push_back({}); if(par>=0){adj[v].push_back(par);adj[par].push_back(v);} for(int w:nodes[id].ch) build(w,v,adj); }
static u64 bruteChecked=0;
static void brute(const std::vector<std::vector<int>>&adj,const u64*dexp,int gam,int Gam){
  int n=adj.size(); std::vector<unsigned> nb(n); for(int v=0;v<n;v++){ nb[v]=1u<<v; for(int w:adj[v]) nb[v]|=1u<<w; }
  std::vector<u64> d(n+1,0); int g=n,G=0; unsigned full=(1u<<n)-1;
  for(unsigned S=0;S<=full;S++){ bool dom=true; for(int v=0;v<n;v++) if(!(nb[v]&S)){dom=false;break;} if(!dom)continue; int sz=__builtin_popcount(S); d[sz]++; if(sz<g)g=sz;
    int a=0; for(int v=0;v<n;v++) if(S>>v&1){ unsigned T=S&~(1u<<v); bool dm=true; for(int u=0;u<n;u++) if(!(nb[u]&T)){dm=false;break;} if(!dm)a++; }
    if(a==sz && sz>G) G=sz; if(a>2*Gam-sz || a+sz<2*gam){ fprintf(stderr,"two-sided bound violated\n"); exit(4);} }
  for(int i=0;i<=n;i++) if(d[i]!=dexp[i]){ fprintf(stderr,"brute mismatch n=%d\n",n); exit(5);} if(g!=gam||G!=Gam){ fprintf(stderr,"gamma/Gamma mismatch n=%d %d %d %d %d\n",n,g,gam,G,Gam); exit(6);} bruteChecked++;
}
int main(int argc,char**argv){ NMAX=atoi(argv[1]); int BR=argc>2?atoi(argv[2]):14; int NT=argc>3?atoi(argv[3]):10;
  memset(&ONE,0,sizeof ONE); ONE.c[0]=1; int half=NMAX/2; firstId.assign(half+2,0); lastId.assign(NMAX+2,0); lastId[0]=-1;
  for(int s=1;s<=half;s++){ firstId[s]=nodes.size(); std::vector<int> cur; if(s==1){ Node nd; nd.size=1; nd.P1=nd.P2=nd.P3=ONE; nd.in=1; nd.out=0; finalize(nd); nodes.push_back(nd);} else genRooted(s,s-1,(int)nodes.size()-1,cur); for(int q=s;q<=NMAX+1;q++) lastId[q]=nodes.size()-1; }
  // Otter numbers
  std::vector<u128> R(NMAX+2,0),T(NMAX+2,0); R[1]=1; for(int m=2;m<=NMAX;m++){ u128 s=0; for(int j=1;j<m;j++){ u128 sd=0; for(int e=1;e<=j;e++) if(j%e==0) sd+=(u128)e*R[e]; s+=sd*R[m-j]; } R[m]=s/(m-1);} for(int m=1;m<=NMAX;m++){ u128 cv=0; for(int k=1;k<m;k++) cv+=R[k]*R[m-k]; u128 e=(m%2==0)?R[m/2]:0; T[m]=R[m]-(cv-e)/2; }
  for(int s=1;s<=half;s++){ u64 cnt=(s<half? firstId[s+1]:(int)nodes.size())-firstId[s]; if(cnt!=(u64)R[s]){ fprintf(stderr,"rooted count mismatch %d\n",s); return 2; } }
  ahu.assign(nodes.size(),std::string());
  for(size_t id=0;id<nodes.size();id++) rooted_code((int)id);
  u64 total=1; // K_1
  for(int n=2;n<=NMAX;n++){ int cap=(n-1)/2; std::vector<Acc> accs(NT);
    // tasks: first child id
    std::vector<int> tasks; for(int id=lastId[std::min(cap,n-1)];id>=0;id--) tasks.push_back(id);
    std::atomic<size_t> next(0); std::vector<std::thread> th;
    for(int t=0;t<NT;t++) th.emplace_back([&,t](){ Acc&acc=accs[t]; while(true){ size_t k=next++; if(k>=tasks.size())break; int id=tasks[k]; const Node&w=nodes[id]; std::vector<int> cur{id}; dfs(n,n-1-w.size,id,cap,w.S,w.AB,w.Bv,1+w.out,std::max(w.in,w.out),acc,cur);} });
    for(auto&x:th)x.join(); Acc tot; for(auto&a:accs){ tot.count+=a.count; tot.codes.insert(tot.codes.end(),a.codes.begin(),a.codes.end()); tot.lcFail+=a.lcFail; tot.uniFail+=a.uniFail; for(auto&kv:a.hist)tot.hist[kv.first]+=kv.second; for(size_t i=0;i<a.wit.size();i++){tot.wit.push_back(a.wit[i]);tot.witPoly.push_back(a.witPoly[i]);} if(a.maxJump.valid)offer(tot.maxJump,a.maxJump.num,a.maxJump.den,a.maxJump.j); if(a.maxRestricted.valid)offer(tot.maxRestricted,a.maxRestricted.num,a.maxRestricted.den,a.maxRestricted.j); }
    if(n%2==0){ int h=n/2; int lo=firstId[h], hi=lastId[h]; std::vector<int> cur; for(int i=lo;i<=hi;i++) for(int j=i;j<=hi;j++){ const Node&a=nodes[i],&b=nodes[j]; Poly p1,p2,p3; mul(a.P1,b.S,p1); mul(a.P2,b.AB,p2); mul(a.P3,b.Bv,p3); cur={-1,i,j}; evalTree(n,p1,p2,p3,a.in+b.out,a.out+std::max(b.in,b.out),tot,cur);} }
    if(tot.count!=(u64)T[n]){ fprintf(stderr,"free tree count mismatch n=%d got %llu want %llu\n",n,tot.count,(u64)T[n]); return 2; }
    if(tot.codes.size()!=tot.count){fprintf(stderr,"AHU code-count mismatch n=%d\n",n);return 9;}
    std::sort(tot.codes.begin(),tot.codes.end());
    if(std::adjacent_find(tot.codes.begin(),tot.codes.end())!=tot.codes.end()){fprintf(stderr,"DUPLICATE AHU free tree n=%d\n",n);return 10;}
    fprintf(stderr,"CANONICAL_PASS n=%d code_distinct=%zu otter=%llu\n",n,tot.codes.size(),(u64)T[n]);
    total+=tot.count;
    printf("{\"n\":%d,\"trees\":%llu,\"nonLC\":%llu,\"nonUnimodal\":%llu,\"maxJump\":[%lld,%llu,%d],\"maxRestricted\":[%lld,%llu,%d],\"hist\":[",n,tot.count,tot.lcFail,tot.uniFail,tot.maxJump.num,tot.maxJump.den,tot.maxJump.j,tot.maxRestricted.num,tot.maxRestricted.den,tot.maxRestricted.j); bool f=true; for(auto&kv:tot.hist){ printf("%s[%d,%d,%llu]",f?"":",",kv.first[0],kv.first[1],kv.second); f=false;} printf("]}\n");
    for(size_t i=0;i<tot.wit.size();i++){ printf("WITNESS n=%d children:",n); for(int id:tot.wit[i]) printf(" %d",id); printf(" poly:"); for(int k=0;k<=n;k++) printf(" %llu",tot.witPoly[i].c[k]); printf("\n"); 
      // print structure as parent array
      if(tot.wit[i].size()&&tot.wit[i][0]>=0){ std::vector<std::vector<int>> adj; adj.push_back({}); for(int id:tot.wit[i]) build(id,0,adj); printf("WITNESS degrees:"); for(auto&a:adj) printf(" %zu",a.size()); printf("\n"); } }
    fflush(stdout);
    if(n<=BR){ // brute force every tree of this order (single thread, re-enumerate)
      struct L{ static void go(int n,int rem,int maxId,int cap,std::vector<int>&cur){ if(rem==0){ std::vector<std::vector<int>> adj; adj.push_back({}); Poly P1=ONE,P2=ONE,P3=ONE; int in=1,out=0; for(int id:cur){ build(id,0,adj); mul(P1,nodes[id].S,P1); mul(P2,nodes[id].AB,P2); mul(P3,nodes[id].Bv,P3); in+=nodes[id].out; out+=std::max(nodes[id].in,nodes[id].out);} u64 d[30]; int g=-1; for(int i=0;i<=n;i++){ d[i]=(i>=1?P1.c[i-1]:0)+P2.c[i]-P3.c[i]; if(g<0&&d[i])g=i;} brute(adj,d,g,std::max(in,out)); return;} int c=std::min(rem,cap); int hi=std::min(maxId,lastId[c]); for(int id=hi;id>=0;id--){ cur.push_back(id); go(n,rem-nodes[id].size,id,cap,cur); cur.pop_back(); } } };
      std::vector<int> cur; L::go(n,n-1,(int)nodes.size()-1,cap,cur);
      if(n%2==0){ int h=n/2; for(int i=firstId[h];i<=lastId[h];i++) for(int j=i;j<=lastId[h];j++){ std::vector<std::vector<int>> adj; build(i,-1,adj); build(j,0,adj); const Node&a=nodes[i],&b=nodes[j]; Poly p1,p2,p3; mul(a.P1,b.S,p1); mul(a.P2,b.AB,p2); mul(a.P3,b.Bv,p3); u64 d[30]; int g=-1; for(int k=0;k<=n;k++){ d[k]=(k>=1?p1.c[k-1]:0)+p2.c[k]-p3.c[k]; if(g<0&&d[k])g=k;} brute(adj,d,g,std::max(a.in+b.out,a.out+std::max(b.in,b.out))); } }
    }
  }
  printf("TOTAL trees with K1 up to %d: %llu ; brute-force checked: %llu\n",NMAX,total,bruteChecked);
  return 0; }

