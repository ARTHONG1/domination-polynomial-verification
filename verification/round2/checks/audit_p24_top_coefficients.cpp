// Completely independent labelled-tree subset audit of submitted Section 7,
// equation (top). Trees are generated from all Prufer words (n=5..8).
// We enumerate 2- and 3-vertex complements directly; no domination DP,
// polynomial recurrence, or submitted tree enumerator is called.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

static unsigned long long power(unsigned n, unsigned e) {
  unsigned long long v=1;
  while(e--) v*=n;
  return v;
}

int main() {
  unsigned long long total=0, mismatch=0, equality_bad=0;
  for(unsigned n=5;n<=8;++n) {
    unsigned long long count=power(n,n-2), equal=0, bad=0;
    for(unsigned long long code=0;code<count;++code) {
      unsigned pr[8]={0}, deg[8]={0}, neigh[8]={0};
      for(unsigned i=0;i<n;++i) deg[i]=1;
      unsigned long long q=code;
      for(unsigned i=0;i<n-2;++i) {pr[i]=q%n;q/=n;deg[pr[i]]++;}
      auto add_edge=[&](unsigned a,unsigned b) {
        neigh[a]|=(1u<<b);neigh[b]|=(1u<<a);
      };
      for(unsigned i=0;i<n-2;++i) {
        unsigned leaf=0;
        while(deg[leaf]!=1) ++leaf;
        add_edge(leaf,pr[i]);
        --deg[leaf];--deg[pr[i]];
      }
      unsigned a=0,b=0;
      while(deg[a]!=1) ++a;
      b=a+1;
      while(deg[b]!=1) ++b;
      add_edge(a,b);
      unsigned leaves=0;
      for(unsigned i=0;i<n;++i) leaves+=(__builtin_popcount(neigh[i])==1);
      // T - S fails to dominate iff some closed N[v] is contained in S.
      auto forbidden=[&](unsigned rem) {
        for(unsigned v=0;v<n;++v) {
          unsigned closed=neigh[v]|(1u<<v);
          if((closed&rem)==closed) return true;
        }
        return false;
      };
      unsigned dn2=0,dn3=0;
      for(unsigned x=0;x<n;++x)
        for(unsigned y=x+1;y<n;++y) {
          dn2+=!forbidden((1u<<x)|(1u<<y));
          for(unsigned z=y+1;z<n;++z)
            dn3+=!forbidden((1u<<x)|(1u<<y)|(1u<<z));
        }
      unsigned expected_b=n*(n-1)/2-leaves;
      bool inequality=(3u*n*dn3<=2u*dn2*(dn2-1u));
      bool is_star=leaves==n-1;
      bool equality=(3u*n*dn3==2u*dn2*(dn2-1u));
      if(equality) ++equal;
      if(!inequality || dn2!=expected_b) ++bad;
      if(equality!=is_star) ++equality_bad;
    }
    total+=count;mismatch+=bad;
    std::printf("n=%u trees=%llu inequality_failures=%llu star_equalities=%llu\n",
      n,count,bad,equal);
  }
  std::printf("P24_ALL_LABELLED_PASS=%s trees=%llu mismatches=%llu equality_failures=%llu\n",
    mismatch==0&&equality_bad==0?"true":"false",total,mismatch,equality_bad);
  return mismatch==0&&equality_bad==0?0:1;
}
