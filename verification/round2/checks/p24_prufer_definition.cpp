// Input: n=3..9 and all Prufer words over {0,...,n-1}.
// Run: build via check_p24_final.py, invoke binary with optional max_n (default 9).
// Output: JSON lines by n, each giving exact-rational c_(n-1)-c_(n-2) checks.
// Deliberately uses the definition of domination and critical vertices, not
// the manuscript's leaf formulas, inclusion-exclusion, or incidence identity.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;

int main(int argc, char** argv) {
  int max_n = argc > 1 ? atoi(argv[1]) : 9;
  if (max_n < 3 || max_n > 9) return 2;
  for (int n=3; n<=max_n; ++n) {
    int full=(1<<n)-1;
    uint64_t words=1;
    for(int k=0;k<n-2;k++) words*=n;
    uint64_t failures=0, eq_false=0, eq_missing=0, eq_count=0, stars=0;
    uint64_t last_failure=0, top_count_failure=0, gamma_failure=0;
    int first_failure=-1;
    array<int,9> seq{},degree{},N{};
    array<int,512> D{}; // one entry for every subset mask, up to 2^9
    for(uint64_t number=0;number<words;number++) {
      uint64_t q=number;
      degree.fill(1); N.fill(0);
      for (int k=0;k<n-2;k++) {seq[k]=q%n; q/=n; ++degree[seq[k]];}
      auto addedge=[&](int a, int b) {
        N[a]|=1<<b; N[b]|=1<<a;
      };
      for(int k=0;k<n-2;k++) {
        int leaf=-1;
        for(int v=0;v<n;v++) if(degree[v]==1){leaf=v;break;}
        if(leaf<0) return 3;
        addedge(leaf,seq[k]);
        --degree[leaf];--degree[seq[k]];
      }
      int u=-1,v=-1;
      for(int x=0;x<n;x++) if(degree[x]==1) { if(u<0) u=x; else v=x; }
      if(u<0 || v<0) return 4;
      addedge(u,v);
      degree.fill(0);
      for(int x=0;x<n;x++) {degree[x]=__builtin_popcount((unsigned)N[x]); N[x]|=1<<x;}
      bool star=false;
      for(int x=0;x<n;x++) if(degree[x]==n-1) star=true;
      if(star) ++stars;
      for(int S=1;S<=full;S++) {
        int coverage=0;
        for(int x=0;x<n;x++) if((S>>x)&1) coverage|=N[x];
        D[S]=coverage;
      }
      array<int64_t,10> counts{},critical{};
      for(int S=1;S<=full;S++) {
        if(D[S]!=full) continue;
        int k=__builtin_popcount((unsigned)S);
        counts[k]++;
        int a=0;
        for(int x=0;x<n;x++) if((S>>x)&1) {
          if(D[S^(1<<x)]!=full) ++a;
        }
        critical[k]+=a;
      }
      if(counts[n]!=1 || counts[n-1]!=n) ++top_count_failure;
      if(critical[n]!=0 || critical[n-1]<0) ++last_failure;
      if(counts[n-2]==0) {++failures; continue;}
      // c_(n-1)-c_(n-2) <= 1-2/n, exact cross-multiplication.
      int64_t b=counts[n-2], left=critical[n-1]*b-critical[n-2]*n;
      int64_t right=(n-2)*b;
      bool eq=left==right;
      if(left>right) {++failures;if(first_failure<0)first_failure=(int)number;}
      if(eq && !star) ++eq_false;
      if(!eq && star) ++eq_missing;
      if(eq) ++eq_count;
      if(n>=5) {
        // Gamma bound via every tree having a dominating set of size <= n/2.
        int gamma=n+1;
        for(int k=1;k<=n;k++) if(counts[k]>0){gamma=k;break;}
        if(2*gamma>n || !(n<2*(n-2))) ++gamma_failure;
      }
    }
    cout << "{\"n\":"<<n<<",\"trees\":"<<words
      <<",\"stars\":"<<stars<<",\"equalities\":"<<eq_count
      <<",\"inequality_violations\":"<<failures
      <<",\"star_false_positives\":"<<eq_false
      <<",\"star_false_negatives\":"<<eq_missing
      <<",\"top_count_violations\":"<<top_count_failure
      <<",\"last_step_violations\":"<<last_failure
      <<",\"gamma_bound_violations\":"<<gamma_failure
      <<",\"first_bad_word\":"<<first_failure<<"}"<<endl;
  }
}
