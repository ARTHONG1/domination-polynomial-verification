#!/usr/bin/env python3
"""Build a non-mutating extension of the existing third free-tree generator.

Adds a collision-free AHU bit-code uniqueness check at each order n<=22.
The original third_check.cpp remains untouched and the extended checker
must be compared to the original per-order output before making claims.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
ORIGINAL = HERE / 'audit_third/third_check.cpp'
DEST = HERE / 'audit_canonical_22.cpp'
src = ORIGINAL.read_text()


def replace_once(old: str, new: str):
    global src
    if src.count(old) != 1:
        raise RuntimeError(f'Expected one insertion anchor, got {src.count(old)}: {old[:80]}')
    src = src.replace(old, new)


replace_once('#include <algorithm>', '#include <algorithm>\n#include <string>\n#include <cstdint>')

new_functions = r'''
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
'''
replace_once('struct Jump {', new_functions+'\nstruct Jump {')
replace_once('std::vector<Poly> witPoly; Jump maxJump', 'std::vector<Poly> witPoly; std::vector<uint64_t> codes; Jump maxJump')
replace_once('  acc.count++; int g=0;', '  acc.count++; acc.codes.push_back(tree_code(n,desc)); int g=0;')
replace_once('  u64 total=1; // K_1',
             '  ahu.assign(nodes.size(),std::string());\n  for(size_t id=0;id<nodes.size();id++) rooted_code((int)id);\n  u64 total=1; // K_1')
replace_once('tot.count+=a.count; tot.lcFail+=a.lcFail;',
             'tot.count+=a.count; tot.codes.insert(tot.codes.end(),a.codes.begin(),a.codes.end()); tot.lcFail+=a.lcFail;')
replace_once('    total+=tot.count;\n',
             '    if(tot.codes.size()!=tot.count){fprintf(stderr,"AHU code-count mismatch n=%d\\n",n);return 9;}\n'
             '    std::sort(tot.codes.begin(),tot.codes.end());\n'
             '    if(std::adjacent_find(tot.codes.begin(),tot.codes.end())!=tot.codes.end()){fprintf(stderr,"DUPLICATE AHU free tree n=%d\\n",n);return 10;}\n'
             '    fprintf(stderr,"CANONICAL_PASS n=%d code_distinct=%zu otter=%llu\\n",n,tot.codes.size(),(u64)T[n]);\n'
             '    total+=tot.count;\n')

DEST.write_text(src)
print(f'Generated {DEST} from original {ORIGINAL}; original unchanged')
