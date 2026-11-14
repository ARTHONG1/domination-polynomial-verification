#!/usr/bin/env python3
"""Literal submitted-LaTeX vs independent integer calculation and archived results.

Reads only original manuscript and prior evidence; writes summary to research.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
import importlib.util
import json
import re

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[2] / 'manuscript/submitted/main.tex'
SUBMITTED_PDF = HERE.parents[2] / 'manuscript/manuscript_en.pdf'
EXPECTED_SHA = '4df950b679a7c906e53721b9fc551e482042dfa824a30aa5d6014f68dfa99c63'


def main() -> None:
    if sha256(SUBMITTED_PDF.read_bytes()).hexdigest() != EXPECTED_SHA:
        raise RuntimeError('Original PDF changed')
    src = SOURCE.read_text()
    saved = json.loads((HERE / 'audit_numeric.json').read_text())
    prior_trees = [json.loads(line) for line in (HERE / 'third_27.jsonl').read_text().splitlines()
                   if line.startswith('{')]

    def macro(name: str) -> int:
        r = re.search(r'\\newcommand\{\\' + re.escape(name) + r'\}\{([^}]+)\}', src)
        if not r: raise RuntimeError('Missing numeric macro '+name)
        return int(re.sub(r'[^0-9]', '', r.group(1)))

    # Source's exact U polynomial (NOT a Python hard-coded coefficient list).
    U_source = src[src.index(r'\begin{proposition}\label{prop:U}'):
                   src.index(r'\end{proposition}', src.index(r'\begin{proposition}\label{prop:U}'))]
    expr = U_source[U_source.index('D(U,x)='):U_source.index(r'\end{align*}')]
    matches = re.findall(r'(\d*)x\^\{(\d+)\}', expr)
    parsed = {int(j):int(c) if c else 1 for c,j in matches}
    if len(parsed)!=19: raise RuntimeError(f'Unexpected U monomials: {len(parsed)}')
    spec = importlib.util.spec_from_file_location('audit_numeric', HERE/'audit_numeric.py')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    _,_,_,independent_poly = mod.poly_tree((2,2,3),2)
    mismatches_U={j:(c,independent_poly[j]) for j,c in parsed.items() if independent_poly[j]!=c}
    if any(v and j not in parsed for j,v in enumerate(independent_poly)):
        raise RuntimeError('Nonzero U coefficient absent from submitted LaTeX')

    # Exact 26 rows of r_n,t_n are compared with independently derived
    # rooted-tree multiset and unrooted-tree dissymmetry recurrences.
    R={1:1}; T={1:1}
    for n in range(2,28):
        R[n]=sum(R[n-j]*sum(d*R[d] for d in range(1,j+1) if j%d==0)
                   for j in range(1,n))//(n-1)
        C=sum(R[i]*R[n-i] for i in range(1,n))
        T[n]=R[n]-(C-(R[n//2] if n%2==0 else 0))//2
    tab = src[src.index(r'\begin{tabular}{rrr@{\qquad\qquad}rrr}'):
              src.index(r'\end{tabular}', src.index(r'\begin{tabular}{rrr@{\qquad\qquad}rrr}'))]
    observed={}
    for line in tab.splitlines():
        if '&' not in line or not re.match(r'^\s*\d+\s*&',line): continue
        fields=[int(re.sub('[^0-9]','', part)) for part in line.split(r'\\')[0].split('&')]
        if len(fields)!=6: raise RuntimeError('Bad tabular row '+line)
        observed[fields[0]]=fields[1:3]
        observed[fields[3]]=fields[4:6]
    if len(observed)!=26: raise RuntimeError(f'Expected 26 table rows, got {len(observed)}')
    table_errors={n:{'printed':observed[n], 'calculated':[R[n],T[n]]}
                  for n in range(2,28) if observed[n]!=[R[n],T[n]]}
    generator_errors={v['n']:{'archived':v['trees'],'computed':T[v['n']]}
                      for v in prior_trees if v['trees']!=T[v['n']]}

    total26=1+sum(T[n] for n in range(2,27))
    total27=total26+T[27]
    macro_checks={
        'MaxLC':(macro('MaxLC'),26),
        'MinNonLC':(macro('MinNonLC'),27),
        'MaxOrder':(macro('MaxOrder'),27),
        'TotalTreesLC':(macro('TotalTreesLC'),total26),
        'TotalTreesAll':(macro('TotalTreesAll'),total27),
    }
    macro_errors={k:v for k,v in macro_checks.items() if v[0]!=v[1]}
    if r'$751\,065\,460$ trees' not in src:
        raise RuntimeError('Submitted unique exception count not found verbatim')
    if T[27]!=751065460: raise RuntimeError('n27 free tree count mismatch')
    if r'$1\,290\,927$' not in src:raise RuntimeError('Submitted gap4 forest count not found')
    if r'$9\,114\,285$' not in src:raise RuntimeError('Submitted <=22 count not found')
    if r'$32\,507$ such trees' not in src:raise RuntimeError('Submitted <=16 brute count not found')
    # The submitted Program I counts n=2..16; K1 is explicitly added
    # separately later in Appendix A. Distinguish these two conventions.
    if sum(T[n] for n in range(2,17)) != 32507:
        raise RuntimeError('n=2..16 program brute-count disagrees')

    # Original inequalities are checked with exact Fraction computed before;
    # the JSON stores those fractions as large numerator/denominator strings.
    j6501=Fraction(saved['P22_P23']['6501']['jump_at_gamma_plus_1'])
    j15485=Fraction(saved['P22_P23']['15485']['jump_at_gamma_plus_1'])
    numeric_ok=(j6501>2 and j15485>Fraction(43,20) and
                saved['P22_P23']['6501']['formula_DP_match'] and
                saved['P22_P23']['15485']['formula_DP_match'] and
                saved['P19']['match'] and saved['P16_P18']['U']['match'] and
                saved['P16_P18']['T(2,2,3)']['match'])
    status='pass' if not (mismatches_U or table_errors or generator_errors or macro_errors) and numeric_ok else 'fail'
    out={
        'status':status, 'submission_pdf_sha256':EXPECTED_SHA,
        'source_sha256':sha256(SOURCE.read_bytes()).hexdigest(),
        'exact_U_source_monomials':len(parsed),'exact_U_coefficient_mismatches':mismatches_U,
        'rooted_unrooted_table_rows_checked':len(observed),'table_discrepancies':table_errors,
        'archived_third_generator_count_discrepancies':generator_errors,
        'printed_macros_vs_independent_counts':macro_checks,'macro_discrepancies':macro_errors,
        'program_n2_to16':sum(T[n] for n in range(2,17)),
        'including_K1_n1_to16':1+sum(T[n] for n in range(2,17)),
        'n22_cumulative':1+sum(T[n] for n in range(2,23)),
        'n26_cumulative':total26,'n27_cumulative':total27,
        'n27_free_trees':T[27],'W_6501_jump_gt_2':j6501>2,
        'W_15485_jump_gt_2p15':j15485>Fraction(43,20),
        'existing_independent_numeric_checks_passed':numeric_ok,
        'limitation':'This parses fixed submitted TeX numbers and reuses archived numeric computation; not all prose/theorem arguments are certified by this check.',
    }
    (HERE/'SOURCE_NUMERIC_PARITY.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
    print(f'SUBMISSION_SOURCE_NUMERIC_{status.upper()} rows={len(observed)} U_monomials={len(parsed)} root/free table_discrepancies={len(table_errors)} macro_discrepancies={len(macro_errors)}')
    if status!='pass': raise SystemExit(1)


if __name__=='__main__':
    main()
