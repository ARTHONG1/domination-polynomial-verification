# Lemma 6.2: finite nonnegative log-concave convolution (expanded hand proof)

Audit target: submitted `main.tex` Lemma 6.2 (`lem:product`, PDF p.10).
This document supplies a complete mathematical argument for the lemma, written out independently of the proof in the paper.

## Exact statement and conventions

Let \(a,b:\mathbb Z\to\mathbb R_{\ge0}\) be finitely supported. Assume each is log-concave (\(a_k^2\ge a_{k-1}a_{k+1}\), likewise for \(b\), for every \(k\in\mathbb Z\)), and has no internal zero (the set of indices with positive value is either empty or an integer interval). Define \(c_k=\sum_{h\in\mathbb Z}a_hb_{k-h}\). Then \(c\) has finite support, nonnegative entries, no internal zero, and \(c_k^2\ge c_{k-1}c_{k+1}\) for all \(k\). Extend the coefficient sequence of each polynomial by zeros to all integer indices. This is precisely Lemma 6.2 of the submitted manuscript.

## Detailed proof

1. **Adjacent balancing.** Suppose \(x_p,x_q>0\) and \(p+2\le q\), where \(x\) is one of the assumed log-concave interval-supported sequences. All entries between \(p\) and \(q\) are positive. Log-concavity implies the ratios \(x_{k+1}/x_k\) are nonincreasing for \(p\le k<q\). Hence
   \[
   x_{p+1}x_{q-1}\ge x_px_q.
   \]
   If one of \(x_p,x_q\) is zero, the same inequality follows from nonnegativity. Repeating balancing proves: whenever \(u\le v\), \(u\le p,q\le v\) and \(p+q=u+v\), then \(x_px_q\ge x_ux_v\). When \(v=u+1\) or \(p,q\) equal the endpoints, the statement is equality. The empty-support case is zero throughout.

2. **Order-two Toeplitz minors.** Put \(T_x(i,j)=x_{j-i}\) for integer row/column indices. For \(i_1<i_2\), \(j_1<j_2\), write \(u=j_1-i_2\), \(v=j_2-i_1\), \(p=j_1-i_1\), \(q=j_2-i_2\). Then \(u<p,q<v\) and \(p+q=u+v\). By step 1,
   \[
   \det\begin{pmatrix}T_x(i_1,j_1)&T_x(i_1,j_2)\\ T_x(i_2,j_1)&T_x(i_2,j_2)\end{pmatrix}
   =x_px_q-x_ux_v\ge0.
   \]
   All such minors are nonnegative, including those with zero factors.

3. **Convolution as Toeplitz product.** For fixed \(i,j\),
   \[
   (T_aT_b)(i,j)=\sum_{k\in\mathbb Z}a_{k-i}b_{j-k}=\sum_{h\in\mathbb Z}a_hb_{j-i-h}=c_{j-i}=T_c(i,j).
   \]
   The sum is finite since the supports of \(a,b\) are finite. For any chosen two rows and columns, choose one finite set \(K\subset\mathbb Z\) large enough to contain every index that contributes to any of the four entries of the product. The **finite** Cauchy–Binet identity gives
   \[
   \det (T_c)_{\{i_1,i_2\},\{j_1,j_2\}}=
   \sum_{k_1<k_2\atop k_1,k_2\in K}
   \det (T_a)_{\{i_1,i_2\},\{k_1,k_2\}}
   \det (T_b)_{\{k_1,k_2\},\{j_1,j_2\}}\ge0,
   \]
   because every summand is a product of two nonnegative minors proved in step 2. There is **no** convergence or infinite-matrix exchange issue: each identity uses a finite index set \(K\).

4. **Recover coefficient log-concavity.** Take rows \(0,1\) and columns \(k,k+1\) in step 3. Their determinant is exactly
   \[
   \begin{vmatrix}c_k&c_{k+1}\\c_{k-1}&c_k\end{vmatrix}=c_k^2-c_{k-1}c_{k+1}\ge0.
   \]
   This is true for every integer \(k\), so it also covers both endpoints of either polynomial's finite coefficient list.

5. **Support and nonnegativity.** Every \(c_k\) is a finite sum of nonnegative products, so it is nonnegative. Its support is finite and contained in the sum of the finite supports. If either factor is identically zero, so is \(c\), with no internal zeros. Otherwise, the supports are intervals \([A,B]\cap\mathbb Z\) and \([C,D]\cap\mathbb Z\), with every element strictly positive. Each \(k\in[A+C,B+D]\cap\mathbb Z\) admits some \(i\in[A,B]\), \(k-i\in[C,D]\) (take \(i=\max(A,k-D)\)); hence \(c_k\ge a_ib_{k-i}>0\). Outside that interval all summands vanish. Thus \(c\) has no internal zeros.

Together steps 3–5 establish all three properties for polynomial multiplication, with no restriction on degrees, including zero and constant polynomials.

## Source correspondence and scope

- Submitted lemma: manuscript/submitted/main.tex, label lem:product (PDF p. 10). The proof in the paper invokes the TP2 inequality and Cauchy–Binet; this note expands both and handles the support and zero boundaries explicitly.
- The proof uses ordinary real division only where both endpoints are strictly positive; no truncated natural-number subtraction occurs.
- Formal status: this lemma was also checked in Lean during round 2 (for natural and for nonnegative real coefficients), but that proof depends on a separate, larger development that is not part of this repository. It is therefore not offered here as reproducible evidence; within this repository the lemma rests on the proof in the paper and on this expanded hand proof.
