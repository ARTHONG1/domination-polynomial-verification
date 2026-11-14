# Theorem 5.1, Theorem 1.2, Corollary 5.2 — 일반 upper domination gap 논증의 전개 (수기)

기준: 제출 main.tex의 lem:jump(4절), thm:main(Theorem 5.1), thm:criterion-intro(Theorem 1.2), cor:gapthree(Corollary 5.2). 이 문서는 수기 유도다.

작업용 번호: P2 = Lemma 2.2(Ore), P4 = Lemma 3.1, P5 = Lemma 3.2, P6 = 식 (4) Γ=α, P7 = Corollary 3.3·3.4, P8 = Lemma 4.1–4.3.

## 입력 명제와 기호

그래프 \(G\)에서 \(n=|V(G)|\), 최소 지배수 \(\gamma\), \(d_j\)는 크기 \(j\)의 지배집합 수, \(c_j\)는 해당 지배집합의 평균 임계정점 수. 모든 지배집합 \(S\)가 \(2\gamma-|S|\le a(S)\le2\gamma+2h-|S|\)를 만족하는 성질을 \(H_h\)라 한다. \(K_h=\lceil(h+1)^2/4\rceil\). 숲은 P4/P5/P6에 의해 \(h=\Gamma-\gamma\)로 이 성질을 만족한다.

### A. Lemma 4.3의 실제 산술 단계

\(j>\gamma\)이고 \(j-\gamma\ge K_h\)로 둔다. 고정된 \(j\)에서 \(L=2\gamma-j\), \(x=c_j-L\)이면 \(0\le x\le2h\). 지배집합별 \((a(S)-L)(L+2h-a(S))\ge0\)를 평균하면 \(v_j\le x(2h-x)\). 또한

\[
2(j-c_j)-x(2h-x)=[x-(h+1)]^2+4(j-\gamma)-(h+1)^2\ge0.
\]

여기서 마지막 부등식은 \(j-\gamma\ge K_h\ge(h+1)^2/4\) 때문이고 자연수 절단을 쓰지 않는다. P8(Lemma 4.2)의 공분산 부등식을 결합해 \((j-c_j)(c_j-c_{j-1})\le v_j\le2(j-c_j)\)를 얻는다. \(j>\gamma\)이면 최소 지배집합의 진상위집합 중 크기 \(j\)인 지배집합이 존재하여 하나 이상의 비임계정점을 가지므로 평균 \(j-c_j>0\). 나눗셈이 허용돼 \(c_j-c_{j-1}\le2\)가 성립한다.

### B. Theorem 5.1

\(A=\lfloor(n+2\gamma+1)/3\rfloor=\gamma+\lfloor(n-\gamma+1)/3\rfloor\)로 둔다. \(H_h\)의 하계와 incidence 항등식은 \(j\le A\)에서 \(d_{j-1}\le d_j\)를 준다(P7과 대응). \(N=n-\gamma\ge0\)라 하자. \(N\ge3K_h-7\)에서

\[
\left\lfloor\frac{N+1}{3}\right\rfloor\ge K_h-2,
\quad A+2\ge\gamma+K_h.
\]

이것은 \(K_h\ge2\)일 때 \(\lfloor(N+1)/3\rfloor\ge K_h-2\iff N+1\ge3(K_h-2)\)의 정수 항등식이다. \(K_h=1\)일 때 두 부등식 모두 \(N\ge0\)에서 자동으로 참이다. \(K_h=2\)에서도 자동으로 참이다. 따라서 작은 h에서 \(3K_h-7\)을 자연수에서 무작정 잘라 쓰는 오류가 없다.

비단봉이라면 가장 이른 엄격 하강 위치 \(k\)와 그 뒤 가장 이른 엄격 상승 위치 \(i\)가 존재하며, 그 사이에 \(d_{i-1}\ge d_i<d_{i+1}\). 상승 위치는 \(i<n\)이다. \(k+1>A\)이므로 \(i+1\ge A+2\ge\gamma+K_h\). P8(Lemma 4.1)은 \(c_{i+1}-c_i>2\), Lemma 4.3은 같은 지수에서 \(c_{i+1}-c_i\le2\)를 준다. 모순. 따라서 \(D(G,x)\)는 단봉이다.

### C. Theorem 1.2(i)–(iii)

(i) 숲에서 P4/P5/P6을 합쳐 얻는 \(H_h\)에 B를 적용한다.

(ii) 숲에 고립점이 없고 단봉이 아니라고 가정한다. (i)의 대우로 \(n-\gamma<3K_h-7\), 정수에서 \(n-\gamma\le3K_h-8\). P2(Ore)로 \(n\ge\gamma+\Gamma=2\gamma+h\)이므로 \(\gamma\le(n-\gamma)-h\)이고

\[
n=(n-\gamma)+\gamma\le 2(n-\gamma)-h\le6K_h-h-16.
\]

\(h=0,1,2\)일 때 각각 \(K_h=1,1,3\)이므로 우변은 \(-10,-11,0\)이다. 고립점 없는 비공집합 숲은 \(n>0\)이므로 불가능하다. 따라서 \(h\ge3\). 원고의 두 결론을 모두 얻었다.

(iii) \(K_h=\lceil(h+1)^2/4\rceil\le((h+1)^2+3)/4\)이므로

\[
6K_h-h-16\le(3h^2+4h-20)/2.
\]

\(3h^2+4h-19\le2n\)이면 \(n\ge(3h^2+4h-19)/2>(3h^2+4h-20)/2\). 따라서 (ii)의 비단봉 상한 \(n\le6K_h-h-16\)과 양립하지 않아 단봉이다.

### D. Corollary 5.2

P3로 모든 고립점을 제거해도 gap, \(n-\gamma\), 단봉성이 유지된다. 고립점 없는 숲이 gap≤3에서 비단봉이라고 가정하면 (ii)에 의해 gap은 정확히 3이다. \(K_3=4\)로 \(n\le6\cdot4-3-16=5\)이고 Ore로 \(n\ge2\gamma+3\). 고립점 없는 비공집합 숲에서는 \(\gamma\ge1\)이므로 \(n=5\), \(\gamma=1\). 한 정점이 나머지 네 정점을 모두 지배하고 숲에 사이클이 없으므로 그래프는 별 \(K_{1,4}\)이다. 그런데

\[
D(K_{1,4},x)=x(1+x)^4+x^4=x+4x^2+6x^3+5x^4+x^5
\]

는 단봉이어서 모순이다. 이는 고립점 포함한 모든 gap≤3 숲을 포괄한다. 공집합 그래프는 지배다항식 1로 단봉이며 원고의 비공집합 정리 적용 경계와 구분한다.

## 형식 검증과의 관계

이 문서는 수기 전개다. 같은 세 결과의 명제는 이후 Lean으로도 확인했다: Theorem 5.1은 FinalVerificationGeneralHGraph.graph_unimodal_of_Hh_large, Theorem 1.2는 FinalVerificationGeneralGap의 세 정리, Corollary 5.2는 FinalVerificationGapThreeFull.forest_gap_le_three_unimodal (명제는 verification/round2/lean_targets/, 증명은 lean/domination_gap3/). Theorem 1.2의 Lean 명제는 정점 집합이 비어 있지 않다고 가정한다(빈 숲은 D=1로 자명).
