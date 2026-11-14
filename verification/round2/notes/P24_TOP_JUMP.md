# Section 7의 식 (top): c_(n−1) − c_(n−2) ≤ 1 − 2/n, 등호는 별에서만

대상: manuscript/submitted/main.tex 894–914행. 나무 T의 정점 수는 n≥5, 잎의 수는 L이다.

## 논문이 말하는 것

1. γ(T) ≤ n/2 < n−2.
2. c_n − c_(n−1) = −c_(n−1) ≤ 0.
3. c_(n−1) − c_(n−2) ≤ 1 − 2/n.
4. 3의 등호는 T가 별 K_(1,n−1)일 때, 그리고 그때만 성립한다.

## Lean으로 확인한 것

명제는 verification/round2/lean_targets/FinalVerificationP24FinalTarget.lean, 증명은 lean/domination_gap3/FinalVerificationP24FinalCandidate.lean에 있다. 명제는 나무보다 넓은 **연결 단순그래프**에 대해 쓰여 있고, 나무는 연결 그래프이므로 논문의 문장을 함의한다.

| Lean 정리 | 내용 | 가정 |
|---|---|---|
| top_minus_one_count | d_(n−1) = n | 연결, n≥2 |
| last_step | c_n = 0 이고 c_(n−1) ≥ 0 (주장 2) | 연결, n≥2 |
| top_jump_le | c_(n−1) − c_(n−2) ≤ 1 − 2/n (주장 3) | 연결, n≥5 |
| top_jump_eq_iff_star | 위 등호 ⇔ 별 (주장 4, 양방향) | 연결, n≥5 |

증명의 뼈대는 논문과 같다. 지배집합이 아닌 집합은 여집합이 어떤 닫힌 이웃을 포함하는 집합이다. 크기 2인 닫힌 이웃은 잎의 것뿐이고 서로 다르므로 b = d_(n−2) = C(n,2) − L 이다. 3원소 집합에 대한 포함배제로 d_(n−3) ≤ C(n,3) − L(n−2) + C(L,2) 를 얻는다. 논문의 식 (5)로 c_(n−1) = n−1 − 2b/n, c_(n−2) = n−2 − 3d_(n−3)/b 이므로 식 (top)은 3n·d_(n−3) ≤ 2b(b−1) 과 동치이고, 이는 인수분해

    2b(b−1) − 3nu = (1/2)(n−1−L)(L(3n−4) + n(n−2)) ≥ 0

에서 나온다. 등호이면 L = n−1 이고, 이는 별과 동치다. 역으로 별에서는 중심을 포함하는 크기 n−3 집합이 모두 지배집합이므로 d_(n−3) ≥ C(n−1,3) 이고 등호가 성립한다.

중간 단계는 각각 별도 파일로 확인했다: P24TopAlgebra(인수분해), P24Overlap(포함배제), P24GraphBridge·P24TreeLeaves(잎의 닫힌 이웃), P24TopTwo(d_(n−2)), P24IntegerBound(계수 부등식).

## 주장 1의 수기 증명

나무 T (n≥5)에는 고립점이 없다. Lemma 2.2(Ore; Lean 정리 FinalVerificationOreAlpha.ore_gamma_plus_upperdom_le_card)에 의해 γ + Γ ≤ n 이고 γ ≤ Γ 이므로 2γ ≤ n, 즉 γ ≤ n/2 이다. n/2 < n−2 는 n > 4 와 동치다. n=4 에서는 등호가 되어 엄격 부등식이 성립하지 않으므로 논문의 n≥5 제한이 필요하다. 이 주장은 Lean 명제로 따로 만들지 않았다.

## 정의로 직접 센 검산

checks/p24_prufer_definition.cpp 와 checks/check_p24_final.py 는 3–9정점의 모든 표지 나무 5,063,360개를 Prüfer 수열로 만들고, 모든 부분집합에 대해 지배 여부와 임계정점 수를 정의대로 세어 주장 2–4를 정수 교차곱으로 비교한다. 위반 0건, 등호는 별에서만 발생했다(n=3,4 결과도 checks/P24_PRUFER_AUDIT.json 에 있다). checks/audit_p24_top_coefficients.cpp 는 5–8정점 표지 나무 280,372개에서 계수 부등식을 따로 확인한다.

## 증명 문단의 재유도

원고에 적힌 증명 문단(894–915행)을 문장 단위로 다시 유도한 기록은
[PROOF_REVIEW_SEC6_7_APPENDIX_A.md](PROOF_REVIEW_SEC6_7_APPENDIX_A.md)의 10절에 있다.
