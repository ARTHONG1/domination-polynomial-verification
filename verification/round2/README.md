# 2차 검증 (2026-11-13~14)

투고 원고의 주장을 하나씩 다시 확인한 기록이다. 근거는 네 종류로 나눈다.

- **Lean**: 명제를 증명과 따로 적어 두고(lean_targets/), 그 증명을 Lean 4.27.0 커널과 SafeVerify로 확인했다. 표준 공리 propext, Classical.choice, Quot.sound만 쓴다.
- **계산 3종**: 투고 프로그램 2개와 새로 쓴 제3 프로그램의 전수 계산이 일치한다.
- **직접 계산**: 투고 코드를 쓰지 않고 정의대로 다시 센 정확 정수·유리수 계산.
- **재유도**: 원고의 증명을 문장 단위로 다시 유도했다(notes/).

## 주장별 근거

"Lean: 이름"은 lean_targets/의 FinalVerification이름Target.lean(또는 이름Target.lean)에 적힌 명제를 뜻한다. 파일 이름은 checks/와 notes/ 안의 것이다.

| 논문 위치 | Lean | 계산 | 재유도 |
|---|---|---|---|
| Lemma 2.1 (기초 성질, 식 (5)) | 투고 보충자료의 graph_domination_lemma3_identity | 직접 계산: 6정점 이하 표지 그래프 33,868개(audit_small_graphs.json), 7정점 이하 표지 숲 40,233개와 표지 이분그래프 108,842개(SEC2_4_LABELLED_CENSUS.json), DEFINITION_CHECKS.json | PROOF_REVIEW_SEC2_5.md 1절, SEC2_4_HAND_PROOFS.md |
| Lemma 2.2 (Ore, n ≥ γ+Γ) | OreAlpha | 위와 같음 | 같은 문서 2절 |
| Lemma 2.3 (고립점 제거) | Isolates (명제 5개) | 위와 같음 | 3절 |
| Lemma 3.1 | 투고 보충자료의 forest_critical_inequality | 16정점 이하 나무 32,507개의 모든 지배집합(BF16_REPLAY_AUDIT.json), 표지 숲 | 4절 |
| Lemma 3.2, 식 (4) Γ = α | 투고 보충자료의 bipartite_critical_le_two_independence, OreAlpha | 표지 이분그래프 | 5절 |
| Corollary 3.3, 3.4 (단조 구간, avd) | 증가 구간: left_wing_from_critical_lower | 표지 숲과 이분그래프에서 두 단조 구간과 avd의 상·하계 | 6절, SEC2_4_HAND_PROOFS.md |
| Lemma 4.1–4.3 | MeanJumpNoStrict, 투고 보충자료 | 표지 숲과 이분그래프, IDENTITY_CHECKS.json(분산 항등식 828건) | 7–9절 |
| Theorem 5.1 | GeneralHGraph (h<K, A+2≤n 같은 추가 가정 없이) | DEFINITION_CHECKS.json | 10절 |
| Theorem 1.2 (i)–(iii) | GeneralGap, GapArithmetic | DEFINITION_CHECKS.json, NARRATIVE_ARITHMETIC.json | 11절 |
| Corollary 5.2 (gap ≤ 3) | GapThreeFull (고립점 포함 모든 숲) | DEFINITION_CHECKS.json | 12절 |
| Lemma 6.2 (로그오목 곱) | LogConcaveProduct | IDENTITY_CHECKS.json(Cauchy–Binet 항등식 31,248건) | PROOF_REVIEW_SEC6_7_APPENDIX_A.md 2절, P12_CONVOLUTION_PROOF.md |
| Theorem 6.1 (26정점 이하 로그오목) | 컴퓨터 보조 | 계산 3종(위수 2..27, third_crosscheck.json), 표준형 중복 검사(위수 2..27, canonical_27.log), 전체 재실행 2회 | COMPLETENESS_PROOF.md, APPENDIX_A_CODE_AUDIT.md |
| Corollary 6.3 | LogConcaveProduct (단봉) | COMPONENT_PRODUCT.json(숲 750개) | 3절, THEOREM_1_1_CHAIN.md |
| Theorem 1.1 (gap ≤ 4) | gap ≤ 3: GapThreeFull. gap = 4: GapFourBridge가 "22정점 이하 숲은 단봉"을 전제로 받아 결론을 낸다 | 그 전제는 Theorem 6.1의 계산과 Lemma 6.2 | 4절, THEOREM_1_1_CHAIN.md |
| Remark 6.4 (1,290,927개) | | 직접 계산: 제3 프로그램의 분포에서 Euler 곱으로 재집계, 10정점 이하는 숲을 직접 열거해 대조(REMARK_6_4.json) | |
| Proposition 6.5 (27정점 U) | | 직접 계산: 부분집합 2^27개 전부(U_BRUTEFORCE.json). 본문 정의·그림 1·두 프로그램 출력의 동형(U_FIGURE_ISOMORPHISM.json) | 5절 |
| Theorem 6.6 (27정점 유일 예외) | 컴퓨터 보조 | 계산 3종, 위수 27의 표준형 코드 751,065,460개가 모두 다름 | 6절 |
| Remark 6.7 (중심 포함·제외 분해) | | U_BRUTEFORCE.json의 with_centre, without_centre | |
| Remark 6.8 (가족의 예외 6개) | | 직접 계산: r ≤ 5, 34정점 이하 매개변수 268가지 전부(FAMILY_REMARK_6_8.json) | |
| Section 7의 수치 | | 정확 유리수: 전체 최대 점프 73094/70925, 제한 범위 최대 12/13(SEC7_JUMP_CENSUS.json) | |
| Proposition 7.2 (i) | JumpBound | | 8절 |
| Proposition 7.2 (ii) | | 계수 상계 288건, θ 상계 648건(PROP_7_2_EXACT.json), 식 (W)와 점화식의 전체 계수 대조(IDENTITY_CHECKS.json, audit_numeric.json) | 9절, P22_SECOND_PASS.md |
| 6501·15485정점 예 | | 서로 다른 두 계산 경로로 전체 계수와 점프 대조(audit_numeric.json) | |
| 식 (top), 별에서만 등호 | P24Final 외 6개 | 표지 나무 5,063,360개(P24_PRUFER_AUDIT.json) | 10절, P24_TOP_JUMP.md |
| Appendix A 점화식 | | 12정점 이하 모든 나무·모든 뿌리의 부분나무 124,534개에서 정의와 대조(DP_SEMANTICS.json), 16정점 이하 32,507개 부분집합 전수 대조 | APPENDIX_A_DP_PROOF.md |
| Appendix A 프로그램 서술, 자료형 | | TABLE_COUNTS.json | APPENDIX_A_CODE_AUDIT.md |
| 표 1, 본문 숫자 | | 표 1의 숫자 52개(TABLE_COUNTS.json), 원고 소스의 숫자 대조(SOURCE_NUMERIC_PARITY.json), 상수와 작은 예(NARRATIVE_ARITHMETIC.json) | |

Theorem 1.1의 gap = 4 부분과 Theorem 6.1, 6.6은 원고에 적힌 대로 컴퓨터 보조 결과다.

## 결과

수학적 오류나 반례는 없었다. 서술에 관해 확인한 것은 다음과 같다.

1. Appendix A의 "every tree of order at most 16 … 32,507 such trees": 32,507은 프로그램이 처리한 위수 2..16의 개수다. K₁을 포함하면 32,508개다.
2. Lemma 2.3과 Theorem 1.2는 위수 0인 그래프의 규약을 적지 않는다. 빈 그래프에서는 D = 1이어서 결론이 자명하게 성립한다. Lean 명제 GeneralGap은 정점 집합이 비어 있지 않은 경우를 다룬다.
3. Appendix A의 "All arithmetic is exact integer arithmetic": 명제의 성립 여부를 가르는 검사는 모두 정수 산술이다. Program I이 출력하는 통계값 max_mean_jump만 부동소수점으로 계산하며, 정확한 값은 따로 유리수로 확인했다(notes/APPENDIX_A_CODE_AUDIT.md).
4. 보충자료 설명에는 jumps/check_boundary.py가 Python 3.10 이상을 요구한다는 것과, Program I의 수록 출력이 위수 23..26은 6개, 위수 27은 12개 프로세스로 만든 것이라는 설명이 없다.
5. 투고 보충자료의 Lean 정리 graph_uniform_gap_unimodal은 h<K, A+2≤n을 추가로 가정한다(Appendix B의 설명과 일치). 이 가정이 없는 명제는 GeneralHGraph로 따로 확인했다.
6. Lean의 평균 critMean은 d_j = 0일 때 0으로 정의된다(Lean의 x/0 = 0). 논문은 γ ≤ j ≤ n에서만 c_j를 쓰며, 각 명제가 분모가 양수인 범위만 쓰는지 확인했다.

## 폴더

| 폴더 | 내용 |
|---|---|
| [lean_targets/](lean_targets/) | 고정한 명제 17개 파일(증명 자리는 sorry). 증명은 저장소의 lean/domination_gap3/ |
| [safeverify/](safeverify/) | 명제별 SafeVerify 결과(정리 이름, 사용 공리) |
| [checks/](checks/) | 계산 프로그램과 출력 |
| [notes/](notes/) | 문장 단위 재유도와 손 증명 |

## 다시 실행하기

    checks/run_quick_checks.sh

위 스크립트는 빠른 검사를 모두 다시 실행하고 저장소의 출력과 비교한다(약 2분, C++17 컴파일러와 Python 3.10 이상). 위수 27까지의 표준형 검사는 메모리와 시간이 많이 들어 따로 실행한다(인자는 최대 위수, 부분집합 직접 대조의 최대 위수, 스레드 수).

    c++ -O3 -std=c++17 -pthread checks/audit_canonical_27.cpp -o /tmp/canon27
    /tmp/canon27 27 12 10 > canonical_27.jsonl 2> canonical_27.log

Lean 명제의 공리 점검은 lean/에서 lake build 뒤에 lake env lean Round2CheckAxioms.lean으로 한다.
