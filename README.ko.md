# 상지배 간격이 4 이하인 숲의 지배다항식의 단봉성

[![Verification](https://github.com/ARTHONG1/domination-polynomial-verification/actions/workflows/verify.yml/badge.svg)](https://github.com/ARTHONG1/domination-polynomial-verification/actions/workflows/verify.yml)

English: [README.md](README.md)

다음 논문의 원고, 프로그램, 계산 출력, Lean 4 형식화, 검증 기록을 담은 저장소다.

> 홍찬우 (Chanu Hong), *Unimodality of domination polynomials of forests with upper domination gap at most four*, 2026.

이 논문은 학술지에 투고되어 심사 중이다. 투고한 뒤 원고의 모든 정리와 증명, 계산을 다시 검증했고, 이 저장소는 그 검증의 전체 기록이다. **오류나 반례는 발견되지 않았다.** 독립적인 검토와 반례 제보를 환영한다([Issues](https://github.com/ARTHONG1/domination-polynomial-verification/issues)).

## 논문의 결과

위수가 n인 유한 단순 그래프 G에서 크기 j인 지배집합의 개수를 d_j(G), 지배다항식을 D(G, x) = Σ d_j(G) x^j라 한다. γ(G)는 지배수, Γ(G)는 상지배수(극소 지배집합의 최대 크기), h = Γ(G) − γ(G)는 상지배 간격이다. Alikhani와 Peng은 D(G, x)가 항상 단봉이라고 추측했고, 이 추측은 나무에서도 미해결이다.

1. **정리 1.1.** Γ(F) − γ(F) ≤ 4인 모든 숲 F의 지배다항식은 단봉이다.
2. **정리 1.2.** 위수 n, 간격 h인 숲 F와 K_h = ⌈(h+1)²/4⌉에 대해, n − γ(F) ≥ 3K_h − 7이면 D(F, x)는 단봉이다. 고립점이 없는 숲 F의 지배다항식이 단봉이 아니면 h ≥ 3이고 n ≤ 6K_h − h − 16이다.
3. **정리 1.3.** 꼭짓점이 26개 이하인 모든 나무의 지배다항식은 로그오목이고, 27개인 나무 751,065,460종 가운데 로그오목이 아닌 것은 정확히 하나다.
4. **명제 7.2.** 모든 숲에서 γ < j < n이면 c_{j+1} − c_j < 2(j − γ) + 1이고(c_j는 크기 j인 지배집합의 임계 꼭짓점 수의 평균), 이 상계는 나무에서도 최선이다.

## 검증 요약

| 확인한 것 | 규모 |
|---|---|
| Lean 4 커널이 확인한 정리 문장 | 59개. propext, Classical.choice, Quot.sound 세 공리만 사용 |
| 증명과 따로 적어 두고 SafeVerify로 대조한 명제 | 17개 파일의 48개 |
| 전수 열거한 나무 | 1,198,738,056종(27정점 이하 전부). 생성 방식이 다른 프로그램 3개 |
| 열거의 완전성 | 위수 2~27의 생성된 나무마다 표준형 코드를 계산(제3 프로그램). 모두 다르고 개수가 Otter 수와 같음 |
| 보충자료만으로 전체 재실행 | 위수 2~27 전체를 2회. 투고한 결과와 같음 |
| 점화식 없이 부분집합을 직접 열거 | 위수 2~16의 나무 32,507종 전부, 예외 나무 U의 부분집합 2^27개 전부 |
| 2~5절을 정의대로 검사 | 6정점 이하 표지 그래프 전부(33,868개), 7정점 이하 표지 숲과 이분그래프 전부(검사 79,594,429건) |
| 상단 계수 부등식(7절) | 3~9정점 표지 나무 5,063,360개 전부 |
| 부록 A의 점화식과 정의의 대조 | 12정점 이하 모든 나무, 모든 뿌리의 부분나무 124,534개 |
| 증명을 문장 단위로 다시 유도 | proof 환경 20개 전부와 추가 논증 3개 |
| 본문의 숫자 | 표 1(52개), U의 계수, 상수와 예시를 정확 산술로 재계산 |

Lean 빌드와 공리 점검, 위수 22까지의 전수 계산, 빠른 검사들은 커밋마다 [GitHub Actions](https://github.com/ARTHONG1/domination-polynomial-verification/actions)에서 다시 실행된다. 그보다 무거운 계산(위수 23~27, 위수 27까지의 표준형 코드)은 CPU 시간이 몇 시간 걸리므로 출력과 로그를 저장소에 두었다.

## 주장별 근거

"Lean"은 명제가 [verification/round2/lean_targets/](verification/round2/lean_targets/)(또는 투고 보충자료)에 고정되어 있고 [lean/](lean/)의 증명을 Lean 4.27.0 커널이 받아들였다는 뜻이다. "계산"은 정확한 정수·유리수 산술이다. "재유도"는 [verification/round2/notes/](verification/round2/notes/)의 문장 단위 기록이다.

| 주장 | Lean | 계산 | 재유도 |
|---|---|---|---|
| 보조정리 2.1 (기초 성질, 입사 항등식) | graph_domination_lemma3_identity | 표지 그래프: [전수 검사](verification/round2/checks/SEC2_4_LABELLED_CENSUS.json), [정의 검사](verification/round2/checks/DEFINITION_CHECKS.json) | [2–5절](verification/round2/notes/PROOF_REVIEW_SEC2_5.md) |
| 보조정리 2.2 (Ore), n ≥ γ + Γ | OreAlpha | 위와 같음 | 위와 같음 |
| 보조정리 2.3 (고립점 제거) | Isolates | 위와 같음 | 위와 같음 |
| 보조정리 3.1 (숲: \|S\| + a(S) ≥ 2γ) | forest_critical_inequality | 나무 32,507종의 모든 부분집합: [대조](verification/round2/checks/BF16_REPLAY_AUDIT.json) | 위와 같음 |
| 보조정리 3.2 (이분그래프: \|S\| + a(S) ≤ 2α), Γ = α | bipartite_critical_le_two_independence, OreAlpha | 표지 이분그래프 | 위와 같음 |
| 따름정리 3.3, 3.4 | left_wing_from_critical_lower | 표지 숲과 이분그래프 | 위와 같음, [손 증명](verification/round2/notes/SEC2_4_HAND_PROOFS.md) |
| 보조정리 4.1–4.3 | MeanJumpNoStrict | 위와 같음 | 위와 같음 |
| 정리 5.1 | GeneralHGraph | [정의 검사](verification/round2/checks/DEFINITION_CHECKS.json) | 위와 같음 |
| 정리 1.2 (i)–(iii) | GeneralGap, GapArithmetic | 위와 같음 | 위와 같음 |
| 따름정리 5.2 (간격 3 이하) | GapThreeFull | 위와 같음 | 위와 같음 |
| 보조정리 6.2 (로그오목 다항식의 곱) | LogConcaveProduct | [항등식 검사](verification/round2/checks/IDENTITY_CHECKS.json) | [6–7절](verification/round2/notes/PROOF_REVIEW_SEC6_7_APPENDIX_A.md) |
| 정리 6.1 (26정점 이하 나무) | 컴퓨터 보조 | 프로그램 3개: [비교](verification/round2/checks/third_crosscheck.json), 표준형 코드: [로그](verification/round2/checks/canonical_27.log), 재실행 | [완전성](verification/round2/notes/COMPLETENESS_PROOF.md) |
| 따름정리 6.3 | LogConcaveProduct | [성분 곱](verification/round2/checks/COMPONENT_PRODUCT.json) | 위와 같음 |
| 정리 1.1 (간격 4 이하) | GapThreeFull, GapFourBridge | 유한 부분 n ≤ 22는 정리 6.1 | [증명 사슬](verification/round2/notes/THEOREM_1_1_CHAIN.md) |
| 주의 6.4 (숲 1,290,927개) | | [재집계](verification/round2/checks/REMARK_6_4.json) | |
| 명제 6.5 (나무 U) | | [부분집합 2^27개](verification/round2/checks/U_BRUTEFORCE.json), [그림 1과의 동형](verification/round2/checks/U_FIGURE_ISOMORPHISM.json) | |
| 정리 6.6 (27정점에서의 유일성) | 컴퓨터 보조 | 프로그램 3개, 위수 27의 표준형 코드 | |
| 주의 6.7, 6.8 | | [중심 분해](verification/round2/checks/U_BRUTEFORCE.json), [매개변수 268가지](verification/round2/checks/FAMILY_REMARK_6_8.json) | |
| 7절의 수치 서술 | | [정확한 최댓값](verification/round2/checks/SEC7_JUMP_CENSUS.json) | |
| 명제 7.2 (i) | JumpBound | | [6–7절](verification/round2/notes/PROOF_REVIEW_SEC6_7_APPENDIX_A.md) |
| 명제 7.2 (ii), 6,501정점과 15,485정점 나무 | | [계수 상계](verification/round2/checks/PROP_7_2_EXACT.json), [전체 다항식](verification/round2/checks/audit_numeric.json) | 위와 같음, [두 번째 유도](verification/round2/notes/P22_SECOND_PASS.md) |
| 부등식 (top)과 별에서의 등호 | P24Final 외 6개 파일 | [표지 나무 5,063,360개](verification/round2/checks/P24_PRUFER_AUDIT.json) | [기록](verification/round2/notes/P24_TOP_JUMP.md) |
| 부록 A (점화식, 프로그램, 표 1) | | [점화식과 정의의 대조](verification/round2/checks/DP_SEMANTICS.json), [표 1](verification/round2/checks/TABLE_COUNTS.json) | [증명](verification/round2/notes/APPENDIX_A_DP_PROOF.md), [소스 대조](verification/round2/notes/APPENDIX_A_CODE_AUDIT.md) |
| 부록 B (형식화의 범위) | 커밋마다 다시 빌드 | | |

정리 1.1의 간격 4 부분과 정리 1.3은 원고에 적힌 대로 컴퓨터 보조 정리이고, 부록 A의 전수 계산에 기댄다. 사슬의 나머지는 모두 Lean 커널이 확인한 명제다. 파일 단위의 자세한 표는 [verification/round2/README.md](verification/round2/README.md)에 있다.

## 재현 방법

필요한 것: 128비트 정수를 지원하는 C++17 컴파일러(clang 또는 gcc), Python 3.10 이상, 형식 증명에는 Lean 4.27.0(elan이 lean/lean-toolchain을 읽어 설치).

정리 1.1에 필요한 범위인 위수 2~22와 예외 나무(약 1분):

    cd computation
    ./run_all.sh 22
    ./bin/bruteforce_tree 0 1 2 3 1 5 6 1 8 9 0 11 12 13 11 15 16 0 18 19 20 18 22 23 0 25

2차 검증의 빠른 검사 전부(약 2분). 저장소의 출력과 비교한다:

    verification/round2/checks/run_quick_checks.sh

정리 1.3의 전체 범위인 위수 2~27(약 3 CPU-시간):

    cd computation
    ./run_all.sh 27 12

Lean 빌드와 공리 점검:

    cd lean
    lake exe cache get
    lake build
    lake env lean CheckAxioms.lean
    lake env lean RefereeAudit.lean
    lake env lean Round2CheckAxioms.lean

## 구성

| 경로 | 내용 |
|---|---|
| [manuscript/](manuscript/) | 투고한 원고(PDF와 LaTeX 소스), 국문 번역 |
| [computation/](computation/) | 전수 계산 프로그램 2개, 부분집합 열거기, 7절의 스크립트와 출력 |
| [lean/](lean/) | Lean 4 패키지: 부록 B의 형식화와 검증 중에 추가한 증명 |
| [independent_checks/](independent_checks/) | 또 다른 나무 생성기, 비연결 숲과 순환이 있는 이분그래프의 정확 산술 검사 |
| [verification/](verification/) | 검증 기록: 투고 직전 재실행, 1차, 2차 |
| [docs/](docs/) | 보충자료 설명, 나무 U에 관한 기록 |
| [SHA256SUMS](SHA256SUMS) | 모든 파일의 SHA-256 |

투고한 원고는 [manuscript/manuscript_en.pdf](manuscript/manuscript_en.pdf)이고 SHA-256은 `4df950b679a7c906e53721b9fc551e482042dfa824a30aa5d6014f68dfa99c63`이다. 투고한 단일 LaTeX 파일은 [manuscript/submitted/main.tex](manuscript/submitted/main.tex)이며, 검증 기록의 행 번호는 이 파일의 행이다.

## 원고의 서술에 관한 참고 사항

검증에서 수학적 오류는 나오지 않았다. 서술에 관해 다음 네 가지를 확인했고, 어느 것도 정리에 영향을 주지 않는다.

1. 부록 A는 16정점 이하 나무가 32,507개라고 적는다. 이것은 프로그램이 처리한 위수 2~16의 개수이고, K₁을 넣으면 32,508개다.
2. 보조정리 2.3과 정리 1.2는 위수 0인 그래프의 규약(D = 1, γ = Γ = 0)을 적지 않는다. 모든 꼭짓점이 고립점인 숲에서는 D = x^n이어서 결론이 자명하게 성립한다.
3. 부록 A는 모든 산술이 정확한 정수 산술이라고 적는다. 명제의 성립 여부를 가르는 검사는 모두 그렇다. 첫째 프로그램이 출력하는 통계값 max_mean_jump는 부동소수점으로 계산하는데, 정확한 값 73094/70925를 유리수 산술로 다시 구해 7절의 상계 1.04를 확인했다.
4. 보충자료 설명에는 jumps/check_boundary.py가 Python 3.10 이상을 요구한다는 것과, 첫째 프로그램의 수록 출력이 위수 23~26은 6개 프로세스, 위수 27은 12개 프로세스로 만든 것이라는 설명이 없다.

## 검증 방법

검증은 저자가 AI 코딩 에이전트를 써서 수행했다. 논문을 쓰는 데에도 대규모 언어 모델을 썼고, 이는 원고에 밝혀 두었다. 그래서 누구의 판단에도 기대지 않고 확인할 수 있는 자료로 기록을 구성했다. Lean 커널이 받아들인 명제와, 누구나 다시 실행할 수 있는 정확한 계산이다. 여기에 더해 원고의 증명을 문장 단위로 다시 유도했다.

## 연락처와 라이선스

홍찬우 (Chanu Hong), 경인교육대학교, skdl3965@gmail.com.

프로그램, 스크립트, Lean 소스, 검증 자료는 BSD 3-Clause 라이선스로 공개한다([LICENSE](LICENSE)). manuscript/ 아래의 원고 파일은 © 2026 Chanu Hong이며 열람과 검증을 위해 제공한다. 오픈소스 라이선스의 대상이 아니다. 인용 정보는 [CITATION.cff](CITATION.cff)에 있다.
