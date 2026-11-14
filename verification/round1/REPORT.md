# 1차 검증 보고서

- 검토 대상: Chanu Hong, Unimodality of domination polynomials of forests with upper domination gap at most four (2026년 11월)
- 검토한 자료: 이 저장소의 manuscript/, computation/, lean/ 과 같은 내용의 2026-11-12 스냅샷
- 검증 일자: 2026-11-13
- 결과: 수학적 오류 0건. 원고의 주 정리(정리 1.1, 1.2, 1.3, 명제 7.2), 보조정리, 전수 계산, Lean 4.27.0 형식화에서 오류를 찾지 못했다. 서술과 패키징에 관한 보완 사항 4건은 2절에 있다.

---

## 1. 핵심 결과

1. 본문 수학 증명 검증: 정리 1.1(상지배 간격 Γ(F) − γ(F) ≤ 4인 모든 유한 숲 F의 지배다항식 단봉성), 정리 1.2(일반 간격 h에서의 단봉 충분조건 n − γ(F) ≥ 3K_h − 7 및 무고립점 유한 환원 n ≤ 6K_h − h − 16), 정리 1.3(26정점 이하 모든 나무 447,672,596종의 로그오목성과 27정점 유일 비로그오목 나무 U), 명제 7.2(평균 임계 꼭짓점 점프 상계 c_{j+1} − c_j < 2(j − γ) + 1 및 2t + 1 수렴 최선성)의 수기 증명을 줄 단위로 검산한 결과 논리 비약, 부등호 방향 착오, 첨자 범위 누락, 반례는 발견되지 않았습니다.
2. Lean 4.27.0 커널 직접 빌드 및 공리 감사: 고정된 Mathlib4 커밋(a3a10db0e9d66acbebf76c5e6a135066525ac900)과 Lean 4.27.0에서 전체 7,905개 빌드 잡을 로컬에서 처음부터 컴파일해 성공했습니다. CheckAxioms.lean 출력(85행)은 저장소 참조본(CheckAxioms.output.txt)과 공백 단위까지 일치하며, 모든 형식화 정리가 sorryAx나 native_decide 없이 표준 고전 공리 3개(propext, Classical.choice, Quot.sound)만 사용합니다. 또한 본 검증에서 RefereeAudit.lean을 추가 작성해 내부 네임스페이스 4곳의 지배집합·임계꼭짓점 정의 동치, 별 그래프 K_{1,4} 비공허성, 미형식화 보조정리 2.3의 영점 추가 단봉 동치, h = 1(K_1 = 1) 및 n − γ ≤ 2 단봉 경계를 Lean 4.27.0 커널로 직접 증명했습니다.
3. 다중 알고리즘 독립 계산 재검증:
   - 저자 C++17 검사기 2종(independent_check.cpp, wrom_check.cpp) 및 restricted_census.cpp를 로컬 LLVM-MinGW clang++(-O3 -std=c++17)로 재컴파일해 위수 2..22(비동형 나무 9,114,284종, 16정점 이하 32,507종 부분집합 전수 대조 포함) 및 GitHub CI 범위를 넘는 위수 23(비동형 나무 14,828,074종)까지 실행한 결과, 나무 개수·최댓값·총 지배집합 수·64비트 다중집합 해시 지문(n=23: 2831328136764df1)이 참조 파일과 100% 일치했습니다.
   - 저자 코드(수준 수열 기반 BH·WROM)와 전혀 다른 제3 독립 C++17 검증기(independent_third_tree_verifier.cpp: 정수 분할 다중집합 상향식 루트 나무 생성 + Jordan 중심 표준형 + 비무게중심 루트 DFS DP)를 새로 작성해 위수 2..19(자유 나무 522,958종, 루트 나무 7,421,145종)를 전수 대조한 결과 모든 지표와 64비트 해시 지문이 100% 일치했습니다.
   - 27정점 예외 나무 U의 2^27 = 134,217,728개 부분집합을 독립 Node.js 및 C++ 비트마스크 열거기로 직접 계산해 계수열(d_9 = 2, d_10 = 75, d_11 = 2837, 75^2 − 2×2837 = −49 < 0, 유일 로그오목 실패 지수 j = 10, j = 17에서 최댓값 1,454,340을 갖는 단봉 수열)을 재확인했습니다.
   - 저자 전수 코드가 직접 시험하지 않은 비연결 숲 220종, 고립점 포함 숲 136종, 순환 이분그래프 150종, C_4 하계 실패 예시, Cauchy–Binet 항별 전개 200쌍, 6,501정점(점프 2.0000071) 및 15,485정점(점프 2.1594) 반례 나무 전체 다항식을 정확 유리수(Fraction)로 검증해 위반 0건을 확인했습니다.
4. 선행연구 원문 PDF 직접 대조: Beaton & Schoonhoven (2024, arXiv:2411.02288v1), Mohamed Omar (2026, arXiv:2601.14494v1), Du, Heilman & Panova (2026, arXiv:2605.02193v1) 원문 PDF 전문과 Iain Beaton의 2026년 10월까지 공개된 arXiv 논문 전체를 직접 대조해 정리 번호·가정 왜곡이 없고 주 정리 중복이 없음을 확인했습니다.

---

## 2. 보완 권고 사항 (총 4건 — 수학적 결론 불변, 편집·재현성 개선 항목)

| 번호 | 구분 | 위치 | 상세 내용 | 권고 조치 |
|---|---|---|---|---|
| 1 | 본문 경계 서술 | body_part1.tex 보조정리 2.3 및 따름정리 5.2 | 모든 꼭짓점이 고립점인 숲 G = K̄_n (r = n ≥ 1)에서 고립점을 모두 삭제한 G°는 위수 0인 공그래프가 되는데, 정리 5.1은 n ≥ 1을 가정하고 본문에 위수 0 공그래프 규약(D(∅,x)=1, γ(∅)=Γ(∅)=0)이 명시되어 있지 않음 | 보조정리 2.3에 r < n 조건을 두거나(r = n이면 D(K̄_n,x) = x^n으로 자명히 단봉), 위수 0 공그래프 규약 한 문장을 추가 |
| 2 | 형식화 경계 기록 | lean/domination_gap3/UniformGapJumpCandidate.lean 및 부록 B | 본문 보조정리 4.3·정리 5.1은 식 (5)로 j − c_j > 0을 얻어 모든 h ≥ 0, n ≥ 1에서 성립하지만, Lean의 graph_uniform_gap_unimodal은 h < K(h=1일 때 K_1=1이므로 불성립)와 A + 2 ≤ n(n − γ ≤ 2일 때 불성립)을 추가 가정함(부록 B의 설명 자체는 정직하고 정확함) | 일반 h를 Lean으로 확장할 때 본 검증의 RefereeAudit.lean에 작성한 lemma_jump_without_h_lt_K와 short_tail_unimodal을 결합해 경계 제거 가능 |
| 3 | Windows 줄바꿈 이식성 | 저장소 루트 (.gitattributes 부재), SHA256SUMS | Git 원본 blob(LF) 기준으로는 SHA256SUMS(125개)·SUPPLEMENT_SHA256SUMS(110개) 전수 일치하나, Windows 기본 core.autocrlf=true 클론 시 작업 트리가 CRLF로 변환되어 sha256sum -c, run_all.sh, ProofWidgets 트레이스 검사가 실패함 | * text=auto eol=lf 설정의 .gitattributes 추가 및 README에 Windows 클론 옵션 안내 |
| 4 | 보충자료 JSON·경로 | computation/jumps/ 하위 스크립트 및 verify_result.json | ① verify_result.json에 gamma와 Gamma 키가 함께 쓰여 대소문자 비구분 JSON 파서(PowerShell ConvertFrom-Json 등)에서 중복 키 오류 발생 ② verify_counterexample.py, sharpness.py, restricted_on_family.py가 jumps/results/가 아닌 jumps/에 출력하며 verify_result.json이 중복 커밋됨 ③ search_small.py 2행에 개인 경로(research/q72_jump) 잔존 | 키 명칭 분리(예: gamma_min / gamma_upper), 출력 경로를 jumps/results/로 통일, 불필요 sys.path 제거 |

---

## 3. 정리·보조정리별 전수 검증 요약표

| 항목 | 핵심 명제 | 수기 검산 | Lean 4.27.0 커널 | 독립 계산 검산 | 결과 |
|---|---|---|---|---|---|
| 보조정리 2.1 | 지지 구간 [γ,n], Crit 반단조성, 입사 항등식 | 통과 | graph_domination_lemma3_identity 통과 | 나무 32,507종 + 비연결 숲 220종 일치 | 통과 |
| 보조정리 2.2 | 무고립점 극소 지배집합 여집합 지배성 및 n ≥ γ + Γ | 통과 | isDominating_compl_of_minimal 통과 | 무고립점 숲·이분그래프 퍼징 통과 | 통과 |
| 보조정리 2.3 | 고립점 r개 제거 시 D(G,x)=x^r D(G°,x), 단봉·간격 보존 | 통과 (r=n 규약 메모) | RefereeAudit.unimodal_prepend_zeros 입증 | 고립점 포함 숲 136종 대조 통과 | 통과 |
| 보조정리 3.1 | 숲에서 |S| + a(S) ≥ 2γ(F) | 통과 | forest_critical_inequality 통과 | 나무 32,507종 + 숲 220종 + C_4 반례 확인 | 통과 |
| 보조정리 3.2 | 이분그래프에서 |S| + a(S) ≤ 2α(G), Γ = α | 통과 | bipartite_critical_le_two_independence 통과 | 순환 이분그래프 150종 위반 0건 | 통과 |
| 따름정리 3.3, 3.4 | 양측 경계, 단조 증가·감소 구간, avd 경계 | 통과 | left_wing 및 이분 상계 포함 | 이분그래프 150종 단조·avd 위반 0건 | 통과 |
| 보조정리 4.1~4.3 | 골짜기 점프 > 2, 공분산 부등식, j ≥ γ+K_h 점프 ≤ 2 | 통과 | graph_incidence_variance_inequality + RefereeAudit 통과 | 정확 유리수 전수 대조 위반 0건 | 통과 |
| 정리 5.1 & 정리 1.2 | n − γ ≥ 3K_h − 7 단봉성 및 n ≤ 6K_h − h − 16 유한 환원 | 통과 | graph_uniform_gap_unimodal, forest_gap_four_large_unimodal, no_isolates_gap_four_large_or_at_most_twenty_two 통과 | 숲 퍼징 및 유한 환원 대조 통과 | 통과 |
| 따름정리 5.2 | Γ(F) − γ(F) ≤ 3인 모든 숲의 단봉성 | 통과 | forest_gap_three_unimodal_no_isolates + star5 비공허성 통과 | K_{1,4} 및 숲 퍼징 통과 | 통과 |
| 정리 1.3 (6.1, 6.5, 6.6) | n ≤ 26 모든 나무 로그오목, n = 27 유일 예외 U | 통과 | 컴퓨터 보조 증명(부록 B 명시) | C++ 2종 n=2..23 + 제3 생성기 n=2..19 + U의 2^27 열거 일치 | 통과 |
| 보조정리 6.2, 따름정리 6.3, 정리 1.1 | 로그오목 다항식 곱 보존 및 간격 4 이하 모든 숲 단봉성 | 통과 | 유한 환원 형식화 + 다항식 곱·전수 계산 결합 | Cauchy–Binet 200쌍 + 1,290,927종 gap-4 숲 재집계 일치 | 통과 |
| 명제 7.2 & 식 (16) | 점프 상계 2(j−γ)+1 최선성 및 상단 1−2/n 부등식 | 통과 | 수기 점근 증명 + 명시적 반례 계산 | 6,501·15,485정점 전체 DP + 라벨 나무 18,247개 전수 통과 | 통과 |