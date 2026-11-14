# Theorem 1.1의 증명 사슬

대상은 원고(manuscript/submitted/main.tex) 6절 626–647행이다. 단계마다 무엇이 그
단계를 뒷받침하는지 적었다. "Lean: 이름"은
[../lean_targets/](../lean_targets/)의 고정 명제를 뜻한다.

## Corollary 6.3 (626–637행)

| 단계 | 내용 | 근거 |
|---|---|---|
| 1 | 서로소 합집합의 지배다항식은 성분 지배다항식의 곱이고 D(K₁,x)=x이다 | 성분별 지배집합 선택의 전단사. 정의 기반 대조 750개 숲: [COMPONENT_PRODUCT.json](../checks/COMPONENT_PRODUCT.json) |
| 2 | 계수는 음이 아니고 내부에 0이 없다 | Lemma 2.1(i) |
| 3 | 각 성분의 다항식은 로그오목이다 | K₁은 x. 나무는 Theorem 6.1(전수 계산) |
| 4 | 로그오목이고 내부에 0이 없는 음 아닌 계수열의 곱도 그러하다 | Lemma 6.2. Lean: LogConcaveProduct |
| 5 | 그런 유한 수열은 단봉이다 | Lean: LogConcaveProduct |

## Theorem 1.1 (640–647행)

| 단계 | 내용 | 근거 |
|---|---|---|
| 1 | gap≤3인 숲은 단봉이다 | Corollary 5.2. Lean: GapThreeFull |
| 2 | gap=4인 숲에서 고립점을 지워도 gap과 단봉 여부가 바뀌지 않는다 | Lemma 2.3. Lean: Isolates |
| 3 | 고립점이 없는 gap=4 숲이 단봉이 아니면 n≤22이다 | Theorem 1.2(ii), K₄=7, 6·7−4−16=22. Lean: GeneralGap |
| 4 | 22정점 이하인 숲은 단봉이다 | Corollary 6.3과 22정점 이하 나무의 전수 계산 |
| 5 | 1–4를 합치면 gap≤4인 모든 숲이 단봉이다 | Lean: GapFourBridge가 단계 4를 전제로 받아 결론을 낸다 |

단계 4의 계산은 세 프로그램의 일치, 표준형 중복 검사, 점화식의 정의 대조로 확인했다
([COMPLETENESS_PROOF.md](COMPLETENESS_PROOF.md),
[APPENDIX_A_DP_PROOF.md](APPENDIX_A_DP_PROOF.md)). Theorem 1.1은 이 유한 계산에
기대는 컴퓨터 보조 정리이고, 나머지 단계는 Lean 커널이 확인한 명제로 이어진다.
