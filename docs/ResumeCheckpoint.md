# 작업 중단 지점 — 2026-10-03

사용자의 중단 요청에 따라 작업을 일시정지했습니다. 전체 theorem·definition을 `sorry`와 추가 수학 공리 없이 형식화하는 목표는 아직 미완료이며, 사용자가 재개를 요청하면 이어서 진행합니다.

## 검증된 상태

- 문서 정리와 초안 경로 변경 후 `lake build`가 2,838 jobs를 통과했습니다. 로그는 `.lake/documentation-checkpoint-build.log`에 있습니다. 중단 직전의 `.lake/pause-checkpoint-build.log`도 같은 수치를 기록합니다.
- Audit은 프로젝트 정리 선언 4,948개와 정의 753개를 검사했습니다. 허용 의존 공리는 `propext`, `Classical.choice`, `Quot.sound`뿐입니다. 선언 수에는 보조·생성 선언이 포함되므로 논문 항목 완료율은 별도로 셉니다.
- Conjecture를 제외한 번호 있는 증명 대상 21개 중 19개를 검증했고, 정의 45개와 conjecture 명제 7개를 구현했습니다. **Conjecture 전체 명제의 증명은 0/7개입니다.** 일부 동치·함의와 cubic strong embedding 특수 경우는 증명했습니다. [PaperCoverage.md](PaperCoverage.md)는 승인된 loop 관련 수정과 원문 일치 검토의 한계를 기록합니다.
- 검증 범위는 library import closure의 source module 344개와 별도 Audit target입니다. 아래 두 초안은 제외됩니다.

빌드 로그는 Git이 무시하는 로컬 `.lake/`에 있습니다. 클론 후 기본 `lake build`로 검사 결과를 재현할 수 있습니다.

원문 PDF는 공개 `main`·태그의 이력에서 제거했고, 로컬 `paper.pdf`만 유지합니다. 새 저장소 [cycle-double-cover-lean4](https://github.com/sjpark2147/cycle-double-cover-lean4)에는 정리된 `main`과 태그를 게시했습니다. [SourcePaper.md](SourcePaper.md)는 논문 버전과 공식 링크를, [HistoryCleanup.md](HistoryCleanup.md)는 이력 정리와 이전 PR 이력을 제외한 저장소 이전 과정을 기록합니다.

## 남은 본문 증명

- Theorem 24에는 모든 finite bridgeless 그래프의 nowhere-zero 6-flow 존재와 일반 ten-layer six-cover 변환이 남아 있습니다. 최소 반례를 구성해 six-flow 목표는 simple·cubic·3-edge-connected·girth ≥ 6·nontrivial cut ≥ 4 경우로, cover 목표는 같은 cut 조건에서 girth ≥ 5·정점 수 ≥ 12 경우로 줄였습니다. 두 핵심 경우의 존재 증명이 필요합니다.
- Theorem 27에는 일반 Fano-free/regular 구조 및 CDC 존재 증명이 남아 있습니다. 작은 rank·dual rank·ground 경우와 Fano minor에서 separation을 구성하는 증명은 검증했습니다. ΔY 교환과 최소성을 이용해 regular 최소 반례의 triangle-free 조건도 도출했습니다.
- 번호 없는 결과 중 일반 matroid equivalence(U26)와 일반 regular matroid CDC(U28)가 남아 있습니다. U04의 cubic strong-embedding implication은 검증했습니다.

## 재개할 때 먼저 확인할 초안

다음 두 파일은 내용을 바꾸지 않고 `CycleDoubleCover/`에서 `docs/drafts/`로 옮겼습니다. 기본 빌드와 공리 검사에서 제외한 미완료 초안입니다. 재개하면 원래 모듈 경로로 복원한 뒤, 별도 빌드·공리 검사와 남은 증명 목표에 대한 검토를 거쳐 통합해야 합니다.

- [`FanoFreeThreeSumCovers.lean`](drafts/FanoFreeThreeSumCovers.lean): triangle 교환에서 얻은 singleton interface profile을 이용한 proper regular three-sum cover gluing. 임의 binary summand의 CDC가 호환 profile을 갖는다고 가정하면 안 됩니다.
- [`TernaryBranchInterfaceForest.lean`](drafts/TernaryBranchInterfaceForest.lean): optimizer의 branch-free support 성분 사이 zero-edge incidence forest와 원래 boundary port 구성. Full-branch 성분 안의 simultaneous repair는 아직 해결해야 합니다.

Fan 변환에는 outside forest와 correction colouring에서 affine obstruction의 parity를 증명하는 작업이 남았습니다. Favorable factor·routing·colour assignment의 존재를 가정한 결과를 사용하려면 그 존재도 증명해야 합니다.

Theorem별 상태와 과거 검증 기록은 [PaperCoverage.md](PaperCoverage.md)에 있습니다.
