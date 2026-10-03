# 작업 중단 지점 — 2026-10-03

사용자가 적당한 지점에서 멈추도록 요청하여 작업을 일시정지했습니다. 전체 theorem·definition을 `sorry`와 추가 수학 공리 없이 형식화하는 목표는 유지하며, 완료로 처리하지 않습니다.

## 검증된 상태

- 문서 정리와 초안 경로 변경 후 기본 `lake build` 재검증 성공: 2,838 jobs. 최신 로그: `.lake/documentation-checkpoint-build.log`. 중단 직전 로그 `.lake/pause-checkpoint-build.log`도 같은 검증 수치를 기록합니다.
- Audit 검사: 프로젝트 정리 4,948개, 정의 753개. 허용 의존 공리는 `propext`, `Classical.choice`, `Quot.sound`뿐입니다. 이 수에는 보조·생성 선언이 포함되며 논문 항목 완료율을 뜻하지 않습니다.
- 번호 있는 증명 대상 21개 중 19개 검증. 이 수에는 conjecture가 포함되지 않습니다. 논문 정의 45개와 conjecture 명제 7개 구현. **Conjecture의 원래 전체 명제를 증명한 수는 0/7개**이며, 일부 동치·함의와 cubic strong embedding 특수 경우만 증명했습니다. 승인된 loop 관련 최소 수정과 원문 일치 검토의 한계는 `PaperCoverage.md`에 기록되어 있습니다.
- library import closure 344개 source module와 별도 Audit target이 검증 범위입니다.
- 이 커밋 지점에는 기본 빌드로 검증한 소스, 현재 상태 문서, 기본 빌드에서 제외한 두 초안의 보관본을 포함합니다. 빌드 로그는 `.gitignore`에 따라 로컬 `.lake/`에만 남으며, 클론 후 기본 `lake build`로 검사 결과를 재현할 수 있습니다.
- 원문 PDF는 현재 Git tree에서 제외하고 로컬 `paper.pdf`만 유지합니다. 재개에 필요한 정확한 논문 버전과 공식 링크는 [SourcePaper.md](SourcePaper.md)에 기록했습니다. 과거에 push된 PDF의 이력은 별도로 남아 있습니다.

## 남은 본문 증명

- **Theorem 24:** 모든 finite bridgeless 그래프의 nowhere-zero 6-flow 존재와 일반 ten-layer six-cover 변환. 현재 실제 최소 반례를 통해 six-flow는 simple·cubic·3-edge-connected·girth ≥ 6·nontrivial cut ≥ 4 경우로, cover는 girth ≥ 5·정점 수 ≥ 12인 같은 cut 조건으로 축약했습니다. 이 핵심 경우의 존재 증명은 아직 없습니다.
- **Theorem 27:** 일반 Fano-free/regular 구조 및 CDC 존재. 작은 rank·dual rank·ground 경우와 실제 Fano minor에서의 separation 구성을 검증했습니다. Regular 최소 반례의 triangle-free 조건도 실제 ΔY 교환과 최소성에서 도출했습니다. 일반 구조·cover 증명은 아직 없습니다.
- **번호 없는 결과:** 일반 matroid equivalence(U26)와 일반 regular matroid CDC(U28)가 남아 있습니다. U04의 cubic strong-embedding implication은 검증했습니다.

## 재개할 때 먼저 확인할 초안

다음 두 파일은 원래 `CycleDoubleCover/`에서 `docs/drafts/`로 내용 변경 없이 옮겨 보존했습니다. 기본 import closure에 포함되지 않으며, 이번 통합 검증의 완료 결과로 계산하지 않습니다. 재개 시 원래 모듈 경로로 복원하고 별도 빌드·공리 검사와 실제 남은 목표에 대한 검토 후에만 통합해야 합니다.

- [`FanoFreeThreeSumCovers.lean`](drafts/FanoFreeThreeSumCovers.lean): 실제 triangle 교환에서 얻는 singleton interface profile을 이용한 proper regular three-sum cover gluing 작업. 임의 binary summand의 CDC를 호환 profile로 가정하면 안 됩니다.
- [`TernaryBranchInterfaceForest.lean`](drafts/TernaryBranchInterfaceForest.lean): 실제 optimizer의 branch-free support 성분 사이 zero-edge incidence forest와 원래 boundary port 작업. Full-branch 성분 안의 simultaneous repair는 여전히 해결해야 합니다.

Fan 변환 쪽에서는 실제 outside forest와 correction colouring에서 affine obstruction의 parity를 증명하는 작업이 남았습니다. Favorable factor·routing·colour assignment를 가정하는 조건부 결과로 전체 존재 증명을 대체하면 안 됩니다.

자세한 theorem별 상태와 과거 검증 기록은 [PaperCoverage.md](PaperCoverage.md)가 기준입니다. 형식화 작업은 사용자가 재개를 요청할 때까지 일시정지 상태를 유지합니다.
