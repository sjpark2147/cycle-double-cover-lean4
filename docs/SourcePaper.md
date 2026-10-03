# Source paper and PDF distribution

The source is Sang-il Oum's *A proof of the cycle double cover conjecture by OpenAI: An exposition*, [arXiv:2607.16356v3](https://arxiv.org/abs/2607.16356v3). Version 3 was submitted on 2026-08-01. The local ten-page PDF was generated on 2026-08-04, and its XMP metadata identifies that version.

The license check on 2026-10-03 found the [arXiv non-exclusive distribution license](https://arxiv.org/licenses/nonexclusive-distrib/1.0/license.html) in both the PDF's `dc:rights` metadata and the arXiv record. It grants distribution rights to arXiv. General redistribution rights for this GitHub repository, such as those granted by a Creative Commons license, have not been established. arXiv's [license guidance](https://info.arxiv.org/help/license/index.html) distinguishes free viewing and downloading from redistribution permissions.

The repository links to the official paper. A working copy may be kept at the root as `paper.pdf`; Git ignores it, along with extracted text and build logs under `.lake/`. The PDF's distribution policy and the Lean code's license are separate.

On 2026-10-03, the user authorized removal of `paper.pdf` from every commit reachable through `main` and the `v4.35.0-rc3` tag. The cleanup preserved all non-PDF file trees and removed the PDF from local Codex snapshot refs, reflogs and obsolete Git objects.

GitHub retained the old head of closed PR #1 in a read-only internal reference and rejected both its deletion and reopening the PR with cleaned history. The user then deleted the repository and created [cycle-double-cover-lean4](https://github.com/sjpark2147/cycle-double-cover-lean4). The new repository received only the cleaned `main` history and `v4.35.0-rc3` tag. [HistoryCleanup.md](HistoryCleanup.md) records the checks and migration. Erasure of GitHub's internal retained copies or other people's clones has not been verified.
