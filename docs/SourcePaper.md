# Source paper and PDF distribution

The formalization uses Sang-il Oum, *A proof of the cycle double cover conjecture by OpenAI: An exposition*, [arXiv:2607.16356v3](https://arxiv.org/abs/2607.16356v3), submitted in version 3 on 2026-08-01. The local ten-page PDF was generated on 2026-08-04; its XMP metadata identifies this exact arXiv version.

Checked on 2026-10-03, both the PDF's `dc:rights` metadata and the arXiv record identify the [arXiv non-exclusive distribution license](https://arxiv.org/licenses/nonexclusive-distrib/1.0/license.html). This grants distribution rights to arXiv. It is not a Creative Commons license granting general redistribution rights to this GitHub repository. arXiv's [license guidance](https://info.arxiv.org/help/license/index.html) also distinguishes freely viewing or downloading articles from the permissions granted by their chosen licenses. Separate permission for redistribution here has not been established.

The repository therefore links to the official paper instead of distributing the PDF in its current tree. A working copy may be kept at the repository root as `paper.pdf`, which is ignored by Git. The local extracted text and build logs under `.lake/` are also ignored. This PDF policy does not select or change a license for the Lean code.

On 2026-10-03, the user authorized a history rewrite. `paper.pdf` was removed from every commit reachable through the published `main` branch and `v4.35.0-rc3` tag. All non-PDF file trees were preserved. The current local repository's commit history, Codex snapshot refs, reflogs and old Git PDF object were also cleaned. See [HistoryCleanup.md](HistoryCleanup.md) for verification and the remaining server-side scope.

GitHub still retains the old head of closed PR #1 as a read-only internal reference. An attempted deletion was rejected by GitHub. That PR and any cached copies require GitHub-side handling; rewriting branches and tags does not guarantee removal from these locations or from other people's clones. No claim of complete server-side erasure is made.
