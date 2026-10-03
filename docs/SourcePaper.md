# Source paper and PDF distribution

The formalization uses Sang-il Oum, *A proof of the cycle double cover conjecture by OpenAI: An exposition*, [arXiv:2607.16356v3](https://arxiv.org/abs/2607.16356v3), submitted in version 3 on 2026-08-01. The local ten-page PDF was generated on 2026-08-04; its XMP metadata identifies this exact arXiv version.

Checked on 2026-10-03, both the PDF's `dc:rights` metadata and the arXiv record identify the [arXiv non-exclusive distribution license](https://arxiv.org/licenses/nonexclusive-distrib/1.0/license.html). This grants distribution rights to arXiv. It is not a Creative Commons license granting general redistribution rights to this GitHub repository. arXiv's [license guidance](https://info.arxiv.org/help/license/index.html) also distinguishes freely viewing or downloading articles from the permissions granted by their chosen licenses. Separate permission for redistribution here has not been established.

The repository therefore links to the official paper instead of distributing the PDF in its current tree. A working copy may be kept at the repository root as `paper.pdf`, which is ignored by Git. The local extracted text and build logs under `.lake/` are also ignored. This PDF policy does not select or change a license for the Lean code.

The PDF was already included in commit `d6a6553` and in previously pushed history. Removing it from the current tree does **not** remove those historical copies. This cleanup uses a normal removal commit; it does not rewrite published history. Full historical removal would require a separately authorized and coordinated history rewrite, and would not guarantee removal from existing clones or caches.
