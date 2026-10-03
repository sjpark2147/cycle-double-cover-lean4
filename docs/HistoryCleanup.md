# PDF history cleanup — 2026-10-03

The user authorized removal of the reference PDF from Git history. The ignored local `paper.pdf` remains available for reference. The mathematical formalization is paused.

## Completed and verified

- Rewrote the published `main` branch and annotated `v4.35.0-rc3` tag with `git-filter-repo`, removing `paper.pdf` throughout their histories.
- Compared the non-PDF file trees of 12 commits in the separate remote clone and 10 in the working repository with their cleaned counterparts. All retained paths, modes and blob identities matched; the latest tracked tree was unchanged.
- Checked six local Codex snapshot tree refs, removing the PDF from the three that contained it while preserving all other snapshot entries.
- Expired local reflogs and pruned obsolete Git objects. Both reachability checks and direct object lookup confirmed that the old PDF blob was absent from the cleaned local repositories.
- Updated the intended remote branch and tag with an atomic push guarded by their expected old values, so a concurrent change to either ref would have rejected the push.
- Kept `/paper.pdf` in `.gitignore` and retained the official source and license links. No Lean source or proof statement was edited for this cleanup.

The rewrite changed commit IDs. Replace or clean existing clones before pushing again; merging old history would restore the PDF's history.

## Previous repository's PR retention

Closed, unmerged PR #1 retained the PDF-containing history in `refs/pull/1/head` until the previous repository was deleted. GitHub rejected deletion with `deny updating a hidden ref`; even a repository administrator cannot remove this reference through a normal Git push. At inspection time, the release had no separately uploaded assets and the repository reported no forks.

The original source branch was temporarily recreated at the rewritten, PDF-free PR head to test reopening. GitHub returned HTTP 422, `state cannot be changed`, because the branch had been force-pushed or recreated. The temporary branch was deleted with an expected-commit lease. This test used cleaned history throughout; the PR stayed closed at its old head until repository deletion.

GitHub's [history-removal guidance](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/removing-sensitive-data-from-a-repository) describes residual references and the limits of sensitive-data removal assistance. Whether a copyright-related request qualifies was not established. A draft with the affected identifiers remains local at `.lake/history-cleanup/GitHubSupportRequest.md`; it was never sent.

## Migration to a fresh repository

On 2026-10-03, the user deleted the previous repository and supplied the empty [cycle-double-cover-lean4](https://github.com/sjpark2147/cycle-double-cover-lean4) as the new remote. The previous repository API returned 404. The new repository had a distinct ID and no Git refs. Local `origin` now points to `https://github.com/sjpark2147/cycle-double-cover-lean4.git`.

The push published the cleaned `main` branch and annotated `v4.35.0-rc3` tag, excluding previous PR refs and local Codex snapshot refs. An independent clone of a Git bundle containing the cleaned branch and tag had no PDF path history or old PDF blob. The migration preserved Lean sources, dependency pins and the paused proof status.

Erasure of GitHub's internal retained objects, caches or copies held by other people has not been verified.
