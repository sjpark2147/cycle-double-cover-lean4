# PDF history cleanup — 2026-10-03

The user authorized removal of the reference PDF from Git history. The mathematical formalization remains paused. The ignored local `paper.pdf` working copy remains available for reference; the file is not part of the tracked project or cleaned Git history.

## Completed and verified

- Rewrote the published `main` branch and annotated `v4.35.0-rc3` tag with `git-filter-repo`, removing `paper.pdf` throughout their histories.
- Compared the non-PDF file tree of every one of the separate remote clone's 12 commits and the working repository's 10 commits against its corresponding cleaned commit. All retained file paths, modes and blob identities matched. The latest tracked tree was unchanged by the rewrite.
- Checked six local Codex snapshot tree refs, removing the PDF from the three that contained it while preserving all other snapshot entries.
- Expired local reflogs and pruned obsolete Git objects. Both reachability checks and direct object lookup confirmed that the old PDF blob was absent from the cleaned local repositories.
- Updated only the intended remote branch and tag with an atomic push and explicit expected old values. Other concurrent remote updates would have caused the push to fail.
- Kept `/paper.pdf` in `.gitignore` and retained the official source and license links. No Lean source or proof statement was edited for this cleanup.

The published commit IDs have changed. Existing clones must be replaced or carefully cleaned before further pushes; merging the old history back would restore the PDF's history.

## Previous repository's PR retention

Before the previous repository was deleted, closed, unmerged PR #1 retained its previous head in `refs/pull/1/head`, whose history contained the PDF. GitHub rejected an attempted deletion with `deny updating a hidden ref`. Repository administrators cannot remove this internal reference through a normal Git push. The previous release had no separately uploaded assets, and that repository reported no forks at inspection time.

To test whether the PR could be updated, its original source branch was temporarily recreated at the rewritten, PDF-free PR head. GitHub rejected reopening the PR with HTTP 422: `state cannot be changed`, because the branch had been force-pushed or recreated. The temporary branch was then deleted with an explicit expected-commit lease. The old PDF-containing branch history was not restored, and the PR stayed closed at its old head until repository deletion.

GitHub's [history-removal guidance](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/removing-sensitive-data-from-a-repository) describes residual references and limits its sensitive-data removal assistance; a copyright-related request is not guaranteed to qualify. A support request draft and the exact affected identifiers were prepared locally in `.lake/history-cleanup/GitHubSupportRequest.md`; no request was sent.

## Migration to a fresh repository

On 2026-10-03, the user deleted the previous repository and supplied the empty [cycle-double-cover-lean4](https://github.com/sjpark2147/cycle-double-cover-lean4) repository as the new remote. The previous repository API returned 404, while the new repository had a distinct repository ID and no Git refs. The local `origin` is connected to `https://github.com/sjpark2147/cycle-double-cover-lean4.git`.

Only the cleaned `main` branch and annotated `v4.35.0-rc3` tag are selected for publication. Previous PR refs and local Codex snapshot refs are not included in the push. A complete Git bundle containing the cleaned branch and tag was independently cloned and checked: neither the PDF path history nor the old PDF blob was present. Lean sources, dependency pins and the paused proof status remain unchanged.

This report confirms cleanup of the controllable Git histories and publication to a fresh repository. It does not claim erasure of GitHub's internal retained objects, caches or copies held by other people.
