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

## Remaining GitHub-side scope

Closed, unmerged [PR #1](https://github.com/sjpark2147/cdc-fmlz/pull/1) retains its previous head in `refs/pull/1/head`, whose history contains the PDF. GitHub rejected an attempted deletion with `deny updating a hidden ref`. Repository administrators cannot remove this internal reference through a normal Git push. The release has no separately uploaded assets, and the repository reported no forks at inspection time.

To test whether the PR could be updated, its original source branch was temporarily recreated at the rewritten, PDF-free PR head. GitHub rejected reopening the PR with HTTP 422: `state cannot be changed`, because the branch had been force-pushed or recreated. The temporary branch was then deleted with an explicit expected-commit lease. The old PDF-containing branch history was not restored, and the PR remains closed at its old head.

GitHub-side removal of the PR reference and cached old objects is still pending. GitHub's [history-removal guidance](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/removing-sensitive-data-from-a-repository) describes these residual references and limits its sensitive-data removal assistance; a copyright-related request is not guaranteed to qualify. A support request draft and the exact affected identifiers are prepared locally in `.lake/history-cleanup/GitHubSupportRequest.md`; no request has been sent.

This report confirms cleanup of the controllable Git histories. It does not claim erasure of GitHub's retained PR objects, caches or copies held by other people.
