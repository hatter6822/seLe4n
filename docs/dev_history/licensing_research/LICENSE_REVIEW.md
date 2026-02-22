# License compatibility review (for adopting MIT)

Requested by repository owner: review potential licensing conflicts **before** adding an MIT
license, then complete pre-adoption actions and add the license.

## Scope reviewed

- Lean source in `SeLe4n/` plus `Main.lean` and `SeLe4n.lean`.
- Project docs in `README.md` and `docs/`.
- Build metadata (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`).
- Local scripts and tests under `scripts/` and `tests/`.

## Findings

1. **No existing repository license file is present yet**
   - There is currently no `LICENSE` / `COPYING` file in this repo.

2. **No third-party package dependencies are declared in the Lake manifest**
   - `lake-manifest.json` has an empty `packages` list, reducing immediate risk of pulling in
     incompatible dependency licenses.

3. **Project appears to be an original Lean model rather than vendored upstream seL4 code**
   - The repository describes itself as a Lean formalization *of* seL4 semantics.
   - The code and docs use seL4 terminology/references, but there are no in-file notices indicating
     copied or embedded upstream source blocks.

4. **MIT is likely appropriate for this codebase as it stands**
   - Based on the current tree contents, there are no visible copyleft triggers or conflicting
     license headers.

## Risks to keep in mind

- **Provenance risk (human process risk):** if any file was copied from external sources and that
  provenance is not recorded, this review cannot detect it with certainty.
- **Trademark/branding:** references to “seL4” are descriptive, but MIT licensing does not grant
  trademark rights; keep naming usage factual and non-endorsing.
- **Future dependency drift:** adding Lake packages later may introduce non-MIT-compatible terms;
  re-run dependency license checks when that changes.

## Recommendation before adding MIT

1. Add a standard MIT `LICENSE` file at repository root.
2. Add copyright holder line(s).
3. Add a short note in `README.md` pointing to `LICENSE`.
4. Keep a lightweight provenance policy for new contributions (e.g., “no copied code without
   explicit attribution and license compatibility”).
5. Re-check licenses whenever external packages are added to `lake-manifest.json`.

## Recommendation completion status

The pre-adoption recommendations above have now been completed in this repository:

1. ✅ Added MIT `LICENSE` at repository root.
2. ✅ Included a copyright holder line in the MIT text.
3. ✅ Added a short `README.md` note pointing to `LICENSE`.
4. ✅ Added a lightweight provenance policy note in `README.md` (no copied third-party code
   without explicit attribution and license-compatibility confirmation).
5. ✅ Kept dependency re-check guidance documented in this review; re-run this check whenever
   external Lake packages are introduced.

## Bottom line

With the repository in its current state, I did **not** see a clear blocker to adopting MIT, and
the repository now includes an MIT `LICENSE` plus the related process/documentation follow-ups.
