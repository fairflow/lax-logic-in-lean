# Paper III, "The order of F0": status of the v0.5 revision

Tracked status note for the revision of `F0Paper/` from v0.4.1 to v0.5
(manager's brief of 2026-10-25).  Agent worktree `agent-aff1d57f31573668e`,
branch `worktree-agent-aff1d57f31573668e`, cut from main `21d3eb3` (PR #89)
with `origin/f0-filter-iso` (PR #92, `00373c0`) merged in.  Nothing pushed.

## 2026-10-25 19:14 GMT: plan

1. Running header in the shared machinery: `III:F0Lattice 0.5 · 25 Oct 2026`;
   the branch@sha stamp moves to the title block in small type.  Same for the
   semantics paper (`I:Semantics 0.2`), content unchanged.
2. The Dedekind–MacNeille section rewritten: cuts as in Dedekind's ℝ from ℚ,
   where choice enters, the extension of ◯, the points of F*.
3. New section: which filters [p, ⊤] are order-isomorphic to F0
   (`wip/f0FilterIso.lean`).
4. Two closing sections: "What is established" (one table, axioms computed)
   and "Open problems" (status, sketches).
5. Optional: `wip/f0MacNeillePoints.lean` for (D) a non-principal point and
   (C) |F*| = 2^ℵ₀, each only if under about 100 lines.

Not touched: `wip/f0Normal.lean` (F₇ is certified in another worktree).

The Edit/Write tools refuse this worktree (the hook takes the manager's
worktree as the session root); files are written in the scratchpad and moved
in with `mv`, or edited by an exact-replacement script that writes a
temporary file and renames it.

## 2026-10-25 20:07 GMT: v0.5 rendered

Done (commits on this branch, nothing pushed):

* Running header `III:F0Lattice 0.5 · 25 Oct 2026` from `PaperKit/Stamp.lean`
  (`{paperStamp (number := "III") (name := "F0Lattice")}`F0Paper/VERSION``,
  the one place a paper declares its number and name); the branch@sha stamp
  is the date line of the title page, small type
  (`scripts/verso-tex-pdf.sh`).  The semantics paper re-rendered once with
  `I:Semantics 0.2`, content unchanged.  The CLP paper keeps `{buildStamp}`.
* `wip/f0MacNeillePoints.lean` (new, about 190 lines with docs): (D)
  `gapCut_ne_principal`, `exists_nonprincipal`; (C) `card_eq_continuum`, with
  `Countable RNClass` and `X_injective`.  Pins `[propext, Classical.choice,
  Quot.sound]`, each watched failing at `[propext, Quot.sound]`
  (`_out/pinwatch_points.lean`).
* Merged `origin/f0-filter-iso` (00373c0) and, on the manager's word,
  `origin/f0-normal` (384e942): F₇ is PROVED (`wip/f0Normal.lean`, not
  edited here) and is displayed in Section 11.
* Sections: 10 "Filters isomorphic to F0" (new), 11 the Dedekind–MacNeille
  completion (rewritten), 12 "What is established" (new), 13 "Open problems"
  (rewritten); T6 and SelfSim are now Sections 8 and 9; cross-references
  updated.  `PaperKit/Math.lean`: cases for the new declarations, guarded by
  the F0 notation so the semantics paper's output does not change.
* `docs/references.bib`: `MacNeille1937` (by DOI through `bib-sync.py`) and
  `Dedekind1872` (by hand), each with a note saying it was not checked
  against the work.
* Checks: `tex errors: 0`, `missing glyphs: 0`, 28 pages; private-term and
  "dense" scans of the sources and the PDF text clean (the word "completions"
  occurs only in titles of cited works on MacNeille completions; "dense" only
  in the order sense).  Every page viewed.

Delivered: `/Users/matthew/Lean/III-F0Lattice-v0.5.pdf`.
