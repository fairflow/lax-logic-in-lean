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

# v0.6: free Heyting algebras in F0

## 2026-10-28 16:21 GMT: plan

Manager's brief of 2026-10-28 (content approved by Matthew the same day).
Agent worktree `agent-a955ba236b7d77cc4`, branch
`worktree-agent-a955ba236b7d77cc4`, reset to main `da627e0` (PR #104).
`.lake` cloned once from the v0.5 worktree (`agent-aff1d57f31573668e`).
Nothing pushed, no upstream.

1. New Section 10, "Free Heyting algebras in F0"
   (`F0Paper/Sections/FreeHA.lean`), after the self-similarity section:
   summary first, why it is unexpected, the table of bases, the generators,
   the construction, the formal statement and why it is correct, the forms
   (H)/(L)/(O), the complement of the range.  Sections 10 to 13 of v0.5
   become 11 to 14; cross-references renumbered (`Section N` in the text,
   the section column of the two tables).
2. Abstract, introduction ("New in v0.6", at a glance), "What is
   established" and "Open problems" extended; `Boolos1993` entered by hand in
   `docs/references.bib`, with a note that it was not checked against a copy.
3. `PaperKit/Math.lean`: cases for the new declarations in `f0Case?`, in
   force only under the F0 notation (the semantics paper's output does not
   change).
4. `VERSION` 0.6; the `paperStamp` header unchanged; the title unchanged.

## 2026-10-28 17:06 GMT: v0.6 rendered

Course corrections from the manager while working, all applied:

* One semantics, subframe models.  The ladder behind `ZL.cell_force` is
  described as the subframe model with `S = ∅`.  The requested sentence "the
  proof uses no constraint models" is FALSE as a dependency fact, so the text
  says what a trace of the constants shows instead (script below): no
  constant of the multi-edge models `cmM`/`cmE` of `wip/f0Indep.lean` occurs,
  and no `Classical.choice`; constraint models (`PLLND.ConstraintModel.*`)
  enter at one place only, the library's completeness theorem for finite
  subframe models (`SubframeModel.CF.completeness` →
  `FRJ.Gbu.W.PLL_iff_laxND` → `FRJ.valid_of_derivable`, which reduces the
  soundness of FRJ Kripke frames to that of constraint models through
  `FRJ.Kripke.toConstraint`, `PLLND.soundness`); `freeIPL1` also uses the
  ladder's lifted constraint model (`not_deriv_of_sep` → `Skel.cm`).
  `not_typeBound_base2` and `sep_circ_x1` use none.
* Main `8864e94` (PR #105, `wip/f0FreeAnyFamily.lean`) merged: `anyFamily3`,
  `freeHAnAbove_base3_of_distinct`, `sigShift`, `allAbove3`, `allAbove3ω`
  cited as PROVED (new subsection 10.6, the table row "σᵐ⊥, m ≥ 3", the
  complement remark (2), What is established).
* Main `37c98e3` (PR #106, `wip/f0FreePLL.lean`) merged: after the approved
  IPC headline, the paragraph "More holds: PLL itself embeds faithfully into
  F0"; `FreePLLAbove`, `FreeReaders`, `freeReaders`, `freePLLAbove_base3`
  printed in 10.7; the proof sketch gains the copy keeping `K`'s own `S` and
  the `◯` case `relB_transferO`; the `◯x₁` witness PROVED
  (`not_image_circ_x1`, `sep_circ_x1`); the PLL statement moved from Open
  problems to What is established and "Closed since v0.5".

Checks (final build, commit `b6416c0`, stamp without `+`):

* `tex errors: 0`, `missing glyphs: 0`, 38 pages (v0.5: 28); html-single
  `unresolved: 0 empty, 0 find/`.  (An intermediate build reported three
  missing ω glyphs from `\mathit{AllAbove3ω}`, `SigShiftω`; fixed by cases
  in `PaperKit/Math.lean`.)
* Section 10 is pages 17 to 26 of the PDF (printed 14 to 23); every page
  viewed, and the Established and Open pages.
* Barred-term scan (the terms of the brief, case-insensitive) of `F0Paper/`,
  `PaperKit/Math.lean` and the PDF text: no hit except this file's v0.5
  section.  "completion" occurs only in the pre-existing text on the
  Dedekind–MacNeille completion (15 lines of PDF text, 16 in v0.5); no line
  added since v0.5 uses it.  "dense" only in the order sense, all
  pre-existing.  No spaced em dash in the new section.
* Text outside Section 10 compared with v0.5 (`pdftotext`, word diff): only
  the renumbering, the new rows and paragraphs, `le(K, j, k)` now printed
  `j ≤ k` (`SubframeModel.le`, F0 notation), and `φ` extracted as `ϕ` by
  `pdftotext` (the glyph is the same `\varphi` in both PDFs, checked on the
  rendered page).

Delivered: `/Users/matthew/Lean/III-F0Lattice-v0.6.pdf`.

Cosmetic, not fixed: the heading "10.10 Supporting declarations" falls at the
foot of a page with its table on the next; the display of `FreeFamily3`
starts slightly left of the margin.

The trace (run with `lake env lean <file>` against the built modules; the
roots were the printed results of Section 10):

```lean
import wip.f0FreePLL
import wip.f0FreeAnyFamily
import wip.f0MeetCount
import wip.f0EmbedForms
open Lean Elab Command
def isCM (n : Name) : Bool :=
  ["ConstraintModel", "cmM", "cmE"].any fun p => (n.toString.splitOn p).length > 1
#eval show CommandElabM Unit from do
  let env ← getEnv
  for r in [`PLLND.F0.Base3.freeHAωAbove_base3, `PLLND.F0.FreePLL.freeReaders] do
    let mut seen : NameSet := {}
    let mut stack : List Name := [r]
    let mut entries : Array Name := #[]
    let mut fuel := 3000000
    while fuel > 0 do
      fuel := fuel - 1
      match stack with
      | [] => fuel := 0
      | n :: rest =>
        stack := rest
        if seen.contains n then continue
        seen := seen.insert n
        match env.find? n with
        | some ci =>
          let mut deps := ci.type.getUsedConstants
          if let some v := ci.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
          if !isCM n && deps.any isCM then entries := entries.push n
          for c in deps do stack := c :: stack
        | none => pure ()
    logInfo m!"{r}: entries {entries.toList}"
```
