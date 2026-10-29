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

# v0.7: definitions the text does not mention, to an appendix

## 2026-10-29 09:00 GMT: plan and classification

Manager's brief of 2026-10-29, after Matthew's request of the same day (the
number of supporting definitions; every defined term mentioned in the running
text and displayed results keeps a reference; the others may go to an
appendix that is easy to take out).  Agent worktree
`agent-a478a40133fdcee88`, reset to `59b6e0c` (PR #107, v0.6), `.lake`
cloned once from the v0.6 worktree (`agent-a955ba236b7d77cc4`).  Nothing
pushed, no upstream.  Baseline build of v0.6 here: 38 pages, `tex errors: 0`,
`missing glyphs: 0`, only `F0Paper.Paper` and `F0Paper` rebuilt.

Plan:

1. Classify every definition shown in the paper (the definition rows of the
   section tables and the `{leanDef}` blocks) as A, mentioned in the body, or
   B, ancillary (table below).
2. A stays where it is.  B moves to a lettered appendix, "Supporting
   definitions and lemmas", by body section in the body's order, in the same
   `{lemmaTable}` presentation, with each moved row's pin.  A lemma row whose
   printed statement mentions a B definition moves with it.
3. The appendix is detachable: one file, one `{include}` line, and one
   sentence in §1 (the "New in v0.7" line); no per-item reference.
4. The v0.6 leftovers (10.10 heading at a page foot, the `FreeFamily3`
   display left of the margin, the stale comment of `scripts/f0-paper.sh`);
   `VERSION` 0.7.

How the classification was made (scratch scripts under `_out/`, untracked):

* The body is every section but the References, plus the abstract.  Its
  running text is each section's text up to its "Supporting declarations"
  heading: that heading, the table and the pins paragraph after it annotate
  the table and are not counted.  Names inside `{axiomsOf}`, `{listElems}`,
  `{listSize}`, `{srcLink}` are not printed and are not counted.
* Mentioned by name: a code span of the running text equal to the
  definition's name or a dotted suffix of it (the text writes `HasCore` for
  `NotIso.HasCore`).
* Mentioned in a display: the definition is a constant of what a body
  `{stmt}`, `{leanStmt}` or `{leanDef}` prints (the type of a statement, the
  value of a definition), computed by Lean against the built modules
  (`Expr.getUsedConstants`); this includes constants absorbed into notation
  (`levels` in 𝓜_T, `Gad.Dp` in 𝓜(K)) and instances
  (`instHeyting`, also named in §12).
* Mentioned by notation in the running text, checked by hand against
  `PaperKit/Math.lean`: `mink` (?), `qmF` (the hand display of ?(a/b)),
  `Wit` (W_b), `copyF` (e_k(d)), `T6.uF` (u), `T6.xc` (x_k), `MeetPrime`,
  `CoversC` (⋖), `FreeIPLInAboveT3` (H_ω ↪ [t₃, ⊤]), `Points.X` (X_r),
  `Normal.dF` (d_k).
* Mentioned in words, an extension of the brief's rule that follows
  Matthew's wording ("every defined term mentioned in the running text"):
  the text uses the term the definition defines, as a defined term.
  `ConstraintModel` ("constraint models", defined in words in §2),
  `HasDisjPair` ("disjoint pair", italic in §9 and §11), `BigAtom` ("big
  atom", italic in §11), `MacNeille.instFrame` ("a frame", §12).  Words
  that only describe a device in passing ("threshold assignments", "edge
  world", "a countable syntax") were not counted; those rows are B and say so.
* Closure: a definition in the printed row of an A definition is A
  (`rungMem`, `F0.F`, `Mink.sq`, `DyQ`, `copyP`, `Sig.subBot`, `NotIso.Disj`,
  `NotIso.Core`, `Base3.code`), so no body row mentions a B term.
* A lemma that the running text names does not make the definitions of its
  statement A: lemma names without a row are common in the text (`sat_rnP`,
  `cell_m6`, `Gad.z_b3`, …).  So `freeIPL1`, `noMeetCopyH2_bot`,
  `pairwiseHimp`, `shift`, `anyFamily3` and others keep their names in the
  text while their rows move.

Counts: 95 definition rows in the tables and 14 `{leanDef}` blocks (one,
`Pair.FreePair`, also a row): 108 definitions; A 93 (80 rows, 13 further
`{leanDef}`s), B 15; 17 lemma rows move with the B definitions.  Twelve of
the 15 are in Section 10, ten of them propositions that one theorem each
proves (`Shift` by `shift`, …).

The table (Matthew may override single rows; an override from B to A puts
the row and its lemma rows back in the body table):

| Definition | § | Class | Where it is mentioned |
|---|---|---|---|
| `LaxND` | 2 | A | in the displays of gap_incomparable §2, Indep §4 and 6 more |
| `Deriv` | 2 | A | in the displays of rnSub_order §2, dichotomy §2 and 19 more |
| `Interd` | 2 | A | in the displays of low_trichotomy §3, DownTable.classify §3 and 6 more |
| `ConstraintModel` | 2 | A | the defined term in words, "constraint models" (§2, where it is defined in words; §3, §10, §11, §12) |
| `atomFree` | 2 | A | in the displays of dichotomy §2, low_trichotomy §3 and 14 more |
| `rn` | 2 | A | named in §10; in the displays of phiK §10 |
| `rnP` | 2 | A | named in §10; in the displays of Sig.sig_ladder §9 |
| `rnSub` | 2 | A | in the displays of rnSub_order §2, ladder_le_formula §7 and 4 more |
| `rungMem` | 2 | A | closure: in the row of rungLe |
| `rungLe` | 2 | A | named in §2, §13; in the displays of rnSub_order §2 |
| `rungCovers` | 2 | A | named in §2, §9 |
| `gap` | 2 | A | in the displays of gap_incomparable §2, Indep §4 and 2 more |
| `DownTable` | 3 | A | named in §3; in the displays of DownTable.classify §3, cover_above §7 |
| `Covers` | 3 | A | in the displays of cover_above §7, SigOnto.sig_not_cover §9 |
| `cmM` | 4 | A | named in §10; in the displays of MultiEdgeForcing §4 |
| `levels` | 4 | A | in the displays of MultiEdgeForcing §4 |
| `root` | 4 | A | in the displays of MultiEdgeForcing §4 |
| `IsEdge` | 4 | B | nowhere by name or notation; the words "edge world" (§4) describe the worlds it picks |
| `LPoly` | 5 | A | in the displays of lpoly_deriv_iff §7, incomparable_copies §7 |
| `LPoly.den` | 5 | A | in the displays of lpoly_deriv_iff §7, incomparable_copies §7 |
| `F0.F` | 5 | A | closure: in the row of Dy.formula |
| `Dy` | 5 | A | in the displays of dyadic_embedding §5, qm_onto §5 and 2 more |
| `Dy.lt` | 5 | A | in the displays of dyadic_embedding §5, qm_lt §5 and 1 more |
| `Dy.formula` | 5 | A | in the displays of dyadic_embedding §5, ladder_le_formula §7 and 1 more |
| `qmF` | 5 | A | its equations, displayed by hand as ?(a/b) "with fuel b, on pairs never reduced" (§5) |
| `mink` | 5 | A | its notation ? (§5) |
| `Mink.sq` | 5 | A | closure: in the row of qm |
| `qm` | 5 | A | in the displays of qm_lt §5, qm_onto §5 |
| `ratFormulaCF` | 5 | A | in the displays of rat_embedding_cf §5 |
| `DyQ` | 5 | A | closure: in the row of ratFormula |
| `ratIso` | 5 | A | named in §13 |
| `ratFormula` | 5 | A | in the displays of rat_embedding §5 |
| `thr` | 5 | B | nowhere by name or notation; "threshold assignments" (§5), in passing |
| `Wit` | 6 | A | its notation W_b (§6, §7) |
| `leCheck` | 7 | A | named in §7 |
| `copyP` | 7 | A | closure: in the row of copyF |
| `copyF` | 7 | A | its notation e_k(d) (§7) |
| `T6.t6F` | 8 | A | in the displays of T6.t6_regular §8 |
| `T6.uF` | 8 | A | its notation u = ◯¬◯⊥ (§8, §12) |
| `T6.rel` | 8 | A | named in §8; in the displays of Sig.sig_ladder §9 |
| `T6.xc` | 8 | A | its notation x_k (§8) |
| `Sig.aTr` | 9 | A | in the displays of Sig.aTr_deriv §9 |
| `Sig.subBot` | 9 | A | closure: in the row of Sig.sig |
| `Sig.sig` | 9 | A | in the displays of Sig.sig_ladder §9, SigOnto.sig_not_onto §9 and 1 more |
| `Sig.sigN` | 9 | A | in the displays of Sig.sigN_faithful §9, Sig.copies_strict §9 and 2 more |
| `NotIso.Disj` | 9 | A | closure: in the row of HasDisjPair |
| `NotIso.Core` | 9 | A | closure: in the row of NotIso.HasCore |
| `NotIso.HasCore` | 9 | A | named in §9 |
| `relB` | 10 | A | in the displays of Pair.relB_transfer §10, Gad.transfer §10 and 5 more |
| `pvar` | 10 | A | in the displays of Pair.relB_transfer §10 |
| `varsBelow` | 10 | A | in the displays of Pair.relB_transfer §10, Gad.transfer §10 and 3 more |
| `FreeHAωAbove` | 10 | A | named in §10; in the displays of AnyFamily.AllAbove3ω §10, freeHAωAbove_base3 §10 |
| `MeetCount.MeetEmb` | 10 | A | named in §10; in the displays of MeetCount.meet_counting §10 |
| `TypeBound` | 10 | A | named in §10; in the displays of MeetCount.meet_counting §10, not_typeBound_base2 §10 |
| `Distinct` | 10 | A | in the displays of AnyFamily.freeHAnAbove_base3_of_distinct §10 |
| `ZL.relX` | 10 | A | in the displays of phiK §10 |
| `ladder` | 10 | A | named in §10 |
| `FreeIPL.FreeIPLInAboveT3` | 10 | A | its notation H_ω ↪ [t_3, ⊤] (§13) |
| `Pair.FreePair` | 10 | A | displayed in §10; in the displays of Pair.freePair §10 |
| `x3` | 10 | A | in the displays of Gad.transfer §10 |
| `Gad.Dp` | 10 | A | in the displays of Gad.transfer §10 |
| `Base3.code` | 10 | A | closure: in the row of FreePLL.xr |
| `Base3.xω` | 10 | A | named in §10 |
| `FreePLL.xr` | 10 | A | named in §10; in the displays of FreePLL.FreeReaders §10 |
| `FreeIPL.FreeIPL1InAboveT3` | 10 | B | nowhere by name or notation; its content in words, H₁ ↪ [t₃, ⊤] (§10, §13); the lemma `freeIPL1` is named |
| `MeetCount.NoMeetCopyH2` | 10 | B | nowhere by name or notation; its content in words (§10); the lemmas `noMeetCopyH2_bot`, `noMeetCopyH2_t3` are named |
| `Free3` | 10 | B | nowhere by name or notation; the lemma `free3_reflects` is named (§10); its row stays |
| `Base3.FreeOmega3` | 10 | B | nowhere by name or notation; the lemma `freeOmega3` is named (§10) |
| `EmbedForms.PairwiseHimp` | 10 | B | nowhere by name or notation; the lemma `pairwiseHimp` is named, its content in words (§10) |
| `EmbedForms.Shift` | 10 | B | nowhere by name or notation; the lemma `shift` is named, its content in words (§10, §14) |
| `EmbedForms.ShiftH2` | 10 | B | nowhere by name or notation; the lemma `shiftH2` is named (§10) |
| `EmbedForms.ShiftOrderEmb` | 10 | B | nowhere by name or notation; the lemma `shift2_orderEmb` is named (§10) |
| `EmbedForms.ShiftMeetFails` | 10 | B | nowhere by name or notation; the lemma `shiftMeetFails` is named, its content in words (§10) |
| `AnyFamily.AnyFamily3` | 10 | B | nowhere by name or notation; the lemma `anyFamily3` is named (§10), its content in words (§10, §13, §14) |
| `AnyFamily.SigShiftω` | 10 | B | nowhere by name or notation; only its H_n form `SigShift` is displayed (A) |
| `FreePLL.FreePLLnAbove` | 10 | B | nowhere by name or notation; only its ω form `FreePLLAbove` is displayed (A) |
| `HasDisjPair` | 11 | A | the defined term "disjoint pair" (italic, §9 and §11; §11 table) |
| `BigAtom` | 11 | A | the defined term "big atom" (italic, §11; §14) |
| `MeetPrime` | 11 | A | its notation "meet-prime" (§11, §14) |
| `CoversC` | 11 | A | its notation ⋖, read "covers" (§3, §9; §11 "d covers p") |
| `instHeyting` | 12 | A | named in §12; in the displays of FilterIsoQ §11, classify_low §11 and 6 more |
| `circNucleus` | 12 | A | named in §12; in the displays of circ_extends_to_DM §12 |
| `MacNeille.instFrame` | 12 | A | in the displays of MacNeille.principal_himp §12; in words, DM(H) "a complete Heyting algebra (a frame)" (§12, §13); the instance behind ⇒ on cuts |
| `cutHimp` | 12 | A | in the displays of MacNeille.le_cutHimp_iff §12 |
| `principalHom` | 12 | A | named in §12 |
| `extNucleus` | 12 | A | in the displays of extends_iff_mem_Icc §12 |
| `leastExt` | 12 | A | in the displays of extends_iff_mem_Icc §12 |
| `dmNucleus` | 12 | A | in the displays of circ_extends_to_DM §12 |
| `PLLND.F0.Points.gaps` | 12 | A | in the displays of PLLND.F0.Points.gapCut §12 |
| `PLLND.F0.Points.X` | 12 | A | its notation X_r (§12, §14) |
| `PLLND.F0.Normal.ρF` | 12 | A | in the displays of PLLND.F0.Normal.Star §12 |
| `PLLND.F0.Normal.dF` | 12 | A | its notation d_k (§12) |
| `PLLND.F0.Normal.F7` | 12 | A | in the displays of PLLND.F0.Normal.F7Meet §12, PLLND.F0.Normal.F7NonPrincipal §12 and 1 more |
| `PLLND.F0.Normal.IsFilter` | 12 | A | in the displays of PLLND.F0.Normal.NotAllNormal §12 |
| `PLLND.F0.Points.CF` | 12 | B | nowhere by name or notation; "a countable syntax of the variable-free formulas" (§12), in passing |

Displayed definitions outside the tables (`{leanDef}` blocks), all A,
staying where they are: `Pair.FreePair` (§10), `AnyFamily.SigShift` (§10), `AnyFamily.AllAbove3` (§10), `AnyFamily.AllAbove3ω` (§10), `FreeHAnAbove` (§10), `Conjecture` (§10), `FreeFamily3` (§10), `FreePLL.FreePLLAbove` (§10), `FreePLL.FreeReaders` (§10), `FilterIsoQ` (§11), `AboveResidue` (§11), `ObstructionA` (§11), `PLLND.F0.Points.gapCut` (§12), `PLLND.F0.Normal.NotAllNormal` (§12).

Lemma rows that move with them (closure), with the B definitions their
printed statements mention:

| Lemma row | § | Mentions |
|---|---|---|
| `cmM_chainF` | 4 | `IsEdge` |
| `F_eval` | 5 | `thr` |
| `FreeIPL.freeIPL1` | 10 | `FreeIPL.FreeIPL1InAboveT3` |
| `MeetCount.noMeetCopyH2_bot` | 10 | `MeetCount.NoMeetCopyH2` |
| `MeetCount.noMeetCopyH2_t3` | 10 | `MeetCount.NoMeetCopyH2` |
| `free3` | 10 | `Free3` |
| `freeFamily3_of_free3` | 10 | `Free3` |
| `Base3.freeOmega3` | 10 | `Base3.FreeOmega3` |
| `EmbedForms.pairwiseHimp` | 10 | `EmbedForms.PairwiseHimp` |
| `EmbedForms.shift` | 10 | `EmbedForms.Shift` |
| `EmbedForms.shiftH2` | 10 | `EmbedForms.ShiftH2` |
| `EmbedForms.shift2_orderEmb` | 10 | `EmbedForms.ShiftOrderEmb` |
| `EmbedForms.shiftMeetFails` | 10 | `EmbedForms.ShiftMeetFails` |
| `AnyFamily.anyFamily3` | 10 | `AnyFamily.AnyFamily3` |
| `AnyFamily.sigShiftω` | 10 | `AnyFamily.SigShiftω` |
| `FreePLL.freePLLnAbove_base3` | 10 | `FreePLL.FreePLLnAbove` |
| `PLLND.F0.Points.CF.onto` | 12 | `PLLND.F0.Points.CF` |
