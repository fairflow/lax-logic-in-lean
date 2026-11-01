# `wip/f0InsideOut.lean` — status

The nesting `F0 ⊋ σ(F0) ⊋ σ²(F0) ⊋ ⋯ ⊋ σ^ω(F0)` turned inside out in ZF by
well-founded recursion along `<` on `WithTop ℕ` (Matthew, 2026-11-01; an
experiment, `Classical.choice` permitted in this module).  Branch
`f0-inside-out`, local only.

## Stage 1 (2026-11-01 10:15 GMT): statements committed, no proofs

Definitions: `tag`, `Dstep`, `D` (by `WellFounded.fix`), `single`, `D1`,
`inSig`, `inLim`, `inLevel`, `shell`, `natsCode`, `strCode`, `code`,
`classCode`, `Colouring`, `colLab`, `bagSet`, `bagLab`, `threadLab`,
`thread`, `thrLab`, `lab`, `DF`, the example colouring `rb` (red/blue), and
the cell predicates `IsColour`, `InBag`.

Deviation from the brief, recorded: the generic `D` takes a family of labels
`lab k i` at tag `k + 1`,

    D lab i = range (j < i ↦ (tag 0, D lab j)) ∪ ⋃ₖ {tag (k+1)} × lab k i,

so that colours (tag 1), bags (tag 2) and thread limits (tag 3) are all
direct members of `D i`, as in the brief's description of `D(n)`.  The
brief's single-label form is `D1 lab = D (single lab)`, with its own
unfolding equation (`Stmt.D1Unfold`).  `mem_label_iff` is stated for every
tag `k + 1`.

Statements (all `Prop` definitions in `PLLND.F0.InsideOut.Stmt`, all OPEN at
this stage): `DUnfold`, `D1Unfold`, `MemDIff`, `DInjective`, `MemOrderIff`,
`MemLabelIff`, `MemTop`, `CodeInjective`, `ClassCodeEqIff`, `ColourIff`,
`BagIff`, `Readback`, `ThreadLimitInjective`, `ThreadLimitIff`,
`ThreadReadback`, `ThreadsOnlyAtTop`, `ShellShift`, `LimEqTop`,
`OrbitOrderLimit`, `OrbitsVsL0`; designed cells `CellSig2Colour`,
`CellTopColour`, `CellSig2Red`, `CtrlBot`, `CellThreadsDiffer`,
`CellThreadShift`, `CellThreadReadback`.

The only proofs in the stage-1 file are the side conditions of the
structure instance `rb` (`tag_succ_ne_zero`, `rbCode_inj`, `rbS_inv`,
`rbBase_af`), pinned `[propext, Quot.sound]`.

Check: `gtimeout 600 lake env lean wip/f0InsideOut.lean`, exit 0, 12 s.
`lake build --no-build wip.f0InsideOut`: exit 3, the only out-of-date target
is `wip.f0InsideOut` itself (0 Mathlib modules to compile).
