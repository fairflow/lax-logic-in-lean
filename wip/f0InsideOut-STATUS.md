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

## Stages 2 and 3 (2026-11-01 10:30 GMT): cells and proofs

Every statement of stage 1 is PROVED; nothing is OPEN and there is no
`sorry` in the file.  The theorem proving `Stmt.X` has the snake-case
name of `X`.

### Cell verdicts (stage 2, kernel-checked)

| cell | statement | verdict |
|---|---|---|
| `cell_sig2_colour` | σ²⊥ is a colour of D 0, D 1, D 2, not of D 3 | pass (PROVED) |
| `cell_top_colour` | ⊤ is a colour of every D n and of D ⊤ | pass (PROVED) |
| `cell_sig2_red` | σ²⊥ is in the red bag of D 1 and D 2, not of D 3 | pass (PROVED) |
| `ctrl_bot` | negative control: ⊥ is a colour of D 0, NOT of D 1 | pass (PROVED) |
| `cell_threads_differ` | T_⊥(ω) ≠ T_{◯⊥}(ω) | pass (PROVED) |
| `cell_thread_shift` | T_{σ⊥}(0), T_⊥(1) carry the same colour but differ; T_{σ⊥}(ω) ≠ T_⊥(ω) | pass (PROVED) |
| `cell_thread_readback` | (3, T_⊥(ω)), (3, T_{◯⊥}(ω)) ∈ D(ω) of `rb`; (3, T_{σ⊥}(ω)) ∉ D(ω) | pass (PROVED) |

The negative halves: `σ²⊥ ⊣⊢ σ³y` gives `σ³⊥ ⊢ σ³y ⊢ σ²⊥`, against
`sigN_bot_strict 2` (`not_inSig3_sig2`); `σy ⊣⊢ ⊥` gives `t3 = σ⊥ ⊢ σy ⊢ ⊥`,
against `nd_t3_bot`.  The thread cells read off `thread_limit_injective`
with `nd_e_bot`, `nd_t3_bot`, `nd_t3_e`.

Gates watched failing (`_out/gatewatch.lean`, a copy of the module with
corruptions, `lake env lean`, exit 1, four errors as intended):
- the negative control: the proof pattern of the positive colour cells (a
  witness `y` with `σⁿ y ⊣⊢ x` by `Interd.refl`) is rejected at `x = ⊥`,
  `n = 1`; the module pins the error with `#guard_msgs`, and a changed
  expected message (`↑2` for `↑1`) fails;
- three pins narrowed below the actual set fail: `lim_eq_top` at
  `[propext]`, `mem_order_iff` and `orbits_vs_L0` at `[propext, Quot.sound]`.

### Theorems (stage 3)

Generic: `d_unfold`, `d1_unfold`, `mem_D_iff`, `D_injective` (by
foundation: `no_mem3`, no ∈-cycle of length three), `mem_order_iff`,
`mem_label_iff`, `mem_top`.

Instance: `code_injective`, `classCode_eq_iff`, `colour_iff`, `bag_iff`,
`readback`, `thread_limit_injective` (the sketch of the addition: `(0, T_a(0))
∈ T_b(ω)` gives `T_a(0) = T_b(m)`; `m ≥ 1` would put `(0, T_b(0))` in `T_a(0)`,
which has no 0-tagged member; so `m = 0` and the colours agree),
`thread_limit_iff`, `thread_readback`, `threads_only_at_top`.

F0 facts: `shell_shift`; `lim_eq_top` and `orbit_order_limit`, proved
together through `cm_eventually` and the fixpoint lemma `bot_everywhere`
(the truth sets of `σⁿ⊥` on a finite subframe countermodel stabilise at
some `U`; `σⁿ⁺¹⊥ = ◯σⁿ⊥ ∨ (◯σⁿ⊥ ↠ σⁿ⊥)` then forces `U` to be everything);
`orbits_vs_L0` (existence from `orbit_order_limit` at `a = ⊥` and the last
level containing `x`; uniqueness from `sigN_faithful`).

### Classical.choice

Uses it (pins `[propext, Classical.choice, Quot.sound]`): `D`, `D1`, `code`,
`classCode`, `thread`, `DF` and every theorem that unfolds them:
`d_unfold`, `mem_D_iff`, `order_mem`, `not_order_mem_self`, `D_injective`,
`mem_order_iff`, `mem_label_iff`, `mem_top`, `d1_unfold`,
`strCode_injective`, `code_injective`, `mem_classCode`,
`classCode_eq_of_interd`, `interd_of_classCode_eq`, `classCode_eq_iff`,
`mem_colLab`, `colour_iff`, `mem_bagLab`, `bag_iff`, `mem_bagSet`,
`readback`, `mem_thread_label`, `thread_zero_no_order`,
`thread_limit_injective`, `threadLab_congr`, `thread_limit_iff`,
`mem_thrLab_top`, `thread_readback`, `threads_only_at_top`, `isColour_iff`,
`inBag_iff`, all seven cells, and `orbits_vs_L0` (with `exists_last`).
Sources: `ZFSet.range` (`Quotient.out`), `ZFSet.mem_range`,
`ZFSet.mem_prod`; `String.toList` (Lean core v4.31) for `code`; excluded
middle on `inSig` for `exists_last`.

Choice-free: `shell_shift`, `lim_eq_top`, `orbit_order_limit`,
`bot_everywhere`, `cm_eventually`, `stabilise` and the counting lemmas
(`[propext, Quot.sound]`), `inLim_of_deriv` (`[propext]`), the `sigN`
identities (no axioms).  Two edits made them so: `SubframeModel.CF.soundness₁`
in place of `SubframeModel.soundness` (which reaches choice through
`toConstraint_force`), and a Boolean `allBelow` in place of
`List.all_eq_false` (which reaches choice through `not_forall`).

Pins: `#axioms_within` with the actual set reported by `#print axioms`, for
all 83 theorems and six definitions (the stage-1 pins of `rbS_inv` and
`rbBase_af` were upper bounds; they are now `[propext]` and `[]`).

### Commands

| command | exit | wall time |
|---|---|---|
| `gtimeout 600 lake env lean wip/f0InsideOut.lean` (final) | 0 | 13 s |
| `gtimeout 600 lake env lean _out/axprobe.lean` (axiom census: 40 of 83 theorems use choice) | 0 | not timed |
| `gtimeout 600 lake env lean _out/gatewatch.lean` (gates) | 1, as intended | not timed |
| `gtimeout 3600 lake build wip.f0InsideOut` | 0 | 16.7 s (8705 jobs, only `wip.f0InsideOut` built) |

No skips, no caps: no search was run, and every verdict is a kernel-checked
theorem.
