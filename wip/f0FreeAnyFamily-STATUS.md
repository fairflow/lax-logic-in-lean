# wip/f0FreeAnyFamily.lean — status

Two follow-ups to `wip/f0FreeBase3.lean` (brief 2026-10-28).  Public order
theory about F0.  Target pins `[propext, Quot.sound]`; no `Classical.choice`,
no `sorry`, no `native_decide`.

## The statements (committed before any proof, METHOD.md §1)

Goal 1, the choice of reader family does not matter:

    AnyFamily3 :  ∀ n,  Distinct σ²⊥ (n + 1)  →  FreeHAnAbove σ³⊥ n

Cleaner variant, the two killers inside the family:

    CellsKill n F :  (∀ i j ≤ n, i ≠ j → (F i).Separated (F j)) ∧
                     (F 0).w ⊮ ◯σ²⊥ ∧ (F 1).w ⊩ ◯σ²⊥
    FromCells3 :  ∀ n F,  CellsKill n F  →  FreeHAnAbove σ³⊥ n

Goal 2, the σ-shift, for variable-free `b`:

    SigShift   :  ∀ b vf, ∀ k n,  FreeHAnAbove b n  →  FreeHAnAbove (σᵏ b) n
    SigShiftω  :  ∀ b vf, ∀ k,    FreeHAωAbove b    →  FreeHAωAbove (σᵏ b)
    AllAbove3  :  ∀ m ≥ 3, ∀ n,  FreeHAnAbove σᵐ⊥ n
    AllAbove3ω :  ∀ m ≥ 3,       FreeHAωAbove σᵐ⊥

Fragment first (CLAUDE.md rule 8): degenerate, as in `f0FreeBase3` (the
◯-free variable-free fragment is `{⊥, ⊤}`).

## Status table

| statement | theorem | status |
|-----------|---------|--------|
| **`AnyFamily3`** | `anyFamily3` | **PROVED** |
| `Distinct σ²⊥ (n + 1) → FreeHAnAbove σ³⊥ n` | `freeHAnAbove_base3_of_distinct` | **PROVED** |
| check: `∀ n, FreeHAnAbove σ³⊥ n` again, via `base2_unbounded` | `freeHAnAbove_base3'` | PROVED |
| **`FromCells3`** | `fromCells3` | **PROVED** |
| **`SigShift`**, **`SigShiftω`** | `sigShift` (`freeHAnAbove_sigN`), `sigShiftω` (`freeHAωAbove_sigN`) | **PROVED** |
| **`AllAbove3`**, **`AllAbove3ω`** | `allAbove3` (`freeHAnAbove_base_ge3`), `allAbove3ω` (`freeHAωAbove_base_ge3`) | **PROVED** |
| `σᵏ (relB b x A) = relB (σᵏ b) (σᵏ ∘ x) A`, every `A` | `sigN_relB` (via `sig_relB`) | PROVED |
| `σᵃ (σᵇ φ) = σᵇ⁺ᵃ φ`; `σᵏ (σᵐ⊥) = σᵐ⁺ᵏ⊥` | `sigN_sigN`, `sigN_base` | PROVED |
| `relB b x A` variable-free for variable-free `b`, `x` | `relB_vf` | PROVED |
| every world above a cell's `σ²⊥`-maximal world forces `σ³⊥` | `cone_b3` | PROVED |
| the turn: `w ⊮ φ ⟹ w ⊩ φ ↠ σ²⊥`; `w ⊩ φ ⟹ w ⊮ φ ↠ σ²⊥` | `turn`, `not_turn` | PROVED |
| two-way separation | `orient` | PROVED |
| reader separators (a disjunction) | `disj_sep` | PROVED |
| finite choice of variable-free formulas, choice-free | `choose_vf` | PROVED |
| disjoint sum, summands generated submodels | `Sum`, `sum_force` | PROVED |
| gadget over any `U`: `U` generated submodel, killers, back, readings | `GadU.uforce`, `GadU.w_not_b3`, `GadU.w_back`, `GadU.w_gen0`, `GadU.w_gen_false`, `GadU.w_gen_true` | PROVED |
| the transfer for a family of cells | `transferF` | PROVED |
| a family with separators gives a free copy | `freeHAn_of_seps` | PROVED |
| the non-`S` killer `kn` as a cell; `kn ⊩ ◯σ²⊥`; `ZL 0 ⊮ ◯σ²⊥` | `kNcell`, `kN_box`, `kS_box` | PROVED |
| bounded search, choice-free; the double skip | `bsearch`, `skip2_props` | PROVED |
| `gen = genC sepC` | `gen_eq_genC` | PROVED |
| Stage 1 base facts, two-way turn, control | `baseFacts1_a/b/c`, `twoWay1`, `control_naive` | PROVED (tables) |
| Stage 1 readings | `read1_a/b/c` | PROVED (tables) |
| Stage 1 cells Ca, Cb, Cc, reversed readers | `cell1_Ca`, `cell1_Cb`, `cell1_Cc` | PROVED (countermodels) |

## The design (pen, checked before building on it)

The brief's design, with the changes marked.

1. Two-way separation (brief point 1, verified).  `u`, `v` `σ²⊥`-maximal,
   `u ⊩ φ`, `v ⊮ φ`: then `v ⊩ φ ↠ σ²⊥` (a successor `v'` of `v` forcing
   `φ` and refuting `σ²⊥` lies below `v`, so `v ⊩ φ`) and `u ⊮ φ ↠ σ²⊥`
   (`u ⊩ φ`, `u ⊮ σ²⊥`).  Needs decidable forcing at `v'` (finite cell).
   `Cell.sep_bot`/`Cell.sepimp_bot` of `f0FreeBase3` are the `ZL` instances
   of the two halves, not this lemma.
2. Reader separators (brief point 2, verified): `c_g` = a disjunction with one
   disjunct for each other distinguished world, holding there and failing
   at the reader.
3. Killers (brief point 3, CHANGED).  The S-killer only has to refute
   `◯σ²⊥` (then `w_k ⊮ ◯σ²⊥` by monotonicity; `S`-membership is not
   needed), the non-`S` killer has to force `◯σ²⊥` and refute `σ²⊥`.
   Selection "at most one cell shares each killer's theory" is a case split
   on an undecidable predicate (equal variable-free theories), so it is not
   used.  Instead: each given cell forces `◯σ²⊥` or not (decidable, finite
   cell).  If some given cell refutes `◯σ²⊥`, it is the S-killer, else the
   fixed `ZL 0` bottom is, and then every given cell is separated from it by
   `◯σ²⊥` itself; the same for the non-`S` killer with `kn`.  The readers are
   the given cells less the (at most two) used as killers: `n − 1` of them.
4. Gadget (brief point 4, generalised): over ANY subframe model `U` (in the
   proof the disjoint sum of the cells), copies `w_k` seeing the cones of the
   killers always and the cone of the reader of `p_g` iff `k ⊮ p_g`.

## Stage 1: one designed instance (CLAUDE.md rules 7, 9)

`n = 3`, killers `m₀` (`ZL 0` bottom) and `kn`, readers REVERSED: `p₁` read
by `m₂`, `p₂` by `m₁`.  Separators by the recipe of point 2:

    c₁ = φ₂ ∨ (φ₂ ∨ φ₃),     c₂ = φ₂ ∨ (φ₂ ∨ (φ₃ ↠ σ²⊥))

(`φ₃` holds at `m₁` and fails at `m₂`; for `c₂` it is turned by point 1.)
Upper structure shared as in `f0FreeBase3` Stage 1; tables written by a
script from the description.  Cells `Ca = (p₁ → p₂) ∨ (p₂ → p₁)`,
`Cb = ¬¬p₂ → p₂`, `Cc = (p₀ → p₂) ∨ (p₂ → p₀)` all PASS (images no
theorems), with the base facts and the readings, by `decide +kernel`.

Gates watched failing (scratch file, `lake env lean`):

* `baseFacts1 sepC T1a = true` (`f0FreeBase3`'s separators, reversed
  readers): REJECTED ("is false").
* the reading table with `genC sepC`: REJECTED.
* `#axioms_within cell1_Ca [propext]`: FAIL (Quot.sound).
* in the module: `control_naive`, the base facts with `φ₃` left unturned in
  `c₂`, evaluate to `false`.

## Stage 2: the proofs (PROVED)

Goal 1, in three layers.

1. The gadget over any subframe model `U` (`GadU.MK`): worlds `u a` (`a ∈ U`)
   and copies `w k` (`k ∈ K`); `w k ≤ u b` iff `vis k b`, an up-set of `U`
   antitone in `k`; `w k ∈ S` iff `S0 k`, a down-set; `U`'s valuation on `U`,
   none on the copies (the cells may carry atoms; forcing of variable-free
   formulas ignores them).  `U` is a generated submodel (`GadU.uforce`, by
   `force_pmorph`).  Lemmas with the facts about `U` as hypotheses:
   `w_not_b3` (a visible `dS ⊮ ◯σ²⊥` and a visible `dN ⊩ ◯σ²⊥`, `dN ⊮ σ²⊥`),
   `w_back`, `w_gen0`, `w_gen_false`, `w_gen_true`.
2. A family `F` of cells (`transferF`, `freeHAn_of_seps`): `U` = the
   disjoint sum (`Sum`, `sum_force`), `d r = (r, w_r)`, `w k` sees the cones
   of `d 0`, `d 1` always and of `d (g+1)` iff `k ⊮ p_g` (`1 ≤ g < n`).
   Separators `c_g` with `F (g+1) ⊮ c_g` and `F j ⊩ c_g` for the other
   `j ≤ n` give the readings and, by `relB_transfer` of `f0FreePair`,
   `w_k ⊩ relB σ³⊥ (xC c) A ⟺ k ⊩ A`; then `completeness_imp` as in
   `free3_reflects`.  `fromCells3`: the separators from `disj_sep` (one
   disjunct per other cell, `orient`) and `choose_vf`.
3. `anyFamily3`: the given cells `cs 0 … cs n`, then `ZL.cell 0` at `n + 1`
   and `kNcell` at `n + 2` (`ext`).  `bsearch` finds a given cell refuting
   `◯σ²⊥` or shows every given cell forces it (then the `S`-killer is
   `ZL.cell 0`, separated from each given cell by `◯σ²⊥`); likewise for the
   non-`S` killer with `kNcell`.  `skip2_props` gives an injection `σ`
   avoiding the two killer indices with `σ r ≤ r + 2`, so the readers
   `σ 0 … σ (n-2)` are given cells.  `famK`, `famK_sep` assemble `CellsKill`.

Goal 2: `sigN_relB` by induction on `A` (`sig_relB`) and then on `k`;
`freeHAnAbove_sigN`: `x' a = σᵏ (x a)`, `sigN_vf`, `sigN_mono`, and
`[A] ⊢ B ⟺ [relB b x A] ⊢ relB b x B ⟺ [σᵏ relB b x A] ⊢ σᵏ relB b x B`
(`sigN_faithful`, `relB_vf`) `= [relB (σᵏ b) x' A] ⊢ relB (σᵏ b) x' B`.  The
same without `varsBelow` for `FreeHAωAbove`.  `sigN_sigN`
(`σᵃ (σᵇ φ) = σᵇ⁺ᵃ φ`, via `sig_sigN`) gives `sigN_base`; with
`freeHAnAbove_base3` and `freeHAωAbove_base3` of `f0FreeBase3`,
`allAbove3` and `allAbove3ω`.

Reused from `f0FreeBase3`/`f0FreePair`: `force_pmorph`, `relB_transfer`,
`relB_preserves`, `idx_pvar`, `Cell.bot_S`, `Ca`, `Cb`, `Cc`.  Not reused:
`Base3.Gad`, which hard-wires the cells `ZL r`; `GadU` replaces it.

## Gates (watched failing, 2026-10-28, scratch files, `lake env lean`)

Stage 2:

* `#axioms_within anyFamily3 [propext]`: FAIL (Quot.sound);
  `#axioms_within allAbove3 []`: FAIL (propext, Quot.sound);
  `#axioms_within fromCells3 [Quot.sound]`: FAIL (propext).
* `bmaxB TkN 3 = true` (world `f`): REJECTED ("is false").
* `kn`'s table with the bottom put back into `S`: `◯σ²⊥` at the bottom
  REJECTED.  Controls `bmaxB TkN 4`, `TkN.forceB 4 ◯σ²⊥`: pass.
* `freeHAnAbove_base3_of_distinct n (base2_unbounded n)` (one cell short):
  type error.  Control `freeHAnAbove_base3' n`: passes.

## Skips and caps

None.  No producer runs.  Builds: `lake build wip.f0FreeAnyFamily` only
(three times: Stage 0, Stage 1, Stage 2); `lake env lean` on scratch files
(drafts and gate files).  The Stage 1 tables were written by a script from
the description in the module (transitivity asserted there, and `okB` checks
them in the kernel).

## Log

* 2026-10-28: Stage 0, statements written and built
  (`lake build wip.f0FreeAnyFamily`), committed before any proof.
* 2026-10-28: Stage 1, the designed instance PASSES; gates watched failing.
* 2026-10-28: Stage 2, all six statements PROVED (`lake build
  wip.f0FreeAnyFamily` clean, every pin `[propext, Quot.sound]`); gates
  watched failing.
