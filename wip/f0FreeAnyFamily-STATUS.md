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
| `AnyFamily3` | — | OPEN (Stage 0) |
| `FromCells3` | — | OPEN (Stage 0) |
| `SigShift`, `SigShiftω` | — | OPEN (Stage 0) |
| `AllAbove3`, `AllAbove3ω` | — | OPEN (Stage 0) |
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

## Log

* 2026-10-28: Stage 0, statements written and built
  (`lake build wip.f0FreeAnyFamily`), committed before any proof.
* 2026-10-28: Stage 1, the designed instance PASSES; gates watched failing.
