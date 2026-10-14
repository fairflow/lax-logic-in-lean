# The PLL amalgamation lemma: proved at level 4ν + 2

*2026-10-14. Branch `semui-amalg-push`. Claims are marked PROVED (kernel-checked,
`sorry`-free, axioms pinned in-file), REFUTED (kernel-checked countermodel) or
OPEN. Anything computed by the Python tool is evidence and is labelled so.*

## 0. Status

| statement | status | where |
|---|---|---|
| amalgamation from an escape-form link at level `4·ν + 2` | **PROVED** `[propext, Classical.choice, Quot.sound]` | `LayeredAmalg.amalgamationE` |
| the same from the strong link `LayeredBisim (· ≠ p)` | **PROVED**, corollary | `LayeredAmalg.amalgamation_strong` |
| amalgamation at level `2·ν + 1`, as `SemUILayered.amalgamation` states it | **OPEN**; survived the refutation stage of §2 | still a `sorry` at `SemUILayered.lean:821` |
| a link in the escape form follows from agreement on formulas | **REFUTED** (already, 2026-07) | `pair_escape_not_from_agreement` |
| uniform interpolation for PLL | **OPEN** | §5, §6 |

The lemma that the route's own docstring calls its central open problem is
proved, with a larger budget than the one written down. It does not by itself
give uniform interpolation: the step before it in the route is refuted in the
form this lemma consumes (§5). A way round that is proposed in §6 and is not
built.

New files: `LaxLogic/PLL/SemUI/SemUILayeredAmalg.lean` (663 lines, 73
declarations, none sorried) and `scripts/semui_fibres.py`.

## 1. The statement

With `nu X` the number of variables, implications and `◯`-formulas in `X`:

    theorem amalgamationE (X : Finset PLLFormula) (hX : SubClosed X)
        (p : String) (K M : ConstraintModel) (k₀ : K.W) (m₀ : M.W)
        (A : String → Prop) (hA : ∀ a, a ≠ p → PLLFormula.prop a ∈ X → A a)
        (B : LayeredBisimE A K M)
        (hB : B.Z (4 * nu X + 2) k₀ m₀) :
        ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
          C.Z m₀ n₀ ∧ ∀ φ ∈ X, (N.force n₀ φ ↔ K.force k₀ φ)

Three differences from `SemUILayered.amalgamation`:

* the level is `4·ν + 2`, not `2·ν + 1`;
* the link is the escape form `LayeredBisimE`, a weaker hypothesis than the
  strong `LayeredBisim`, so this is the stronger theorem on that axis;
* the link need protect only the atoms of `X` other than `p`. The output is
  still a `p`-variant of `M` for the whole alphabet, because the amalgam reads
  every other atom from `M`. This is the form the route needs: `K` comes from
  completeness and knows nothing of `M`'s other atoms.

## 2. The refutation stage

Before any proof, the statement at `2·ν + 1` was tested on designed cells
(`METHOD.md`, rule 9). The tool is `scripts/semui_fibres.py`; it decides the
lemma exactly on finite poset models.

**What it computes.** For a finite `M`, the *fibre* of a world `m` is the set of
`V ⊆ X` that are the `X`-theory of some `p`-variant point over `m`. It is the
`V`-projection of the greatest set of pairs (type, world) closed under eight
local conditions, a type being `(V, P)` with `P` the bodies `ξ` of
`◯ξ ∈ X` that no `Rₘ`-successor forces. Both inclusions are argued in the
script's header. A `p`-variant of `K` is still linked to `M`, so the lemma at
level `L` is equivalent to

    k₀ and m₀ linked at level ≥ L   ⟹   fibre(k₀) = fibre(m₀),

and the tool reports, per model, `L*` = 1 + the highest link level between two
worlds with different fibres. The lemma as stated needs `L* ≤ 2ν + 1`.

**Results** (`python3 scripts/semui_fibres.py all`, 11 s):

| family | closures × models | worst `L*` | `2ν+1` ranges over |
|---|---|---|---|
| alternating chains, fallible witnesses | 9 × 1 | 0 | 7 to 13 |
| alternating chains, `q`-witnesses (the shape of the old obstruction) | 8 × 4 | 2 | 11 to 15 |
| Rieger–Nishimura ladders over `q`, six `Rₘ` patterns × three fallibility options | 10 × 18 | 3 | 7 to 15 |

No violation. The margin is the finding: on these families the realisable
types are fixed by the first three levels of the link.

**The tool's own gates.** It reproduces 18 quantifier values that are theorems
of the library or were derived by hand, on 15 small models: 702 world-cells, 0
mismatches. Every world's own type is asserted to lie in the fixpoint, and
bisimilar worlds are asserted to have equal fibres. With the budget forced down
to 1 the same cells are flagged as violations (watched). A first family of
"deep chains" turned out to be fully bisimilar and so tested nothing; it was
dropped.

## 3. The proof

**Where the earlier attempt stopped.** The witnessing-triple construction
(`wip/semui_henkin.lean`) pairs a canonical theory with a world of `M` under two
links, at levels `2d+1` and `2d`, `d` the depth of the theory. It stopped at the
forward `◯`-case: a world `k` refuting `◯ξ` has a successor `v` none of whose
`Rₘ`-successors forces `ξ`, and when `v` forces the same closure formulas as
`k` the depth does not drop, so nothing pays for the move. In iSL the case does
not arise, because the refuter is chosen `⊏`-maximal, which needs the Löb
structure.

**Two observations.**

1. *Only `X`-rigid refuters are needed.* Call `z` `X`-rigid when every
   `Rₘ`-successor of `z` forces exactly the `X`-formulas `z` forces. Every world
   has an `X`-rigid `Rₘ`-successor (`exists_rigid`: along `Rₘ` the set of forced
   `X`-formulas only grows, and `X` is finite). Being blocked for `ξ` is
   inherited along `Rₘ`, so the refuter can always be taken `X`-rigid. At an
   `X`-rigid world `◯ξ` and `ξ` have the same truth value, so a rigid world
   refutes in place every `◯ξ` it does not force. The alternation of promises
   along an `Rᵢ`-chain, which no finite budget pays for, never has to be
   reproduced.

2. *A rigid pair is its own reservoir for `Rₘ`.* The amalgam has two kinds of
   world over a point `m` of `M` (plus a certificate-free kind over fallible
   points):

   | kind | certificate | levels (`d` = depth) |
   |---|---|---|
   | normal | reservoir `k′ Z m′` below; current `k Z m`; `k′`, `k` force the same `X`-formulas | `4d+2`, `4d+1` |
   | rigid | the same reservoir; `z₀` `X`-rigid with `z₀ Z m₀`; current `z Z m` with `z₀ Rₘ z`, `m₀ Rₘ m` | `4d+2`, `4d`, `4d−1` |

   An `Rₘ`-move of `M` out of `m` is an `Rₘ`-move out of `m₀` by transitivity,
   so it is answered from `(z₀, m₀)` and lands on a rigid world with the same
   certificate: no decay. The amalgam's `Rₘ` out of a rigid world reaches only
   rigid worlds with the same theory, which is what makes it block.

**The level arithmetic.** Each move spends one level; a strict move lands at
depth `≤ d − 1`, where a fresh world needs `4(d−1) + 2 = 4d − 2`.

| move | from | lands at | needed |
|---|---|---|---|
| `M` moves (`Rᵢ` or `Rₘ`), answered from the reservoir | `4d+2` | `4d+1` | `4d+1` (same theory), `4d−2` (strict) |
| `K` moves strictly from a normal current | `4d+1` | `4d` | `4d−2` |
| hop to a rigid refuter | `4d+1` | `4d` | `4d` |
| `M` moves along `Rₘ` from a rigid world, answered from `(z₀, m₀)` | `4d` | `4d−1` | `4d−1` |
| `K` moves strictly from a rigid current | `4d−1` | `4d−2` | `4d−2` |

The last row is tight. The two rows involving the rigid pair are what the `2d+1`
budget has no room for.

**A check made before writing Lean.** The proof uses only types with `P = ∅`
(normal) and `P` = everything blockable (rigid). Restricting the fixpoint of §2
to those two kinds changes no fibre: 23 closures × 23 models, 8,602 world-cells,
0 differences (`semui_fibres.py types`). Evidence, and it is what made the
construction worth writing down.

**Checked.** `lake build LaxLogic.PLL.SemUI.SemUILayeredAmalg` on `main` at
`04fd908`, exit 0. In-file pins: `exists_rigid`, `amal_force`, `amalgamationE`,
`amalgamation_strong`, all `[propext, Classical.choice, Quot.sound]`. The gate
was watched failing on a planted false theorem and a wrong pin. Ledger: 73 new
rows, none `sorryAx`, none `native_decide`; totals unchanged at 23 and 2.

## 4. What is not proved

**The level `2·ν + 1`.** OPEN. The method above cannot reach it: the hop to the
rigid pair and the derivation of its current link each cost a level per unit of
depth. The cells of §2 give no reason to doubt the sharper statement. Nothing
downstream uses the constant; the route needs only that some computable level
works.

**The `sorry` in the library.** `SemUILayered.amalgamation` is unchanged and
still sorried. No proof term uses it. Turning it into a `Prop` (rule 1) means
editing `SemUILayered.lean`, which is upstream of the LJF build, so it is left
for a decision.

**`wip/semui_henkin.lean`.** Its two open claims, `wit_pbisim` and `wit_force`,
are still sorried there. Pillar 3 no longer depends on them. I am not calling
the file superseded: its budget is `2·|cl| + 1` against `4·ν + 2` here, and
neither bounds the other.

## 5. What this does to the route

The route is: (1) the rank-bounded fragment is finite; (2) agreement on that
fragment gives a layered link; (3) a layered link gives the amalgam.

* (1) PROVED, `frag_reps_exist'`.
* (3) PROVED today, from the escape form.
* (2) is **REFUTED** in the escape form: `forkF` and `oneW` agree on every
  formula and are not linked at level 1 (`pair_escape_not_from_agreement`). The
  weak form that agreement might deliver does not preserve forcing
  (`weak_escape_breaks_force_iff`), so it cannot feed (3).

So the gap in the semantic route is now exactly (2), and it is a mismatch of
notions, not a missing proof: the bisimulations of this development see
`Rₘ`-structure that no formula sees.

*An observation, checked by hand and not in Lean.* The mismatch is not only
about fallible worlds. Take `K` the chain `k < s < u` with `k Rₘ u`, `q` true at
`u` only, and `M` the chain `m < u′` with `Rₘ` trivial, `q` true at `u′`. Then
`k ⊩ ◯ξ ⟺ s ⊩ ξ ∧ u ⊩ ξ ⟺ s ⊩ ◯ξ`, so `k` and `s` force the same formulas, and
`s`, `m` have isomorphic cones; hence `k` and `m` agree on everything. But
`k Rₘ u`, `u` is not fallible, and the only `Rₘ`-successor of `m` is `m`, which
differs from `u` on `q`. So the forth-`Rₘ` clause fails from full agreement at a
non-fallible successor. The 2026-07 probe that found no such failure was
variable-free; I have not reconciled the two.

**Is the fibre a logical invariant?** If realisable types depended on
`Rₘ`-structure that formulas cannot see, no `p`-free formula could meet
`IsSemEx` and `SemExDefinable` would be false as formalised, whatever the truth
about uniform interpolation. On a finite poset, `w ⊩ ◯ξ` iff every rigid
non-fallible world above `w` forces `ξ`; so models on one poset with one set of
rigid worlds force the same formulas whatever their other `Rₘ`-edges. Five such
realisations of each of six rigid sets on a ladder were compared: 660 cells, 0
with a realisation-dependent fibre; a control with two different rigid sets
differs in 11 cells (`semui_fibres.py realisations`). Evidence that the
specification is sound, not a proof.

## 6. A proposal: run the route in a semantics where (2) holds

Not built. Not started: the UI search was halted on 2026-09-06 and this needs
Matthew's word. Recorded because today's proof suggests it.

The remark of §5 is a semantics in its own right. An *S-model* is `(W, ≤, S, V)`
with `≤` a preorder, `S ⊆ W` arbitrary, `V` hereditary, `⊥` never forced, and

    x ⊩ ◯φ   ⟺   ∀ y ≥ x, y ∈ S → y ⊩ φ.

This is the subframe reading of a nucleus (Bezhanishvili–Ghilardi). `◯` is a
universal clause, so:

* **Completeness** should go by the usual canonical model: worlds the prime
  theories, `S` the *reflexive* ones (`◯ψ ∈ Δ ⟹ ψ ∈ Δ`). For `◯ψ ∉ Δ`, a theory
  maximal among those containing `Δ` and omitting `◯ψ` is prime, and it is
  reflexive: if `◯χ ∈ T` and `χ ∉ T` then `T, χ ⊢ ◯ψ`, so `T ⊢ ◯χ → ◯◯ψ`, so
  `◯ψ ∈ T`.
* **(2) holds** by the standard character argument, with no escapes: there are
  no fallible worlds and no `∀∃` clause. The `S`-step costs four ranks, not two.
* **(3)** is today's argument with less in it. An `S`-point of the amalgam is a
  pair of an `S`-point of `M` and a reflexive theory; it refutes in place every
  `◯ξ` it lacks; every move of `M`, including a move to an `S`-point, is answered
  from the reservoir, because there is no monotonicity of promises to respect.
  Three levels per unit of depth.
* The `∀`-side needs the usual gluing of a new root (Visser's push-down lemma).

The uniform interpolation theorem is a statement about derivability, so the
semantics used to prove it is free. What this would cost: S-models, soundness,
completeness, invariance, characters, the port of §3, the gluing lemma and the
assembly. None of it is checked and the sketch may have holes; the two places I
would test first are completeness and the `∀`-side. It would leave
`SemExDefinable`, which quantifies over constraint models and `PBisim`, as a
separate and harder statement.

## 7. Iemhoff's proof: where contraction is used

Read against arXiv:2209.08976v2 (21 August 2026), which now carries an erratum
withdrawing the main theorem.

The uniform interpolation argument (her §6) defines the interpolants by
recursion along a well-founded order on sequents and proves three properties
by induction over derivations. It applies her Theorem 5, quoted from her 2019
paper, whose hypothesis is a **balanced** calculus: reductive, with Cut and
Weakening admissible. G4iLL is reductive (her Fact 2). That Cut is admissible
in it, and that it derives what PLL derives, comes from one place only:
Corollary 1, the equivalence of G3iLL and G4iLL, obtained from a theorem of her
2020 note. Her erratum says that theorem needs G4ip + R to be closed under
contraction and that she does not know whether G4iLL is.

This repository settled that on 2026-07-08 (`LaxLogic/PLL/G4/G4Gap.lean`):
G4iLL does not derive `◯((◯p→r)→◯p), ◯p→r ⇒ r`, which PLL does; with two copies
of `◯p→r` it does. So contraction is **not** admissible and G4iLL is
**incomplete**: the hypothesis fails, and the erratum's open question has a
negative answer.

So contraction-freedom is used once, and the gap is not local. The rule at
fault is `L◯→`, which drops the principal implication from its left premise.
Keeping it restores completeness (`G4c`, PROVED complete with cut and
contraction admissible) and loses the well-founded order, because the left
premise is then no smaller. That trade is the budget problem of the syntactic
route (`docs/ui-endgame.md`). Her interpolant assignment for the four modal
rules may well survive on a repaired calculus; what has to be replaced is the
measure, and that is the part nobody has.

## 8. Reproduce

    lake build LaxLogic.PLL.SemUI.SemUILayeredAmalg
    python3 scripts/semui_fibres.py all        # exit 0; 11 s

Pull `main` (or check out `semui-amalg-push`) first.
