# wip/f0FreeHAn.lean — status

Free Heyting algebras on `n` generators inside the filters `[σᵐ⊥, ⊤]` of F0,
and the counting criterion (Matthew, 2026-10-27; follow-up to
`wip/f0FreeIPL.lean`, PR #97).  Public order theory about F0.  Pins
`[propext, Quot.sound]` throughout; no `Classical.choice`, no `sorry`, no
`native_decide`.

## A. Statements (`def … : Prop`, committed before any proof)

    relB b x A       = A[a := x a, ⊥ := b]
    FreeHAnAbove b n = ∃ x ≥ b vf, ∀ A B ◯-free in p0 … p(n-1),
                         [A] ⊢ B ⟺ [relB b x A] ⊢ relB b x B
    FreeHAωAbove b   = the same for every variable        (FreeIPLInAboveT3 = FreeHAωAbove t3)
    base m           = σᵐ⊥                                 (base 0 = ⊥, base 1 = t3, base 2 = ◯t3 ∨ (◯t3 ↠ t3))
    Conjecture       = ∀ n ∃ m, FreeHAnAbove (base m) n
    BMax b M w       = w refutes b, no proper successor refutes b
    TypeBound b K    = k(b) ≤ K: K valuations Ts, a type function ty on all worlds of all
                       FinDec subframe models, every b-maximal w has type Ts (ty w)
    Distinct b K     = k(b) ≥ K: K b-maximal cells with pairwise different vf theories
    TypesFinite b    = ∃ K, TypeBound b K
    Companion        = ∀ b vf, ⊬ b → TypesFinite b
    CountingCriterion= FreeHAnAbove b n → TypeBound b K → 2ⁿ ≤ K
    PatternsRealised b n = cells indexed by the sign patterns Fin n → Bool, pairwise separated
    TwoGenPatterns b x₀ x₁ = ∀ ε, ⊬ (x₀^ε₁ ∧ x₁^ε₂) ↠ b

The candidate pair high up (in `[σ²⊥, ⊤]`):

    Y  = t4 ∨ ¬t4,   x = ◯Y,
    x₀ = ◯σ²⊥ = σ²(◯⊥),   x₁ = σ²⊥ ∨ ((◯Y ↠ t3) ↠ t3).

(The variables are `pvar i = "p", "pp", "ppp", …`, so `pvar 0 = pv`; the
first commit had `"p" ++ toString i`, changed before any proof used it.)

## A. Status table

| statement | formula | theorem | status |
|-----------|---------|---------|--------|
| the sign-pattern condition for `(x₀, x₁)` over `σ²⊥` | `∀ ε, ⊬ (x₀^ε₁ ∧ x₁^ε₂) ↠ σ²⊥` | `twoGenPatterns_x0_x1`, cells `cell_00 … cell_11` | PROVED (four kernel-checked countermodels) |
| `k(σ²⊥) ≥ K` for every `K` | `Distinct (base 2) K` | `base2_unbounded` | PROVED |
| no finite type bound at `σ²⊥` | `¬ TypeBound (base 2) K` | `not_typeBound_base2` | PROVED |
| the companion | `∀ b vf, ⊬ b → ∃ K, TypeBound b K` | `not_Companion` | REFUTED (at `b = σ²⊥`) |
| `TypeBound ⊥ 2`, `TypeBound t3 3` | the known counts | not restated here (`FreeIPL.rmax_force`, `rmax_inS_or_hasN` give `t3`) | known, PROVED in `f0FreeIPL` |
| the counting criterion | `FreeHAnAbove b n → TypeBound b K → 2ⁿ ≤ K` | — | pen (below); Lean proof not started |
| `Conjecture` | `∀ n ∃ m, FreeHAnAbove (σᵐ⊥) n` | — | OPEN; not refutable by the count at any `n`, `m ≥ 2` |
| `FreeHAnAbove (σ²⊥) 2` with `(x₀, x₁)` | faithfulness on two-variable formulas | — | OPEN (necessary condition passes) |

## A. The counting criterion (pen; the mechanism is the one of `noFreeHA2`)

If `x₀ … x_{n-1} ≥ b` are free over `b` then for every sign pattern `ε` the
IPC formula `¬(p₀^ε₀ ∧ … ∧ p_{n-1}^ε_{n-1})` is no theorem (the one-world
model with valuation `ε`), so `(x₀^ε₀ ∧ … ∧ x_{n-1}^ε_{n-1}) ↠ b` is no
theorem of PLL; a finite subframe countermodel has a world forcing the signed
conjunction and refuting `b`, and above it a `b`-maximal world `w_ε` forcing
it (`exists_rmax` generalised from `t3` to `b`).  At `w_ε` the generator
`x_i` holds iff `ε_i = true` (`x_i ↠ b` and `¬ b` give `¬ x_i`), so the `2ⁿ`
worlds `w_ε` have pairwise different theories (`x_i` separates), hence
pairwise different types: `2ⁿ ≤ K`.  The two-generator instance is exactly
`not_twoGenFaithful` of `f0FreeIPL`.  The Lean proof is routine (an `n`-ary
`pattern_of_force`, the one-world model with valuation `ε`, and the Nat
pigeonhole `nat_pigeon` composed with a bit-decoding of `Fin n → Bool` into
`[0, 2ⁿ)`); estimate 250 lines; not needed for the verdicts below.

## A. The type count: `k(⊥) = 2`, `k(t3) = 3`, `k(σ²⊥) = ∞`

The method of `f0FreeIPL` for `t3`: in a finite subframe model, `G = {t3}`
splits as `Gₑ ⊔ Gₙ` (`◯⊥` / `¬◯⊥`), each with a single variable-free theory,
and a `t3`-maximal world's theory is fixed by two bits.  Iterating with `σ`
(the region `R₁ = {¬t3}` of a model `M`, restricted, is a model `M|R₁` in which
`σ(ψ)` holds at `x ∈ R₁` iff `ψ` holds at `x` in `M|R₁`; this is `top_sig`,
`orig_sig` of `f0SelfSim` read backwards), the `σ²⊥`-maximal worlds of `M`
are the `t3`-maximal worlds of `M|R₁`, but their FULL theory also records
which theories of the shell `R₁ ∖ R₂ = {¬t3, σ(t3)}` lie above them.  The
shell splits as `{◯t3} ⊔ {g1}`, `g1 = ◯t3 ↠ t3`; the `◯t3`-part carries one
theory, but the `g1`-part `Z = {g1 ∧ ¬t3}` carries a Rieger–Nishimura ladder
over the generator `x = ◯(t4 ∨ ¬t4)` relative to `t3`:

    ZL n:  tops e₀ (◯⊥, ∉ S) and n₀ (¬◯⊥, ∈ S);  ladder w₀ … wₙ (∈ S; w_j sees w_{j'} for j'+2 ≤ j,
           e₀ always, n₀ from w₁ up);  f ∉ S seeing both tops;  m ∈ S seeing everything.

`x` holds exactly at `w₀` and `f` among the non-tops (`force_x_iff`), `t3`
holds exactly at the tops, so the relativisation `A[p := x, ⊥ := t3]` of a
one-variable ◯-free `A` holds at `w_j` iff `A` holds at `j` on the ladder
skeleton of `rnEmbed`, and at `m` iff `A` holds at `n + 2` (`transfer`).  Every
world but `m` forces `σ²⊥` (`force_b2`) and `m` refutes it (`f` forces `◯t3`
and refutes `t3`), so `m` is `σ²⊥`-maximal (`bmax_m`).  The relativised odd
rung `rn (2(n+2)+1)` holds at the `m` of `ZL n` and fails at the `m` of
`ZL n'` for `n < n'` (`cell_force`, by the choice-free `sat_rn_odd_cf`), so the
bottoms of `ZL 0, ZL 1, …` are `σ²⊥`-maximal worlds with pairwise different
theories: `k(σ²⊥) = ∞`.  In particular `[t3, g1]` is infinite (the `g1 ∧ r_k`
for the relativised rungs `r_k` are pairwise distinct), and `[t3, ⊤]` has
elements `a = σ²⊥` with infinitely many maximal points of `{¬a}` in the dual
space.

Exploration (not evidence): `_out/ladder.py`, `_out/cells.py` evaluate the
models; the kernel-checked facts are the Lean theorems.

## A. The designed cells

| cell | model | verdict | theorem |
|------|-------|---------|---------|
| `(x₀ ∧ x₁) ↠ σ²⊥` | `ZL 0`, `m ∉ S` (5 worlds, root `m`) | REFUTED | `cell_11` |
| `((x₀ ↠ σ²⊥) ∧ x₁) ↠ σ²⊥` | `ZL 0`, `m ∈ S` | REFUTED | `cell_01` |
| `(x₀ ∧ (x₁ ↠ σ²⊥)) ↠ σ²⊥` | `ZL 1`, `m ∉ S` (6 worlds) | REFUTED | `cell_10` |
| `((x₀ ↠ σ²⊥) ∧ (x₁ ↠ σ²⊥)) ↠ σ²⊥` | `ZL 1`, `m ∈ S` | REFUTED | `cell_00` |

Each cell is a `SubCM` table checked by `SubTab.no` (`decide +kernel`); the
subframe tableau (`refbench fact`, independent producer) refutes the same
four formulas with countermodels of 6, 5, 7, 8 worlds (`_out/` log in the
session).  `x₀` holds at `m` iff `m ∉ S`; `x₁` holds at `m` iff `m` does not
see `w₁` (then `¬¬x` relative to `t3` holds at `m`).

## A. Verdict on the conjecture

The counting criterion is the only tool the brief named, and it cannot
refute `FreeHAnAbove (σᵐ⊥) n` for any `n` once `m ≥ 2`: `k(σ²⊥) = ∞` (and
`k(σᵐ⊥) = ∞` for `m ≥ 2`, since `σ` carries the family: pen).  The companion
is REFUTED.  Whether `(x₀, x₁)` or any pair is free over `σ²⊥` is a
construction (every finite two-variable Kripke model must be simulated by a
subframe model inside `{¬σ²⊥}` with `x₀`, `x₁` reading its valuation); the
two-generator necessary condition passes.  OPEN.

## B. The weaker notions (scoping; pen, cited where fetched)

    (lattice)  ∃ S ⊆ [t3, ⊤], a sublattice, with S ≅ free IPL on ℵ₀ generators
    (order)    ∃ S ⊆ [t3, ⊤], a sub-poset,  with S ≅ free IPL on ℵ₀ generators

Notation: `FD(ω)` the free distributive lattice on ℵ₀ generators, `FB(ω)` the
free Boolean algebra, `H_ω` the free Heyting algebra on ℵ₀ generators.
F0 contains `FD(ω)` as the lattice generated by the odd gaps (`indep`,
`lpoly_deriv_iff`, PROVED), and `σ` carries it into `[t3, ⊤]` (`sigN_faithful`,
PROVED), so `[t3, ⊤] ⊇ σ(FD(ω)) ≅ FD(ω)` as a sublattice.

### B1. The route through `FD(ω)`: REFUTED (pen, with Balbes 1967)

Balbes, *Projective and injective distributive lattices*, Pacific J. Math.
21 (1967) 405–420, Definition 4.3 and Theorem 4.6 (p. 412): a subset `D` of a
distributive lattice is *a-disjointed* if `xy = a` for distinct `x, y ∈ D`;
**in a free distributive lattice every a-disjointed subset is finite**.
(Lemma 4.4 is the combinatorial core; Example 4.8, p. 412: the lattice of
finite sets of integers is not projective, its singletons being an infinite
disjointed set.  Binns–Simpson, *Embeddings into the Medvedev and Muchnik
lattices of Π⁰₁ classes*, Arch. Math. Logic (2004), p. 16, cite exactly this
theorem for "neither L₁ nor L₂ [finite, co-finite subsets of ω] is embeddable
in FD(ω)", and p. 2 for "every finite distributive lattice can be embedded
into FD(ω)" and, Lemma 4.10, "every countable distributive lattice is
isomorphic to a sublattice of FB(ω)".)

`H_ω` has an infinite `⊥`-disjointed set: `d_i = p_i ∧ ¬p_1 ∧ … ∧ ¬p_{i-1}`,
pairwise meets `⊥`, pairwise distinct and non-zero (one-world models).  A
lattice embedding `f : H_ω → FD(ω)` would carry it to an infinite
`f(⊥)`-disjointed subset of `FD(ω)`, against Theorem 4.6.  So the lattice
reduct of `H_ω` is not a sublattice of `FD(ω)`, and the odd-gap copy cannot
host (lattice).  (The same holds for `H_2`, with the `p₁`-disjointed family
`p₁ ∨ φ_m` over the de Jongh formulas `φ_m` of the infinitely many
`p₁`-maximal points of the two-variable universal model: pen, standard
universal-model facts not fetched here.)

The brief's other candidate obstruction, relatively complemented elements:
in `FD(ω) ⊆ FB(ω) = Clop(2^ω)`, an interval `[a, b]` with `a, b` on the
generators `F` (finite) has finitely many relatively complemented elements:
`c ∧ c' = a`, `c ∨ c' = b` force `c' = ¬c` on `R = {a = 0, b = 1}`, and `c`,
`c'` both monotone make `c` constant along every chain of `R`, hence a
function of the `F`-coordinates only (at most `2^(2^|F|)` choices).  This is
the same obstruction in another coat (an infinite `a`-disjointed set inside
`[a, b]` with joins `b` gives infinitely many relative complements), and it
is REFUTED as an obstruction to (lattice) in `[t3, ⊤]` itself, see B2.

### B2. (lattice) in `[t3, ⊤]`: OPEN, no obstruction found

An embedding `f : H_ω → [t3, ⊤]` as a lattice sends `⊥ ↦ a ≥ t3` and the
`d_i` to an infinite `a`-disjointed family of `F0`, which needs infinitely
many maximal points of `{¬a}` in the dual space (each `f(d_i) ∖ â` contains
one, and they are pairwise disjoint).  At `a = t3` there are three such
points (`rmax_inS_or_hasN`), so `f(⊥) = t3` is impossible; but `a = σ²⊥` has
infinitely many (`base2_unbounded`, Lean), so this obstruction does not
apply to `[t3, ⊤]`.  By Priestley duality `FD(ω)` with bounds is the lattice
of clopen up-sets of the Cantor cube `2^ω`, and `[t3, ⊤]` of the clopen down
set `{¬t3}` of the dual space of F0; a lattice embedding of `H_ω` into
`[t3, ⊤]` is a Priestley surjection from a convex clopen piece of `{¬t3}`
onto the dual space of `H_ω`.  No construction and no further obstruction;
OPEN.

### B3. (order): holds, by a pen construction (not mechanised)

`FD(ω)` contains every countable poset as a sub-poset.  Pen proof: in
`Clop(2^ω)` enumerate the poset `p₀, p₁, …` and choose clopen up-sets `U_n`
in turn with `U_n := G ∪ (L ∩ {x_N = 1})`, `N` a fresh coordinate,
`G = ⋃_{m<n, p_m ≤ p_n} U_m`, `L = ⋂_{m<n, p_n ≤ p_m} U_m` (so `G ⊆ L` by
transitivity); the invariant "for disjoint finite `I, J ⊆ {0..n−1}` with no
`i ∈ I`, `j ∈ J` having `p_i ≤ p_j`, the cell `⋂_I U_i ∖ ⋃_J U_j` is
non-empty" is preserved (the fresh coordinate splits every cell in two
non-empty halves, both up-closed where needed), and it gives
`U_n ⊄ U_m` when `p_n ≰ p_m` and `U_m ⊄ U_n` when `p_m ≰ p_n`.  Hence
`H_ω`, a countable poset, order-embeds into `FD(ω) ⊆ F0`, and
`σ` carries the copy into `[t3, ⊤]` (`sigN_faithful`).  The sub-poset `S`
then is a Heyting algebra with its own operations (it is isomorphic to
`H_ω`); nothing is said about F0's `∧`, `∨`, `↠` on `S`.  So (order) is a
pen theorem with two mechanised ingredients (`indep`/`lpoly_deriv_iff`,
`sigN_faithful`) and one unmechanised (the universality of `FD(ω)` for
countable posets); a citation for the latter was not found in the fetched
sources (Balbes Thm 4.2, p. 411, gives only "no uncountable chains in a
projective distributive lattice", the countable direction is open-ended).
Verdict: pen argument, not OPEN; Lean work not attempted (the construction
is not a cell).

## Gates (watched failing, 2026-10-27, `_out/f0FreeHAn_gate.lean`)

* pins: `#axioms_within not_Companion [propext]` and `base2_unbounded [propext]`: FAIL (both need `Quot.sound`); `[propext, Quot.sound]` passes in the module.
* the table of `cell_11` with `m` put into `S`: REJECTED by `decide +kernel` ("proved that the proposition … is false"); `ZL.cell_sep' rfl` at equal indices: type error (`2 ≠ 2` expected).

## Log

* 2026-10-27 11:4x: statements written and committed before any proof
  (METHOD.md §1), `206226d`.  Exploration of the shell structure
  (`_out/shell.py`, `_out/ladder.py`): the ladder inside `[t3, g1]` and the
  `σ²⊥`-maximal bottoms with pairwise distinct rung vectors.
* 2026-10-27 12:xx: the four sign-pattern cells designed (`_out/cells.py`),
  cross-checked by `refbench fact`, kernel-checked in Lean.
* 2026-10-27 14:3x: `base2_unbounded`, `not_typeBound_base2`,
  `not_Companion` PROVED; `omega` found reaching `Classical.propDecidable`
  through negated conjunctions and `iff` hypotheses (the frontend pushes
  negations with `Classical.propDecidable`): every `omega` goal reduced to
  `False`, an equation, an inequality or a disjunction of those; the ladder
  truth set taken from the choice-free `sat_rn_odd_cf` (`f0Indep`).
