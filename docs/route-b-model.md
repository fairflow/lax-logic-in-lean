# Route B: a realisability constraint model for PLL — precise definition and proof obligations

*Design document, 2026-07-16. Goal: enrich the Fairtlough–Mendler constraint
semantics (mechanised in `LaxLogic/PLLKripke.lean`) with realisers at each world,
so that (i) worlds carry computational information, (ii) `◯M` is evaluated at a
world against that information, and (iii) belief grows monotonically over a
branching preorder. Everything below marked OPEN is a Lean obligation under the
machine-checked mandate; PROVED items cite the existing mechanisation.*

Throughout, `A` is a partial combinatory algebra (PCA) with application `·`
(partial), pairing `⟨−,−⟩` with projections `p₁, p₂`, and tags `0, 1` for case
analysis; `a·b↓` means the application is defined.

---

## 1. The model

**Definition (realisability constraint model).** A realisability constraint model
over a PCA `A` is a tuple `(W, Rᵢ, Rₘ, F, E)` where `(W, Rᵢ, Rₘ, F)` is exactly a
Fairtlough–Mendler constraint frame (F&M Def 3.1 = `ConstraintModel` minus `V`,
`PLLKripke.lean:28`): `Rᵢ, Rₘ` preorders, `Rₘ ⊆ Rᵢ` (`sub_mi`), `F` hereditary —
and `E` assigns to each atom `p` and world `w` a set `E_w(p) ⊆ A` of **evidence
for `p` at `w`**, subject to

>  (heredity)      `w Rᵢ v  ⟹  E_w(p) ⊆ E_v(p)`
>  (fallible saturation)  `w ∈ F  ⟹  E_w(p) = A`.

`E` replaces the valuation `V`; the truth-level model is recovered by
`w ∈ V(p) :⟺ E_w(p) ≠ ∅` (or by the trivial instantiation of §6).

**Definition (realisability).** For `a ∈ A`, `w ∈ W`, define `a ⊩_w φ` by
induction on `φ` (each world-quantified clause carries the fallibility guard
`v ∈ F ∨ …`, mirroring `force_of_fallible`, `PLLKripke.lean:75`):

>  `a ⊩_w p`    iff  `w ∈ F  ∨  a ∈ E_w(p)`
>  `a ⊩_w ⊥`    iff  `w ∈ F`
>  `a ⊩_w φ∧ψ`  iff  `w ∈ F  ∨  (p₁·a ⊩_w φ  ∧  p₂·a ⊩_w ψ)`
>  `a ⊩_w φ∨ψ`  iff  `w ∈ F  ∨  (∃b. a = ⟨0,b⟩ ∧ b ⊩_w φ)  ∨  (∃b. a = ⟨1,b⟩ ∧ b ⊩_w ψ)`
>  `a ⊩_w φ⊃ψ`  iff  `∀v. w Rᵢ v →  v ∈ F  ∨  ∀b. (b ⊩_v φ → a·b↓ ∧ a·b ⊩_v ψ)`
>  `a ⊩_w ◯φ`   iff  `∀v. w Rᵢ v →  v ∈ F  ∨  ∃u. v Rₘ u ∧ a ⊩_u φ`

The `⊃`-clause is the standard Kripke-realisability clause (Lipton). The
`◯`-clause is the F&M `∀∃` clause with the **same realiser `a` carried to the
constraint-witness `u`**: the evidence for `◯φ` *is* evidence for `φ`, valid once
the constraint (the passage `v ⤳ u`) is discharged. This is the *uniform-evidence*
design; see §7 for the alternative.

**Lemma 1 (heredity of realisability = increasing belief).** OPEN.
>  `w Rᵢ v  ∧  a ⊩_w φ   ⟹   a ⊩_v φ`.
Induction on `φ`, exactly parallel to `force_hered` (`PLLKripke.lean:61`, PROVED
at truth level). This is clause (iii) — belief grows along the (branching)
order — obtained from heredity, not imposed.

## 2. The belief algebra and the nucleus obligations

**Definition (semantic propositions).** `𝓗(W,A)` := the set of `P : W → 𝒫(A)`
that are hereditary (`w Rᵢ v ⟹ P(w) ⊆ P(v)`) and fallible-saturated
(`w ∈ F ⟹ P(w) = A`), ordered by pointwise inclusion. Meet is the pairing meet
`(P ⊓ Q)(w) = {c | p₁·c ∈ P(w) ∧ p₂·c ∈ Q(w)}` (up to the `F`-guard); join and
implication by the `∨`/`⊃` clauses read as operations on predicates.

**Obligation O1.** OPEN. `𝓗(W,A)` is a Heyting algebra (or at least a Heyting
prealgebra under realisable entailment, §4).

**Definition (the believer).** `◯ : 𝓗(W,A) → 𝓗(W,A)`,
>  `(◯P)(w)  =  {a | ∀v. w Rᵢ v →  v ∈ F  ∨  ∃u. v Rₘ u ∧ a ∈ P(u)}`.

**Obligation O2 (local nucleus, stable).** OPEN. On `𝓗(W,A)`:
>  (stability)   `◯P ∈ 𝓗(W,A)`            — uses `trans_i`  (cf. `force_hered`, somehow case)
>  (inflation)   `P ≤ ◯P`                  — uses heredity of `P` + `refl_m`  (cf. `laxIntro` soundness, `PLLKripke.lean:129`)
>  (idempotence) `◯◯P ≤ ◯P`               — uses `trans_m` + `refl_i`  (cf. `OM`)
>  (meet)        `◯P ⊓ ◯Q ≤ ◯(P ⊓ Q)`     — **sequential composition**, §3  (cf. `laxElim` soundness, `PLLKripke.lean:132`)
>  (monotone)    `P ≤ Q ⟹ ◯P ≤ ◯Q`.
Note inflation *requires* heredity of `P`: `◯` is a nucleus on `𝓗(W,A)`, not on
arbitrary `A`-predicates. All five have one-line proofs mirroring the truth-level
soundness cases cited; in the uniform-evidence design the realiser transformations
are identities/pairing plumbing.

## 3. No confluence — the sequential-composition argument

Forward confluence must NOT be assumed. Machine-checked at truth level:
- confluent models force `◯(A∨B) ⊃ ◯A ∨ ◯B`
  (`force_somehow_or_dist_of_confluent`, `PLLFrames.lean:240` — PROVED);
- that formula is **not** a PLL theorem
  (`not_provable_somehow_or_dist`, `PLLFrames.lean:142` — PROVED, F&M Fig. 3).
So any frame class validating forward confluence is unsound for PLL. Valliappan's
λSL frames need forward confluence because his modal clause is the bare
existential `⟦◆A⟧w = Σv.(w Rₘ v) × ⟦A⟧v`, which is not hereditary by itself; the
F&M `∀∃` clause internalises heredity, so no confluence is needed anywhere.

What replaces confluence in the meet law is **sequential composition**: given
`c` with `p₁·c ∈ (◯P)(w)`, `p₂·c ∈ (◯Q)(w)` and `v ⊒ᵢ w`, `v ∉ F`:
1. the `◯P` clause at `v` yields `u₁` with `v Rₘ u₁` and `p₁·c ∈ P(u₁)`;
2. `w Rᵢ u₁` (via `sub_mi`, `trans_i`), so the `◯Q` clause **at `u₁`** yields
   `u₂` with `u₁ Rₘ u₂` and `p₂·c ∈ Q(u₂)` (or `u₁ ∈ F`, absorbed by saturation);
3. `v Rₘ u₂` by `trans_m`, and `p₁·c ∈ P(u₂)` by heredity of `P` along
   `u₁ Rᵢ u₂` (`sub_mi`). Hence `c ∈ (P ⊓ Q)(u₂)`.
The second constraint is discharged *after* the first, at the world the first
produced — no common refinement of independent successors is ever required. This
is the same argument as the mechanised `laxElim` soundness case
(`PLLKripke.lean:132–141`) and F&M's `◯S`.

## 4. Soundness with evidence extraction (the slogan as a theorem)

**Obligation O3 (realiser soundness).** OPEN.
>  If `γ₁, …, γₙ ⊢ φ` in `LaxND`, there is a term `r` of the PCA such that in
>  every realisability constraint model, for all `w` and all `a₁ ⊩_w γ₁, …,
>  aₙ ⊩_w γₙ`:  `r·a₁·⋯·aₙ ↓ ⊩_w φ`.
By induction on the derivation, mirroring `soundness` (`PLLKripke.lean:97` —
PROVED at truth level); the extracted combinators for `laxIntro`/`laxElim` are
exactly the evidence operations `C_I`/`C_M`/`C_S` of the Curry paper (mechanised
as `unitC`/`bindC` infrastructure in `wip/context_completeness.lean`).

**Corollary (the paper's slogan, exact).** A proof of `◯M` yields a realiser `a`
which, at every world and modulo discharging one constraint step, is itself
evidence for `M` — "a proof of `◯M` contains the evidence for believing M" is the
`◯`-clause read off O3.

## 5. The evidential bite is an INCOMPLETENESS theorem (revised 2026-07-16)

*Matthew's observation: the "bite" of the first draft's §5 and the completeness
squeeze of its §6 are incompatible. Correct — and the mechanism is a theorem.
The uniform-evidence clause of §1 makes PLL sound but NOT complete:*

**(a) Bite at the root.** In the split model (`modelOrSplit`,
`PLLFrames.lean:116`: root `r`, maximal `a ⊨ A`, `b ⊨ B`, `F = ∅`) with full
evidence, `r` truth-forces `◯(A∨B)` but no element realises it at `r`: a realiser
is one fixed tagged pair, and its tag would have to decide disjunct `A` at world
`a` and `B` at world `b`. OPEN (mechanise).

**(b) Universal validation of `∨`-distribution.** Suppose `b ⊩_w ◯(A∨B)`. At
every non-fallible witness `u` the clause forces `b = ⟨i,c⟩` with one fixed tag
`i`; the clause for `b` then says precisely `c ⊩_w ◯(disjunct i)`. Hence (with
decodable pairing, e.g. `K₁`; the all-fallible-witness case is trivial)
`e = λb.⟨p₁b, p₂b⟩` realises

>  `◯(A∨B) ⊃ (◯A ∨ ◯B)`  at every world of every uniform-evidence model,

while `not_provable_somehow_or_dist` (PROVED, `PLLFrames.lean:142`) machine-refutes
it in PLL. **So PLL is sound (O3) but incomplete for `⊩ᵘ`.** (a) and (b) are one
phenomenon: uniform evidence for a disjunctive belief rigidly commits to a
disjunct across all constraint futures — which is exactly `◯A ∨ ◯B`. Status of
(b): pen-and-paper here; OPEN to mechanise.

**The induced logic.** `PLLᵘ := {φ | φ realiser-valid under ⊩ᵘ}` satisfies
`PLL + ◯(A∨B)⊃(◯A∨◯B) ⊆ PLLᵘ`, strictly containing PLL — a candidate **logic of
rigid evidence**. Characterisation OPEN (axiomatise? decidable?).

**The collapse stops at implication (Matthew's reservation, 2026-07-16).**
In `PLLᵘ` the modality fully distributes over `∧` (PLL already) and `∨` (§5(b)),
and `◯◯ = ◯` — so far the "push `◯` to the atoms" normal form works. But it
**fails at `⊃`**: only the K direction `◯(A⊃B) ⊃ (◯A⊃◯B)` holds; the converse

>  `(◯A ⊃ ◯B) ⊃ ◯(A ⊃ B)`   is **not** `⊩ᵘ`-valid,

so `◯(A⊃B)` is not reducible to `◯A ⊃ ◯B`, and `PLLᵘ` is *not* "IPC with tagged
atoms `◯p, ◯⊥` freely added". Refutation (pen-and-paper, OPEN to mechanise as
triptych piece (iv)): work over the chain model `modelNoImpDist`
(`PLLFrames.lean:175`: `r ≤ a ≤ b`, `Rₘ` reflexive + `a Rₘ b`, `A` at `{a,b}`,
`B` at `{b}`, `F = ∅`) with full evidence, over any PCA with an identity
combinator `I` (`I·b = b`, e.g. `skk`):
1. **No element realises `◯A` at `r`** (at `v = r` the only `Rₘ`-witness is `r`,
   and `E_A(r) = ∅`); at `a` and `b`, *every* element realises `◯A` and `◯B`
   (full evidence at the witnesses). Hence `I ⊩ᵘ_r ◯A ⊃ ◯B` — vacuously at
   `v = r`, and by totality of the consequent's realisers at `v ∈ {a,b}`.
2. **No element realises `A ⊃ B` at `r`**: at the future `a`, evidence for `A`
   exists but `E_B(a) = ∅` (and `a ∉ F`), so no output can realise `B` there.
3. Hence no `e` realises `(◯A⊃◯B) ⊃ ◯(A⊃B)` at `r`: feeding it `I` would give a
   realiser `y ⊩ᵘ_r ◯(A⊃B)`, whose `v = r` instance demands a realiser of
   `A ⊃ B` at `r` — contradicting 2.
All three steps are application-light (only `I` is used), so the argument lives
in the genuine-PCA validity class. What *survives* of the reservation: the
`∧`/`∨`/idempotence part is exactly right, and at the **atomic** level the
picture "each `p` acquires a tag `◯p` = *potentially true*" is a fair reading —
with the timing-circuit gloss (`p` settled vs `◯p` will-settle) a candidate
application of `PLLᵘ` itself. The modal content that survives rigidification is
concentrated at implication (and at `◯⊥`, which stays quarantined: `¬◯⊥` is not
`⊩ᵘ`-valid — the F&M fallible model refutes it realiser-wise).

## 6. The witness-strategy clause `⊩ˢ` — the completeness-compatible semantics

Replace the `◯`-clause: evidence for `◯φ` is a **constraint-discharge strategy** —

>  `a ⊩ˢ_w ◯φ`  iff  `∀v. w Rᵢ v →  v ∈ F ∨ (a·⌜v⌝↓ = ⟨⌜u⌝, b⟩  with  v Rₘ u  ∧  b ⊩ˢ_u φ)`

over a computably presented frame (worlds coded in `A`; trivial for finite
models). This is the honest BHK reading of F&M's `∀∃` clause: given any
intuitionistic future `v`, the evidence names a constraint-witness `u` and
delivers evidence for `φ` there.

**Locality — a strategy needs no foreknowledge (Matthew's question, 2026-07-16).**
The clause does *not* require the frame to be encoded at the world. The realiser
is a *reactive* function: the future `v` is its **input**, supplied when it
arrives; the side conditions (`v Rₘ u`, and that the output realises `φ` at `u`)
are checked **in the semantics**, not computed by the realiser — so no
decidability of `Rᵢ`/`Rₘ` and no representation of the frame inside `A` is
needed. All that is required of the coding `κ : W → A` is injectivity (distinct
futures distinguishable as inputs). Moreover only the **upset** `↑w` is ever
consulted (the clause quantifies over `v ⊒ᵢ w` only — the "past" is invisible),
so everything is stable under passing to the generated submodel. "A strategy to
deal with future situations does not imply foreknowledge of what those
situations will actually be" — exactly; the strategy is a function *on*
presented futures, not a table *of* them. Mechanised: the `⊩ˢ` clause and its
heredity in `wip/belief_realisability.lean` (`realS`, `realS_hered`) carry no
frame-decidability hypotheses at all.

- **Bite vanishes:** `◯(A∨B)` regains a realiser at `r` (choose the disjunct per
  branch: `r ↦ (a,⟨0,c⟩)`, `a ↦ (a,⟨0,c⟩)`, `b ↦ (b,⟨1,c⟩)`).
- **Distribution refuted again:** a realiser of `◯A ∨ ◯B` at `r` must commit its
  tag at `r`, and whichever tag it commits fails at the opposite branch — the
  truth countermodel survives realiser-level. OPEN (mechanise; per-candidate
  argument is uniform in `e`).
- **Completeness squeeze — now for `⊩ˢ`:** derivable ⟹ `⊩ˢ`-valid (O3ˢ) ⟹
  truth-valid over full-evidence models (collapse lemma: `∃a. a ⊩ˢ_w φ ⟺ w ⊨ φ`,
  by mutual induction — the strategy clause restores the truth ⟹ realiser
  direction that `⊩ᵘ` breaks; may use choice, harmless in Lean) ⟹ derivable (F&M
  completeness, PROVED: `PLLCompleteness.lean`). Status: OPEN; no new canonical
  model needed if the collapse lemma lands.

**Paper shape.** `⊩ˢ` is *the* semantics of evidential belief (sound + complete,
conjecturally); `⊩ᵘ` with §5(b) is the **evidential-bite theorem** — what uniform
(strategy-free) evidence costs — and `◯(A∨B)` is the separating formula. Both
clauses share §§1–4 unchanged (heredity, nucleus laws, sequential meet,
evidence-extraction soundness).

## 7. Variants and relation to Nakata

- **Modal-witness variant.** Replace the `◯`-clause by one where the realiser
  *computes* the witness: `a·⌜v⌝ = ⟨⌜u⌝, b⟩` with `b ⊩_u φ`. Requires a
  computably presented frame (worlds coded in `A`, relations trackable). More
  expressive (realisers carry constraint-discharge strategies), heavier to
  mechanise. Deferred; the uniform-evidence clause is the right first system.
- **Nakata (arXiv:2602.23218) is a template, not a competitor.** His nucleus is a
  *translation parameter on arithmetic* — there is no lax modality in his object
  language (Def 3.4: `j` a variable of type `PΩ`; atoms translated `R ↦ jR`). His
  worlds-as-nuclei forcing (Def 4.4) lives one assembly floor above ours: our `◯`
  is a single point of `N(O(W))` (Alexandrov opens of our world poset); his ℙ
  ranges over such points; a lax modality on *his* worlds would be an element of
  `N(N(O(W)))` — belief about belief. His technical payoff (Thm 6.19, separation
  of semi-classical arithmetic principles, unobtainable by plain
  `j`-realizability) is realizability-specific: local operators in `Eff` act as
  *generalized oracles* (`j_f` = Kleene realizability with oracle `f`), and
  ℙ-realizability extends de Jongh–Goodman sheaf realizability (Thm 5.20).

## 8. Mechanisation ladder (proposed order, revised)

*Status 2026-07-16: rungs 1–2 LANDED, plus triptych piece (i) — see
`wip/belief_realisability.lean`: `Pca`, `Evidence`, `realU`, `realS`,
`realU_hered`/`realS_hered` (increasing belief), `realU_of_fallible`/
`realS_of_fallible` (all axiom-FREE), `natPca`, `fullEvidence`,
`bite_uniform_split` (audit `[propext, Classical.choice, Quot.sound]`).
Matthew's rulings: rungs up to 6 approved; rung 7 (tripos/categorical) last —
it depends on Mathlib's category-theory library, untouched territory for this
repo, "worth a try if previous material has gone through". Validity-class
caution for all refutation rungs: state them over genuine PCAs (with `k`, `s`) —
or keep the arguments application-independent, as (i) and (iv) are — so that
refutations are not artefacts of degenerate applicative structures.*

1. `RealisabilityModel` structure + the two relations `⊩ᵘ`, `⊩ˢ` over an abstract
   PCA (a structure with `·`, `k`, `s`, decodable pairing; finite frames coded
   for `⊩ˢ`).
2. **Lemma 1** (heredity — increasing belief), for both clauses. Mirrors
   `force_hered`.
3. **O2** (stable local nucleus, all five laws — the sequential-composition
   meet), for `⊩ᵘ` first.
4. **The separation triptych on the split model** (the paper's new theorem):
   (i) §5(a) no `⊩ᵘ`-realiser for `◯(A∨B)` at `r`;
   (ii) §5(b) the universal `⊩ᵘ`-realiser for `◯(A∨B)⊃(◯A∨◯B)` — PLL incomplete
   for `⊩ᵘ`;
   (iii) §6 the `⊩ˢ`-refutation of `◯(A∨B)⊃(◯A∨◯B)` at `r`.
5. **O3 / O3ˢ** (soundness with evidence extraction, both clauses).
6. **§6 collapse lemma** for `⊩ˢ` (`∃`-realisability ⟺ truth over full-evidence
   models); completeness squeeze through `PLLCompleteness.lean`.
7. O1 / tripos refinement (realisable entailment, evidence operations as the
   Curry combinators) — the categorical statement, for the paper's §6.
8. `PLLᵘ` exploration (what else beyond `∨`-distribution does rigid evidence
   validate?) — small-model search, then axiomatisation attempt.
