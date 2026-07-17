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

**Design ruling (Matthew, 2026-07-16).** The realiser structure is a **genuine
partial combinatory algebra in the classical realisability tradition** (Kleene's
`K₁`, or a PCF-style closed-term model) — chosen precisely because it connects
the model solidly to prior art in realisability semantics. Practically one would
realise with Lean's own language and type system; but the primary aim is to
study **what is calculable** with the belief semantics, not **how** things are
calculated, and the motivation section is to be written in exactly those terms.
(The Lean development keeps `Pca` minimal — pairing + total tag decode — adding
`k`/`s` only where a result needs them; the refutation theorems are parametrised
by an identity combinator `I`, derivable in any genuine PCA as `skk`.)

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

**Scoping note (2026-07-16).** O3 is stated over models **without fallible
worlds** (`F = ∅`), the standard Kleene-style class: at fallible worlds the
`F`-guards make hypothesis-realisers non-strict, so applications may diverge and
no extracted value need exist. Extending O3 to `F ≠ ∅` needs a strictness
discipline (guarded application / lazy pairing) — OPEN. The countermodel and
separation results are unaffected (they already use `F = ∅` models).
**Extraction shape:** `iden ↦` variable, `impIntro ↦` bracket abstraction,
`impElim ↦` application, `∧/∨ ↦` pairing/tagging/case, and the lax rules:
`laxIntro ↦` **identity**, `laxElim ↦` **let** — under uniform evidence the
`◯`-monad's computational shadow is the identity monad, which is exactly the
rigidity the incompleteness theorem (§5) detects.

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
- **Completeness — the collapse lemma is REFUTED as first sketched
  (2026-07-17).** The hoped-for lemma `∃a. a ⊩ˢ_w φ ⟺ w ⊨ φ` over full-evidence
  models **fails in both directions**, for `⊩ˢ` as much as `⊩ᵘ`, at nested
  implications:
  1. *truth ⇏ realisability (tag-mixing):* over full evidence every element
     evidences every true atom, so a realiser of `p ⊃ (q∨r)` must send
     arbitrary elements to one **fixed-tag** value — but the `p`-cone may force
     `q` at one future and `r` at another; one tag cannot serve a mixed cone.
  2. *realisability ⇏ truth (vacuity):* where (1) empties the antecedent's
     realisers, any element realises `(p⊃(q∨r)) ⊃ s` vacuously while its truth
     fails.
  (The `◯`-clause direction I had checked does hold; the error was generalising
  it past `⊃`.) Consequently the completeness question for `⊩ˢ` — is
  `{φ : ⊩ˢ`-valid`} = {φ : PLL ⊢ φ}`? — is genuinely **OPEN**, and needs one of:
  (a) **canonical term-model realisability**: realisers = extracted polynomials
  over a syntactic PCA, evidence tailored so realisability tracks derivability
  by construction; or (b) **per-formula tailored evidence**: given a truth
  countermodel of `φ` (F&M completeness, PROVED), choose `E` so that `φ` is not
  realised at the refuting world — evidence rich enough that antecedent
  realisers exist and carry branch information. Route (b) per-formula may be
  easier than a uniform collapse. Soundness (O3ˢ) is unaffected and comes
  first.

**Paper shape.** `⊩ˢ` is *the* semantics of evidential belief (soundness O3ˢ
pending mechanisation; completeness genuinely OPEN per the 2026-07-17 finding
above); `⊩ᵘ` with §5(b) is the **evidential-bite theorem** — what uniform
(strategy-free) evidence costs — and `◯(A∨B)` is the separating formula. Both
clauses share §§1–4 unchanged (heredity, nucleus laws, sequential meet,
evidence-extraction soundness).

**Named-witness upgrade (2026-07-17).** The `⊩ˢ` `◯`-clause now requires the
package to *name* its constraint-witness: `fst y = ⌜u⌝`. This is forced by
strategy-soundness: the extracted `laxElim` composite must apply the
continuation *at the witness's code*, which the purely semantic `∃u` clause
withholds. Mechanised (`realS` revised; heredity, saturation, and the
triptych-(iii) theorems all survive the upgrade, with the concrete `splitPca`
strategy now returning `(⌜witness⌝, evidence)` packages).

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

*Status 2026-07-17 (evening): **rung 6 RESOLVED — by repair, and the repair is
a theorem.** First the obstruction: `realS_fullness_obstruction` (audit
`[propext, Quot.sound]`, choice-free) — on a three-world frame (`t` at both
leaves, `p` only at one, `q` only at the other), **no** evidence assignment is
both atom-adequate and full for `⊩ˢ`, for every PCA with finite tables against
the world-coding. The failure is **`◯`-essential**: one strategy table
realises `◯t` at both incomparable leaves, so a would-be realiser of
`◯t ⊃ (p∨q)` must give one answer for two futures demanding opposite tags;
purely intuitionistic antecedents are rescued by world-tagged evidence, but
strategies carry no world-marks. So the `⊃`-clause must present the future —
exactly as the `◯`-clause already does. `realP` (`⊩ᵖ`, presented-strategy
realisability) makes that single change: the `⊃`-realiser is applied to
`pair (κ v) b`. Then, over ANY finite frame validated by the verified
countermodel checker (`PLLCountermodelEmit.lean`) with token evidence:
**`realP_adequate_and_full`** — realised ⟺ forced, with explicit
table-built witnesses (the `∨`-witness branches by the executable `forceB`,
the `◯`-witness searches the finite frame, the `⊃`-witness looks up the
consequent's witness at the presented world) — and
**`realP_refutes_sequent`** — every checked countermodel is a
`⊩ᵖ`-refutation: hypotheses realised at the refuting world, conclusion
unrealisable. BOTH `[propext, Quot.sound]` — **no choice anywhere in the
chain** (checker certificate, obstruction, decoration, squeeze). Flagship:
`somehow_p_not_p_realP` realisability-refutes `◯p ⊢ p` at the pinned emitted
model by `decide`. Still OPEN for the full constructive completeness of PLL
w.r.t. `⊩ᵖ`: **emitter completeness** (a proof that `CounterEmit.emit`
succeeds on every underivable sequent — per-instance certificates exist
today; the classical existence route via the FMP is available meanwhile), and
a concrete PCA instantiation of the table hypotheses (met in `K₁`,
pen-and-paper). The triptych statements for `⊩ˢ` are untouched — `⊩ˢ` remains
the right relation for the separation story; `⊩ᵖ` is the completeness-grade
refinement the obstruction forces.*

*Status 2026-07-17: **rung 5 COMPLETE for BOTH clauses**. `wip/belief_realisability.lean`
now has combinatory completeness (`Poly.abs_spec`, `Poly.eval_bump`), the two
extractions `extract` (uniform, `[propext]`) and `extractS` (strategy, `[propext]`),
and the two soundness-with-extraction theorems `extract_sound` and **`extractS_sound`**
(both clean audits): over models without fallible worlds, from every `LaxND`
derivation an extracted polynomial evaluates to a realiser of the conclusion. The
strategy extraction needed the named-witness clause (`fst y = κ u`) and one de
Bruijn `bump`; `laxIntro` extracts to `λc. ⟨c, ·⟩`, `laxElim` to
`λc. (⌜run p₂⌝ · snd(s₁·c)) · fst(s₁·c)` — belief-evidence as a genuine
constraint-discharge program. Remaining: rung 6 completeness for `⊩ˢ` (OPEN — the
collapse lemma is refuted, see §6; needs canonical term-model or per-formula
tailored evidence, possibly seeded by a countermodel extractor from the mechanised
PLL decision procedure `decidablePLL`), then `PLLᵘ` characterisation, then the
tripos/categorical rung.*


*Status 2026-07-16 (evening): triptych pieces (ii) and (iv) LANDED —
`uniform_dist_valid` (the identity `⊩ᵘ`-realises `◯(φ∨ψ)⊃(◯φ∨◯ψ)` at every
world of every model, arbitrary `φ,ψ`, any structure with an identity
combinator; **axiom-free**) and `impdist_not_uniform` (+ its lemma chain: no
`⊩ᵘ`-realiser for `(◯A⊃◯B)⊃◯(A⊃B)` at the chain-model root; audit clean). With
`bite_uniform_split` (i) and the PROVED `not_provable_somehow_or_dist`, the
incompleteness of `⊩ᵘ` and the `⊃`-barrier of §5 are now fully machine-checked;
and (iii) LANDED as well — `strategy_realises_obAB`(_split) (a case-splitting
strategy realises `◯(A∨B)` at the root: the bite vanishes under `⊩ˢ`) and
`strategy_dist_refuted`(_split) (`◯(A∨B)⊃(◯A∨◯B)` has no `⊩ˢ`-realiser at the
root: the countermodel survives). **The separation triptych is complete and
fully machine-checked.** The strategy is the first genuine program in the
development — hypothesised by its application equations (class-robust; met in
`K₁` by combinatory completeness) and witnessed concretely by `splitPca`.*

*Status 2026-07-16 (later): rung 3 LANDED too — `HProp`, `ob`, `obH`
(stability), `ob_infl`, `ob_mono`, `ob_idem`, `ob_strength` (the sequential-
composition meet, machine-checked with **no confluence**), `realU_somehow_mem`
(the `⊩ᵘ` clause = the operator) — all **axiom-free**. Also
`force_somehow_iff_notnot`: the **double-negation believer** — in constraint
models with `Rₘ = Rᵢ` and `F = ∅`, `◯M` is forced exactly where `¬¬M` is; the
continuation reading `◯ = ¬¬` is the `Rₘ = Rᵢ` instance of the semantics
(inhabitation reading: every strong monad interprets the proof theory —
idempotence is inter-derivability, not a computational identity; the nucleus
picture is its propositional shadow).*

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
