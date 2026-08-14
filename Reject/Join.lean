/-
THE JOIN RULE — a fresh root below SEVERAL premise models.

`Reject/Build.lean` gives `addRoot`, which puts a new root below ONE
model, so the calculus builds only chains; that is why its demos are
the corpus's two smallest facts.  The join generalises it: a fresh
root below the DISJOINT UNION of premise models `Mᵢ`, with the root's
modal cone `S` declaring which component worlds are its
`Rm`-successors.

The construction factors, and the factorisation is the whole design:

    join Mods D  =  addRoot (union Mods) D

so `union` is the only new constructor, and every lemma of
`Reject/Build.lean` — `addRoot_force_some`, the two ◯-refutation
rules, `boxHolds`/`boxHoldsRoot`, `addRoot_reduced`,
`not_laxND_of_root` — applies to a join unchanged.  What is new here
is `union_force` (the load-bearing preservation lemma), the
componentwise form of the modal rules, and the confluence analysis.

**THE CONFLUENCE DECISION — (a), the PCLL-first route.**  The audit
(`Reject/Audit.lean`, `addRoot_not_confluent`) showed `addRoot` does
not preserve mutual confluence, and the unary-arity licence for the
◯-rule holds on reduced AND confluent frames (docs/frj-lifting.md §3).
So T1 had to choose.  Taken: **(a) — the join carries a confluence
side condition.**  `join_confluent_iff` makes the condition exact:

    MutuallyConfluent (join Mods D)
      ↔ (∀ i, MutuallyConfluent (Mods i)) ∧ ConeDominates Mods D

and `join_cone_empty_of_confluent_branching` shows what the condition
costs: when the join genuinely BRANCHES (two inhabited components),
confluence forces the root's modal cone to be EMPTY.  That is not a
workaround but a structural fact about the class — on a confluent
frame `◯A` at `w` is `∃u. w Rₘ u ∧ u ⊩ A`
(`force_somehow_iff_of_confluent`), and a branching root's only
`Rm`-successor is itself, so the ◯-rule at a branching root is unary
with the root as its own witness.  The price is paid in the right
currency: the models built stay inside the confluent class, so a
refutation certifies underivability in PCLL as well as in PLL
(`not_derivU_of_root`) — which is the logic the acceptance corpus
(docs/pcll-closed-fragment-catalogue.md) is stated in.

The screen that preceded these proofs is `lean_exe joinscreen`
(`wip/join_screen.lean`, output `wip/join_screen_out.txt`): seven
sections, each with a control that must fail in the same run.
-/
import Reject.Build
import Reject.Audit
import LaxLogic.PLLConfluentComplete

namespace Reject

open PLLND

variable {ι : Type} {Mods : ι → ConstraintModel}

/-! ## 1. The disjoint union

The one piece of dependent plumbing, kept as thin as possible: an
inductive family lifting a componentwise relation to `Σ i, (Mods i).W`.
Its single constructor is the fact that the union relates only worlds
of the SAME component, so `rcases` on it recovers the component
without a transport. -/

/-- A componentwise relation, lifted to the disjoint union. -/
inductive Lift (Mods : ι → ConstraintModel)
    (R : ∀ i, (Mods i).W → (Mods i).W → Prop) :
    (Σ i, (Mods i).W) → (Σ i, (Mods i).W) → Prop
  | mk {i : ι} {a b : (Mods i).W} : R i a b → Lift Mods R ⟨i, a⟩ ⟨i, b⟩

/-- A lifted relation never leaves its component. -/
theorem Lift.fst_eq {R : ∀ i, (Mods i).W → (Mods i).W → Prop}
    {x y : Σ i, (Mods i).W} (h : Lift Mods R x y) : x.1 = y.1 := by
  cases h; rfl

/-- **The disjoint union of premise models.** -/
def union (Mods : ι → ConstraintModel) : ConstraintModel where
  W := Σ i, (Mods i).W
  Ri := Lift Mods (fun i => (Mods i).Ri)
  Rm := Lift Mods (fun i => (Mods i).Rm)
  F := { x | x.2 ∈ (Mods x.1).F }
  V a := { x | x.2 ∈ (Mods x.1).V a }
  refl_i := by rintro ⟨i, a⟩; exact .mk ((Mods i).refl_i a)
  trans_i := by rintro x y z ⟨h1⟩ ⟨h2⟩; exact .mk ((Mods _).trans_i h1 h2)
  refl_m := by rintro ⟨i, a⟩; exact .mk ((Mods i).refl_m a)
  trans_m := by rintro x y z ⟨h1⟩ ⟨h2⟩; exact .mk ((Mods _).trans_m h1 h2)
  sub_mi := by rintro x y ⟨h⟩; exact .mk ((Mods _).sub_mi h)
  hered_F := by rintro x y ⟨h⟩ hx; exact (Mods _).hered_F h hx
  hered_V := by rintro c x y ⟨h⟩ hx; exact (Mods _).hered_V h hx
  full_F := by rintro c ⟨i, a⟩ hx; exact (Mods i).full_F hx

/-- **Forcing is unchanged inside a component** — the load-bearing
lemma.  Nothing a component world can see is affected by the presence
of the other components, because both relations stay inside their
component. -/
theorem union_force (φ : PLLFormula) :
    ∀ (i : ι) (a : (Mods i).W),
      (union Mods).force ⟨i, a⟩ φ ↔ (Mods i).force a φ := by
  induction φ with
  | prop a => exact fun _ _ => Iff.rfl
  | falsePLL => exact fun _ _ => Iff.rfl
  | and φ ψ ihφ ihψ => exact fun i w => and_congr (ihφ i w) (ihψ i w)
  | or φ ψ ihφ ihψ => exact fun i w => or_congr (ihφ i w) (ihψ i w)
  | ifThen φ ψ ihφ ihψ =>
      intro i a
      constructor
      · intro h b hab hφ
        exact (ihψ i b).mp (h ⟨i, b⟩ (.mk hab) ((ihφ i b).mpr hφ))
      · rintro h y ⟨hab⟩ hφ
        exact (ihψ _ _).mpr (h _ hab ((ihφ _ _).mp hφ))
  | somehow φ ih =>
      intro i a
      constructor
      · intro h b hab
        obtain ⟨y, hy, hφ⟩ := h ⟨i, b⟩ (.mk hab)
        cases hy with
        | mk hbu => exact ⟨_, hbu, (ih _ _).mp hφ⟩
      · rintro h y ⟨hab⟩
        obtain ⟨u, hu, hφ⟩ := h _ hab
        exact ⟨⟨_, u⟩, .mk hu, (ih _ _).mpr hφ⟩

/-! ## 2. The join -/

/-- **The join**: a fresh root below the disjoint union of the premise
models.  `D.S` is the root's modal cone, read componentwise as
`D.S ⟨i, u⟩`. -/
def join (Mods : ι → ConstraintModel) (D : RootData (union Mods)) :
    ConstraintModel :=
  addRoot (union Mods) D

/-- **The preservation lemma for the join**: forcing inside each
component is exactly what it was in that component alone.  This is the
analogue of `addRoot_force_some`, and it is what makes a join
derivation compose: the premise refutations are still valid where they
were established. -/
theorem join_force_comp (D : RootData (union Mods)) (φ : PLLFormula)
    (i : ι) (a : (Mods i).W) :
    (join Mods D).force (some ⟨i, a⟩) φ ↔ (Mods i).force a φ :=
  (addRoot_force_some D φ ⟨i, a⟩).trans (union_force φ i a)

/-- A cone built componentwise: `C i` selects the worlds of component
`i` that become `Rm`-successors of the root.  Each `C i` must be
`Rm`-upward closed in its own component, and root atoms must hold
everywhere (screened: `wip/join_screen.lean` §A′ rejects cones and
atoms that violate either). -/
def coneData (Mods : ι → ConstraintModel)
    (C : ∀ i, (Mods i).W → Prop)
    (hC : ∀ i {u v : (Mods i).W}, C i u → (Mods i).Rm u v → C i v)
    (At : String → Prop)
    (hAt : ∀ {a : String}, At a → ∀ (i : ι) (w : (Mods i).W), w ∈ (Mods i).V a) :
    RootData (union Mods) where
  S x := C x.1 x.2
  S_up := by rintro x y hx ⟨h⟩; exact hC _ hx h
  At := At
  At_hered := by rintro a h ⟨i, w⟩; exact hAt h i w

/-! ## 3. The modal rules at a join

One theorem states them all, in the EXACT form `boxRefuteHere_exact`
demands: the premises are equivalent to the semantic condition, so the
rules are neither vacuous nor over-strong.  The two conjuncts are the
two obligations the design predicted (docs/frj-lifting.md §4) —
the root's own modal cone, and the ◯-positive obligation checked
against each premise. -/

/-- **The ◯ rule at a join, exactly.**  The root forces `◯A` iff

* the root's `Rm`-cone realises `A` — either at the root ITSELF
  (`Rm` is reflexive: the case `boxHolds` could not express, and the
  audit's finding), or at a component world in the cone; AND
* every world of every component has an `Rm`-successor forcing `A`
  (the ◯-positive obligation, checked premise by premise). -/
theorem join_force_box_iff (D : RootData (union Mods)) (A : PLLFormula) :
    (join Mods D).force none (.somehow A) ↔
      ((join Mods D).force none A ∨
        ∃ (i : ι) (u : (Mods i).W), D.S ⟨i, u⟩ ∧ (Mods i).force u A) ∧
      (∀ (i : ι) (a : (Mods i).W), ∃ u, (Mods i).Rm a u ∧ (Mods i).force u A) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨(_ | ⟨i, x⟩), hu, hA⟩ := h none True.intro
      · exact .inl hA
      · exact .inr ⟨i, x, hu, (join_force_comp D A i x).mp hA⟩
    · intro i a
      obtain ⟨(_ | y), hy, hA⟩ := h (some ⟨i, a⟩) True.intro
      · exact absurd hy not_false
      · cases hy with
        | mk hab => exact ⟨_, hab, (join_force_comp D A _ _).mp hA⟩
  · rintro ⟨h1, h2⟩ (_ | ⟨i, a⟩) _
    · rcases h1 with hA | ⟨i, u, hS, hA⟩
      · exact ⟨none, True.intro, hA⟩
      · exact ⟨some ⟨i, u⟩, hS, (join_force_comp D A i u).mpr hA⟩
    · obtain ⟨u, hu, hA⟩ := h2 i a
      exact ⟨some ⟨i, u⟩, .mk hu, (join_force_comp D A i u).mpr hA⟩

/-- **`◯∈` at a join** — the refuting world is the root: neither the
root nor any component world in its modal cone forces `A`. -/
theorem joinBoxRefuteHere (D : RootData (union Mods)) {A : PLLFormula}
    (hroot : ¬ (join Mods D).force none A)
    (hcone : ∀ (i : ι) (u : (Mods i).W), D.S ⟨i, u⟩ → ¬ (Mods i).force u A) :
    ¬ (join Mods D).force none (.somehow A) := by
  intro h
  rcases ((join_force_box_iff D A).mp h).1 with hA | ⟨i, u, hS, hA⟩
  · exact hroot hA
  · exact hcone i u hS hA

/-- **`◯∉` at a join** — the refuting world is above the root, in
premise `i`: some world of that component has no `Rm`-successor
forcing `A`.  The premise is stated ENTIRELY inside the component, so
it is exactly a premise refutation. -/
theorem joinBoxRefuteAbove (D : RootData (union Mods)) {A : PLLFormula}
    (i : ι) (a : (Mods i).W)
    (ha : ∀ u, (Mods i).Rm a u → ¬ (Mods i).force u A) :
    ¬ (join Mods D).force none (.somehow A) := by
  intro h
  obtain ⟨u, hu, hA⟩ := ((join_force_box_iff D A).mp h).2 i a
  exact ha u hu hA

/-- **The ◯-POSITIVE rule at a join**, in the complete form: the root
may witness `◯A` through itself or through its cone. -/
theorem joinBoxHolds (D : RootData (union Mods)) {A : PLLFormula}
    (hroot : (join Mods D).force none A ∨
      ∃ (i : ι) (u : (Mods i).W), D.S ⟨i, u⟩ ∧ (Mods i).force u A)
    (habove : ∀ (i : ι) (a : (Mods i).W),
      ∃ u, (Mods i).Rm a u ∧ (Mods i).force u A) :
    (join Mods D).force none (.somehow A) :=
  (join_force_box_iff D A).mpr ⟨hroot, habove⟩

/-- **The two refutation rules are jointly EXACT**: the root refutes
`◯A` iff `◯∈`'s premises hold or `◯∉`'s do.  So the pair is complete
for `◯`-refutation at a join, not merely sound. -/
theorem join_refute_box_iff (D : RootData (union Mods)) (A : PLLFormula) :
    ¬ (join Mods D).force none (.somehow A) ↔
      (¬ (join Mods D).force none A ∧
        ∀ (i : ι) (u : (Mods i).W), D.S ⟨i, u⟩ → ¬ (Mods i).force u A) ∨
      (∃ (i : ι) (a : (Mods i).W),
        ∀ u, (Mods i).Rm a u → ¬ (Mods i).force u A) := by
  classical
  constructor
  · intro h
    by_cases hc : ∃ (i : ι) (a : (Mods i).W),
        ∀ u, (Mods i).Rm a u → ¬ (Mods i).force u A
    · exact .inr hc
    · refine .inl ⟨fun hA => h ?_, fun i u hS hA => h ?_⟩
      · exact joinBoxHolds D (.inl hA) (by
          intro i a
          by_contra hn
          exact hc ⟨i, a, fun u hu hA' => hn ⟨u, hu, hA'⟩⟩)
      · exact joinBoxHolds D (.inr ⟨i, u, hS, hA⟩) (by
          intro i a
          by_contra hn
          exact hc ⟨i, a, fun u hu hA' => hn ⟨u, hu, hA'⟩⟩)
  · rintro (⟨h1, h2⟩ | ⟨i, a, ha⟩)
    · exact joinBoxRefuteHere D h1 h2
    · exact joinBoxRefuteAbove D i a ha

/-! ## 4. Confluence — the side condition, exactly

Decision (a).  `ConeDominates` is the condition; `join_confluent_iff`
proves it is exactly right; the two corollaries say what it gives and
what it costs. -/

/-- **The side condition carried by the join.**  Every proper
`Rm`-successor of the root dominates every world: `∀ s ∈ S, ∀ t,
∃ u. s Rᵢ u ∧ t Rₘ u`. -/
def ConeDominates (Mods : ι → ConstraintModel) (D : RootData (union Mods)) : Prop :=
  ∀ s t : (union Mods).W, D.S s → ∃ u, (union Mods).Ri s u ∧ (union Mods).Rm t u

/-- **Confluence of `addRoot`, exactly.**  The general form, for one
premise model; the audit's `addRoot_not_confluent` is the instance
where the second conjunct fails. -/
theorem addRoot_confluent_iff {M : ConstraintModel} (D : RootData M) :
    MutuallyConfluent (addRoot M D) ↔
      MutuallyConfluent M ∧ ∀ s t : M.W, D.S s → ∃ u, M.Ri s u ∧ M.Rm t u := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a w v h1 h2
      obtain ⟨(_ | u), hu1, hu2⟩ := @h (some a) (some w) (some v) h1 h2
      · exact absurd hu1 not_false
      · exact ⟨u, hu1, hu2⟩
    · intro s t hs
      obtain ⟨(_ | u), hu1, hu2⟩ := @h none (some s) (some t) hs True.intro
      · exact absurd hu1 not_false
      · exact ⟨u, hu1, hu2⟩
  · rintro ⟨hM, hD⟩ (_ | a) (_ | w) (_ | v) h1 h2
    · exact ⟨none, True.intro, True.intro⟩
    · exact ⟨some v, True.intro, M.refl_m v⟩
    · exact ⟨some w, M.refl_i w, h1⟩
    · obtain ⟨u, hu1, hu2⟩ := hD w v h1
      exact ⟨some u, hu1, hu2⟩
    · exact absurd h1 not_false
    · exact absurd h1 not_false
    · exact absurd h2 not_false
    · obtain ⟨u, hu1, hu2⟩ := hM h1 h2
      exact ⟨some u, hu1, hu2⟩

/-- The union is confluent exactly when every premise is. -/
theorem union_confluent_iff :
    MutuallyConfluent (union Mods) ↔ ∀ i, MutuallyConfluent (Mods i) := by
  constructor
  · intro h i a w v h1 h2
    obtain ⟨y, hy1, hy2⟩ := @h ⟨i, a⟩ ⟨i, w⟩ ⟨i, v⟩ (.mk h1) (.mk h2)
    cases hy1 with
    | mk k1 => cases hy2 with
      | mk k2 => exact ⟨_, k1, k2⟩
  · rintro h x w v ⟨h1⟩ ⟨h2⟩
    obtain ⟨u, hu1, hu2⟩ := h _ h1 h2
    exact ⟨⟨_, u⟩, .mk hu1, .mk hu2⟩

/-- **The confluence side condition, exactly.** -/
theorem join_confluent_iff (D : RootData (union Mods)) :
    MutuallyConfluent (join Mods D) ↔
      (∀ i, MutuallyConfluent (Mods i)) ∧ ConeDominates Mods D := by
  rw [join, addRoot_confluent_iff, union_confluent_iff]
  rfl

/-- **What the side condition gives**: confluent premises and an empty
modal cone yield a confluent join — so branching constructions stay in
the class where the ◯-rule is unary. -/
theorem join_confluent_of_cone_empty (D : RootData (union Mods))
    (hcomp : ∀ i, MutuallyConfluent (Mods i))
    (hcone : ∀ x, ¬ D.S x) : MutuallyConfluent (join Mods D) :=
  (join_confluent_iff D).mpr ⟨hcomp, fun s _ hs => absurd hs (hcone s)⟩

/-- **What the side condition costs**: a join that genuinely BRANCHES
— two distinct components, one carrying a cone world and the other
inhabited — cannot be confluent.  So inside the confluent class a
branching root's modal cone is EMPTY, and its only `Rm`-successor is
itself.

This is the join-level form of the audit's `addRoot_not_confluent`,
and it is what makes decision (a) a design rather than a restriction:
on a confluent frame `◯A` at `w` is `∃u. w Rₘ u ∧ u ⊩ A`
(`force_somehow_iff_of_confluent`), so a branching root witnesses `◯A`
through itself — the ◯-rule is unary with the root as witness. -/
theorem join_cone_empty_of_confluent_branching (D : RootData (union Mods))
    (h : MutuallyConfluent (join Mods D)) {i j : ι} (hij : i ≠ j)
    {s : (Mods i).W} (t : (Mods j).W) : ¬ D.S ⟨i, s⟩ := by
  intro hs
  obtain ⟨u, hu1, hu2⟩ := ((join_confluent_iff D).mp h).2 ⟨i, s⟩ ⟨j, t⟩ hs
  exact hij ((Lift.fst_eq hu1).trans (Lift.fst_eq hu2).symm)

/-! ## 5. Degenerate cases

Checked because the audit found `boxHolds` incomplete exactly at a
degenerate case.  The empty and unary joins are proved here; the full
pointwise agreement of a unary join with `addRoot` is SCREENED
(`joinscreen` §E, 5/5 cells), not proved. -/

/-- **The empty join** (no premises): the root is alone, and `◯` is
the identity there — the same fact `solo_force_somehow` records for
the base constructor. -/
theorem join_empty_box_iff (Mods : Empty → ConstraintModel)
    (D : RootData (union Mods)) (A : PLLFormula) :
    (join Mods D).force none (.somehow A) ↔ (join Mods D).force none A := by
  rw [join_force_box_iff]
  constructor
  · rintro ⟨hA | ⟨i, _⟩, _⟩
    · exact hA
    · exact i.elim
  · exact fun hA => ⟨.inl hA, fun i _ => i.elim⟩

/-- **The unary join degenerates to `addRoot`**: with one premise the
modal rule's two conjuncts are literally `boxHoldsRoot`/`boxHolds`'s
premise and the ◯-positive obligation for that single model. -/
theorem join_unit_box_iff (M : ConstraintModel)
    (D : RootData (union (fun _ : Unit => M))) (A : PLLFormula) :
    (join (fun _ : Unit => M) D).force none (.somehow A) ↔
      ((join (fun _ : Unit => M) D).force none A ∨
        ∃ u : M.W, D.S ⟨(), u⟩ ∧ M.force u A) ∧
      (∀ a : M.W, ∃ u, M.Rm a u ∧ M.force u A) := by
  rw [join_force_box_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun a => h2 () a⟩
    rcases h1 with hA | ⟨_, u, hS, hA⟩
    · exact .inl hA
    · exact .inr ⟨u, hS, hA⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun _ a => h2 a⟩
    rcases h1 with hA | ⟨u, hS, hA⟩
    · exact .inl hA
    · exact .inr ⟨(), u, hS, hA⟩

/-! ## 6. Reading a PCLL conclusion off a confluent root

The payoff of decision (a): a confluent construction certifies
underivability in PCLL (`ConfluentU.DerivU`, the logic the acceptance
corpus is stated in) as well as in PLL. -/

/-- A root of a CONFLUENT model that forces `Γ` and refutes `ψ`
certifies PCLL underivability. -/
theorem not_derivU_of_root {N : ConstraintModel} (hc : MutuallyConfluent N)
    {w : N.W} {Γ : List PLLFormula} {ψ : PLLFormula}
    (hΓ : ∀ χ ∈ Γ, N.force w χ) (hψ : ¬ N.force w ψ) :
    ¬ ConfluentU.DerivU Γ ψ :=
  fun h => hψ (ConfluentU.derivU_sound h hc w hΓ)

/-! ## 7. A worked composition — a refutation that PROVABLY needs branching

Target: `ρ6 = ¬¬◯⊥ ∨ ¬◯⊥`, the catalogue's crank-4 class
(docs/pcll-closed-fragment-catalogue.md, `ρ6 = t 5 = q7`).  It was
chosen on evidence, not by guess: `joinscreen` §G enumerates the chain
models exhaustively (2,378 closed chains up to 5 worlds, 5,510
p,q-chains up to 4) and finds NO chain refuting it, while a
two-component join does.  `rho6_needs_branching` then turns that
screen result into a theorem — every world refuting `ρ6`, in any
constraint model whatever, has two `Ri`-INCOMPARABLE successors.  So
this refutation is out of reach of `addRoot` alone, which builds only
chains.

The construction, as a derivation:

    solo(fallible)                    solo(infallible)
    ─────────────── addRoot            ────────────────
    PA ⊩ ◯⊥ at its root                infSolo ⊩ ¬◯⊥
    ──────────────────────────────────────────────── join, cone = ∅
    root ⊮ ¬◯⊥   (witness: PA's root)
    root ⊮ ¬¬◯⊥  (witness: infSolo's world)
    ──────────────────────────────────────────────── ∨-refutation
    root ⊮ ¬¬◯⊥ ∨ ¬◯⊥
    ──────────────────────────────────────────────── not_laxND_of_root
    ⊬ ¬¬◯⊥ ∨ ¬◯⊥            and, the join being confluent,
    ⊬_PCLL ¬¬◯⊥ ∨ ¬◯⊥       by not_derivU_of_root
-/

/-- `◯⊥`. -/
def oBot : PLLFormula := .somehow .falsePLL
/-- `¬◯⊥`. -/
def nOBot : PLLFormula := .ifThen oBot .falsePLL
/-- `¬¬◯⊥`. -/
def nnOBot : PLLFormula := .ifThen nOBot .falsePLL
/-- The catalogue's class `ρ6 = t 5 = q7`, crank 4. -/
def rho6 : PLLFormula := .or nnOBot nOBot

/-- **Refuting `ρ6` REQUIRES branching.**  In any constraint model, a
world refuting `¬¬◯⊥ ∨ ¬◯⊥` has two `Ri`-successors neither of which
is `Ri`-above the other.  (Both directions are blocked by the same
fact: `◯⊥` is hereditary while `¬◯⊥` kills it.)  Hence no chain, and
in particular no `addRoot` tower over a linear premise, refutes it. -/
theorem rho6_needs_branching {N : ConstraintModel} {w : N.W}
    (h : ¬ N.force w rho6) :
    ∃ u v : N.W, N.Ri w u ∧ N.Ri w v ∧ ¬ N.Ri u v ∧ ¬ N.Ri v u := by
  classical
  have h1 : ¬ N.force w nnOBot := fun hA => h (.inl hA)
  have h2 : ¬ N.force w nOBot := fun hA => h (.inr hA)
  have e2 : ∃ v, N.Ri w v ∧ N.force v oBot ∧ ¬ N.force v .falsePLL := by
    by_contra hc
    exact h2 (fun v hv hb => by
      by_contra hf
      exact hc ⟨v, hv, hb, hf⟩)
  obtain ⟨v, hwv, hvo, hvf⟩ := e2
  have e1 : ∃ u, N.Ri w u ∧ N.force u nOBot ∧ ¬ N.force u .falsePLL := by
    by_contra hc
    exact h1 (fun u hu hn => by
      by_contra hf
      exact hc ⟨u, hu, hn, hf⟩)
  obtain ⟨u, hwu, huo, huf⟩ := e1
  refine ⟨u, v, hwu, hwv, fun huv => hvf (huo v huv hvo),
    fun hvu => huf (huo u (N.refl_i u) (N.force_hered hvu hvo))⟩

/-! ### The two premises -/

/-- A single fallible world. -/
def falSolo : ConstraintModel := solo (fun _ => True) True (fun _ _ => True.intro)

/-- The full modal cone over it. -/
def fullCone : RootData falSolo where
  S _ := True
  S_up _ _ := True.intro
  At _ := False
  At_hered h := absurd h not_false

/-- **Premise 1**: an infallible root below a fallible world.  Its
root forces `◯⊥` without being fallible — the model that separates
`◯⊥` from `⊥`.  (Same construction as `Reject.M₁` of `Demo.lean`.) -/
def PA : ConstraintModel := addRoot falSolo fullCone

theorem PA_forces_oBot : PA.force none oBot :=
  boxHolds fullCone ⟨(), True.intro, True.intro⟩
    (fun a => ⟨a, True.intro, True.intro⟩)

theorem PA_root_infallible : ¬ PA.force none .falsePLL := fun h => h

theorem PA_confluent : MutuallyConfluent PA :=
  (addRoot_confluent_iff fullCone).mpr
    ⟨fun _ _ => ⟨(), True.intro, True.intro⟩,
     fun _ _ _ => ⟨(), True.intro, True.intro⟩⟩

/-- **Premise 2**: one infallible world with no atoms.  `◯⊥` holds
nowhere in it, so `¬◯⊥` holds vacuously. -/
def infSolo : ConstraintModel :=
  solo (fun _ => False) False (fun h => absurd h not_false)

theorem infSolo_forces_nOBot : infSolo.force () nOBot := by
  intro v _ hb
  obtain ⟨_, _, hu⟩ := hb v True.intro
  exact hu.elim

theorem infSolo_infallible : ¬ infSolo.force () .falsePLL := fun h => h

theorem infSolo_confluent : MutuallyConfluent infSolo :=
  fun _ _ => ⟨(), True.intro, True.intro⟩

/-! ### The join -/

def prem : Bool → ConstraintModel
  | true => PA
  | false => infSolo

/-- The join data: the EMPTY modal cone, which is what decision (a)
requires of a branching join (`join_cone_empty_of_confluent_branching`). -/
def joinD : RootData (union prem) where
  S _ := False
  S_up h _ := absurd h not_false
  At _ := False
  At_hered h := absurd h not_false

/-- The constructed model: a fresh root below both premises. -/
def MJ : ConstraintModel := join prem joinD

/-- The root refutes `¬◯⊥`: premise 1's root forces `◯⊥` and is
infallible. -/
theorem MJ_refutes_nOBot : ¬ MJ.force none nOBot := by
  intro h
  exact PA_root_infallible
    ((join_force_comp joinD .falsePLL true none).mp
      (h (some ⟨true, none⟩) True.intro
        ((join_force_comp joinD oBot true none).mpr PA_forces_oBot)))

/-- The root refutes `¬¬◯⊥`: premise 2's world forces `¬◯⊥` and is
infallible. -/
theorem MJ_refutes_nnOBot : ¬ MJ.force none nnOBot := by
  intro h
  exact infSolo_infallible
    ((join_force_comp joinD .falsePLL false ()).mp
      (h (some ⟨false, ()⟩) True.intro
        ((join_force_comp joinD nOBot false ()).mpr infSolo_forces_nOBot)))

/-- The root refutes `ρ6`. -/
theorem MJ_refutes_rho6 : ¬ MJ.force none rho6 := by
  rintro (h | h)
  · exact MJ_refutes_nnOBot h
  · exact MJ_refutes_nOBot h

/-- The join is CONFLUENT: both premises are, and the cone is empty
(decision (a)'s side condition, discharged). -/
theorem MJ_confluent : MutuallyConfluent MJ :=
  join_confluent_of_cone_empty joinD
    (fun b => by cases b with
      | true => exact PA_confluent
      | false => exact infSolo_confluent)
    (fun _ h => h)

/-- The root's two incomparable successors, obtained from the
refutation itself rather than checked by hand. -/
theorem MJ_root_branches :
    ∃ u v : MJ.W, MJ.Ri none u ∧ MJ.Ri none v ∧ ¬ MJ.Ri u v ∧ ¬ MJ.Ri v u :=
  rho6_needs_branching MJ_refutes_rho6

/-- **`⊬ ¬¬◯⊥ ∨ ¬◯⊥` — the catalogue's class `ρ6`, by construction.** -/
theorem not_derivable_rho6 : ¬ Nonempty (LaxND [] rho6) :=
  not_laxND_of_root (by simp) MJ_refutes_rho6

/-- **`⊬_PCLL ¬¬◯⊥ ∨ ¬◯⊥`** — the same derivation, read in PCLL,
because the construction stayed confluent. -/
theorem not_derivU_rho6 : ¬ ConfluentU.DerivU [] rho6 :=
  not_derivU_of_root MJ_confluent (by simp) MJ_refutes_rho6

/-! ## 8. Pins

Every line below is transcribed VERBATIM from the build output
(`lake env lean` on `#print axioms`), not written by hand.  The core
of the join — the preservation lemma and all three modal rules — is
AXIOM-FREE, as `Reject/Build.lean`'s core is. -/

/--
info: 'Reject.union_force' does not depend on any axioms
-/
#guard_msgs in
#print axioms union_force

/--
info: 'Reject.Lift.fst_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms Lift.fst_eq

/--
info: 'Reject.join_force_comp' does not depend on any axioms
-/
#guard_msgs in
#print axioms join_force_comp

/--
info: 'Reject.join_force_box_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms join_force_box_iff

/--
info: 'Reject.joinBoxRefuteHere' does not depend on any axioms
-/
#guard_msgs in
#print axioms joinBoxRefuteHere

/--
info: 'Reject.joinBoxRefuteAbove' does not depend on any axioms
-/
#guard_msgs in
#print axioms joinBoxRefuteAbove

/--
info: 'Reject.joinBoxHolds' does not depend on any axioms
-/
#guard_msgs in
#print axioms joinBoxHolds

/--
info: 'Reject.join_refute_box_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms join_refute_box_iff

/--
info: 'Reject.addRoot_confluent_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms addRoot_confluent_iff

/--
info: 'Reject.union_confluent_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms union_confluent_iff

/--
info: 'Reject.join_confluent_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms join_confluent_iff

/--
info: 'Reject.join_confluent_of_cone_empty' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms join_confluent_of_cone_empty

/--
info: 'Reject.join_cone_empty_of_confluent_branching' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms join_cone_empty_of_confluent_branching

/--
info: 'Reject.join_empty_box_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms join_empty_box_iff

/--
info: 'Reject.join_unit_box_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms join_unit_box_iff

/--
info: 'Reject.not_derivU_of_root' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms not_derivU_of_root

/--
info: 'Reject.rho6_needs_branching' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rho6_needs_branching

/--
info: 'Reject.MJ_confluent' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms MJ_confluent

/--
info: 'Reject.MJ_refutes_rho6' does not depend on any axioms
-/
#guard_msgs in
#print axioms MJ_refutes_rho6

/--
info: 'Reject.MJ_root_branches' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MJ_root_branches

/--
info: 'Reject.not_derivable_rho6' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_derivable_rho6

/--
info: 'Reject.not_derivU_rho6' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms not_derivU_rho6

end Reject
