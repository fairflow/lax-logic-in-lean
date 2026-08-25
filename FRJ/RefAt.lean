/-
# `RefAt` — refutations a join root certifies from its own shape

The repair of the FRJ(◯) incompleteness witnesses #80/#81
(`docs/refat-plan.md`; the failure analysis is the 2026-08-25 session
report).  A barren join creates a root `r` with four properties the
soundness proof already carries: `r` refutes every premise right formula
(Υ), forces its own context, has modal cone `{r}`, and is infallible.
`RefAt Υ ctx` is the closure of Υ under the refutations those four facts
license:

    C ∈ Υ                                (the premise mechanism)
    ⊥                                    (`r` is infallible)
    A ⊃ B   if A ∈ Cl(ctx), B ∈ RefAt    (`r` itself is the witness)
    ◯Z      if Z ∈ RefAt                 (cone = {r}; BARREN roots only,
                                          gated by the `cone` flag)
    Z₁ ∨ Z₂ if both;  Z₁ ∧ Z₂ if either

The semantic content is `refAt_refutes` at the end of this file; the
stratified retention certificate `KeptChain` is what the V-joins of
`FRJ/CalculusV.lean` consume.  The stratification is load-bearing: a
SELF-referential retention condition (each kept implication's antecedent
`RefAt` over the WHOLE final context) admits mutually-justifying kept
pairs with no soundness argument, so each link may cite only the base
context and the links BEFORE it.
-/
import FRJ.Basic

namespace FRJ

open Form

/-- `RefAt cone Υ ctx X`: the new root refutes `X`.  `cone = true` means
the root's modal cone is the root itself (a barren join), enabling the
`◯`-clause. -/
inductive RefAt (cone : Bool) (Υ ctx : List Form) : Form → Prop
  | ups {C : Form} : C ∈ Υ → RefAt cone Υ ctx C
  | bot : RefAt cone Υ ctx .bot
  | imp {A B : Form} : Clo ctx A → RefAt cone Υ ctx B →
      RefAt cone Υ ctx (.imp A B)
  | circ {Z : Form} : cone = true → RefAt cone Υ ctx Z →
      RefAt cone Υ ctx (.circ Z)
  | or {Z₁ Z₂ : Form} : RefAt cone Υ ctx Z₁ → RefAt cone Υ ctx Z₂ →
      RefAt cone Υ ctx (.or Z₁ Z₂)
  | andL {Z₁ Z₂ : Form} : RefAt cone Υ ctx Z₁ →
      RefAt cone Υ ctx (.and Z₁ Z₂)
  | andR {Z₁ Z₂ : Form} : RefAt cone Υ ctx Z₂ →
      RefAt cone Υ ctx (.and Z₁ Z₂)

/-- `RefAt` grows with its context (only the `imp` clause consults it,
through `Clo`, which is monotone) — and with Υ. -/
theorem refAt_mono {cone : Bool} {Υ Υ' ctx ctx' : List Form}
    (hu : Υ ⊆ Υ') (hc : ctx ⊆ ctx') {X : Form} :
    RefAt cone Υ ctx X → RefAt cone Υ' ctx' X := by
  intro h
  induction h with
  | ups h => exact .ups (hu h)
  | bot => exact .bot
  | imp hA _ ih => exact .imp (clo_mono hc hA) ih
  | circ hcone _ ih => exact .circ hcone ih
  | or _ _ ih₁ ih₂ => exact .or ih₁ ih₂
  | andL _ ih => exact .andL ih
  | andR _ ih => exact .andR ih

/-- Decision procedure for `RefAt`. -/
def refAtB (cone : Bool) (Υ ctx : List Form) : Form → Bool
  | .bot => true
  | .imp A B =>
      decide (Form.imp A B ∈ Υ) || (cloB ctx A && refAtB cone Υ ctx B)
  | .circ Z => decide (Form.circ Z ∈ Υ) || (cone && refAtB cone Υ ctx Z)
  | .or Z₁ Z₂ =>
      decide (Form.or Z₁ Z₂ ∈ Υ) ||
        (refAtB cone Υ ctx Z₁ && refAtB cone Υ ctx Z₂)
  | .and Z₁ Z₂ =>
      decide (Form.and Z₁ Z₂ ∈ Υ) ||
        refAtB cone Υ ctx Z₁ || refAtB cone Υ ctx Z₂
  | .atom p => decide (Form.atom p ∈ Υ)

theorem refAtB_iff {cone : Bool} {Υ ctx : List Form} :
    ∀ {X : Form}, refAtB cone Υ ctx X = true ↔ RefAt cone Υ ctx X := by
  intro X
  induction X with
  | atom p =>
      simp only [refAtB, decide_eq_true_eq]
      exact ⟨.ups, fun h => by
        cases h with | ups h => exact h⟩
  | bot => simp only [refAtB]; exact ⟨fun _ => .bot, fun _ => trivial⟩
  | and Z₁ Z₂ ih₁ ih₂ =>
      simp only [refAtB, Bool.or_eq_true, decide_eq_true_eq, ih₁, ih₂]
      constructor
      · rintro ((h | h) | h)
        · exact .ups h
        · exact .andL h
        · exact .andR h
      · intro h
        cases h with
        | ups h => exact Or.inl (Or.inl h)
        | andL h => exact Or.inl (Or.inr h)
        | andR h => exact Or.inr h
  | or Z₁ Z₂ ih₁ ih₂ =>
      simp only [refAtB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        ih₁, ih₂]
      constructor
      · rintro (h | ⟨h₁, h₂⟩)
        · exact .ups h
        · exact .or h₁ h₂
      · intro h
        cases h with
        | ups h => exact Or.inl h
        | or h₁ h₂ => exact Or.inr ⟨h₁, h₂⟩
  | imp A B ihA ihB =>
      simp only [refAtB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        cloB_iff, ihB]
      constructor
      · rintro (h | ⟨hA, hB⟩)
        · exact .ups h
        · exact .imp hA hB
      · intro h
        cases h with
        | ups h => exact Or.inl h
        | imp hA hB => exact Or.inr ⟨hA, hB⟩
  | circ Z ih =>
      simp only [refAtB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro (h | ⟨hc, hZ⟩)
        · exact .ups h
        · exact .circ hc hZ
      · intro h
        cases h with
        | ups h => exact Or.inl h
        | circ hc hZ => exact Or.inr ⟨hc, hZ⟩

instance decRefAt (cone : Bool) (Υ ctx : List Form) (X : Form) :
    Decidable (RefAt cone Υ ctx X) :=
  decidable_of_iff _ refAtB_iff

/-! ## The stratified retention certificate -/

/-- `KeptChain Υ base pool kept`: the kept zone, as a chain.  Each link
is an implication drawn from `pool` (the joint second-zone implications
`Θ^⊃∩`), whose antecedent the root refutes — certified by `RefAt` over
the BASE context plus the links already in place.  The list grows at the
head, so the tail is the earlier part of the chain. -/
inductive KeptChain (Υ base pool : List Form) : List Form → Prop
  | nil : KeptChain Υ base pool []
  | cons {Y B : Form} {rest : List Form} :
      KeptChain Υ base pool rest →
      Form.imp Y B ∈ pool →
      RefAt true Υ (base ++ rest) Y →
      KeptChain Υ base pool (Form.imp Y B :: rest)

theorem keptChain_subset {Υ base pool kept : List Form}
    (h : KeptChain Υ base pool kept) : kept ⊆ pool := by
  induction h with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons _ hmem _ ih =>
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · exact h ▸ hmem
      · exact ih h

theorem keptChain_isImp {Υ base pool kept : List Form}
    (h : KeptChain Υ base pool kept) : ∀ X ∈ kept, X.isImp = true := by
  induction h with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons _ _ _ ih =>
      intro X hX
      rcases List.mem_cons.mp hX with h | h
      · subst h; rfl
      · exact ih X h

/-- The paper's `Θ^⊃/Υ` is a chain in ANY order: every antecedent is in
Υ, which is the context-free base clause of `RefAt`. -/
theorem keptChain_of_ups {Υ base pool : List Form} :
    ∀ {kept : List Form},
      (∀ X ∈ kept, X ∈ pool) →
      (∀ {A B : Form}, Form.imp A B ∈ kept → A ∈ Υ) →
      (∀ X ∈ kept, X.isImp = true) →
      KeptChain Υ base pool kept
  | [], _, _, _ => .nil
  | X :: rest, hpool, hups, himp => by
      match X, himp X List.mem_cons_self with
      | .imp A B, _ =>
          exact .cons
            (keptChain_of_ups (fun x hx => hpool x (List.mem_cons_of_mem _ hx))
              (fun h => hups (List.mem_cons_of_mem _ h))
              (fun x hx => himp x (List.mem_cons_of_mem _ hx)))
            (hpool _ List.mem_cons_self)
            (.ups (hups List.mem_cons_self))

/-- Decision procedure for `KeptChain` (the certificate is checked link
by link). -/
def keptChainB' (Υ base pool : List Form) : List Form → Bool
  | [] => true
  | X :: rest =>
      match X with
      | .imp Y _ =>
          keptChainB' Υ base pool rest && decide (X ∈ pool) &&
            refAtB true Υ (base ++ rest) Y
      | _ => false

theorem keptChainB'_iff {Υ base pool : List Form} :
    ∀ {kept : List Form},
      keptChainB' Υ base pool kept = true ↔ KeptChain Υ base pool kept := by
  intro kept
  induction kept with
  | nil => simp only [keptChainB']; exact ⟨fun _ => .nil, fun _ => trivial⟩
  | cons X rest ih =>
      cases X with
      | imp Y B =>
          simp only [keptChainB', Bool.and_eq_true, decide_eq_true_eq, ih,
            refAtB_iff]
          constructor
          · rintro ⟨⟨hrest, hmem⟩, hY⟩
            exact .cons hrest hmem hY
          · intro h
            cases h with
            | cons hrest hmem hY => exact ⟨⟨hrest, hmem⟩, hY⟩
      | atom p =>
          simp only [keptChainB']
          exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
      | bot =>
          simp only [keptChainB']
          exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
      | and Z₁ Z₂ =>
          simp only [keptChainB']
          exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
      | or Z₁ Z₂ =>
          simp only [keptChainB']
          exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
      | circ Z =>
          simp only [keptChainB']
          exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩

instance decKeptChain (Υ base pool kept : List Form) :
    Decidable (KeptChain Υ base pool kept) :=
  decidable_of_iff _ keptChainB'_iff

/-! ## The computed chain (the engine's discovery order)

A greedy fixpoint: repeatedly adopt any pool implication whose antecedent
the current context certifies.  `pool.length` rounds suffice; the result
carries its own `KeptChain` certificate. -/

def growChain (Υ base pool : List Form) : Nat → List Form → List Form
  | 0, acc => acc
  | fuel + 1, acc =>
      match pool.find? (fun f =>
        match f with
        | .imp Y _ => !decide (f ∈ acc) && refAtB true Υ (base ++ acc) Y
        | _ => false) with
      | some f => growChain Υ base pool fuel (f :: acc)
      | none => acc

/-- The chain the engine keeps: greedy, fuelled by the pool size. -/
def keptOf (Υ base pool : List Form) : List Form :=
  growChain Υ base pool pool.length []

theorem growChain_ok {Υ base pool : List Form} :
    ∀ (fuel : Nat) {acc : List Form}, KeptChain Υ base pool acc →
      KeptChain Υ base pool (growChain Υ base pool fuel acc)
  | 0, acc, h => h
  | fuel + 1, acc, h => by
      simp only [growChain]
      cases hf : pool.find? (fun f =>
        match f with
        | .imp Y _ => !decide (f ∈ acc) && refAtB true Υ (base ++ acc) Y
        | _ => false) with
      | none => exact h
      | some f =>
          have hp := List.find?_some hf
          have hmem := List.mem_of_find?_eq_some hf
          cases f with
          | imp Y B =>
              simp only [Bool.and_eq_true, Bool.not_eq_true',
                decide_eq_false_iff_not] at hp
              exact growChain_ok fuel (.cons h hmem (refAtB_iff.mp hp.2))
          | atom p => simp at hp
          | bot => simp at hp
          | and Z₁ Z₂ => simp at hp
          | or Z₁ Z₂ => simp at hp
          | circ Z => simp at hp

theorem keptOf_ok (Υ base pool : List Form) :
    KeptChain Υ base pool (keptOf Υ base pool) :=
  growChain_ok _ .nil

/-! ## The semantic content -/

/-- **`RefAt` members are refuted at the root.**  The four hypotheses are
the invariants a barren join's soundness case already carries: the root
refutes every premise right formula, forces its context, is its own
modal cone, and is infallible. -/
theorem refAt_refutes {K : Kripke} {r : K.W} {Υ ctx : List Form}
    (hups : ∀ C ∈ Υ, ¬ K.force r C)
    (hctx : K.forces r ctx)
    (hcone : ∀ c, K.Rm r c → c = r)
    (hinf : ¬ K.Fal r) :
    ∀ {X : Form}, RefAt true Υ ctx X → ¬ K.force r X := by
  intro X h
  induction h with
  | ups h => exact hups _ h
  | bot => exact hinf
  | imp hA _ ih =>
      intro hf
      exact ih (hf r (K.le_refl r) (clo_forces hctx hA))
  | circ _ _ ih =>
      intro hf
      obtain ⟨c, hrc, hc⟩ := hf r (K.le_refl r)
      exact ih ((hcone c hrc) ▸ hc)
  | or _ _ ih₁ ih₂ =>
      intro hf
      rcases hf with h | h
      · exact ih₁ h
      · exact ih₂ h
  | andL _ ih => exact fun hf => ih hf.1
  | andR _ ih => exact fun hf => ih hf.2

end FRJ
