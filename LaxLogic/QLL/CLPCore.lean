/-
# `LaxLogic.QLL.CLPCore` — CLP proofs with constraint leaves, the `◯`-free pass

Step C2 of `docs/qll-clp-review.md` §4.  A CLP program is a list of
Definition 5.1 clauses without `◯`, whose bodies may contain atoms of
*constraint* predicates (`isC B = true`).  A proof of a Σ-goal is a tree of rule
applications whose leaves are constraint atoms, and its **total constraint**
`total p` (Definition 8.1 of the draft) is the conjunction of those leaves.

    CTyped.prv_total :  CTyped isC Θ S p  →  Θ.forms ⊢ total p ⊃ S

This is Corollary 9.8 in its `◯`-free form: the answer constraint of a proof
entails the query.  `active` and `latent` split `total` at clause boundaries
(`total_equiv`); in the `◯` pass `latent` is what the abstract proof extracts.

The same trees are read abstractly in `CLPAbstract.lean`, as proofs of `◯S♯`
from the abstracted program.
-/
import LaxLogic.QLL.HerbrandLLP

namespace LaxLogic.QLL

/-- A proof tree for a Σ-goal: one constructor per rule of Table 2 of the draft,
`top` for `true`. -/
inductive CProof where
  | top
  | cstr (B : String) (ts : List Tm)
  | andI (p q : CProof)
  | orL (p : CProof)
  | orR (p : CProof)
  | exI (t : Tm) (p : CProof)
  | clause (w : Nat) (ts : List Tm) (p : CProof)
  deriving Repr, Inhabited

/-- `p` proves the Σ-goal `S` from the CLP program `Θ`, with constraint atoms
(`isC`) as leaves. -/
inductive CTyped (isC : String → Bool) (Θ : Program) : Form → CProof → Prop
  | top : CTyped isC Θ .top .top
  | cstr {B : String} {ts : List Tm} : isC B = true → CTyped isC Θ (.pred B ts) (.cstr B ts)
  | andI {A B : Form} {p q : CProof} :
      CTyped isC Θ A p → CTyped isC Θ B q → CTyped isC Θ (.and A B) (.andI p q)
  | orL {A B : Form} {p : CProof} : CTyped isC Θ A p → CTyped isC Θ (.or A B) (.orL p)
  | orR {A B : Form} {p : CProof} : CTyped isC Θ B p → CTyped isC Θ (.or A B) (.orR p)
  | exI {A : Form} {p : CProof} (t : Tm) : Tm.lcAt 0 t →
      CTyped isC Θ (A.openAt 0 t) p → CTyped isC Θ (.exists_ A) (.exI t p)
  | clause {c : Clause} {p : CProof} (w : Nat) (ts : List Tm) : Θ[w]? = some c →
      c.modal = false → ts.length = c.arity → (∀ t ∈ ts, Tm.lcAt 0 t) →
      CTyped isC Θ (Form.instAll ts c.body) p →
      CTyped isC Θ (.pred c.head (Tm.instAllList ts (headVars c.arity))) (.clause w ts p)

/-! ## Definition 8.1: total, active and latent constraints -/

/-- The conjunction of the constraint leaves. -/
def CProof.total : CProof → Form
  | .top => .top
  | .cstr B ts => .pred B ts
  | .andI p q => .and p.total q.total
  | .orL p | .orR p | .exI _ p | .clause _ _ p => p.total

/-- The constraint leaves not under a clause application. -/
def CProof.active : CProof → Form
  | .top => .top
  | .cstr B ts => .pred B ts
  | .andI p q => .and p.active q.active
  | .orL p | .orR p | .exI _ p => p.active
  | .clause _ _ _ => .top

/-- The constraint leaves under a clause application. -/
def CProof.latent : CProof → Form
  | .top => .top
  | .cstr _ _ => .top
  | .andI p q => .and p.latent q.latent
  | .orL p | .orR p | .exI _ p => p.latent
  | .clause _ _ p => .and p.latent p.active

/-! ## Soundness: the answer constraint entails the goal -/

/-- Weakening by one assumption. -/
theorem Prv.weaken_cons {Γ : List Form} {A B : Form} (h : Prv Γ A) : Prv (B :: Γ) A :=
  h.weaken fun _ h => List.mem_cons.2 (Or.inr h)

/-- The first assumption. -/
theorem Prv.hd {Γ : List Form} {A : Form} : Prv (A :: Γ) A := .var (List.mem_cons.2 (Or.inl rfl))

/-- **Answer soundness** (the `◯`-free Corollary 9.8). -/
theorem CTyped.prv_total {isC : String → Bool} {Θ : Program} {S : Form} {p : CProof}
    (h : CTyped isC Θ S p) : Prv Θ.forms (.imp p.total S) := by
  induction h with
  | top => exact .impI .topI
  | cstr _ => exact .impI .hd
  | andI _ _ ih₁ ih₂ =>
      exact .impI (.andI (.impE ih₁.weaken_cons (.andE₁ .hd)) (.impE ih₂.weaken_cons (.andE₂ .hd)))
  | orL _ ih => exact .impI (.orI₁ (.impE ih.weaken_cons .hd))
  | orR _ ih => exact .impI (.orI₂ (.impE ih.weaken_cons .hd))
  | exI t ht _ ih => exact .impI (.exI t ht (.impE ih.weaken_cons .hd))
  | @clause c p w ts hc hm hlen hts _ ih =>
      have hmem : c ∈ Θ := List.mem_of_getElem? hc
      have hf : Prv Θ.forms (Form.foralls ts.length (.imp c.body c.headForm)) := by
        rw [hlen]; exact .var (List.mem_map.2 ⟨c, hmem, rfl⟩)
      have hi := Prv.allEs ts hts hf
      rw [Form.instAll_imp] at hi
      have e : Form.instAll ts c.headForm = .pred c.head (Tm.instAllList ts (headVars c.arity)) := by
        unfold Clause.headForm; rw [hm]; exact Form.instAll_pred ts _ _
      rw [e] at hi
      exact .impI (.impE hi.weaken_cons (.impE ih.weaken_cons .hd))

/-- `total = latent ⊗ active`, up to provable equivalence. -/
theorem CProof.total_equiv : ∀ p : CProof,
    Prv [p.total] (.and p.latent p.active) ∧ Prv [.and p.latent p.active] p.total
  | .top => ⟨.andI .topI .topI, .topI⟩
  | .cstr _ _ => ⟨.andI .topI .hd, .andE₂ .hd⟩
  | .andI p q => by
      obtain ⟨hp₁, hp₂⟩ := p.total_equiv
      obtain ⟨hq₁, hq₂⟩ := q.total_equiv
      refine ⟨?_, ?_⟩
      · have lp : Prv [.and p.total q.total] (.and p.latent p.active) :=
          .impE (Prv.impI hp₁ |>.weaken (fun _ h => nomatch h)) (.andE₁ .hd)
        have lq : Prv [.and p.total q.total] (.and q.latent q.active) :=
          .impE (Prv.impI hq₁ |>.weaken (fun _ h => nomatch h)) (.andE₂ .hd)
        exact .andI (.andI (.andE₁ lp) (.andE₁ lq)) (.andI (.andE₂ lp) (.andE₂ lq))
      · have lp : Prv [.and (.and p.latent q.latent) (.and p.active q.active)] p.total :=
          .impE (Prv.impI hp₂ |>.weaken (fun _ h => nomatch h))
            (.andI (.andE₁ (.andE₁ .hd)) (.andE₁ (.andE₂ .hd)))
        have lq : Prv [.and (.and p.latent q.latent) (.and p.active q.active)] q.total :=
          .impE (Prv.impI hq₂ |>.weaken (fun _ h => nomatch h))
            (.andI (.andE₂ (.andE₁ .hd)) (.andE₂ (.andE₂ .hd)))
        exact .andI lp lq
  | .orL p | .orR p | .exI _ p => p.total_equiv
  | .clause _ _ p => by
      obtain ⟨hp₁, hp₂⟩ := p.total_equiv
      have r : Prv [.and (.and p.latent p.active) .top] p.total :=
        .impE (Prv.impI hp₂ |>.weaken (fun _ h => nomatch h)) (.andE₁ .hd)
      exact ⟨.andI hp₁ .topI, r⟩

/-! ## Checking a proof tree -/

/-- A decidable check that `p` proves `S`. -/
def checkC (isC : String → Bool) (Θ : Program) : Form → CProof → Bool
  | .top, .top => true
  | .pred B ts, .cstr B' ts' => isC B && B == B' && ts == ts'
  | .and A B, .andI p q => checkC isC Θ A p && checkC isC Θ B q
  | .or A _, .orL p => checkC isC Θ A p
  | .or _ B, .orR p => checkC isC Θ B p
  | .exists_ A, .exI t p => Tm.lcAtB 0 t && checkC isC Θ (A.openAt 0 t) p
  | .pred P us, .clause w ts p =>
      match Θ[w]? with
      | some c => !c.modal && c.head == P && ts.length == c.arity && ts.all (Tm.lcAtB 0) &&
          us == Tm.instAllList ts (headVars c.arity) && checkC isC Θ (Form.instAll ts c.body) p
      | none => false
  | _, _ => false

/-- `checkC` is sound: a tree it accepts proves the formula. -/
theorem checkC_sound (isC : String → Bool) (Θ : Program) :
    ∀ (p : CProof) (S : Form), checkC isC Θ S p = true → CTyped isC Θ S p
  | .top, S, h => by cases S <;> first | exact .top | exact absurd h (by simp [checkC])
  | .cstr B' ts', S, h => by
      cases S with
      | pred B ts =>
          simp only [checkC, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨hB, rfl⟩, rfl⟩ := h
          exact .cstr hB
      | _ => exact absurd h (by simp [checkC])
  | .andI p q, S, h => by
      cases S with
      | and A B =>
          simp only [checkC, Bool.and_eq_true] at h
          exact .andI (checkC_sound isC Θ p A h.1) (checkC_sound isC Θ q B h.2)
      | _ => exact absurd h (by simp [checkC])
  | .orL p, S, h => by
      cases S with
      | or A B => exact .orL (checkC_sound isC Θ p A h)
      | _ => exact absurd h (by simp [checkC])
  | .orR p, S, h => by
      cases S with
      | or A B => exact .orR (checkC_sound isC Θ p B h)
      | _ => exact absurd h (by simp [checkC])
  | .exI t p, S, h => by
      cases S with
      | exists_ A =>
          simp only [checkC, Bool.and_eq_true] at h
          exact .exI t ((Tm.lcAtB_iff 0 t).1 h.1) (checkC_sound isC Θ p _ h.2)
      | _ => exact absurd h (by simp [checkC])
  | .clause w ts p, S, h => by
      cases S with
      | pred P us =>
          simp only [checkC] at h
          split at h
          · rename_i c hc
            simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true] at h
            obtain ⟨⟨⟨⟨⟨hm, rfl⟩, hlen⟩, hts⟩, rfl⟩, hb⟩ := h
            exact .clause w ts hc hm hlen (fun t ht => (Tm.lcAtB_iff 0 t).1 (hts t ht))
              (checkC_sound isC Θ p _ hb)
          · exact absurd h (by simp)
      | _ => exact absurd h (by simp [checkC])


/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.CTyped.prv_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTyped.prv_total

/-- info: 'LaxLogic.QLL.CProof.total_equiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms CProof.total_equiv

/-- info: 'LaxLogic.QLL.checkC_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkC_sound

end LaxLogic.QLL
