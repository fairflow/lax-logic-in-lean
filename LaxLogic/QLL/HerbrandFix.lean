/-
# `LaxLogic.QLL.HerbrandFix` — `M_P = T_P↑ω`, and `M_P = lfp T_P`

Lloyd's two fixpoint characterisations of the least Herbrand model, items L3
and L4 of `docs/qll-herbrand-horn-plan.md`.

`LHM_iff_Tpow` is the iteration `T_P↑ω`, by recursion on `ℕ`.  `LHM_eq_lfp`
identifies `LHM` with Mathlib's `OrderHom.lfp` of `T_P` on the complete lattice
of Herbrand interpretations; it is a side theorem, kept apart because
`OrderHom.lfp_le` and `OrderHom.map_lfp` depend on `Classical.choice`, and
nothing else in stage H uses it.
-/
import LaxLogic.QLL.HerbrandLLP
import Mathlib.Order.FixedPoints

namespace LaxLogic.QLL

/-! ## Truth of Σ-formulas grows with the interpretation -/

theorem HTrue_mono_aux {I J : String → List Tm → Prop} (hIJ : ∀ p us, I p us → J p us)
    {S : Form} (hS : IsSigma S) :
    ∀ β : List Tm, (herbrand1 I).force S () Tm.fvar β → (herbrand1 J).force S () Tm.fvar β := by
  induction hS with
  | top => intro _ h; exact h
  | pred P ts =>
      intro β h
      show False ∨ J P ((herbrand1 J).evTms Tm.fvar β ts)
      rw [← HFrame.evTms_eq HFrame.one (fun _ => I) (fun _ h => h) HFrame.one (fun _ => J)
        (fun _ h => h) Tm.fvar β ts]
      exact h.imp id (hIJ _ _)
  | and _ _ ih₁ ih₂ => intro β h; exact ⟨ih₁ β h.1, ih₂ β h.2⟩
  | or _ _ ih₁ ih₂ => intro β h; exact h.imp (ih₁ β) (ih₂ β)
  | ex _ ih => intro β h; obtain ⟨d, hd, h⟩ := h; exact ⟨d, hd, ih (d :: β) h⟩

theorem HTrue_mono {I J : String → List Tm → Prop} (hIJ : ∀ p us, I p us → J p us)
    {S : Form} (hS : IsSigma S) (h : HTrue I S) : HTrue J S :=
  HTrue_mono_aux hIJ hS [] h

theorem IsPP.of_openAt : ∀ (A : Form) (k : Nat) (t : Tm), IsPP (A.openAt k t) → IsPP A
  | .top, _, _, _ => .top
  | .pred P ts, _, _, _ => .pred P ts
  | .and A B, k, t, h => by
      change IsPP (.and (A.openAt k t) (B.openAt k t)) at h
      cases h with
      | and h₁ h₂ => exact .and (IsPP.of_openAt A k t h₁) (IsPP.of_openAt B k t h₂)
  | .exists_ A, k, t, h => by
      change IsPP (.exists_ (A.openAt (k + 1) t)) at h
      cases h with
      | ex h => exact .ex (IsPP.of_openAt A (k + 1) t h)
  | .bot, _, _, h => by change IsPP .bot at h; cases h
  | .or A B, k, t, h => by change IsPP (.or (A.openAt k t) (B.openAt k t)) at h; cases h
  | .imp A B, k, t, h => by change IsPP (.imp (A.openAt k t) (B.openAt k t)) at h; cases h
  | .circ q A, k, t, h => by change IsPP (.circ q (A.openAt k t)) at h; cases h
  | .forall_ A, k, t, h => by change IsPP (.forall_ (A.openAt (k + 1) t)) at h; cases h

section
variable {R : String → List Tm → Prop} {P : List Horn}

/-- Everything that holds is primitive positive. -/
theorem Holds.isPP {φ : Form} (d : Holds R P φ) : IsPP φ := by
  induction d with
  | base _ => exact .pred _ _
  | top => exact .top
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | ex t _ _ ih => exact .ex (IsPP.of_openAt _ 0 t ih)
  | fire _ _ _ _ _ => exact .pred _ _

theorem Tp_mono {I J : String → List Tm → Prop} (hIJ : ∀ p us, I p us → J p us) :
    ∀ p us, Tp R P I p us → Tp R P J p us := by
  rintro p us (hr | ⟨h, hh, ts, hlen, hts, hb, hp, hus⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨h, hh, ts, hlen, hts,
      HTrue_mono hIJ (h.body_pp.instAll ts).isSigma hb, hp, hus⟩

/-! ## `T_P↑ω` -/

/-- `T_P↑n`, from the empty interpretation. -/
def Tpow (R : String → List Tm → Prop) (P : List Horn) : Nat → String → List Tm → Prop
  | 0     => fun _ _ => False
  | n + 1 => Tp R P (Tpow R P n)

theorem Tpow_succ_mono : ∀ (n : Nat) p us, Tpow R P n p us → Tpow R P (n + 1) p us
  | 0,     _, _,  h => (h : False).elim
  | n + 1, p, us, h => Tp_mono (Tpow_succ_mono n) p us h

theorem Tpow_mono {m n : Nat} (hmn : m ≤ n) : ∀ p us, Tpow R P m p us → Tpow R P n p us := by
  induction hmn with
  | refl => exact fun _ _ h => h
  | step _ ih => exact fun p us h => Tpow_succ_mono _ p us (ih p us h)

theorem Tpow_le_LHM (hR : ∀ p us, R p us → Tm.lcAtList 0 us) (hP : ∀ h ∈ P, h.WF) :
    ∀ (n : Nat) p us, Tpow R P n p us → LHM R P p us
  | 0,     _, _,  h => (h : False).elim
  | n + 1, p, us, h => (Tp_LHM hR hP p us).1 (Tp_mono (Tpow_le_LHM hR hP n) p us h)

/-- `M_P = T_P↑ω`. -/
theorem LHM_iff_Tpow (hR : ∀ p us, R p us → Tm.lcAtList 0 us) (hP : ∀ h ∈ P, h.WF)
    (p : String) (us : List Tm) : LHM R P p us ↔ ∃ n, Tpow R P n p us := by
  constructor
  · intro hl
    have key : ∀ {φ : Form}, Holds R P φ → ∃ n, HTrue (Tpow R P n) φ := by
      intro φ d
      induction d with
      | base hr => exact ⟨1, (HTrue_pred (hR _ _ hr)).2 (Or.inl hr)⟩
      | top => exact ⟨0, trivial⟩
      | and d₁ d₂ ih₁ ih₂ =>
          obtain ⟨m, hm⟩ := ih₁
          obtain ⟨n, hn⟩ := ih₂
          exact ⟨max m n, HTrue_and.2
            ⟨HTrue_mono (Tpow_mono (Nat.le_max_left m n)) d₁.isPP.isSigma hm,
             HTrue_mono (Tpow_mono (Nat.le_max_right m n)) d₂.isPP.isSigma hn⟩⟩
      | ex t ht _ ih =>
          obtain ⟨n, hn⟩ := ih
          exact ⟨n, HTrue_exists.2 ⟨t, ht, hn⟩⟩
      | @fire h ts hh hlen hts _ ih =>
          obtain ⟨n, hn⟩ := ih
          exact ⟨n + 1, (HTrue_pred (Tm.lcAtList_instAllList ts h.args hts
            (by rw [hlen]; exact (hP h hh).2))).2 (Or.inr ⟨h, hh, ts, hlen, hts, hn, rfl, rfl⟩)⟩
    obtain ⟨n, hn⟩ := key (φ := .pred p us) hl
    exact ⟨n, (HTrue_pred (LHM_lc hR hP hl)).1 hn⟩
  · rintro ⟨n, hn⟩
    exact Tpow_le_LHM hR hP n p us hn

/-! ## `M_P = lfp T_P`, in Mathlib's terms -/

/-- `T_P` as a monotone map on Herbrand interpretations. -/
def TpHom (R : String → List Tm → Prop) (P : List Horn) :
    (String → List Tm → Prop) →o (String → List Tm → Prop) :=
  ⟨Tp R P, fun _ _ hIJ => Tp_mono hIJ⟩

theorem LHM_eq_lfp (hR : ∀ p us, R p us → Tm.lcAtList 0 us) (hP : ∀ h ∈ P, h.WF) :
    LHM R P = OrderHom.lfp (TpHom R P) := by
  have e := OrderHom.map_lfp (TpHom R P)
  apply le_antisymm
  · intro p us hl
    exact LHM_least hR hP (I := OrderHom.lfp (TpHom R P)) (fun p us h => e.le p us h) p us hl
  · exact OrderHom.lfp_le (TpHom R P) fun p us h => (Tp_LHM hR hP p us).1 h

end

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.HTrue_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms HTrue_mono

/-- info: 'LaxLogic.QLL.Holds.isPP' does not depend on any axioms -/
#guard_msgs in #print axioms Holds.isPP

/-- info: 'LaxLogic.QLL.Tp_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Tp_mono

/-- info: 'LaxLogic.QLL.LHM_iff_Tpow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms LHM_iff_Tpow

/-- info: 'LaxLogic.QLL.LHM_eq_lfp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LHM_eq_lfp

end LaxLogic.QLL
