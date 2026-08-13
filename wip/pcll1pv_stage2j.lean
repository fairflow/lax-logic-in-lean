/-
STAGE 2, part (j): CLOSING `CornerCoreW`.

The corner recursion, on strictly decreasing canonical depth.  At the
current base pair `(k₁, m₁)` (all-level agreement, by collapse
promotion) with the `Rᵢ`-anchored corner seed `u₁`:

* **promised `⊥`** at the trace: fallible realisers on both sides;
  the M-side fallible witness is JOINED with the seed by directedness,
  and fallibility survives the join by `Rᵢ`-heredity — `top` at the
  fallible realiser's trace, which covers everything.
* **promise-stable** trace: the ANCHORED witness clause
  (`agree_mwitN_anchored`) grows the seed to a linked partner; the
  K-partner keeps the trace by `trace_const_of_stable`, the link
  promotes (collapse), and the reflexive proper triple answers at the
  current trace itself (which equals its promise set).
* **unstable**: a promise realiser `κS` (directedness fold over the
  finite promise set) seeds the K-side witness clause; the output
  `κh ⊒ₘ k₁` realises EVERY current promise — a strict trace growth —
  and the recursion descends at `(κh, mh)` with the seed re-joined
  above the new base.  `RmC` chains along `traceC_mforth`; coverage
  chains by monotonicity of the promise set.

Depth 1 never recurses: its val is `cl \ {⊥}`, which contains `◯⊥`,
so the promised-`⊥` branch fires.  Everything is conditional only on
`ClosedCollapse 6` — the same single certificate obligation as
`StableCore`.
-/
import wip.pcll1pv_stage2i

namespace PLLND
open FinComp
namespace SemUI

open Classical

variable {p : String} {K M : ConstraintModel}

/-- Val-equal canonical worlds are `RmC`-related (the `RmC_refl`
argument transported across the equality). -/
theorem rmC_of_val_eq {cl : Finset PLLFormula}
    {Δ Δ' : (canonFinC cl).W} (heq : Δ.1.val = Δ'.1.val) :
    (canonFinC cl).Rm Δ Δ' := by
  refine ⟨fun χ hχ => heq ▸ hχ, fun χ hbox hχ => ?_⟩
  rw [← heq] at hχ
  cases χ with
  | somehow ψ => exact hχ
  | prop a => exact boxUnit (T := ⟨Δ.1, Δ.2.1⟩) hbox hχ
  | falsePLL => exact boxUnit (T := ⟨Δ.1, Δ.2.1⟩) hbox hχ
  | and a b => exact boxUnit (T := ⟨Δ.1, Δ.2.1⟩) hbox hχ
  | or a b => exact boxUnit (T := ⟨Δ.1, Δ.2.1⟩) hbox hχ
  | ifThen a b => exact boxUnit (T := ⟨Δ.1, Δ.2.1⟩) hbox hχ

/-- The promise set is determined by (and monotone in) the val. -/
theorem obInv_val_mono {cl : Finset PLLFormula} {hadeq : OBoxAdeq cl}
    {Δ Δ' : (canonFinC cl).W} (hsub : Δ.1.val ⊆ Δ'.1.val) :
    (obInvW hadeq Δ).1.val ⊆ (obInvW hadeq Δ').1.val := by
  intro χ hχ
  obtain ⟨hχcl, hbox⟩ := obInvFT_val_iff.mp hχ
  exact obInvFT_val_iff.mpr ⟨hχcl, hsub hbox⟩

/-- Depth 1 promises `⊥`: the val is `cl \ {⊥}`, which contains `◯⊥`. -/
theorem obot_of_depth_one {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl)
    (hcl : SubClosed cl) {Δ : (canonFinC cl).W}
    (hd1 : canonDepthC cl Δ = 1)
    (hbot : PLLFormula.falsePLL ∉ Δ.1.val) :
    (PLLFormula.falsePLL).somehow ∈ Δ.1.val := by
  have hsub : Δ.1.val ⊆ cl := Δ.2.1.2.1.1
  have hcard : (cl \ Δ.1.val).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    exact hd1
  have hbotmem : PLLFormula.falsePLL ∈ cl \ Δ.1.val :=
    Finset.mem_sdiff.mpr ⟨hcl.bot, hbot⟩
  have hsingle : cl \ Δ.1.val = {PLLFormula.falsePLL} := by
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
    rw [hx] at hbotmem ⊢
    rw [Finset.mem_singleton.mp hbotmem]
  by_contra hnb
  have hboxcl : (PLLFormula.falsePLL).somehow ∈ cl := hadeq _ hcl.bot
  have : (PLLFormula.falsePLL).somehow ∈ cl \ Δ.1.val :=
    Finset.mem_sdiff.mpr ⟨hboxcl, hnb⟩
  rw [hsingle, Finset.mem_singleton] at this
  exact PLLFormula.noConfusion this

/-- **The promise realiser**: a single `Rₘ`-successor realising every
member of a finite set of promised formulas, by the directedness fold.
`somehow`-promises ride along hereditarily; the rest come from bare
possibility. -/
theorem promise_realiser (hK : MutuallyConfluent K) {k : K.W}
    (S : Finset PLLFormula) (hS : ∀ χ ∈ S, K.force k (boxOf χ)) :
    ∃ κ, K.Rm k κ ∧ ∀ χ ∈ S, K.force κ χ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨k, K.refl_m k, by simp⟩
  | insert χ S hnot ih =>
      obtain ⟨κS, hkκS, hκS⟩ :=
        ih (fun χ' hχ' => hS χ' (Finset.mem_insert_of_mem hχ'))
      have hboxχ : K.force k (boxOf χ) := hS χ (Finset.mem_insert_self χ S)
      have hreal : ∃ κχ, K.Rm k κχ ∧ K.force κχ χ := by
        cases χ with
        | somehow ψ => exact ⟨k, K.refl_m k, hboxχ⟩
        | prop a => exact (force_somehow_iff_of_confluent hK).mp hboxχ
        | falsePLL => exact (force_somehow_iff_of_confluent hK).mp hboxχ
        | and a b => exact (force_somehow_iff_of_confluent hK).mp hboxχ
        | or a b => exact (force_somehow_iff_of_confluent hK).mp hboxχ
        | ifThen a b => exact (force_somehow_iff_of_confluent hK).mp hboxχ
      obtain ⟨κχ, hkκχ, hκχ⟩ := hreal
      obtain ⟨κ2, hkκ2, hκSκ2, hκχκ2⟩ := confluent_directed hK hkκS hkκχ
      refine ⟨κ2, hkκ2, fun χ' hχ' => ?_⟩
      rcases Finset.mem_insert.mp hχ' with rfl | hχ'
      · exact K.force_hered (K.sub_mi hκχκ2) hκχ
      · exact K.force_hered hκSκ2 (hκS χ' hχ')

/-- **The corner descent**: from an all-level base pair and an
`Rₘ`-seed, a triple at an `RmC`-successor of the base trace covering
its ENTIRE promise set, `Rᵢ`-anchored at the seed and `Rₘ`-anchored at
the base. -/
theorem corner_descend {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl)
    (hcl : SubClosed cl) (hcol : ClosedCollapse 6)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M)
    (k₁ : K.W) (m₁ u₁ : M.W)
    (hlink : ∀ β, lvlZ K M β k₁ m₁) (hmu₁ : M.Rm m₁ u₁) :
    ∃ (u₃ : M.W) (Δu : (canonFinC cl).W),
      M.Ri u₁ u₃ ∧ M.Rm m₁ u₃ ∧
      (∀ χ ∈ (obInvW hadeq (traceC hK cl k₁)).1.val, χ ∈ Δu.1.val) ∧
      (canonFinC cl).Rm (traceC hK cl k₁) Δu ∧
      WitTripleC cl (lvlB (p := p) hK hM hPK hPM) Δu u₃ := by
  by_cases hOb : (PLLFormula.falsePLL).somehow ∈ (traceC hK cl k₁).1.val
  · -- PROMISED ⊥: fallible realisers, join the seed, `top`
    have hkbox : K.force k₁ ((PLLFormula.falsePLL).somehow) :=
      (mem_traceT_val.mp hOb).2
    obtain ⟨κ₀, hkκ₀, hκ₀F⟩ :=
      (force_somehow_iff_of_confluent hK).mp hkbox
    have hmbox : M.force m₁ ((PLLFormula.falsePLL).somehow) :=
      (hlink 2 ((PLLFormula.falsePLL).somehow)
        (by simp [crank])
        (by intro a ha; simp [PLLFormula.atoms] at ha)).mp hkbox
    obtain ⟨uh, hm₁uh, huhF⟩ :=
      (force_somehow_iff_of_confluent hM).mp hmbox
    obtain ⟨u₄, hm₁u₄, hRiu₁u₄, hRmuhu₄⟩ := confluent_directed hM hmu₁ hm₁uh
    have hu₄F : u₄ ∈ M.F := M.hered_F (M.sub_mi hRmuhu₄) huhF
    refine ⟨u₄, traceC hK cl κ₀, hRiu₁u₄, hm₁u₄, ?_,
      traceC_mforth hK hkκ₀,
      .top (mem_traceT_val.mpr
        ⟨hcl.bot, K.force_of_fallible hκ₀F⟩) hu₄F⟩
    intro χ hχ
    obtain ⟨hχcl, _⟩ := obInvFT_val_iff.mp hχ
    exact mem_traceT_val.mpr ⟨hχcl, K.force_of_fallible hκ₀F⟩
  by_cases hst : PromiseStable hadeq (traceC hK cl k₁)
  · -- STABLE: the anchored witness clause + trace-constancy + promotion
    have hψt : M.force u₁ (PLLFormula.ifThen .falsePLL .falsePLL) :=
      fun _v _hv h => h
    obtain ⟨u₂, t, hm₁u₂, hRiu₁u₂, _hψ₂, hk₁t, hres⟩ :=
      agree_mwitN_anchored (V := (∅ : Finset String)) (α := 3) hK hM
        (fun χ hc ha => hlink 4 χ (by omega) ha) u₁ hmu₁ hψt
    rcases hres with hZ2 | ⟨htF, _⟩
    · have hall : ∀ β, lvlZ K M β t u₂ :=
        lvlZ_promote hcol hK hM (α := 3) (by omega) hZ2
      have htr : (traceT K cl t).val = (traceC hK cl k₁).1.val :=
        trace_const_of_stable hK hst rfl hk₁t
      refine ⟨u₂, traceC hK cl k₁, hRiu₁u₂, hm₁u₂, ?_,
        (canonFinC cl).refl_m _,
        .proper t t u₂ htr htr (M.refl_i u₂)
          (hall (2 * canonDepthC cl (traceC hK cl k₁) + 1))
          (hall (2 * canonDepthC cl (traceC hK cl k₁))) (K.refl_i t)⟩
      intro χ hχ
      have hst' : (obInvW hadeq (traceC hK cl k₁)).1.val =
          (traceC hK cl k₁).1.val := hst
      rw [← hst']
      exact hχ
    · -- fallible K-partner would put ◯⊥ in the trace — excluded here
      exfalso
      have : K.force k₁ ((PLLFormula.falsePLL).somehow) :=
        (force_somehow_iff_of_confluent hK).mpr
          ⟨t, hk₁t, K.force_of_fallible htF⟩
      exact hOb (mem_traceT_val.mpr ⟨hadeq _ hcl.bot, this⟩)
  · -- UNSTABLE: realise every promise, descend at the grown trace
    have hboxes : ∀ χ ∈ (obInvW hadeq (traceC hK cl k₁)).1.val,
        K.force k₁ (boxOf χ) := by
      intro χ hχ
      obtain ⟨_, hbox⟩ := obInvFT_val_iff.mp hχ
      exact (mem_traceT_val.mp hbox).2
    obtain ⟨κS, hkκS, hκS⟩ :=
      promise_realiser hK (obInvW hadeq (traceC hK cl k₁)).1.val hboxes
    have hpsiS : K.force κS
        (bigAnd (obInvW hadeq (traceC hK cl k₁)).1.val.toList) :=
      (force_bigAnd_iff K κS _).mpr
        (fun D hD => hκS D (Finset.mem_toList.mp hD))
    obtain ⟨κh, mh, hkκh, hψκh, hm₁mh, hres⟩ :=
      agree_mwit (V := (∅ : Finset String)) (α := 3) hK hM
        (fun χ hc ha => hlink 4 χ (by omega) ha) ⟨κS, hkκS, hpsiS⟩
    rcases hres with hZ2 | ⟨hκhF, _⟩
    · have hall : ∀ β, lvlZ K M β κh mh :=
        lvlZ_promote hcol hK hM (α := 3) (by omega) hZ2
      -- strict trace growth: some broken promise is realised
      obtain ⟨χ₀, hχ₀cl, hχ₀box, hχ₀not⟩ :=
        exists_broken_promise (hadeq := hadeq) hst
      have hχ₀κh : K.force κh χ₀ :=
        (force_bigAnd_iff K κh _).mp hψκh χ₀
          (Finset.mem_toList.mpr (obInvFT_val_iff.mpr ⟨hχ₀cl, hχ₀box⟩))
      have hsub : (traceC hK cl k₁).1.val ⊆ (traceC hK cl κh).1.val :=
        (traceC_mforth (cl := cl) hK hkκh).1
      have hne : (traceC hK cl k₁).1.val ≠ (traceC hK cl κh).1.val := by
        intro heq
        exact hχ₀not (heq ▸ mem_traceT_val.mpr ⟨hχ₀cl, hχ₀κh⟩)
      have hlt : canonDepthC cl (traceC hK cl κh) <
          canonDepthC cl (traceC hK cl k₁) := canonDepthC_lt hsub hne
      obtain ⟨u₄, hm₁u₄, hRiu₁u₄, hRmmhu₄⟩ :=
        confluent_directed hM hmu₁ hm₁mh
      obtain ⟨u₃, Δu, hRiu₄u₃, hRmmhu₃, hcov', hRmC', htrip⟩ :=
        corner_descend hadeq hcl hcol hK hM hPK hPM κh mh u₄ hall hRmmhu₄
      refine ⟨u₃, Δu, M.trans_i hRiu₁u₄ hRiu₄u₃,
        M.trans_m hm₁mh hRmmhu₃, ?_,
        (canonFinC cl).trans_m (traceC_mforth hK hkκh) hRmC', htrip⟩
      intro χ hχ
      exact hcov' χ (obInv_val_mono hsub hχ)
    · -- fallible K-witness would put ◯⊥ in the trace — excluded here
      exfalso
      have : K.force k₁ ((PLLFormula.falsePLL).somehow) :=
        (force_somehow_iff_of_confluent hK).mpr
          ⟨κh, hkκh, K.force_of_fallible hκhF⟩
      exact hOb (mem_traceT_val.mpr ⟨hadeq _ hcl.bot, this⟩)
termination_by canonDepthC cl (traceC hK cl k₁)
decreasing_by exact hlt

/-- **`CornerCoreW`, closed** modulo `ClosedCollapse 6`. -/
theorem cornerCoreW_of_collapse {cl : Finset PLLFormula}
    (hadeq : OBoxAdeq cl) (hcl : SubClosed cl) (hcol : ClosedCollapse 6)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M) :
    CornerCoreW cl hadeq (lvlB (p := p) hK hM hPK hPM) := by
  intro Δ Δb m ht hbot _hbotb hdom u hmu k kv _hΔk _hkkv _hZkv
  have hd : 1 ≤ canonDepthC cl Δ := canonDepthC_pos hcl hbot
  cases ht with
  | top hbot' _ => exact absurd hbot' hbot
  | proper k₁' k₁ m₁' hΔk₁ hΔk₁' him hZ' hZ hik =>
      by_cases hOb : (PLLFormula.falsePLL).somehow ∈ Δ.1.val
      · -- promised ⊥ at Δ itself: close at the fallible trace
        have hkbox : K.force k₁ ((PLLFormula.falsePLL).somehow) := by
          rw [← hΔk₁] at hOb
          exact (mem_traceT_val.mp hOb).2
        obtain ⟨κ₀, hkκ₀, hκ₀F⟩ :=
          (force_somehow_iff_of_confluent hK).mp hkbox
        have hmbox : M.force m ((PLLFormula.falsePLL).somehow) :=
          (hZ ((PLLFormula.falsePLL).somehow)
            (by simp [crank]; omega)
            (by intro a ha; simp [PLLFormula.atoms] at ha)).mp hkbox
        obtain ⟨uh, hmuh, huhF⟩ :=
          (force_somehow_iff_of_confluent hM).mp hmbox
        obtain ⟨u₄, hmu₄, hRiuu₄, hRmuhu₄⟩ := confluent_directed hM hmu hmuh
        have hu₄F : u₄ ∈ M.F := M.hered_F (M.sub_mi hRmuhu₄) huhF
        have hRmκ : (canonFinC cl).Rm Δ (traceC hK cl κ₀) := by
          have h := traceC_mforth (cl := cl) hK hkκ₀
          refine ⟨?_, ?_⟩
          · intro χ hχ
            rw [← hΔk₁] at hχ
            exact h.1 hχ
          · intro χ hbcl hχ
            rw [← hΔk₁]
            exact h.2 χ hbcl hχ
        refine ⟨u₄, traceC hK cl κ₀, hRiuu₄, hmu₄, ?_, hRmκ,
          .top (mem_traceT_val.mpr
            ⟨hcl.bot, K.force_of_fallible hκ₀F⟩) hu₄F⟩
        intro χ hχ
        obtain ⟨hχcl, _⟩ := obInvFT_val_iff.mp (hdom χ hχ)
        exact mem_traceT_val.mpr ⟨hχcl, K.force_of_fallible hκ₀F⟩
      · -- ◯⊥-free: depth ≥ 2, promote the base, run the descent
        have hd2 : 2 ≤ canonDepthC cl Δ := by
          rcases Nat.lt_or_ge (canonDepthC cl Δ) 2 with hlt | hge
          · exact absurd
              (obot_of_depth_one hadeq hcl (by omega) hbot) hOb
          · exact hge
        have hall : ∀ β, lvlZ K M β k₁ m :=
          lvlZ_promote hcol hK hM (α := 2 * canonDepthC cl Δ)
            (by omega) hZ
        obtain ⟨u₃, Δu, hRiuu₃, hRmmu₃, hcov, hRmC, htrip⟩ :=
          corner_descend hadeq hcl hcol hK hM hPK hPM k₁ m u hall hmu
        refine ⟨u₃, Δu, hRiuu₃, hRmmu₃, ?_,
          (canonFinC cl).trans_m (rmC_of_val_eq hΔk₁.symm) hRmC, htrip⟩
        intro χ hχ
        refine hcov χ ?_
        obtain ⟨hχcl, hbox⟩ := obInvFT_val_iff.mp (hdom χ hχ)
        refine obInvFT_val_iff.mpr ⟨hχcl, ?_⟩
        show boxOf χ ∈ (traceT K cl k₁).val
        rw [hΔk₁]
        exact hbox

/-- **The crux, closed**: `AmalgamConfluent` for the levelled family
holds outright modulo `ClosedCollapse 6`. -/
theorem amalgamConfluent_of_collapse {cl : Finset PLLFormula}
    (hadeq : OBoxAdeq cl) (hcl : SubClosed cl) (hcol : ClosedCollapse 6)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M) :
    AmalgamConfluent cl (lvlB (p := p) hK hM hPK hPM) :=
  amalgamConfluent_of_coreW hadeq hcl hK hM hPK hPM
    (cornerCoreW_of_collapse hadeq hcl hcol hK hM hPK hPM)

/-! ## Pins -/

/--
info: 'PLLND.SemUI.promise_realiser' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms promise_realiser

/--
info: 'PLLND.SemUI.corner_descend' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms corner_descend

/--
info: 'PLLND.SemUI.cornerCoreW_of_collapse' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms cornerCoreW_of_collapse

/--
info: 'PLLND.SemUI.amalgamConfluent_of_collapse' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms amalgamConfluent_of_collapse

end SemUI
end PLLND
