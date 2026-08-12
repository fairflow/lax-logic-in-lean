/-
STAGE 2, part (g): the CORNER for the levelled family, MBack-free.

Stage 1 discharged `CornerTriple` via `obInvForth_of_core`, whose
linked partner came from the ADVERSARIAL clause `MBack` — which the
levelled family `lvlB` does not have.  The repair observed here: the
corner's M-move `Rm c₂ v₂` is also an `Ri`-move (`sub_mi`), so the
K-side partner comes from the family's PROVED `iback` clause instead,
at level `2d − 1`; and the iback escape (`v₂` fallible) closes through
the family's own `◯⊥`-transfer under bare possibility.

STATEMENT REPAIR (2026-08-12, forced by screen S5): a first version of
the kernel anchored the corner triple AT `obInvW Δ`, and the screen
flagged the promised-`⊥` region — when `◯⊥ ∈ Δ.val` (legal with
`⊥ ∉ Δ.val`), `⊥ ∈ (obInvW Δ).val`, and a triple there with an
INFALLIBLE `u` is impossible: `top` demands `u ∈ M.F`, and a `proper`
K-slot traces through `⊥` (so is fallible) while the fall clause of
any link family then forces `u ∈ M.F` too.  So the anchored kernel was
REFUTABLE.  The corner itself never demanded the anchor — any world
covering the b-side serves — so the kernel below carries the b-side
world as data (dominated by the promise set, which is what
`rmC_le_obInv` supplies) and concludes EXISTENTIALLY.  Stage 1's
`ObInvForthCore` shares the anchor and is superseded by this form.

SECOND REPAIR (same screen, next round): with the b-side freed, the
screen flagged `⊥ ∈ Δb` against an INFALLIBLE `u` — a configuration
the real corner cannot produce: `⊥ ∈ val b₁` makes `b₂` fallible
through b's own triple (fall clause), and fallibility is hereditary
along `Rᵢ b₂ v₂`.  The maintenance lemma therefore carries the tie
`⊥ ∈ Δb.val → u ∈ M.F` (discharged at the consumer exactly so), the
`⊥ ∈ Δb` branch closes by `top` (domination puts `⊥` in the promise
set), and the kernel is gated on `⊥ ∉ Δb.val`.
-/
import wip.pcll1pv_stage1
import wip.pcll1pv_stage2e

namespace PLLND
open FinComp
namespace SemUI

open Classical

variable {p : String} {K M : ConstraintModel}

/-- **The isolated corner kernel**: at a proper-region triple, the
iback-linked partner `kv` (level `2d − 1`, `Rᵢ`-reachable from a world
tracing to `Δ`) demands SOME `RmC`-successor of `Δ` covering the given
promise-dominated b-side and carrying a triple with the SAME `u`.
The `Rᵢ`-partner, existential-conclusion sibling of stage 1's
`ObInvForthCore`. -/
def CornerCoreW (cl : Finset PLLFormula) (hadeq : OBoxAdeq cl)
    (B : LayeredBisimWit (fun a => a ≠ p) K M) : Prop :=
  ∀ {Δ Δb : (canonFinC cl).W} {m : M.W}, WitTripleC cl B Δ m →
    PLLFormula.falsePLL ∉ Δ.1.val →
    PLLFormula.falsePLL ∉ Δb.1.val →
    (∀ χ ∈ Δb.1.val, χ ∈ (obInvW hadeq Δ).1.val) →
    ∀ {u : M.W}, M.Rm m u →
    ∀ {k kv : K.W}, (traceT K cl k).val = Δ.1.val → K.Ri k kv →
      B.Z (2 * canonDepthC cl Δ - 1) kv u →
      ∃ Δu : (canonFinC cl).W, (∀ χ ∈ Δb.1.val, χ ∈ Δu.1.val) ∧
        (canonFinC cl).Rm Δ Δu ∧ WitTripleC cl B Δu u

/-- The corner maintenance for the LEVELLED family, modulo the kernel:
the `⊥`-region and the iback escape both land `top` AT `obInvW Δ`
(there `u` is provably fallible, so the anchor is harmless); the
linked case is the kernel. -/
theorem obInvForthW_of_core {cl : Finset PLLFormula} {hadeq : OBoxAdeq cl}
    (hcl : SubClosed cl) (hK : MutuallyConfluent K)
    (hM : MutuallyConfluent M) (hPK : PPure p K) (hPM : PPure p M)
    (hcore : CornerCoreW cl hadeq (lvlB (p := p) hK hM hPK hPM)) :
    ∀ {Δ Δb : (canonFinC cl).W} {m : M.W},
      WitTripleC cl (lvlB (p := p) hK hM hPK hPM) Δ m →
      (∀ χ ∈ Δb.1.val, χ ∈ (obInvW hadeq Δ).1.val) →
      ∀ {u : M.W}, M.Rm m u →
      (PLLFormula.falsePLL ∈ Δb.1.val → u ∈ M.F) →
      ∃ Δu : (canonFinC cl).W, (∀ χ ∈ Δb.1.val, χ ∈ Δu.1.val) ∧
        (canonFinC cl).Rm Δ Δu ∧
        WitTripleC cl (lvlB (p := p) hK hM hPK hPM) Δu u := by
  intro Δ Δb m ht hdom u hmu hbu
  by_cases hbotb : PLLFormula.falsePLL ∈ Δb.1.val
  · -- ⊥ on the b-side: `u` is fallible by the supplied tie, and the
    -- promise set contains ⊥ by domination — `top` at `obInvW Δ`
    exact ⟨obInvW hadeq Δ, hdom, rm_obInvW hadeq Δ,
      .top (hdom _ hbotb) (hbu hbotb)⟩
  by_cases hbot : PLLFormula.falsePLL ∈ Δ.1.val
  · -- the ⊥-region: the triple is secretly fallible on both sides
    have hmF : m ∈ M.F := by
      cases ht with
      | top _ hmF => exact hmF
      | proper k' k m' hΔk hΔk' him hZ' hZ hik =>
          have hk : PLLFormula.falsePLL ∈ (traceT K cl k).val := by
            rw [hΔk]; exact hbot
          exact ((lvlB (p := p) hK hM hPK hPM).fall hZ).mp
            (mem_traceT_val.mp hk).2
    have hbotcl : PLLFormula.falsePLL ∈ cl := Δ.2.1.2.1.1 hbot
    have hboxbot : PLLFormula.falsePLL.somehow ∈ Δ.1.val :=
      boxUnit (T := ⟨Δ.1, Δ.2.1⟩) (hadeq _ hbotcl) hbot
    exact ⟨obInvW hadeq Δ, hdom, rm_obInvW hadeq Δ,
      .top (obInvFT_val_iff.mpr ⟨hbotcl, hboxbot⟩)
        (M.hered_F (M.sub_mi hmu) hmF)⟩
  · cases ht with
    | top hbot' _ => exact absurd hbot' hbot
    | proper k' k m' hΔk hΔk' him hZ' hZ hik =>
        have hd : 1 ≤ canonDepthC cl Δ := canonDepthC_pos hcl hbot
        have hZbase : (lvlB (p := p) hK hM hPK hPM).Z
            (2 * canonDepthC cl Δ - 1 + 1) k m := by
          have h2 : 2 * canonDepthC cl Δ - 1 + 1 = 2 * canonDepthC cl Δ := by
            omega
          rw [h2]; exact hZ
        -- the iback spend against the corner move, viewed as an Rᵢ-move
        rcases (lvlB (p := p) hK hM hPK hPM).iback hZbase (M.sub_mi hmu) with
          ⟨kv, hkkv, hZkv⟩ | huF
        · exact hcore (.proper k' k m' hΔk hΔk' him hZ' hZ hik)
            hbot hbotb hdom hmu hΔk hkkv hZkv
        · -- u fallible: m ⊩ ◯⊥ by bare possibility; transfer to k; top
          have hforceM : M.force m (PLLFormula.somehow .falsePLL) :=
            (force_somehow_iff_of_confluent hM).mpr ⟨u, hmu, huF⟩
          have hforceK : K.force k (PLLFormula.somehow .falsePLL) :=
            (hZ (PLLFormula.somehow .falsePLL)
              (by simp [crank]; omega)
              (by intro a ha; simp [PLLFormula.atoms] at ha)).mpr hforceM
          have hboxcl : (PLLFormula.falsePLL).somehow ∈ cl :=
            hadeq _ hcl.bot
          have hmem : (PLLFormula.falsePLL).somehow ∈ Δ.1.val := by
            rw [← hΔk]
            exact mem_traceT_val.mpr ⟨hboxcl, hforceK⟩
          exact ⟨obInvW hadeq Δ, hdom, rm_obInvW hadeq Δ,
            .top (obInvFT_val_iff.mpr ⟨hcl.bot, hmem⟩) huF⟩

/-- **`CornerTriple` for the levelled family, modulo the kernel**: the
b-side is promise-dominated (`rmC_le_obInv`), the M-corner comes from
`hM`, and the canonical corner world with its triple from
`obInvForthW_of_core` — no adversarial clause anywhere. -/
theorem cornerTriple_of_coreW {cl : Finset PLLFormula}
    (hadeq : OBoxAdeq cl) (hcl : SubClosed cl)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M)
    (hcore : CornerCoreW cl hadeq (lvlB (p := p) hK hM hPK hPM)) :
    CornerTriple cl (lvlB (p := p) hK hM hPK hPM) := by
  intro _hK _hM a b c hab hac
  obtain ⟨v₂, hbv, hcv⟩ := hM hab.2 hac.2
  -- the fall tie: ⊥ on the b-side makes b₂ (hence v₂) fallible
  have hbF : PLLFormula.falsePLL ∈ b.1.1.1.val → b.1.2 ∈ M.F := by
    intro hbot_b
    cases b.2 with
    | top _ hmF => exact hmF
    | proper k' k m' hΔk hΔk' him hZ' hZ hik =>
        have hk : PLLFormula.falsePLL ∈ (traceT K cl k).val := by
          rw [hΔk]; exact hbot_b
        exact ((lvlB (p := p) hK hM hPK hPM).fall hZ).mp
          (mem_traceT_val.mp hk).2
  obtain ⟨Δu, hb, hRm, htrip⟩ :=
    obInvForthW_of_core hcl hK hM hPK hPM hcore c.2
      (rmC_le_obInv hadeq hab.1 hac.1) hcv
      (fun hbb => M.hered_F hbv (hbF hbb))
  exact ⟨Δu, v₂, hb, hRm, hbv, hcv, htrip⟩

/-- The crux for the levelled family, modulo the kernel. -/
theorem amalgamConfluent_of_coreW {cl : Finset PLLFormula}
    (hadeq : OBoxAdeq cl) (hcl : SubClosed cl)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M)
    (hcore : CornerCoreW cl hadeq (lvlB (p := p) hK hM hPK hPM)) :
    AmalgamConfluent cl (lvlB (p := p) hK hM hPK hPM) :=
  amalgamConfluent_of_corner
    (cornerTriple_of_coreW hadeq hcl hK hM hPK hPM hcore)

/-! ## Pins -/

/--
info: 'PLLND.SemUI.obInvForthW_of_core' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms obInvForthW_of_core

/--
info: 'PLLND.SemUI.cornerTriple_of_coreW' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms cornerTriple_of_coreW

/--
info: 'PLLND.SemUI.amalgamConfluent_of_coreW' depends on axioms: [propext, choice, Quot.sound]
-/
#guard_msgs in
#print axioms amalgamConfluent_of_coreW

end SemUI
end PLLND
