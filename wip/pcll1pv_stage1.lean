/-
STAGE 1 of `docs/pcll-1pv-ui-plan.md`.

Item 1 (`MutuallyConfluent (canonFinC cl)`) turned out to be ALREADY
PROVED: `FinComp.canonFinC_confluent` (wip/canonFinC.lean), witnessed
by the `obInvW` successor — pinned below, not re-derived.

Item 2 (`CornerTriple`): the canonical corner is always `obInvW c₁`
(it is the MAXIMUM `RmC`-successor: any `RmC`-successor's content is
promised content, and `obInvW` collects exactly the promises), and the
b-side inclusion `val b₁ ⊆ val (obInvW c₁)` is structural
(`rmC_le_obInv`: b₁'s members are a₁-promised, promises persist to
c₁).  The M-side corner comes from `hM`.  What remains is a triple AT
`(obInvW c₁, v₂)` — an mforth-shaped maintenance step whose fallible
escapes are proved here (`obInvForth_of_core`) and whose
proper-infallible case is the ONE open Prop `ObInvForthCore`,
isolated exactly as `MforthResidue` was.  Its discharge belongs to
stage 2 (it IS an m-clause: the choice-freedom wall of PROGRESS §43 —
the mback partner carries the link but not the trace, the directed
witness carries the trace but not the link).

Item 3 (`OneVarConfluentAmalgamation`): proved OUTRIGHT — the target
takes `AmalgamConfluent` as an antecedent, and the assembly is
`amalgamation_assembledC`'s own proof term with the confluence
conjunct added.
-/
import wip.pcll1pv_stage0

namespace PLLND
open FinComp
namespace SemUI

variable {p : String} {K M : ConstraintModel}

/-! ## Item 1: the canonical component is confluent (pin only) -/

/--
info: 'PLLND.FinComp.canonFinC_confluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FinComp.canonFinC_confluent

/-! ## Item 2a: the b-side inclusion — `obInvW c₁` dominates every
`RmC`-successor of any `Ri`-predecessor -/

/-- `RmC a₁ b₁` and `val a₁ ⊆ val c₁` give `val b₁ ⊆ val (obInvW c₁)`:
b₁'s members are a₁-promised, and promises persist along `Ri`. -/
theorem rmC_le_obInv {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl)
    {a₁ b₁ c₁ : (canonFinC cl).W}
    (hab : (canonFinC cl).Rm a₁ b₁) (hac : (canonFinC cl).Ri a₁ c₁) :
    ∀ χ ∈ b₁.1.val, χ ∈ (obInvW hadeq c₁).1.val := by
  intro χ hχ
  have hχcl : χ ∈ cl := b₁.2.1.2.1.1 hχ
  exact obInvFT_val_iff.mpr ⟨hχcl, hac (hab.2 χ (hadeq _ hχcl) hχ)⟩

/-! ## Item 2b: the mforth-to-`obInvW` step — escapes proved, the
proper-infallible case isolated -/

/-- **The isolated stage-2 obligation, minimal form**: at a
proper-region triple with the `MBack`-LINKED partner in hand
(`Z_{2d-1} κ u`, `Rm k κ`, `k` tracing to `Δ`), the M-move is answered
by a triple at the maximal canonical successor `obInvW Δ`.  This is
exactly the §43 choice-freedom configuration: κ carries the link but
not the trace; the directed witness carries the trace but not the
link.  Its discharge is pillar-2 m-clause work (stage 2). -/
def ObInvForthCore (cl : Finset PLLFormula) (hadeq : OBoxAdeq cl)
    (B : LayeredBisimWit (fun a => a ≠ p) K M) : Prop :=
  ∀ {Δ : (canonFinC cl).W} {m : M.W}, WitTripleC cl B Δ m →
    PLLFormula.falsePLL ∉ Δ.1.val →
    ∀ {u : M.W}, M.Rm m u →
    ∀ {k κ : K.W}, (traceT K cl k).val = Δ.1.val → K.Rm k κ →
      B.Z (2 * canonDepthC cl Δ - 1) κ u →
      WitTripleC cl B (obInvW hadeq Δ) u

/-- The escapes, proved: outside the proper region the `top`
constructor answers (`⊥` promotes through `boxUnit`); inside it, the
`MBack` spend either returns a LINKED partner (handed to the core) or
a FALLIBLE pair — and one fallible `Rm`-successor forces `◯⊥` at the
base under K's confluence (bare possibility), landing `top` again. -/
theorem obInvForth_of_core {cl : Finset PLLFormula} {hadeq : OBoxAdeq cl}
    {B : LayeredBisimWit (fun a => a ≠ p) K M}
    (hcl : SubClosed cl) (hK : MutuallyConfluent K) (hmb : B.MBack)
    (hcore : ObInvForthCore cl hadeq B) :
    ∀ {Δ : (canonFinC cl).W} {m : M.W}, WitTripleC cl B Δ m →
      ∀ {u : M.W}, M.Rm m u → WitTripleC cl B (obInvW hadeq Δ) u := by
  intro Δ m ht u hmu
  by_cases hbot : PLLFormula.falsePLL ∈ Δ.1.val
  · have hmF : m ∈ M.F := by
      cases ht with
      | top _ hmF => exact hmF
      | proper k' k m' hΔk hΔk' him hZ' hZ hik =>
          have hk : PLLFormula.falsePLL ∈ (traceT K cl k).val := by
            rw [hΔk]; exact hbot
          exact (B.fall hZ).mp (mem_traceT_val.mp hk).2
    have hbotcl : PLLFormula.falsePLL ∈ cl := Δ.2.1.2.1.1 hbot
    have hboxbot : PLLFormula.falsePLL.somehow ∈ Δ.1.val :=
      boxUnit (T := ⟨Δ.1, Δ.2.1⟩) (hadeq _ hbotcl) hbot
    exact .top (obInvFT_val_iff.mpr ⟨hbotcl, hboxbot⟩)
      (M.hered_F (M.sub_mi hmu) hmF)
  · cases ht with
    | top hbot' _ => exact absurd hbot' hbot
    | proper k' k m' hΔk hΔk' him hZ' hZ hik =>
        have hd : 1 ≤ canonDepthC cl Δ := canonDepthC_pos hcl hbot
        have hZbase : B.Z (2 * canonDepthC cl Δ - 1 + 1) k m := by
          have h2 : 2 * canonDepthC cl Δ - 1 + 1 = 2 * canonDepthC cl Δ := by
            omega
          rw [h2]; exact hZ
        rcases hmb hZbase hmu with ⟨κ, hkκ, hZκ | ⟨hκF, huF⟩⟩
        · exact hcore (.proper k' k m' hΔk hΔk' him hZ' hZ hik)
            hbot hmu hΔk hkκ hZκ
        · have hforce : K.force k (PLLFormula.somehow .falsePLL) :=
            (force_somehow_iff_of_confluent hK).mpr
              ⟨κ, hkκ, hκF⟩
          have hbotcl : PLLFormula.falsePLL ∈ cl := hcl.bot
          have hboxcl : (PLLFormula.falsePLL).somehow ∈ cl := hadeq _ hbotcl
          have hmem : (PLLFormula.falsePLL).somehow ∈ Δ.1.val := by
            rw [← hΔk]
            exact mem_traceT_val.mpr ⟨hboxcl, hforce⟩
          exact .top (obInvFT_val_iff.mpr ⟨hbotcl, hmem⟩) huF

/-! ## Item 2c: the corner, conditional on the core -/

/-- **`CornerTriple`, discharged modulo the core**: the canonical
corner is `obInvW c₁` (b-side by `rmC_le_obInv`, c-side by
`rm_obInvW`), the M-corner by `hM`, the triple by
`obInvForth_of_core`. -/
theorem cornerTriple_of_core {cl : Finset PLLFormula}
    (hadeq : OBoxAdeq cl) {B : LayeredBisimWit (fun a => a ≠ p) K M}
    (hcl : SubClosed cl) (hmb : B.MBack)
    (hcore : ObInvForthCore cl hadeq B) : CornerTriple cl B := by
  intro hK hM a b c hab hac
  obtain ⟨v₂, hbv, hcv⟩ := hM hab.2 hac.2
  exact ⟨obInvW hadeq c.1.1, v₂,
    rmC_le_obInv hadeq hab.1 hac.1,
    rm_obInvW hadeq c.1.1,
    hbv, hcv,
    obInvForth_of_core hcl hK hmb hcore c.2 hcv⟩

/-- The crux, conditional on the core. -/
theorem amalgamConfluent_of_core {cl : Finset PLLFormula}
    (hadeq : OBoxAdeq cl) {B : LayeredBisimWit (fun a => a ≠ p) K M}
    (hcl : SubClosed cl) (hmb : B.MBack)
    (hcore : ObInvForthCore cl hadeq B) : AmalgamConfluent cl B :=
  amalgamConfluent_of_corner (cornerTriple_of_core hadeq hcl hmb hcore)

/-! ## Item 3: the target, proved outright -/

/-- **The stage-3 target holds**: `amalgamation_assembledC`'s own
assembly, with the confluence conjunct supplied by the
`AmalgamConfluent` antecedent. -/
theorem oneVarConfluentAmalgamation_holds (p : String) :
    OneVarConfluentAmalgamation p := by
  intro K M cl hcl hadeq hK hM B hmb hres hAC k₀ m₀ hB
  classical
  refine ⟨witAmalgamC cl B, hAC hK hM, ?_⟩
  set Δ₀ : (canonFinC cl).W := traceC hK cl k₀ with hΔ₀
  have hd₀ := canonDepthC_le cl Δ₀
  have htrip : WitTripleC cl B Δ₀ m₀ :=
    .proper k₀ k₀ m₀ rfl rfl (M.refl_i m₀)
      (B.mono_le (by omega) hB) (B.mono_le (by omega) hB) (K.refl_i k₀)
  obtain ⟨C, hC⟩ := wit_pbisimC cl B hcl hK hmb hres
  refine ⟨C, ⟨(Δ₀, m₀), htrip⟩, hC ⟨(Δ₀, m₀), htrip⟩, ?_⟩
  intro φ hφ
  rw [wit_forceC cl B hcl hadeq hK φ hφ ⟨(Δ₀, m₀), htrip⟩]
  constructor
  · intro h
    exact (mem_traceT_val.mp h).2
  · intro h
    exact mem_traceT_val.mpr ⟨hφ, h⟩

/-! ## Pins -/

/--
info: 'PLLND.SemUI.rmC_le_obInv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rmC_le_obInv
/--
info: 'PLLND.SemUI.obInvForth_of_core' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms obInvForth_of_core
/--
info: 'PLLND.SemUI.cornerTriple_of_core' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cornerTriple_of_core
/--
info: 'PLLND.SemUI.amalgamConfluent_of_core' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms amalgamConfluent_of_core
/--
info: 'PLLND.SemUI.oneVarConfluentAmalgamation_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms oneVarConfluentAmalgamation_holds

end SemUI
end PLLND
