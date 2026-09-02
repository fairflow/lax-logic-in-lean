/-
# `≐`-transport for `Gbu◯(G)`

Set-equal contexts derive the same sequents, in both judgments.  This is
the only transport `Gbu◯` admits: `GbuIC` is not monotone
(`gbuIC_not_monotone`, `wip/gbu_ljfo_support.lean`), so irregular
derivations are never moved across context GROWTH — only across `≐`
(same members, different presentation), which preserves membership,
`Clo` (both ways), and `¬ Clo`.

Hoisted out of `wip/gbu_ljfo_transport.lean` on 2026-09-02 with the
promotion of the chain out of `wip/`: the transport is a property of the
calculus, so it must not sit behind the LJF◯ route's imports
(`LJF.OBridge`, `FRJ.Bridge`).  Both `wip.gbu_ljfo_transport` (the LJF◯
translation's support, which stays in `wip/`) and `FRJ.Gbu.W.Search`
(the FRJW corner) use it.
-/
import FRJ.Gbu.Circ

namespace FRJ.Gbu

open FRJ Form

/-- Extending both sides of `≐` by the same formula. -/
theorem ctxEq_cons {Ψ Ψ' : List Form} (h : Ψ ≐ Ψ') (X : Form) :
    (X :: Ψ) ≐ (X :: Ψ') := fun y =>
  ⟨fun hy => (List.mem_cons.mp hy).elim (fun e => e ▸ List.mem_cons_self ..)
      (fun hy' => List.mem_cons_of_mem _ ((h y).mp hy')),
    fun hy => (List.mem_cons.mp hy).elim (fun e => e ▸ List.mem_cons_self ..)
      (fun hy' => List.mem_cons_of_mem _ ((h y).mpr hy'))⟩

/-- `Clo` respects `≐`. -/
theorem clo_ctxEq {Ψ Ψ' : List Form} (h : Ψ ≐ Ψ') {X : Form}
    (hc : Clo Ψ X) : Clo Ψ' X :=
  clo_mono h.subset hc

mutual

/-- Transport a regular `Gbu◯` derivation along `≐`. -/
def transportRC {G : Form} : ∀ {Ψ Ψ' : List Form} {C : Form},
    GbuRC G Ψ C → Ψ ≐ Ψ' → GbuRC G Ψ' C
  | _, _, _, .ax A hΓ, h => .ax A (h.symm.trans hΓ)
  | _, _, _, .lbot C hΓ, h => .lbot C (h.symm.trans hΓ)
  | _, _, _, .landL d hΓ, h => .landL d (h.symm.trans hΓ)
  | _, _, _, .randR d₁ d₂, h => .randR (transportRC d₁ h) (transportRC d₂ h)
  | _, _, _, .lorL d₁ d₂ hΓ, h => .lorL d₁ d₂ (h.symm.trans hΓ)
  | _, _, _, .rorR1 d, h => .rorR1 (transportIC d h)
  | _, _, _, .rorR2 d, h => .rorR2 (transportIC d h)
  | _, _, _, .limpL d₁ d₂ hΓ, h => .limpL d₁ d₂ (h.symm.trans hΓ)
  | _, _, _, .rimpI d hA, h => .rimpI (transportRC d h) (clo_ctxEq h hA)
  | _, _, _, .rimpNI d hA, h =>
      .rimpNI (transportRC d (ctxEq_cons h _))
        (fun hc => hA (clo_ctxEq h.symm hc))
  | _, _, _, .lcirc d hprin hΓ, h => .lcirc d hprin (h.symm.trans hΓ)
  | _, _, _, .rcirc d hgoal, h => .rcirc (transportIC d h) hgoal

/-- Transport an irregular `Gbu◯` derivation along `≐`. -/
def transportIC {G : Form} : ∀ {Ψ Ψ' : List Form} {C : Form},
    GbuIC G Ψ C → Ψ ≐ Ψ' → GbuIC G Ψ' C
  | _, _, _, .ax A hΓ, h => .ax A (h.symm.trans hΓ)
  | _, _, _, .randI d₁ d₂, h => .randI (transportIC d₁ h) (transportIC d₂ h)
  | _, _, _, .rorI1 d, h => .rorI1 (transportIC d h)
  | _, _, _, .rorI2 d, h => .rorI2 (transportIC d h)
  | _, _, _, .rimpII d hA, h => .rimpII (transportIC d h) (clo_ctxEq h hA)
  | _, _, _, .rimpNII d hA, h =>
      .rimpNII (transportRC d (ctxEq_cons h _))
        (fun hc => hA (clo_ctxEq h.symm hc))
  | _, _, _, .lcircI d hprin hΓ, h => .lcircI d hprin (h.symm.trans hΓ)
  | _, _, _, .limpLI d₁ d₂ hsz hgoal hΓ, h =>
      .limpLI d₁ d₂ hsz hgoal (h.symm.trans hΓ)
  | _, _, _, .lbotI hgoal hΓ, h => .lbotI hgoal (h.symm.trans hΓ)
  | _, _, _, .landLI d hgoal hΓ, h => .landLI d hgoal (h.symm.trans hΓ)
  | _, _, _, .lorLI d₁ d₂ hgoal hΓ, h => .lorLI d₁ d₂ hgoal (h.symm.trans hΓ)
  | _, _, _, .rcircI d hgoal, h => .rcircI (transportIC d h) hgoal

end

end FRJ.Gbu
