/-
# ρ12 ⊢? ρ15 — independent countermodel probe

The PATCHED FRJX engine (untrusted) claims a refutation of ρ12 ⊃ ρ15 —
the ONE open cell of the 462-cell ρ-order matrix.  This probe asks the
established, kernel-escalatable machinery for confirmation: the G4c
battery + constructive CounterEmit stage at raised caps.

  lake env lean --run wip/rho1215_probe.lean [emitcap] [budget]
-/
import LaxLogic.PLLSearch
import LaxLogic.RN.Rho

open PLLND RhoOrder

def main (args : List String) : IO Unit := do
  let emitCap := ((args.getD 0 "60").toNat?).getD 60
  let budget := ((args.getD 1 "100000").toNat?).getD 100000
  let φ := PLLFormula.ifThen (rhoF 12) (rhoF 15)
  IO.println s!"probing ρ12 ⊃ ρ15, emitClosureCap={emitCap} findBudget={budget}"
  let t0 ← IO.monoMsNow
  let v := PLLND.Search.settleWhy
    { emitClosureCap := emitCap, findBudget := some budget } [] φ
  let t1 ← IO.monoMsNow
  match v with
  | .refuted M _ _ =>
      IO.println s!"REFUTED — FinCM with {M.n} worlds  [{t1 - t0} ms]"
      IO.println s!"  M = {repr M}"
  | .proved _ => IO.println s!"PROVED?! [{t1 - t0} ms] — conflicts with the FRJX claim"
  | .unknown r => IO.println s!"unknown: {repr r}  [{t1 - t0} ms]"
