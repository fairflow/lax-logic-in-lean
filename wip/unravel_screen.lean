/-
# Three disproof engines on the same cells

Per Matthew's protocol correction (2026-08-15): disproof should be
SEQUENT-DIRECTED — extract the countermodel from the failed search of
the cell itself, verify cheaply — not found by enumerating candidate
models.  This screen compares, on the 302 refutable ρ-order cells and
the 2 flags:

  U  the LJF◯ unraveller (`wip/ljfo_unravel.lean`) — extract from the
     failed FOCUSED search, verify by `checkB`;
  E  `Search.refute?` — the G4c-side extracted algorithm that already
     existed (battery stage OFF here: `frames := []`, so what runs is
     the sequent-directed closure EMITTER, verified output by
     construction);
  B  the blind battery verdict (precomputed vectors) as ground truth.

All three end in `FinCM.checkB`-level certificates, so agreement is a
cross-validation and any U/E "refuted" on a B-underivable cell would
be a soundness event (impossible if the checkers hold).
-/
import wip.rho_order
import wip.ljfo_unravel

open PLLND PLLND.RNC.CFX PLLFormula
open RhoOrder (rhos rhoF rhoN n)

namespace UnravelScreen

def emitCfg : PLLND.Search.Config :=
  { frames := [], findBudget := some 20000, emitClosureCap := 64 }

def run (fuel : Nat) : IO Unit := do
  let out ← IO.getStdout
  let bat := battery ++ framesRooted5.toArray
  IO.println "=== three disproof engines: LJF◯-unravel (U) vs G4c-emitter (E) vs battery (B) ==="
  IO.println s!"unravel fuel {fuel}; emitter budget 20000, closure cap 64, battery stage off"
  out.flush
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  let mut uHit := 0; let mut uMiss : List String := []
  let mut eHit := 0; let mut eMiss : List String := []
  let mut uW := 0; let mut eW := 0
  let mut uT := 0; let mut eT := 0
  let mut cells := 0
  let mut uProved : List String := []
  for i in [0:n] do
    for j in [0:n] do
      if i != j then
        if (firstSep bat (vecs.getD i #[]) (vecs.getD j #[])).isSome then
          cells := cells + 1
          -- U
          let t0 ← IO.monoMsNow
          let r := Unravel.unravel fuel [rhoF i] (rhoF j)
          let t1 ← IO.monoMsNow
          uT := uT + (t1 - t0)
          match r.verdict, r.model? with
          | "refuted", some (M, _) =>
              uHit := uHit + 1; uW := uW + M.n
          | "proved", _ =>
              uProved := s!"{rhoN i}⊢{rhoN j}" :: uProved
          | _, _ => uMiss := s!"{rhoN i}⊬{rhoN j} (worlds {r.worlds}, visits {r.visits})" :: uMiss
          -- E
          let t2 ← IO.monoMsNow
          let e := PLLND.Search.refute? emitCfg [rhoF i] (rhoF j)
          let t3 ← IO.monoMsNow
          eT := eT + (t3 - t2)
          match e with
          | some w => eHit := eHit + 1; eW := eW + w.1.n
          | none => eMiss := s!"{rhoN i}⊬{rhoN j}" :: eMiss
    IO.println s!"  row {rhoN i} done"; out.flush
  IO.println ""
  IO.println s!"cells (battery-refuted, ground truth): {cells}"
  IO.println s!"U unravel : {uHit}/{cells} verified refutations, avg worlds {if uHit == 0 then 0 else uW / uHit}, total {uT} ms"
  if !uProved.isEmpty then
    IO.println s!"  *** U claims PROVED on battery-refuted cells: {uProved.length} — SOUNDNESS EVENT, investigate"
    for c in uProved.reverse.take 5 do IO.println s!"      {c}"
  IO.println s!"  misses: {uMiss.length}"
  for m in uMiss.reverse.take 12 do IO.println s!"    U-miss {m}"
  IO.println s!"E emitter : {eHit}/{cells} certified refutations, avg worlds {if eHit == 0 then 0 else eW / eHit}, total {eT} ms"
  IO.println s!"  misses: {eMiss.length}"
  for m in eMiss.reverse.take 12 do IO.println s!"    E-miss {m}"
  IO.println ""
  -- the two flags
  IO.println "=== the two flags, all three engines ==="
  for (i, j) in [(12, 15), (20, 10)] do
    let t0 ← IO.monoMsNow
    let r := Unravel.unravel fuel [rhoF i] (rhoF j)
    let t1 ← IO.monoMsNow
    IO.println s!"  U {rhoN i} ⊢? {rhoN j}: {r.verdict} (worlds {r.worlds}, visits {r.visits}) [{t1 - t0} ms]"
    match r.model? with
    | some (M, w) =>
        IO.println s!"    *** FLAG SETTLED ⊬: M = ⟨{M.n}, {M.ri}, {M.rm}, {M.fall}, {M.val}⟩ world {w}"
        IO.println s!"    pin: Reject-style via FinCM.not_provable_of_check (by decide)"
    | none => pure ()
    let t2 ← IO.monoMsNow
    let e := PLLND.Search.refute? emitCfg [rhoF i] (rhoF j)
    let t3 ← IO.monoMsNow
    match e with
    | some w =>
        IO.println s!"  E {rhoN i} ⊬ {rhoN j}: CERTIFIED, model {w.1.n} worlds [{t3 - t2} ms]"
        IO.println s!"    *** FLAG SETTLED by the emitter: M = ⟨{w.1.n}, {w.1.ri}, {w.1.rm}, {w.1.fall}, {w.1.val}⟩ world {w.2.1}"
    | none => IO.println s!"  E {rhoN i} ⊬? {rhoN j}: emitter no verdict [{t3 - t2} ms]"
    out.flush
  IO.println "UNRAVEL-SCREEN-DONE"

end UnravelScreen

def main (args : List String) : IO Unit :=
  UnravelScreen.run ((args.head?.bind String.toNat?).getD 200)
