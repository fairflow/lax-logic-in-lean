/-
FRJ◯ on the corpus: the refutation calculus's procedure (`FRJO.refute?`)
on the 302 battery-refuted ρ-order cells and the 2 flags.  Every hit is
a derivation + an extracted model passing the VERIFIED checker; the
searcher's own wf self-check runs inside refute? (control).
-/
import wip.rho_order
import FRJO.Core

open PLLND PLLND.RNC.CFX PLLFormula
open RhoOrder (rhos rhoF rhoN n)

namespace FrjoScreen

def run : IO Unit := do
  let out ← IO.getStdout
  let bat := battery ++ framesRooted5.toArray
  IO.println "=== FRJ◯: derivation-carrying refutation on the corpus ==="
  let vecs : Array (Array (Array Bool)) :=
    (List.range n).toArray.map fun i => bat.map fun M => vecOf M (rhoF i)
  let mut hit := 0; let mut miss : List String := []
  let mut dSize := 0; let mut mW := 0; let mut tT := 0
  let mut cells := 0
  for i in [0:n] do
    for j in [0:n] do
      if i != j then
        if (firstSep bat (vecs.getD i #[]) (vecs.getD j #[])).isSome then
          cells := cells + 1
          let t0 ← IO.monoMsNow
          let r := FRJO.diagnose [rhoF i] (rhoF j)
          let t1 ← IO.monoMsNow
          tT := tT + (t1 - t0)
          match r with
          | .inl (t, M, _) =>
              hit := hit + 1; dSize := dSize + t.size; mW := mW + M.n
          | .inr f => miss := s!"{rhoN i}⊬{rhoN j} [{f.str}]" :: miss
    IO.println s!"  row {rhoN i} done"; out.flush
  IO.println ""
  IO.println s!"FRJ◯: {hit}/{cells} certified refutations (derivation + checkB model)"
  IO.println s!"  avg derivation size {if hit == 0 then 0 else dSize / hit}, avg model worlds {if hit == 0 then 0 else mW / hit}, total {tT} ms"
  IO.println s!"  misses: {miss.length}"
  for m in miss.reverse.take 15 do IO.println s!"    {m}"
  let nd := (miss.filter (·.endsWith "[no-derivation]")).length
  let gm := (miss.filter (·.endsWith "[gate-miss]")).length
  let wr := (miss.filter (·.endsWith "[wf-reject]")).length
  IO.println s!"  breakdown: no-derivation {nd}, gate-miss {gm}, wf-reject {wr}"
  IO.println ""
  IO.println "=== the two flags ==="
  for (i, j) in [(12, 15), (20, 10)] do
    let t0 ← IO.monoMsNow
    let r := FRJO.refute? [rhoF i] (rhoF j)
    let t1 ← IO.monoMsNow
    match r with
    | some (t, M, w) =>
        IO.println s!"  *** FLAG SETTLED {rhoN i} ⊬ {rhoN j} [{t1 - t0} ms]: derivation size {t.size}, model ⟨{M.n}, {M.ri}, {M.rm}, {M.fall}, {M.val}⟩ world {w}"
        IO.println s!"      pin: FinCM.not_provable_of_check (M := …) (by decide)"
    | none => IO.println s!"  {rhoN i} ⊬? {rhoN j}: no derivation found [{t1 - t0} ms]"
    out.flush
  IO.println "FRJO-SCREEN-DONE"

end FrjoScreen

def main (_ : List String) : IO Unit := FrjoScreen.run
