import tools.SubTab.Engine
import wip.two_sided

/-!
# `refbench`: one countermodel search at a time, timed

2026-10-15.  Which countermodel search should `pllfast` fall back
to when its enumeration reaches the cap?  Run one refuter on one formula:

    refbench g4c   "<φ>" [closureCap]   -- PLLND.Search.refute? (battery + closure emitter)
    refbench trees "<φ>" [maxK]         -- Built-class trees (TwoSided.builtFrames), CLOSED φ only
    refbench frjw  "<φ>"                -- the W-engine decision (FRJ.Arity.decideDataByEngine)
    refbench enum  "<φ>" [maxN]         -- the finite-model enumeration of pllfast, no model cap
    refbench tab   "<φ>"                -- the subframe refutation tableau (tools/SubTab/Tableau.lean)
    refbench engine "<φ>"               -- the lean-certify engine: certificate, judged by its certifier

Prints the outcome and the time.  Run the binary under a deadline.
-/

open PLLND PLLND.Search FRJ

/-- The number of rule applications in a closed tableau. -/
def tsize : PLLND.SubTab.TCert → Nat
  | .bot | .ax _ => 1
  | .andL _ _ c | .boxL _ c | .orR _ _ c | .impLoc _ _ c | .boxLoc _ c | .impR _ _ c
  | .boxR _ c => tsize c + 1
  | .orL _ _ c₁ c₂ | .impL _ _ c₁ c₂ | .andR _ _ c₁ c₂ => tsize c₁ + tsize c₂ + 1

def main (args : List String) : IO UInt32 := do
  match args with
  | mode :: fs :: rest =>
    match PLLTools.parseFormula fs with
    | .error e => IO.println s!"parse error: {e}"; return 2
    | .ok φ =>
      let k := (rest.head?.bind String.toNat?).getD 0
      let t0 ← IO.monoMsNow
      let out : String ← match mode with
        | "g4c" =>
          let cfg : Config := { emitClosureCap := if k == 0 then 1000 else k }
          pure <| match refute? cfg [] φ with
            | some ⟨M, w, _⟩ => s!"REFUTED  countermodel {M.n} worlds (witness {w})"
            | none => "none"
        | "trees" =>
          let maxK := if k == 0 then 8 else k
          let hit := (List.range' 1 maxK).findSome? fun j =>
            (TwoSided.builtFrames j).find? (fun M => FinCM.checkB M 0 [] φ)
          pure <| match hit with
            | some M => s!"REFUTED  Built tree {M.n} worlds"
            | none => s!"none up to {maxK + 1} worlds"
        | "frjw" =>
          pure <| match FRJ.Arity.decideDataByEngine (ofPLL φ) ({} : PLLTools.Args).cfg with
            | none => "frontier (store not closed)"
            | some (.inl _) => "PROVED"
            | some (.inr _) => "REFUTED"
        | "enum" =>
          pure <| match PllFast.firstHit φ (if k == 0 then 10 else k) with
            | some (n, _) => s!"REFUTED  enumeration, {n} worlds"
            | none => "none"
        | "tab" =>
          pure <| match SubTab.refute φ with
            | some T => s!"{if T.refutes (ofPLL φ) then "REFUTED" else "UNCONFIRMED (tool defect)"}  tableau, {T.n - 1} worlds + fallible top"
            | none => "closed (provable, by the paper argument)"
        | "engine" =>
          pure <| match PLLND.SubTab.produce φ 0 with
            | .pass c => s!"PROVED   yes.check = {PLLND.SubTab.yes.check φ c}, closed tableau with {tsize c} rules"
            | .fail m => s!"REFUTED  no.check = {PLLND.SubTab.no.check φ m}, SubCM with {m.n} worlds"
            | .flag => "flag"
        | "fact" =>
          let nm := (rest.head?).getD "fact"
          pure <| match PLLND.SubTab.produce φ 0 with
            | .pass c => s!"theorem {nm} : PLLND.SubTab.Holds {PLLTools.srcOfP φ} :=\n  PLLND.SubTab.yes.verdict {PLLTools.srcOfP φ}\n    {SubTab.tcertSrc c}"
            | .fail m =>
              let m' := if m.n ≤ 64 then SubTab.minimiseCM m φ else m
              s!"-- countermodel: {m.n} worlds, minimised to {m'.n}\ntheorem {nm} : PLLND.SubTab.Holds {PLLTools.srcOfP φ} → False :=\n  PLLND.SubTab.no.verdict {PLLTools.srcOfP φ}\n    {SubTab.subcmSrc m'}"
            | .flag => "-- flag"
        | m => pure s!"unknown mode {m}"
      let t1 ← IO.monoMsNow
      if mode == "fact" then IO.println out else IO.println s!"{mode}: {out}  [{t1 - t0} ms]"
      return 0
  | _ => IO.println "usage: refbench g4c|trees|frjw \"<φ>\" [k]"; return 2
