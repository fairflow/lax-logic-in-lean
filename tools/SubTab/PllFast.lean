import tools.Decide
import LaxLogic.PLL.SubTab.Tableau
import LaxLogic.PLL.SubTab.Translate

/-!
# `pllfast`: `pll` with the subframe tableau in front

The searches are library modules: the refutation tableau
(`LaxLogic/PLL/SubTab/Tableau.lean`) and the finite-model enumeration
(`LaxLogic/PLL/SubTab/ModelEnum.lean`); this file is the driver and the output
through `pll`'s layer.

2026-10-22: the proofs come from the tableau too.  When the tableau closes, its
closed tableau (`SubTab.solve`) is judged by `check` and translated into a
`LaxND` derivation by `PLLND.SubTab.termOf` (`LaxLogic/PLL/SubTab/Translate.lean`)
and into a `PLLND.Tm` by `ndToTm`, which `pll`'s output layer prints (and, with
`--check-term`, checks in two passes).  The W-engine is a fallback only, run
when the closed tableau is rejected (a TOOL DEFECT) or when neither search gives
a verdict; it no longer runs alongside the tableau.

## The original header of `pllfast`

(Changed 2026-10-22 as above: the proof terms come from the tableau and the
W-engine no longer runs alongside the searches.)

2026-10-15, after a benchmark of `lake exe pll` on closed cells:
the W-engine proves fast, but on some refutable cells its disproof side runs
out of memory, while direct enumeration of small models finds the
countermodel in milliseconds.

A sequent is unprovable exactly when it has a countermodel, so the two
searches are run together:

  * the W-engine (`FRJ.Arity.decideDataByEngine`, verified `checkClosed`), in a
    dedicated thread, exactly as `lake exe pll` runs it;
  * in the main thread, enumeration of finite rooted subframe models
    (W, ≤, S, V) smallest first: a root below a naturally labelled poset, every
    S ⊆ W, every persistent valuation of the atoms of the formula; the formula
    is evaluated on bitmasks.

The first verdict wins.  A model hit is written as a `Tab` with one fallible
top world (`Rm` reaches it exactly from the worlds outside `S`, so `◯φ` holds
at `x` iff `φ` holds at every S-point above `x`) and CONFIRMED by
`Tab.refutes`, the evaluator the kernel certificate runs; an unconfirmed hit
is reported as a tool defect and ignored.  ORDER (2026-10-15, measured on the
benchmark cells): the subframe refutation tableau first, for the verdict; then
the enumeration, only over the sizes below the tableau's minimised model
(`--maxN`, default 5; `--cap`, default 50,000), to shrink the certificate; the
engine supplies proof terms (and decides alone if both searches fail).
Output layer, exit codes and flags as `lake exe pll`, plus `--maxN=` and
`--cap=`.
-/

open FRJ FRJ.Search FRJ.Gbu FRJ.Gbu.W PLLND

namespace PllFast

/-! ## The race -/

def splitOwn (args : List String) : Nat × Nat × List String :=
  args.foldl (fun (mx, cap, rest) s =>
    if s.startsWith "--maxN=" then ((s.drop 7).toString.toNat!, cap, rest)
    else if s.startsWith "--cap=" then (mx, (s.drop 6).toString.toNat!, rest)
    else (mx, cap, rest ++ [s])) (5, 50000, [])

/-- The output for a model found by enumeration or by the tableau (already
confirmed by `Tab.refutes`): `pll`'s certificate file and, up to 40 worlds,
its SVG.  The drawing of a 158-world model did not finish in 265 s. -/
def emitModel (φ : PLLFormula) (raw min : Tab) (a : PLLTools.Args) : IO UInt32 := do
  IO.println s!"model     {raw.n} worlds → minimised {min.n} (confirmed by Tab.refutes)"
  if min.n ≤ 40 then
    let p := s!"{a.out}.svg"
    IO.FS.writeFile p (PLLSvg.svgOfTab min (ofPLL φ)
      { caption := PLLTools.captionFor φ min "min" raw.n })
    IO.println s!"wrote     {p}"
  else IO.println s!"note      {min.n} worlds: no SVG drawn (> 40)"
  let nm := ((a.out.splitOn "/").getLastD a.out).replace "-" "_"
  let leanPath := s!"{a.out}.lean"
  IO.FS.writeFile leanPath (PLLTools.cmFile min nm φ none)
  IO.println s!"wrote     {leanPath}  (kernel certificate)"
  if a.check then
    match ← PLLTools.twoPass leanPath (fun p => PLLTools.cmFile min nm φ (some p)) with
    | some c => return c
    | none => IO.println "VERDICT   no axiom line found — a TOOL defect."; return 1
  else
    IO.println s!"re-check   lake env lean {a.out}.lean   (or pass --check, under `lake env`; \
the verdict above is confirmed in-process by Tab.refutes, the evaluator the certificate runs)"
    return 0

/-- Smallest-first enumeration over subframe sizes `1..lim`, at most `cap`
models (checked between frames); a hit is confirmed by `Tab.refutes`.
Returns the hit, the models tried, and whether the cap was reached. -/
def enumerate (φ : PLLFormula) (ats : List String) (lim cap : Nat) :
    IO (Option (Nat × Tab) × Nat × Bool) := do
  let mut count := 0
  for n in List.range' 1 lim do
    for rel in posets (n - 1) do
      if count ≥ cap then return (none, count, true)
      let (hit, c) := searchFrame φ ats n (upsOf n rel)
      count := count + c
      if let some m := hit then
        let raw := toTab m ats
        if raw.refutes (ofPLL φ) then return (some (n, raw), count, false)
        IO.println s!"TOOL DEFECT  a bitmask hit on {n} worlds is not confirmed by \
Tab.refutes; ignored"
  return (none, count, false)

def run (fs : String) (a : PLLTools.Args) (maxN cap : Nat) : IO UInt32 := do
  match PLLTools.parseFormula fs with
  | .error e => IO.println s!"parse error: {e}"; return 2
  | .ok φ0 =>
    IO.println s!"formula   {PLLSvg.ppF (ofPLL φ0)}"
    let φ := if a.normalise then Rewrite.simplifyWith Rewrite.fullSetC 40 φ0 else φ0
    if a.normalise && φ != φ0 then
      IO.println s!"normalised {PLLSvg.ppF (ofPLL φ)}   \
(certified: Rewrite.simplifyWith_interd; --raw to skip)"
    let t0 ← IO.monoMsNow
    let ats := (atomsL φ).eraseDups
    -- the W-engine, as `pll` runs it: a fallback only (2026-10-22), run when the
    -- tableau's certificate is rejected or neither search gives a verdict
    let engineAnswer : IO UInt32 := do
      IO.println "fallback  the W-engine (FRJW store, verified checkClosed), as `pll` runs it"
      let dec ← IO.lazyPure fun _ => FRJ.Arity.decideDataByEngine (ofPLL φ) a.cfg
      let t1 ← IO.monoMsNow
      match dec with
      | none =>
          IO.println s!"NOT CLOSED at this budget [{t1 - t0} ms]: the engine's store did not \
pass checkClosed, and no model of ≤ {maxN} worlds (cap {cap}) refutes the formula.  A frontier \
marker, NOT a verdict."
          return 3
      | some d =>
          match PLLTools.answerOf φ d with
          | .proved t =>
              IO.println s!"verdict   PROVED  [{t1 - t0} ms]  (engine: Gbu◯ derivation → LaxND → Tm)"
              PLLTools.emitProved φ t a
          | .refuted raw min =>
              IO.println s!"verdict   REFUTED [{t1 - t0} ms]  (engine: FRJW disproof → Kripke countermodel)"
              PLLTools.emitRefuted φ raw min a
    -- 1. the subframe refutation tableau (LaxLogic/PLL/SubTab/Tableau.lean):
    --    fastest on every measured cell
    let t2 ← IO.monoMsNow
    match SubTab.refute φ with
    | some raw =>
      if raw.refutes (ofPLL φ) then
        let t1 ← IO.monoMsNow
        IO.println s!"verdict   REFUTED [{t1 - t0} ms]  (subframe tableau: {raw.n - 1} worlds \
+ fallible top, tableau {t1 - t2} ms)"
        -- greedy minimisation is cubic in the worlds: skip it past 64
        let min := if raw.n ≤ 65 then raw.minimise (ofPLL φ) else raw
        if raw.n > 65 then
          IO.println s!"note      {raw.n} worlds: minimisation skipped (> 64)"
        -- 2. shrink the certificate: enumerate only the sizes below the minimised model
        let lim := Nat.min maxN (min.n - 2)
        let (hit, count, capped) ← enumerate φ ats lim cap
        match hit with
        | some (n, r2) =>
            let m2 := r2.minimise (ofPLL φ)
            if m2.n < min.n then
              IO.println s!"smaller   enumeration: {n} worlds + fallible top ({count} models), \
minimised {m2.n} < {min.n}"
              IO.Process.exit (← emitModel φ r2 m2 a).toUInt8
        | none =>
            if lim > 0 then
              IO.println s!"shrink    no smaller model on ≤ {lim} worlds ({count} models\
{if capped then ", cap reached" else ""})"
        IO.Process.exit (← emitModel φ raw min a).toUInt8
      else
        IO.println "TOOL DEFECT  the tableau's model is not confirmed by Tab.refutes; \
falling back to the enumeration"
        let (hit, count, _) ← enumerate φ ats maxN cap
        if let some (n, r2) := hit then
          let t1 ← IO.monoMsNow
          IO.println s!"verdict   REFUTED [{t1 - t0} ms]  (finite-model enumeration: {n} worlds \
+ fallible top, {count} models)"
          IO.Process.exit (← emitModel φ r2 (r2.minimise (ofPLL φ)) a).toUInt8
    | none =>
        -- the tableau closed: its closed tableau, judged by `check`, is translated
        -- into a LaxND derivation (`PLLND.SubTab.termOf`) and a proof term (`ndToTm`)
        match SubTab.solve φ with
        | .ok c =>
          if h : PLLND.SubTab.check ⟨false, [], [φ]⟩ c = true then
            let t ← IO.lazyPure fun _ => ndToTm (PLLND.SubTab.termOf φ c h)
            let t1 ← IO.monoMsNow
            IO.println s!"verdict   PROVED  [{t1 - t0} ms]  (subframe tableau: closed tableau, \
checked → LaxND (termOf) → Tm, {t1 - t2} ms)"
            IO.Process.exit (← PLLTools.emitProved φ t a).toUInt8
          else
            IO.println "TOOL DEFECT  the closed tableau is rejected by check; falling back to \
the engine"
        | .error _ =>
            IO.println "TOOL DEFECT  the refuter closed but the certificate search left an \
open tree; falling back to the engine"
    -- 3. the engine (fallback only: a certificate defect, or no verdict from either search)
    engineAnswer

end PllFast

def main (args : List String) : IO UInt32 := do
  let (maxN, cap, rest) := PllFast.splitOwn args
  match PLLTools.parseArgs rest with
  | .error e =>
      IO.println s!"error: {e}"
      IO.println "usage: pllfast \"◯p ⊃ p\" [--maxN=5] [--cap=50000] and the flags of `pll`"
      return 2
  | .ok (f, a) => PllFast.run f a maxN cap
