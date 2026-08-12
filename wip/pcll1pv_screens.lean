/-
Stage-0 screens S2 and S3 (docs/pcll-1pv-ui-plan.md; statements in
wip/pcll1pv_stage0.lean).  Finite proxies, per the plan:

* Canonical worlds are proxied by TRACES of battery worlds (sound as a
  screen: a finite confluent model's world-theories are exactly the
  `Backed` ones).  A corner/answer that exists in the full canonical
  model but not among traces would show here as a spurious failure —
  so S2/S3 FAILURES ARE FLAGS to investigate, while passes are genuine
  support.  Verdict semantics: pass / FLAG, never "refuted".
* The layered link is proxied by the CONSTANT bounded-rank
  variable-free-agreement link (levels dropped) — the constant-family
  screen spirit of wip/stabilise.lean, no dictionary assumed.
* Non-vacuity counters are printed for every screen (the biint
  handoff's lesson: a screen that never exercises its escape hatch
  passes vacuously and lies).

S2: at every componentwise-confluence corner of amalgam worlds, some
corner carries a triple (the `CornerTriple` proxy).
S3: every proper-region amalgam world answers every infallible M-move
with an `RmC`-successor triple (the mforth-maintenance / `ConfResidue`
vacuity proxy), M restricted to mutually confluent models.
-/
import LaxLogic.PLLCountermodelEmit

open PLLND PLLND.FinCM

namespace S0Screens

abbrev F := PLLFormula
def pv : String := "p"
def pf : F := .prop pv
def fls : F := .falsePLL

def worlds (M : FinCM) : List Nat := List.range M.n

/-- Mutual confluence, decided. -/
def confluentB (M : FinCM) : Bool :=
  (worlds M).all fun x => (worlds M).all fun w => (worlds M).all fun v =>
    !(M.rmB x w && M.riB x v) ||
      (worlds M).any fun u => M.riB w u && M.rmB v u

/-- p-purity: only `p` is ever decorated. -/
def pPureB (M : FinCM) : Bool := M.val.all (·.2 = pv)

/-- The variable-free bank for the agreement-link proxy. -/
def vfBank : List F :=
  [fls, .somehow fls, .ifThen (.somehow fls) fls,
   .somehow (.ifThen (.somehow fls) fls),
   .ifThen (.ifThen (.somehow fls) fls) fls,
   .or (.somehow fls) (.ifThen (.somehow fls) fls),
   .somehow (.somehow fls),
   .ifThen fls (.somehow fls)]

def vfAgreeB (K M : FinCM) (k m : Nat) : Bool :=
  vfBank.all fun ρ => K.forceB k ρ == M.forceB m ρ

/-- `boxOf` (◯◯-collapsed box), mirroring `wip/canonFinC.lean`. -/
def boxOfB : F → F
  | .somehow ψ => .somehow ψ
  | φ => φ.somehow

/-- Two ◯-adequate subformula-closed closures over `p`. -/
def cl1 : List F := [fls, .somehow fls, pf, .somehow pf]
def cl2 : List F :=
  cl1 ++ [.ifThen (.somehow pf) (.somehow fls),
          .somehow (.ifThen (.somehow pf) (.somehow fls))]

def traceOf (K : FinCM) (cl : List F) (k : Nat) : List F :=
  cl.filter (K.forceB k ·)

def subsetB (a b : List F) : Bool := a.all (· ∈ b)

/-- Canonical-side `Rᵢ` on trace-values. -/
def riCB (a b : List F) : Bool := subsetB a b

/-- The χ-candidates of the anticipation clause: for each box `◯ψ ∈ cl`,
`χ ∈ {ψ, ◯ψ}`. -/
def boxCand (cl : List F) : List F :=
  (cl.filterMap fun φ => match φ with | .somehow ψ => some ψ | _ => none) ++
  cl.filter fun φ => match φ with | .somehow _ => true | _ => false

/-- Canonical-side `Rₘ` on trace-values: inclusion + anticipation. -/
def rmCB (cl : List F) (a b : List F) : Bool :=
  subsetB a b &&
    (boxCand cl).all fun χ =>
      !(decide (boxOfB χ ∈ cl) && decide (χ ∈ b)) || decide (boxOfB χ ∈ a)

/-- The triple proxy (constant link, levels dropped).  Returns
`(holds, viaTop)`. -/
def tripleB (K M : FinCM) (cl : List F) (Δ : List F) (m : Nat) :
    Bool × Bool :=
  let top := decide (fls ∈ Δ) && M.fallB m
  let proper := (worlds K).any fun k' => (worlds K).any fun k =>
    (worlds M).any fun m' =>
      decide (traceOf K cl k' = Δ) && decide (traceOf K cl k = Δ) &&
      M.riB m' m && vfAgreeB K M k' m' && vfAgreeB K M k m && K.riB k' k
  (top || proper, top && !proper)

def dedup (l : List (List F)) : List (List F) :=
  l.foldr (fun x acc => if x ∈ acc then acc else x :: acc) []

/-- The amalgam-world proxy list, with top-usage count. -/
def amWorlds (K M : FinCM) (cl : List F) :
    List (List F × Nat) × Nat := Id.run do
  let ts := dedup ((worlds K).map (traceOf K cl))
  let mut out := []
  let mut tops := 0
  for Δ in ts do
    for m in worlds M do
      let (h, viaTop) := tripleB K M cl Δ m
      if h then
        out := (Δ, m) :: out
        if viaTop then tops := tops + 1
  return (out, tops)

/-! ## The model bank (law-closed by hand: `ri` transitive, `rm ⊆ ri`,
valuations and fallibility upward-closed) -/

def oneW : FinCM := ⟨1, [], [], [], []⟩
def chain2 : FinCM := ⟨2, [(0,1)], [(0,1)], [], [(1, pv)]⟩
def chain3F : FinCM :=   -- the stab-probe M₂ shape, p-pure
  ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [2], [(0,pv),(1,pv),(2,pv)]⟩
def gadget3 : FinCM := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [], [(2, pv)]⟩
def gadget4 : FinCM :=
  ⟨4, [(0,1),(1,2),(2,3),(0,2),(0,3),(1,3)], [(2,3)], [], [(3, pv)]⟩
def lobT : FinCM := ⟨3, [(0,1),(0,2),(2,1)], [(2,1)], [], [(1, pv)]⟩
def fork : FinCM := ⟨3, [(0,1),(0,2)], [(0,2)], [2], [(1, pv)]⟩
def chain4 : FinCM :=
  ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(2,3)], [3], [(1,pv),(2,pv),(3,pv)]⟩
def deep5 : FinCM :=   -- depth-3 probe frame for the d ≥ 3 region
  ⟨5, [(0,1),(1,2),(2,3),(3,4),(0,2),(0,3),(0,4),(1,3),(1,4),(2,4)],
      [(1,2),(2,3),(3,4),(1,3),(1,4),(2,4)], [4],
      [(2,pv),(3,pv),(4,pv)]⟩

def bank : List (String × FinCM) :=
  [("oneW", oneW), ("chain2", chain2), ("chain3F", chain3F),
   ("gadget3", gadget3), ("gadget4", gadget4), ("lobT", lobT),
   ("fork", fork), ("chain4", chain4), ("deep5", deep5)]

def clBank : List (String × List F) := [("cl1", cl1), ("cl2", cl2)]

/-! ## S2: the corner screen -/

def s2pair (K M : FinCM) (cl : List F) :
    Nat × Nat × Nat × List String := Id.run do
  let (amW, tops) := amWorlds K M cl
  let mut checked := 0
  let mut fails := []
  for (Δa, ma) in amW do
    for (Δb, mb) in amW do
      if rmCB cl Δa Δb && M.rmB ma mb then
        for (Δc, mc) in amW do
          if riCB Δa Δc && M.riB ma mc then
            checked := checked + 1
            let corner := amW.any fun (Δu, mu) =>
              riCB Δb Δu && rmCB cl Δc Δu && M.riB mb mu && M.rmB mc mu
            if !corner then
              fails := s!"corner FLAG at Δa={Δa.length} ma={ma} Δb={Δb.length} mb={mb} Δc={Δc.length} mc={mc}" :: fails
  return (checked, amW.length, tops, fails)

/-! ## S3: the mforth-maintenance / residue-vacuity screen -/

def s3pair (K M : FinCM) (cl : List F) :
    Nat × Nat × List String := Id.run do
  let (amW, _) := amWorlds K M cl
  let mut checked := 0
  let mut fails := []
  for (Δ, m) in amW do
    if !(decide (fls ∈ Δ)) then   -- the proper region
      for u in worlds M do
        if M.rmB m u && !M.fallB u then
          checked := checked + 1
          let answered := amW.any fun (Δ', u') =>
            decide (u' = u) && rmCB cl Δ Δ'
          if !answered then
            fails := s!"residue FLAG at Δ={Δ.length} m={m} u={u}" :: fails
  return (checked, amW.length, fails)

/-! ## S4: the `StableCore` kernel screen (stage 2f)

Configuration: `⊥ ∉ Δ`; `k, t` both tracing to `Δ` with `Rₘ k t`;
`u₂` agreement-linked to `t` (constant proxy for the level-`2d−1`
link); any `m` with `Rₘ m u₂`; any `ψ` from `cl ++ vfBank` forced at
`u₂` (the p-CARRYING members of `cl` are the ones the corrected
vacuity analysis says matter).  Wanted: a triple `(Δ', u₃)` with
`Rₘ m u₃`, `u₃ ⊩ ψ`, `RmC Δ Δ'`. -/

def mentionsP : F → Bool
  | .prop a => a == pv
  | .falsePLL => false
  | .and φ ψ => mentionsP φ || mentionsP ψ
  | .or φ ψ => mentionsP φ || mentionsP ψ
  | .ifThen φ ψ => mentionsP φ || mentionsP ψ
  | .somehow φ => mentionsP φ

def s4pair (K M : FinCM) (cl : List F) :
    Nat × Nat × List String := Id.run do
  let (amW, _) := amWorlds K M cl
  let psiBank := cl ++ vfBank
  let mut checked := 0
  let mut pCarrying := 0
  let mut fails := []
  for Δ in dedup ((worlds K).map (traceOf K cl)) do
    if !(decide (fls ∈ Δ)) then
      for k in worlds K do
        if decide (traceOf K cl k = Δ) then
          for t in worlds K do
            if decide (traceOf K cl t = Δ) && K.rmB k t then
              for u₂ in worlds M do
                if vfAgreeB K M t u₂ then
                  for m in worlds M do
                    if M.rmB m u₂ then
                      for ψ in psiBank do
                        if M.forceB u₂ ψ then
                          checked := checked + 1
                          if mentionsP ψ then pCarrying := pCarrying + 1
                          let answered := amW.any fun (Δ', u₃) =>
                            M.rmB m u₃ && M.forceB u₃ ψ && rmCB cl Δ Δ'
                          if !answered then
                            fails := s!"S4 FLAG Δ={Δ.length} k={k} t={t} u₂={u₂} m={m} ψ={reprStr ψ}" :: fails
  return (checked, pCarrying, fails)

/-! ## S5: the `CornerCoreW` kernel screen (stage 2g, REPAIRED form)

Configuration: a triple at `(Δ, m)` with `⊥ ∉ Δ`; a b-side `Δb`
dominated by the promise set `obInv Δ`; `u` with `Rₘ m u`; `k` tracing
to `Δ`; `kv` with `Rᵢ k kv` agreement-linked to `u`.  Wanted: SOME
`Δu ⊇ Δb` with `RmC Δ Δu` carrying a triple with the SAME `u`.
(A first, anchored form demanded the triple AT `obInv Δ`; this screen
REFUTED it in the promised-`⊥`/infallible-`u` region — see the stage2g
header.  Candidate `Δu`s here: battery traces plus `obInv Δ`.) -/

def obInvOf (cl Δ : List F) : List F :=
  cl.filter fun χ => decide (boxOfB χ ∈ Δ)

def s5pair (K M : FinCM) (cl : List F) :
    Nat × Nat × List String := Id.run do
  let (amW, _) := amWorlds K M cl
  let ts := dedup ((worlds K).map (traceOf K cl))
  let mut checked := 0
  let mut viaTop := 0
  let mut fails := []
  for (Δ, m) in amW do
    if !(decide (fls ∈ Δ)) then
      for Δb in ts do
        if subsetB Δb (obInvOf cl Δ) && !(decide (fls ∈ Δb)) then
          for u in worlds M do
            if M.rmB m u then
              for k in worlds K do
                if decide (traceOf K cl k = Δ) then
                  for kv in worlds K do
                    if K.riB k kv && vfAgreeB K M kv u then
                      checked := checked + 1
                      let cands := obInvOf cl Δ :: ts
                      let ok := cands.any fun Δu =>
                        subsetB Δb Δu && rmCB cl Δ Δu &&
                          (tripleB K M cl Δu u).1
                      let okTop := cands.any fun Δu =>
                        subsetB Δb Δu && rmCB cl Δ Δu &&
                          (tripleB K M cl Δu u).2
                      if ok && okTop then viaTop := viaTop + 1
                      if !ok then
                        fails := s!"S5 FLAG Δ={Δ.length} Δb={Δb.length} m={m} u={u} k={k} kv={kv}" :: fails
  return (checked, viaTop, fails)

def main : IO Unit := do
  let confl := bank.filter fun (_, M) => confluentB M && pPureB M
  IO.println s!"confluent+p-pure models: {confl.map (·.1)}"
  for (nK, K) in confl do
    for (nM, M) in confl do
      for (nCl, cl) in clBank do
        let (checked, nW, tops, fails) := s2pair K M cl
        let (checked3, _, fails3) := s3pair K M cl
        let (checked4, pCarry, fails4) := s4pair K M cl
        let (checked5, tops5, fails5) := s5pair K M cl
        if fails.isEmpty && fails3.isEmpty && fails4.isEmpty
            && fails5.isEmpty then
          IO.println s!"S2-S5 pass  K={nK} M={nM} {nCl}: corners={checked} mmoves={checked3} stable={checked4} (pψ={pCarry}) cornerW={checked5} (top={tops5}) amW={nW} topTriples={tops}"
        else do
          IO.println s!"== K={nK} M={nM} {nCl}: amW={nW} topTriples={tops}"
          for f in fails do IO.println s!"  S2 {f}"
          for f in fails3 do IO.println s!"  S3 {f}"
          for f in fails4 do IO.println s!"  {f}"
          for f in fails5 do IO.println s!"  {f}"
        (← IO.getStdout).flush
  IO.println "SCREENS-DONE"

end S0Screens

def main : IO Unit := S0Screens.main
