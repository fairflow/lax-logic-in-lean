/-
# UNRAVELLING LJF◯: the countermodel extracted from the failed search
of the SPECIFIC sequent

Matthew's protocol, restated (2026-08-15): the G4c decidability proof
carried infeasible bounds that existed only to push termination
through; the usable artefact was the EXTRACTED PARTIAL ALGORITHM,
whose successes are verified after the fact.  The same must hold for
DISPROOF: LJF◯ was meant to find countermodels by unravelling the
failed focused search of the sequent at hand — not by enumerating
candidate models independent of it.  This file is that extraction.

**Division of trust, exactly as for proofs:**

* the extractor below is UNTRUSTED — `partial def`, heuristic
  completion, no theorem about it;
* every model it emits is verified by `FinCM.checkB` — the same
  verified Bool that backs `Search.refute?` and `Reject.certifies` —
  and consumed through `FinCM.not_provable_of_check`.  A wrong
  extraction can only fail the gate.

**The algorithm.**  Saturating backward search over the four LJF◯
judgments with MEMOISATION on canonicalised sequents and a
loop-check (a cycle contributes `false` — derivability is a least
fixed point).  Termination therefore does not need the infeasible
bound: contexts grow monotonically inside the finite subformula
universe, so there are finitely many canonical sequents and each is
visited once.  The infeasible bound of the formal story is replaced
by a MEASURED quantity: the run reports visited-sequent counts.

On failure, the trace is read as a model:

* WORLDS — the failed STABLE sequents' canonical contexts (a stable
  sequent is one where inversion is finished and every focusing
  choice fails: exactly a saturated point);
* `Rᵢ` — context inclusion (contexts only grow, along `⊃`-inversion);
* `Rₘ` — the recorded `circL` jumps (the lax-phase moves that consume
  a `◯`-hypothesis), plus reflexivity;
* VALUATION — the parked atoms `↑a` of each context;
* FALLIBLE LEAVES — the one genuinely heuristic step.  A context
  carrying `◯`-hypotheses needs its cone realised; a fallible leaf
  realises anything, but placed wrongly it forces `◯X` for every `X`
  (the `addTop` unsoundness, BiLax round 2).  So the extractor emits
  a small LADDER of completions — no leaves; leaves over ⊆-maximal
  worlds; `Rₘ = Rᵢ`; a shared top — and the VERIFIER picks the first
  that certifies.  "More-or-less deterministic": the skeleton
  (worlds, `Rᵢ`, valuation) is read off the trace deterministically;
  the completion is a bounded choice resolved by `checkB`.
-/
import LJF.OSearch
import LJF.OBridge
import LaxLogic.PLLCountermodelEmit
import Std.Data.HashMap

namespace Unravel

open LJFO PLLND

/-! ## Canonical keys -/

mutual
partial def keyP : Pos → String
  | .atom a => s!"a{a}"
  | .fls => "F"
  | .or p q => s!"(∨{keyP p}{keyP q})"
  | .down n => s!"(↓{keyN n})"
partial def keyN : Neg → String
  | .up p => s!"(↑{keyP p})"
  | .imp p n => s!"(⊃{keyP p}{keyN n})"
  | .and m n => s!"(∧{keyN m}{keyN n})"
  | .circ p => s!"(◯{keyP p})"
end

def canonCtx (Γ : List Neg) : List Neg :=
  (Γ.mergeSort (fun a b => keyN a ≤ keyN b)).eraseReps

def ctxKey (Γ : List Neg) : String := String.join ((canonCtx Γ).map keyN)

def seqKey : LSeq → String
  | .stab Γ j P => s!"S{if j == .tru then "t" else "l"}{ctxKey Γ}⊢{keyP P}"
  | .rfocus Γ j P => s!"R{if j == .tru then "t" else "l"}{ctxKey Γ}⊢{keyP P}"
  | .lfoc Γ N j P => s!"L{if j == .tru then "t" else "l"}{ctxKey Γ}[{keyN N}]⊢{keyP P}"
  | .inv Γ Ω j C => s!"I{if j == .tru then "t" else "l"}{ctxKey Γ}|{String.join (Ω.map keyP)}⊢{keyN C}"

/-! ## The saturating collector -/

structure St where
  memo : Std.HashMap String Bool := {}
  /-- failed stable sequents: canonical context (the world) -/
  worlds : Std.HashMap String (List Neg) := {}
  /-- circL jumps: (parent ctx key, child ctx key) -/
  jumps : List (String × String) := []
  visits : Nat := 0

/-- Saturate with memo + loop-check.  `inProg` are the sequents on the
current path: a revisit is a cycle and contributes `false` (least
fixed point), uncached. -/
partial def go (fuel : Nat) (inProg : List String) (s : LSeq) (st : St) :
    St × Bool :=
  if fuel == 0 then (st, false) else
  let k := seqKey s
  match st.memo.get? k with
  | some b => (st, b)
  | none =>
    if inProg.contains k then (st, false) else
    let st := { st with visits := st.visits + 1 }
    let inP := k :: inProg
    -- try every instance; a sequent holds if SOME instance has ALL
    -- premises holding
    let step : St × Bool := Id.run do
      let mut st := st
      for ps in s.succs do
        let mut ok := true
        for p in ps do
          if ok then
            let (st', b) := go (fuel - 1) inP p st
            st := st'
            ok := b
        if ok then return (st, true)
      return (st, false)
    let (st, b) := step
    let st :=
      if b then st else
      match s with
      | .stab Γ _ _ =>
          { st with worlds := st.worlds.insert (ctxKey Γ) (canonCtx Γ) }
      | _ => st
    -- record circL jumps: from a lax-stable context, its lfoc on a
    -- circ hypothesis pushes the body into the context; the child
    -- worlds appear with strictly larger contexts and get an Rm edge
    let st :=
      if b then st else
      match s with
      | .lfoc Γ (.circ _) .lax _ =>
          let pk := ctxKey Γ
          { st with jumps :=
              (st.worlds.toList.filterMap fun (ck, _) =>
                if ck != pk then some (pk, ck) else none) ++ st.jumps }
      | _ => st
    ({ st with memo := st.memo.insert k b }, b)

/-! ## Model assembly -/

def atomsOf (Γ : List Neg) : List String :=
  Γ.filterMap fun n => match n with
    | .up (.atom a) => some a
    | _ => none

def subsetCtx (A B : List Neg) : Bool := A.all (· ∈ B)

/-- Assemble one candidate `FinCM` from the collected worlds, under a
completion strategy. -/
def assemble (ws : List (List Neg)) (strategy : Nat) : FinCM := Id.run do
  let n := ws.length
  let idx := ws.zipIdx
  -- Ri: context inclusion
  let mut ri : List (Nat × Nat) := []
  for (a, i) in idx do
    for (b, j) in idx do
      if i != j && subsetCtx a b then ri := (i, j) :: ri
  -- Rm by strategy
  let mut rm : List (Nat × Nat) := []
  let mut fal : List Nat := []
  let mut extraW : Nat := 0
  match strategy with
  | 0 => pure ()                       -- Rm reflexive only
  | 1 => rm := ri                      -- Rm = Ri
  | 2 =>                               -- fallible leaf over each ⊆-maximal world
      let maximal := idx.filter fun (a, i) =>
        idx.all fun (b, j) => i == j || !(subsetCtx a b && !subsetCtx b a)
      for (_, i) in maximal do
        let leaf := n + extraW
        extraW := extraW + 1
        fal := leaf :: fal
        rm := (i, leaf) :: rm
        ri := (i, leaf) :: ri
        -- everything below the maximal world reaches the leaf in Ri
        for (b, j) in idx do
          if j != i && subsetCtx b (idx.find? (fun p => p.2 == i) |>.map (·.1) |>.getD []) then
            ri := (j, leaf) :: ri
  | 3 =>                               -- shared fallible top
      let top := n
      extraW := 1
      fal := [top]
      for (_, i) in idx do
        ri := (i, top) :: ri
        rm := (i, top) :: rm
  | 4 =>                               -- fallible leaf over each BOX-CARRYING world
      -- fallibility exactly where a ◯-hypothesis demands its cone
      -- realised, and nowhere else: a leaf over a box-free world makes
      -- ◯X true there for every X and poisons ¬◯⊥-style forcing
      for (a, i) in idx do
        if a.any (fun nn => match nn with | .circ _ => true | _ => false) then
          let leaf := n + extraW
          extraW := extraW + 1
          fal := leaf :: fal
          rm := (i, leaf) :: rm
          ri := (i, leaf) :: ri
  | _ => rm := ri
  -- valuation from parked atoms, hereditary closure left to checkB's wellB test
  let mut val : List (Nat × String) := []
  for (a, i) in idx do
    for at_ in atomsOf a do
      val := (i, at_) :: val
  -- transitive closures (cheap, small n)
  let total := n + extraW
  let mut riC := ri
  let mut changed := true
  while changed do
    changed := false
    for (x, y) in riC do
      for (y', z) in riC do
        if y == y' && !(riC.contains (x, z)) && x != z then
          riC := (x, z) :: riC
          changed := true
  let mut rmC := rm
  changed := true
  while changed do
    changed := false
    for (x, y) in rmC do
      for (y', z) in rmC do
        if y == y' && !(rmC.contains (x, z)) && x != z then
          rmC := (x, z) :: rmC
          changed := true
  -- fallible leaves force every atom (hered_V/full_F)
  let allAtoms := (ws.flatMap atomsOf).eraseDups
  for l in fal do
    for at_ in allAtoms do
      val := (l, at_) :: val
  return ⟨total, riC, rmC, fal, val⟩

/-! ## The extractor -/

structure Result where
  verdict : String        -- "proved" | "refuted" | "flag"
  model? : Option (FinCM × Nat)  -- the certifying (M, w) on refuted
  strategy : Nat := 0
  worlds : Nat := 0
  visits : Nat := 0

/-- Unravel the failed focused search of `Γ ⊢ φ` into a verified
countermodel.  `none` model with verdict "flag" = extraction missed
(reported, never silent). -/
def unravel (fuel : Nat) (Γ : List PLLFormula) (φ : PLLFormula) : Result := Id.run do
  let s : LSeq := .inv (Γ.map negOfO) [] .tru (negOfO φ)
  let (st, b) := go fuel [] s {}
  if b then
    return { verdict := "proved", model? := none, visits := st.visits }
  let ws := st.worlds.toList.map (·.2)
  if ws.isEmpty then
    return { verdict := "flag", model? := none, visits := st.visits }
  for strat in [0, 1, 2, 3] do
    let M := assemble ws strat
    -- the mining lemma: ANY world that checks settles the cell
    for w in List.range M.n do
      if FinCM.checkB M w Γ φ then
        return { verdict := "refuted", model? := some (M, w),
                 strategy := strat, worlds := M.n, visits := st.visits }
  return { verdict := "flag", model? := none,
           worlds := ws.length, visits := st.visits }

end Unravel
