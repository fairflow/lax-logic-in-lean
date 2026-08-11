/-
The UPPER-BOUND hunt at the GZ-candidate cell (2026-08-11, proof prong).

The cell.  Station S = [◯p ⊃ r, ◯q], goal ↑↓◯p; the eliminated variable
is `p`.  `A_f := interpF "p" f [] S (some ↑↓◯p)` is the fuel-founded
∀p-approximant.  Certified previously: A_f ⊢ A_{f+1} for f = 1..5, with
strict steps 1→2, 3→4, 5→6 (countermodel-certified) and plateaus 2⟛3,
4⟛5; A_2 and A_4 are sufficient (A_f, S ⊢ ◯p).

The question this file attacks: does the SUFFICIENT SET
    Suff := {θ p-free : θ, ◯p⊃r, ◯q ⊢ ◯p}
have a greatest element (= the ∀p pre-interpolant), even though the
`interpF` chain does not stabilise?  A greatest element is an UPPER BOUND
of the chain that is itself in `Suff`, so the test per candidate χ is:
  (i)  sufficiency  χ, ◯p⊃r, ◯q ⊢ ◯p
  (ii) domination   A_f ⊢ χ   (f = 2, 4, 6, 8)

Also here: the chain extension 6→7, 7→8 at raised budget, the soundness
of A_6 / A_8, and the countermodel of the 5→6 strict step.

Engines: PLLND.Search.prove?Bounded (kernel-checkable proof terms) and
PLLND.Search.refute? (checkB-certified finite countermodels), plus the
kernel searcher LJFO.LSeq.search.  `decideFuel` / the decidability
theorem are NOT used anywhere.  Budget exhaustion prints `unk` and is
never a verdict.

OUTCOME (2026-08-11).  The upper bound is

    θmax  :=  ((◯⊥ ⊃ r) ∧ ◯q) ⊃ ◯⊥

— the ⊥-INSTANCE of the cell itself.  Certified: θmax is sufficient;
A_2, A_4, A_6, A_7, A_8 ⊢ θmax; θmax ⊢ A_6.  So A_6 ⊣⊢ θmax and the
chain is logically STATIONARY from f = 6 (its syntax keeps doubling).
Read off the display normal forms, the chain is

    A_1 ⊣⊢ ⊥,  A_2 ⊣⊢ A_3 ⊣⊢ ◯⊥,  A_4 ⊣⊢ A_5 ⊣⊢ q ⊃ ◯⊥,
    A_6 ⊣⊢ A_7 ⊣⊢ A_8 ⊣⊢ (q ∧ (◯⊥ ⊃ r)) ⊃ ◯⊥  ⊣⊢  θmax.

θmax is the GREATEST sufficient p-free formula, by substituting p := ⊥
in any derivation of θ, S ⊢ ◯p; so the ∀p pre-interpolant EXISTS at
this cell and this cell is NOT a Ghilardi–Zawadowski counterexample.
-/
import LaxLogic.LJFOSearch
import LaxLogic.LJFOFuel
import wip.ljfo_attack

open LJFO LJFOAttack PLLND

namespace LJFOUB

/-! ## 1. The cell -/

def stn : List Neg := [hyp, boxQ]                    -- ◯p ⊃ r, ◯q
def gG : Option Neg := some (.up (.down (.circ aP))) -- ↑↓◯p

def A (f : Nat) : Neg := interpF pv f [] stn gG
def Echain (f : Nat) : Neg := interpF pv f [] stn none

/-! ## 2. Verdicts (certificate-carrying; `unk` = budget exhaustion) -/

inductive R | yes | no | unk
deriving DecidableEq

def R.str : R → String
  | .yes => "PROVED"
  | .no  => "REFUTED"
  | .unk => "unk"

/-- `Γ ⊢ C` on the negative syntax, via the two certificate engines. -/
def ent (budget : Nat) (Γ : List Neg) (C : Neg) : R :=
  match Search.prove?Bounded budget (Γ.map negF) (negF C) with
  | some _ => .yes
  | none =>
    match Search.refute? {} (Γ.map negF) (negF C) with
    | some _ => .no
    | none => .unk

/-- `Γ ⊢ C` where the goal is an arbitrary `PLLFormula` (used for `◯p`). -/
def entF (budget : Nat) (Γ : List Neg) (C : PLLFormula) : R :=
  match Search.prove?Bounded budget (Γ.map negF) C with
  | some _ => .yes
  | none =>
    match Search.refute? {} (Γ.map negF) C with
    | some _ => .no
    | none => .unk

/-! ## 3. Display normaliser + printer.

UNTRUSTED and display-only: `dsimpN` rewrites by logical equivalences
(⊤∧X, ⊥∨X, ↑↓M ≡ M, ⊥⊃N ≡ ⊤, Q⊃⊤ ≡ ⊤).  Every formula printed through
it is separately certified interderivable with its original by the
engines (`phase print`), so the printed shape is a fact, not a claim
about the normaliser. -/

def isTopN (M : Neg) : Bool := decide (M = nTop)
def isBotN (M : Neg) : Bool := decide (M = nBot)

mutual
partial def dsimpN : Neg → Neg
  | .up (.or (.down M) (.down N)) =>          -- the `nOr` encoding
      let m := dsimpN M
      let n := dsimpN N
      if isBotN m then n else if isBotN n then m
      else if isTopN m || isTopN n then nTop
      else if decide (m = n) then m                 -- idempotence
      else nOr m n
  | .up (.down M) => dsimpN M
  | .up P => .up (dsimpP P)
  | .imp .fls _ => nTop
  | .imp Q N =>
      let n := dsimpN N
      let q := dsimpP Q
      if isTopN n then nTop
      else if decide (q = Pos.down nTop) then n     -- ⊤ ⊃ N ≡ N
      else if decide (q = Pos.fls) then nTop
      else if decide (q = Pos.down nBot) then nTop  -- ⊥ ⊃ N ≡ ⊤
      else .imp q n
  | .and M N =>
      let m := dsimpN M
      let n := dsimpN N
      if isTopN m then n else if isTopN n then m
      else if isBotN m || isBotN n then nBot
      else if decide (m = n) then m                 -- idempotence
      else .and m n
  | .circ P => .circ (dsimpP P)
partial def dsimpP : Pos → Pos
  | .down M => .down (dsimpN M)
  | .or P Q => .or (dsimpP P) (dsimpP Q)
  | .atom a => .atom a
  | .fls => .fls
end

mutual
partial def ppN (M : Neg) : String :=
  if isTopN M then "⊤" else if isBotN M then "⊥" else
  match M with
  | .up (.or (.down X) (.down Y)) => "(" ++ ppN X ++ " ∨ " ++ ppN Y ++ ")"
  | .up P => ppP P
  | .imp Q N => if isBotN N then "¬" ++ ppP Q
                else "(" ++ ppP Q ++ " ⊃ " ++ ppN N ++ ")"
  | .and X Y => "(" ++ ppN X ++ " ∧ " ++ ppN Y ++ ")"
  | .circ P => "◯" ++ ppP P
partial def ppP : Pos → String
  | .atom a => a
  | .fls => "⊥"
  | .or P Q => "(" ++ ppP P ++ " ∨ " ++ ppP Q ++ ")"
  | .down M => ppN M
end

def show1 (M : Neg) : String := ppN (dsimpN M)

/-! ## 4. The candidate bank (all p-free) -/

def bot : Neg := .up .fls                              -- ⊥
def boxBot : Neg := .circ .fls                         -- ◯⊥
def cimpBot : Neg := .imp (.down boxBot) uR            -- ◯⊥ ⊃ r  (= χ[p:=⊥])

/-- θ_max := (S[p:=⊥]) ⊃ ◯⊥ = ((◯⊥ ⊃ r) ∧ ◯q) ⊃ ◯⊥.  The ⊥-instance of
the whole cell: every sufficient θ must entail it (substitute p:=⊥ in
θ, S ⊢ ◯p), so it is an upper bound of `Suff` by construction. -/
def thMax : Neg := .imp (.down (.and cimpBot boxQ)) boxBot

/-- The curried form of `thMax`. -/
def thMaxC : Neg := .imp (.down boxQ) (.imp (.down cimpBot) boxBot)

/-- The unguarded ⊥-instance (drops ◯q): stronger than `thMax`. -/
def thBot : Neg := .imp (.down cimpBot) boxBot

/-- The hand-read normal form of `A_6`, obtained from `dsimpN (A 6)` by the
PLL depth-reducing laws (◯◯A ⊣⊢ ◯A, ◯(A ⊃ ◯B) ⊣⊢ A ⊃ ◯B, X ∨ Y ⊣⊢ Y when
X ⊢ Y).  The reading is a CONJECTURE until the engines certify
`A_6 ⊣⊢ h6` — which is what `phase h6` does. -/
def h6 : Neg := .imp (.down (.and uQ cimpBot)) boxBot   -- (q ∧ (◯⊥⊃r)) ⊃ ◯⊥

/-- Same for `A_4`. -/
def h4 : Neg := .imp aQ boxBot                          -- q ⊃ ◯⊥

def cands : List (String × Neg) :=
  [ ("θmax  = ((◯⊥⊃r) ∧ ◯q) ⊃ ◯⊥", thMax)
  , ("θmaxC = ◯q ⊃ ((◯⊥⊃r) ⊃ ◯⊥)", thMaxC)
  , ("θbot  = (◯⊥⊃r) ⊃ ◯⊥",        thBot)
  , ("◯⊥",                          boxBot)
  , ("◯(q ∧ ¬q)",   .circ (.down (.and uQ (.imp aQ bot))))
  , ("r ⊃ ◯⊥",      .imp aR boxBot)
  , ("¬¬◯⊥",        .imp (.down (.imp (.down boxBot) bot)) bot)
  , ("(r ⊃ ◯⊥) ⊃ ◯⊥", .imp (.down (.imp aR boxBot)) boxBot)
  , ("◯q ⊃ ◯⊥",     .imp (.down boxQ) boxBot)
  , ("q ⊃ ◯⊥",      .imp aQ boxBot)
  , ("◯(q ⊃ ◯⊥)",   .circ (.down (.imp aQ boxBot)))
  , ("◯q ⊃ ((◯⊥⊃r) ⊃ ◯q)  (weakened conclusion)",
       .imp (.down boxQ) (.imp (.down cimpBot) boxQ))
  , ("((◯⊥⊃r) ∧ ◯q) ⊃ ◯(q ⊃ ◯⊥)",
       .imp (.down (.and cimpBot boxQ)) (.circ (.down (.imp aQ boxBot))))
  , ("⊤  (control)", nTop)
  , ("◯r  (control)", .circ aR)
  , ("r ⊃ ◯q  (control)", .imp aR boxQ)
  ]

/-! ## 5. Countermodel display -/

def showModel (M : FinCM) (w : Nat) : String := Id.run do
  let mut s := s!"  worlds 0..{M.n - 1}, refuting world w = {w}\n"
  s := s ++ s!"  Rᵢ (non-refl) = {M.ri}\n"
  s := s ++ s!"  Rₘ (non-refl) = {M.rm}\n"
  s := s ++ s!"  fallible      = {M.fall}\n"
  s := s ++ s!"  valuation     = {M.val}\n"
  return s

def diagBank : List (String × PLLFormula) :=
  [ ("q",      .prop "q")
  , ("r",      .prop "r")
  , ("p",      .prop "p")
  , ("◯⊥",     .somehow .falsePLL)
  , ("◯q",     .somehow (.prop "q"))
  , ("◯r",     .somehow (.prop "r"))
  , ("◯⊥⊃r",   .ifThen (.somehow .falsePLL) (.prop "r"))
  , ("θmax",   negF thMax)
  , ("θbot",   negF thBot)
  ]

def forceTable (M : FinCM) : String := Id.run do
  let mut s := ""
  for (nm, φ) in diagBank do
    let row := (List.range M.n).map (fun v => if M.forceB v φ then "1" else "·")
    s := s ++ s!"  {nm} : " ++ String.intercalate "" row ++ "\n"
  return s

/-! ## 6. Phases -/

def phasePrint (budget : Nat) : IO Unit := do
  IO.println "== A_f, displayed (dsimp) + certified interderivable with the raw value"
  for f in [1, 2, 3, 4] do
    let a := A f
    let d := dsimpN a
    IO.println s!"-- A_{f}  |raw|={szN a}  |dsimp|={szN d}"
    IO.println s!"   {ppN d}"
    IO.println s!"   raw⊢dsimp = {(ent budget [a] d).str}   dsimp⊢raw = {(ent budget [d] a).str}"
    (← IO.getStdout).flush
  IO.println "== E_f (the ∃p companion), displayed"
  for f in [1, 2, 3] do
    let e := Echain f
    IO.println s!"-- E_{f}  |raw|={szN e}"
    IO.println s!"   {ppN (dsimpN e)}"
    (← IO.getStdout).flush

/-- Display the deeper chain values (no interderivability certification
attempted beyond the given budget — a `unk` there is budget exhaustion). -/
def phasePrint2 (budget : Nat) (fs : List Nat) : IO Unit := do
  for f in fs do
    let a := A f
    let d := dsimpN a
    IO.println s!"-- A_{f}  |raw|={szN a}  |dsimp|={szN d}"
    IO.println s!"   {ppN d}"
    (← IO.getStdout).flush
    IO.println s!"   raw⊢dsimp = {(ent budget [a] d).str}   dsimp⊢raw = {(ent budget [d] a).str}"
    (← IO.getStdout).flush

def phaseCand (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== candidate table (budget {budget}); (i) sufficiency, (ii) domination A_f ⊢ χ"
  -- control: the cell is nontrivial
  IO.println s!"-- control ⊤,S ⊢ ◯p : {(entF budget (nTop :: stn) (.somehow (posF aP))).str}"
  (← IO.getStdout).flush
  for (nm, c) in cands do
    let suf := entF budget (c :: stn) (.somehow (posF aP))
    let mut doms := ""
    for f in fs do
      doms := doms ++ s!" A_{f}⊢χ={(ent budget [A f] c).str}"
    let thm := ent budget [] c
    let up := ent budget [c] thMax
    IO.println s!"-- {nm}"
    IO.println s!"   (i) χ,S ⊢ ◯p = {suf.str}   (ii){doms}   [⊢χ alone = {thm.str}]  [χ⊢θmax = {up.str}]"
    (← IO.getStdout).flush

/-- The `dsimp` route to the deep rows.  `D_f := dsimpN (A_f)` is small;
each row certifies `A_f ⊣⊢ D_f` first, so any entailment proved of `D_f`
transfers to `A_f` by cut.  Nothing is assumed of the normaliser. -/
def phaseVia (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== the dsimp route (budget {budget})"
  for f in fs do
    let a := A f
    let d := dsimpN a
    IO.println s!"-- f={f}  |A_{f}|={szN a}  |D_{f}|={szN d}"
    IO.println s!"   D_{f} = {ppN d}"
    (← IO.getStdout).flush
    IO.println s!"   A_{f}⊢D_{f} = {(ent budget [a] d).str}   D_{f}⊢A_{f} = {(ent budget [d] a).str}"
    (← IO.getStdout).flush
    IO.println s!"   (i)  D_{f},S ⊢ ◯p = {(entF budget (d :: stn) (.somehow (posF aP))).str}"
    (← IO.getStdout).flush
    IO.println s!"   (ii) D_{f} ⊢ θmax = {(ent budget [d] thMax).str}   θmax ⊢ D_{f} = {(ent budget [thMax] d).str}"
    (← IO.getStdout).flush

/-- The chain, run on the display normal forms. -/
def phaseDChain (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== chain on the display normal forms (budget {budget})"
  for f in fs do
    let d1 := dsimpN (A f)
    let d2 := dsimpN (A (f + 1))
    IO.println s!"-- D_{f} (|{szN d1}|) vs D_{f+1} (|{szN d2}|)"
    IO.println s!"   D_{f}   = {ppN d1}"
    IO.println s!"   D_{f+1} = {ppN d2}"
    (← IO.getStdout).flush
    IO.println s!"   fwd D_{f}⊢D_{f+1} = {(ent budget [d1] d2).str}   bwd D_{f+1}⊢D_{f} = {(ent budget [d2] d1).str}"
    (← IO.getStdout).flush

/-- Is `A_6` already the greatest element?  The chain
`A_6 ⊣⊢ D_6 ⊣⊢ h6 ⊣⊢ θmax`, link by link, engines first. -/
def phaseH6 (budget : Nat) : IO Unit := do
  let a6 := A 6
  let d6 := dsimpN a6
  IO.println s!"== is A_6 already θmax?  (budget {budget})"
  IO.println s!"   |A_6|={szN a6}  |D_6|={szN d6}  |h6|={szN h6}  |θmax|={szN thMax}"
  IO.println s!"   h6   = {ppN h6}"
  IO.println s!"   θmax = {ppN thMax}"
  (← IO.getStdout).flush
  IO.println s!"-- h6 ⊢ θmax = {(ent budget [h6] thMax).str}   θmax ⊢ h6 = {(ent budget [thMax] h6).str}"
  (← IO.getStdout).flush
  IO.println s!"-- D_6 ⊢ h6  = {(ent budget [d6] h6).str}   h6 ⊢ D_6  = {(ent budget [h6] d6).str}"
  (← IO.getStdout).flush
  IO.println s!"-- A_6 ⊢ h6  = {(ent budget [a6] h6).str}   h6 ⊢ A_6  = {(ent budget [h6] a6).str}"
  (← IO.getStdout).flush
  IO.println s!"-- A_6 ⊢ D_6 = {(ent budget [a6] d6).str}   D_6 ⊢ A_6 = {(ent budget [d6] a6).str}"
  (← IO.getStdout).flush
  IO.println s!"-- (i) h6,S ⊢ ◯p = {(entF budget (h6 :: stn) (.somehow (posF aP))).str}"
  IO.println s!"-- A_4 ⊣⊢ h4?  A_4⊢h4 = {(ent budget [A 4] h4).str}  h4⊢A_4 = {(ent budget [h4] (A 4)).str}"
  (← IO.getStdout).flush

/-- The kernel searcher on the same links (a `true` result IS a kernel
derivation via `LJFO.LSeq.search_sound`). -/
def phaseKern6 (fuel : Nat) : IO Unit := do
  let a6 := A 6
  let d6 := dsimpN a6
  let a7 := A 7
  IO.println s!"== kernel searcher at fuel {fuel}"
  let rows : List (String × Neg × Neg) :=
    [ ("A_6 ⊢ D_6", a6, d6), ("D_6 ⊢ A_6", d6, a6)
    , ("A_6 ⊢ h6",  a6, h6), ("h6 ⊢ A_6",  h6, a6)
    , ("A_6 ⊢ θmax", a6, thMax), ("θmax ⊢ A_6", thMax, a6)
    , ("A_6 ⊢ A_7", a6, a7), ("A_7 ⊢ A_6", a7, a6) ]
  for (nm, x, y) in rows do
    let r := LSeq.search fuel (.inv [x] [] .tru y)
    IO.println s!"-- {nm} : {if r then "PROVED (kernel)" else "unk"}"
    (← IO.getStdout).flush

/-- The hard direction (`big ⊢ small`) at a raised budget. -/
def phasePush (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== hard direction at budget {budget}"
  for f in fs do
    let d := dsimpN (A f)
    IO.println s!"-- D_{f} (|{szN d}|) ⊢ θmax = {(ent budget [d] thMax).str}"
    (← IO.getStdout).flush
    IO.println s!"-- θmax ⊢ D_{f}            = {(ent budget [thMax] d).str}"
    (← IO.getStdout).flush

/-- The hard direction on the RAW values. -/
def phasePushRaw (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== hard direction, raw values, budget {budget}"
  for f in fs do
    let a := A f
    IO.println s!"-- A_{f} (|{szN a}|) ⊢ θmax = {(ent budget [a] thMax).str}"
    (← IO.getStdout).flush
    IO.println s!"-- θmax ⊢ A_{f}            = {(ent budget [thMax] a).str}"
    (← IO.getStdout).flush

/-- The kernel searcher on the `D`-level rows. -/
def phaseKernD (fuel : Nat) : IO Unit := do
  IO.println s!"== kernel searcher, D-level, fuel {fuel}"
  let rows : List (String × Neg × Neg) :=
    [ ("D_6 ⊢ θmax", dsimpN (A 6), thMax)
    , ("D_7 ⊢ θmax", dsimpN (A 7), thMax)
    , ("D_8 ⊢ θmax", dsimpN (A 8), thMax)
    , ("A_6 ⊢ θmax", A 6, thMax)
    , ("D_6 ⊢ D_7",  dsimpN (A 6), dsimpN (A 7))
    , ("D_7 ⊢ D_6",  dsimpN (A 7), dsimpN (A 6))
    , ("D_7 ⊢ D_8",  dsimpN (A 7), dsimpN (A 8))
    , ("D_8 ⊢ D_7",  dsimpN (A 8), dsimpN (A 7)) ]
  for (nm, x, y) in rows do
    let t0 ← IO.monoMsNow
    let r := LSeq.search fuel (.inv [x] [] .tru y)
    let t1 ← IO.monoMsNow
    IO.println s!"-- {nm} : {if r then "PROVED (kernel)" else "unk"}  [{t1 - t0} ms]"
    (← IO.getStdout).flush

/-- The kernel searcher on one deep row only (fuel is DEPTH fuel: a
successful search returns as soon as it finds a derivation, so raising
the fuel is cheap when a proof exists and expensive when it does not). -/
def phaseKern7 (fuel : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== kernel searcher, D_f ⊢ θmax, fuel {fuel}"
  for f in fs do
    let d := dsimpN (A f)
    let t0 ← IO.monoMsNow
    let r := LSeq.search fuel (.inv [d] [] .tru thMax)
    let t1 ← IO.monoMsNow
    IO.println s!"-- D_{f} (|{szN d}|) ⊢ θmax : {if r then "PROVED (kernel)" else "unk"}  [{t1 - t0} ms]"
    (← IO.getStdout).flush

/-- The kernel searcher on the RAW rows: the links `A_f ⊣⊢ D_f` that
transfer the D-level results to the chain itself, the chain steps, and
the soundness rows `A_f, S ⊢ ◯p`. -/
def phaseKernRaw (fuel : Nat) : IO Unit := do
  IO.println s!"== kernel searcher, raw rows, fuel {fuel}"
  let rows : List (String × List Neg × Neg) :=
    [ ("A_6 ⊢ D_6",  [A 6], dsimpN (A 6))
    , ("D_6 ⊢ A_6",  [dsimpN (A 6)], A 6)
    , ("A_6 ⊢ θmax", [A 6], thMax)
    , ("θmax ⊢ A_6", [thMax], A 6)
    , ("A_7 ⊢ θmax", [A 7], thMax)
    , ("θmax ⊢ A_7", [thMax], A 7)
    , ("A_8 ⊢ θmax", [A 8], thMax)
    , ("θmax ⊢ A_8", [thMax], A 8)
    , ("A_6 ⊢ A_7",  [A 6], A 7)
    , ("A_7 ⊢ A_6",  [A 7], A 6)
    , ("A_7 ⊢ A_8",  [A 7], A 8)
    , ("A_8 ⊢ A_7",  [A 8], A 7)
    , ("sound A_6: A_6,S ⊢ ↑↓◯p", A 6 :: stn, .up (.down (.circ aP)))
    , ("sound A_8: A_8,S ⊢ ↑↓◯p", A 8 :: stn, .up (.down (.circ aP)))
    , ("sound θmax: θmax,S ⊢ ↑↓◯p", thMax :: stn, .up (.down (.circ aP))) ]
  for (nm, Γ, y) in rows do
    let t0 ← IO.monoMsNow
    let r := LSeq.search fuel (.inv Γ [] .tru y)
    let t1 ← IO.monoMsNow
    IO.println s!"-- {nm} : {if r then "PROVED (kernel)" else "unk"}  [{t1 - t0} ms]"
    (← IO.getStdout).flush

/-! ### The certified decomposition

`D_f ⊢ θmax` as a monolithic sequent is past the engines at 4·10⁶ nodes
for f ≥ 7.  It splits, because `θmax` is `◯`-FIXED (`◯θmax ⊢ θmax`,
certified once) and the `D`-skeleton is built from `∨`, `∧` and `◯`:

    X ∨ Y ⊢ θ   from   X ⊢ θ  and  Y ⊢ θ      (∨-elimination)
    X ∧ Y ⊢ θ   from   X ⊢ θ                  (∧-elimination)
    ◯Z    ⊢ θ   from   Z ⊢ θ  and  ◯θ ⊢ θ     (◯-monotonicity, ◯-fixedness)

`reduceTo` tries the engine at each node and descends on these three
shapes when it fails; every leaf it reports is an engine certificate,
and the three steps above are rules of the calculus.  A `false` anywhere
makes the whole run inconclusive (printed as `LEAF-unk`). -/

def splitOr : Neg → Option (Neg × Neg)
  | .up (.or (.down X) (.down Y)) => some (X, Y)
  | _ => none

partial def reduceTo (budget : Nat) (Γ : List Neg) (θ : Neg) (depth : Nat)
    (M : Neg) : IO Bool := do
  let pad := String.mk (List.replicate (2 * depth) ' ')
  match ent budget (M :: Γ) θ with
  | .yes => IO.println s!"{pad}LEAF ⊢ ok  (|{szN M}|)"; return true
  | .no  => IO.println s!"{pad}LEAF REFUTED  (|{szN M}|) {ppN M}"; return false
  | .unk =>
    match splitOr M with
    | some (X, Y) =>
        IO.println s!"{pad}∨-split (|{szN M}|)"
        (← IO.getStdout).flush
        let a ← reduceTo budget Γ θ (depth + 1) X
        let b ← reduceTo budget Γ θ (depth + 1) Y
        return a && b
    | none =>
      match M with
      | .and X Y =>
          IO.println s!"{pad}∧-split (|{szN M}|)"
          (← IO.getStdout).flush
          let a ← reduceTo budget Γ θ (depth + 1) X
          if a then return true else reduceTo budget Γ θ (depth + 1) Y
      | .circ (.down Z) =>
          IO.println s!"{pad}◯-strip (|{szN M}|)"
          (← IO.getStdout).flush
          reduceTo budget Γ θ (depth + 1) Z
      | _ =>
          IO.println s!"{pad}LEAF-unk (|{szN M}|) {ppN M}"
          return false

def phaseSplit (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== certified decomposition of D_f ⊢ θmax (budget {budget})"
  IO.println s!"-- ◯θmax ⊢ θmax (◯-fixedness) = {(ent budget [.circ (.down thMax)] thMax).str}"
  (← IO.getStdout).flush
  for f in fs do
    IO.println s!"-- D_{f}:"
    let ok ← reduceTo budget [] thMax 1 (dsimpN (A f))
    IO.println s!"   ⇒ D_{f} ⊢ θmax : {if ok then "PROVED (decomposed)" else "inconclusive"}"
    (← IO.getStdout).flush

/-- The same decomposition run on the RAW chain values (the `nOr`/`nAnd`
encodings are exactly the `∨`/`∧` shapes `reduceTo` descends on), so the
result is about `A_f` itself, with no appeal to the display normaliser. -/
def phaseSplitRaw (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== certified decomposition of A_f ⊢ θmax, RAW (budget {budget})"
  IO.println s!"-- ◯θmax ⊢ θmax = {(ent budget [.circ (.down thMax)] thMax).str}"
  (← IO.getStdout).flush
  for f in fs do
    IO.println s!"-- A_{f} (|{szN (A f)}|):"
    let ok ← reduceTo budget [] thMax 1 (A f)
    IO.println s!"   ⇒ A_{f} ⊢ θmax : {if ok then "PROVED (decomposed)" else "inconclusive"}"
    (← IO.getStdout).flush
    IO.println s!"   θmax ⊢ A_{f} : {(ent budget [thMax] (A f)).str}"
    (← IO.getStdout).flush

/-- The SOUNDNESS rows by the same decomposition: `A_f, S ⊢ ↑↓◯p`.  The
`◯`-strip step is licensed here too — the goal `◯p` is `◯`-fixed and the
station persists into the lax phase. -/
def phaseSplitSound (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== certified decomposition of A_f, S ⊢ ↑↓◯p (budget {budget})"
  IO.println s!"-- ◯(↑↓◯p) ⊢ ↑↓◯p = {(ent budget [.circ (.down (.up (.down (.circ aP))))] (.up (.down (.circ aP)))).str}"
  (← IO.getStdout).flush
  for f in fs do
    IO.println s!"-- A_{f} (|{szN (A f)}|):"
    let ok ← reduceTo budget stn (.up (.down (.circ aP))) 1 (A f)
    IO.println s!"   ⇒ A_{f}, S ⊢ ◯p : {if ok then "PROVED (decomposed)" else "inconclusive"}"
    (← IO.getStdout).flush

/-- The easy direction on the deep rows (`θmax ⊢ D_f`), plus the sufficiency
of every `D_f` — the two facts that pin `D_f ⊣⊢ θmax` once the hard
direction lands. -/
def phaseEasy (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== easy direction + sufficiency, budget {budget}"
  for f in fs do
    let d := dsimpN (A f)
    IO.println s!"-- θmax ⊢ D_{f} (|{szN d}|) = {(ent budget [thMax] d).str}"
    (← IO.getStdout).flush
    IO.println s!"-- (i) D_{f},S ⊢ ◯p        = {(entF budget (d :: stn) (.somehow (posF aP))).str}"
    (← IO.getStdout).flush

/-- The structural reading: `θmax = E_3 ⊃ A_2`, i.e. the ∀p value is the
∃p value of the station (its ⊥-instance `(◯⊥⊃r) ∧ ◯q`) implying `◯⊥`. -/
def phaseEStruct (budget : Nat) : IO Unit := do
  let e3 := Echain 3
  let ant : Neg := .and cimpBot boxQ          -- (◯⊥⊃r) ∧ ◯q
  let comp : Neg := .imp (.down e3) (A 2)     -- E_3 ⊃ A_2
  IO.println s!"== structural reading (budget {budget})"
  IO.println s!"   E_3   = {ppN (dsimpN e3)}"
  IO.println s!"   ant   = {ppN ant}"
  IO.println s!"-- E_3 ⊢ ant = {(ent budget [e3] ant).str}   ant ⊢ E_3 = {(ent budget [ant] e3).str}"
  (← IO.getStdout).flush
  IO.println s!"-- (E_3 ⊃ A_2) ⊢ θmax = {(ent budget [comp] thMax).str}   θmax ⊢ (E_3 ⊃ A_2) = {(ent budget [thMax] comp).str}"
  (← IO.getStdout).flush

def phaseStrict (budget : Nat) : IO Unit := do
  IO.println s!"== is θmax STRICTLY above the chain?  θmax ⊢ A_f (budget {budget})"
  for f in [2, 4, 6] do
    IO.println s!"-- θmax ⊢ A_{f} : {(ent budget [thMax] (A f)).str}"
    (← IO.getStdout).flush
  IO.println s!"-- θmax ⊢ θbot : {(ent budget [thMax] thBot).str}"
  IO.println s!"-- θbot ⊢ θmax : {(ent budget [thBot] thMax).str}"
  IO.println s!"-- θmax ⊢ θmaxC: {(ent budget [thMax] thMaxC).str}"
  IO.println s!"-- θmaxC ⊢ θmax: {(ent budget [thMaxC] thMax).str}"

def phaseChain (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== chain extension (budget {budget})"
  for f in fs do
    let a1 := A f
    let a2 := A (f + 1)
    IO.println s!"-- A_{f} (|{szN a1}|) vs A_{f+1} (|{szN a2}|):"
    (← IO.getStdout).flush
    IO.println s!"   fwd A_{f}⊢A_{f+1} = {(ent budget [a1] a2).str}"
    (← IO.getStdout).flush
    IO.println s!"   bwd A_{f+1}⊢A_{f} = {(ent budget [a2] a1).str}"
    (← IO.getStdout).flush

def phaseSound (budget : Nat) (fs : List Nat) : IO Unit := do
  IO.println s!"== soundness A_f, S ⊢ ◯p (budget {budget})"
  for f in fs do
    IO.println s!"-- A_{f} (|{szN (A f)}|) : {(entF budget (A f :: stn) (.somehow (posF aP))).str}"
    (← IO.getStdout).flush

def phaseCM (i j : Nat) : IO Unit := do
  IO.println s!"== countermodel for the strict step A_{i} ⊬ A_{j}  (refute? on A_{i} ⊢ A_{j})"
  match Search.refute? {} [negF (A i)] (negF (A j)) with
  | none => IO.println "   no certified countermodel returned"
  | some wit =>
      IO.println (showModel wit.1 wit.2.1)
      IO.println "   forcing (world 0,1,2,… left to right; 1 = forced):"
      IO.print (forceTable wit.1)
      IO.println s!"   A_{i} at w: {wit.1.forceB wit.2.1 (negF (A i))}"
      IO.println s!"   A_{j} at w: {wit.1.forceB wit.2.1 (negF (A j))}"

def phaseKern (fuel : Nat) (pairs : List (Nat × Nat)) : IO Unit := do
  IO.println s!"== kernel searcher LSeq.search at fuel {fuel}"
  for (i, j) in pairs do
    let r := LSeq.search fuel (.inv [A i] [] .tru (A j))
    IO.println s!"-- A_{i} ⊢ A_{j} : {if r then "PROVED (kernel)" else "unk"}"
    (← IO.getStdout).flush

def phaseKernC (fuel : Nat) : IO Unit := do
  IO.println s!"== kernel searcher on the candidate rows at fuel {fuel}"
  for f in [2, 4, 6] do
    let r := LSeq.search fuel (.inv [A f] [] .tru thMax)
    IO.println s!"-- A_{f} ⊢ θmax : {if r then "PROVED (kernel)" else "unk"}"
    (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  let bud := args[1]?.bind (·.toNat?) |>.getD 400000
  match args[0]? with
  | some "print"  => phasePrint 200000
  | some "print2" => phasePrint2 bud [5, 6]
  | some "print3" => phasePrint2 bud [7]
  | some "cand"   => phaseCand bud [2, 4, 6]
  | some "cand8"  => phaseCand bud [8]
  | some "strict" => phaseStrict bud
  | some "chain"  => phaseChain bud [6, 7]
  | some "sound"  => phaseSound bud [6, 8]
  | some "h6"     => phaseH6 bud
  | some "push"   => phasePush bud [6, 7, 8]
  | some "pushraw"=> phasePushRaw bud [6]
  | some "pushraw7" => phasePushRaw bud [7]
  | some "pushraw8" => phasePushRaw bud [8]
  | some "kernD"  => phaseKernD bud
  | some "kernR"  => phaseKernRaw bud
  | some "kern7"  => phaseKern7 bud [7]
  | some "kern8"  => phaseKern7 bud [8]
  | some "split"  => phaseSplit bud [7, 8]
  | some "split6" => phaseSplit bud [6]
  | some "splitraw" => phaseSplitRaw bud [6, 7]
  | some "splitraw8" => phaseSplitRaw bud [8]
  | some "splitsnd" => phaseSplitSound bud [6, 8]
  | some "estruct" => phaseEStruct bud
  | some "easy"   => phaseEasy bud [7, 8]
  | some "kern6"  => phaseKern6 bud
  | some "via"    => phaseVia bud [5, 6]
  | some "via8"   => phaseVia bud [7, 8]
  | some "dchain" => phaseDChain bud [4, 5, 6, 7]
  | some "cm"     => phaseCM 6 5
  | some "cm12"   => phaseCM 2 1
  | some "cm34"   => phaseCM 4 3
  | some "kern"   => phaseKern bud [(6, 7), (7, 6), (7, 8), (8, 7)]
  | some "kernc"  => phaseKernC bud
  | _ => IO.println "usage: ubrun <print|cand|cand8|strict|chain|sound|cm|cm12|cm34|kern|kernc> [budget]"
  IO.println "DONE"
  return 0

end LJFOUB

def main (args : List String) : IO UInt32 := LJFOUB.main args
