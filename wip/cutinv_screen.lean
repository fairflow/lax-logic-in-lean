/-
# `cutinvscreen` — the REFUTE-FIRST screen for `CutInv`

`wip/ui_routeB_n3.lean` proves N3 backward and N6 relative to ONE
typed obligation,

    CutInv := ∀ (Γ Δ : List Neg) (j : JD) (N ψ : Neg),
                Inv Γ [] .tru N → Inv (N :: Δ) [] j ψ → Inv (Γ ++ Δ) [] j ψ

— cut at a negative formula, in the inversion phase, with an empty
pending zone.  Before a cut-admissibility proof for LJF◯ is scoped, the
statement is tested for counterexamples (`CLAUDE.md`, "Testing for
counterexamples").

**What a counterexample can be.**  `Inv.sound` erases any `Inv` to a
`LaxND` derivation and `LaxND` composes derivations without cut
(`OBridge.subst1`), so the ERASURE of a would-be counterexample's
conclusion is always PLL-provable.  `CutInv` can therefore fail only
through incompleteness of LJF◯ at a polarisation outside the image of
`negOfO` — the bridge's completeness `FocalizationPLL` covers only
contexts and goals of that shape, whereas route (B)'s interpolants and
processed stations carry double shifts `↑↓`, `↓↑`.  So the screened
statement is

    PolInv := ∀ (Γ : List Neg) (j : JD) (ψ : Neg),
                Nonempty (LaxND (eraseCtx Γ) (goal j (eraseNeg ψ)))
                → Nonempty (Inv Γ [] j ψ)

(the hypothesis is exactly the conclusion of `Inv.sound` at `Ω = []`),
of which `CutInv` is a consequence.  A `PolInv` failure refutes
`CutInv`'s route through the bridge; it refutes `CutInv` itself only
when the two `CutInv` premises are inhabited at the failing sequent,
which stratum `vi` tests directly.

**The two oracles.**  The erasure is decided by
`FRJ.Gbu.W.decideLaxND` (the FRJW dichotomy, `[propext, Quot.sound]`),
used here as a computation.  The polarised sequent is searched with
`LJFO.LSeq.search`, which is SOUND at every fuel (`search_sound`
rebuilds the derivation) and COMPLETE at fuel = derivation height
(`search_complete_h`).  Both facts matter for the verdicts: a `search`
hit is a certificate, and a `search` miss at fuel `n` says exactly
"no derivation of height ≤ n" — never "no derivation".  So the verdicts
are three-valued:

    pass    the erasure is provable and the search found a derivation
    unprov  the erasure is not PLL-provable — no claim is made
    flag    the erasure is provable and no derivation of height ≤ n

and a `flag` is a frontier marker, re-run at a raised budget.  `fail`
is reserved for a certificate (`succs` empty, hence `search n = false`
at every `n`, hence `IsEmpty (Inv …)`); `Screen.certEmpty` below issues
those, and `wip/cutinv_screen_cert.lean` turns two of them into kernel
theorems.
-/
import LJF.OSearch
import LJF.OBridge
import LJF.OFuelP
import LJF.OFuelPSound
import FRJ.Gbu.W.LaxND

namespace CutInvScreen

open LJFO PLLND

/-! ## 1. Display -/

mutual

def ppPos : Pos → String
  | .atom a => a
  | .fls => "⊥"
  | .or P Q => "(" ++ ppPos P ++ "∨" ++ ppPos Q ++ ")"
  | .down N => "↓" ++ ppNeg N

def ppNeg : Neg → String
  | .up P => "↑" ++ ppPos P
  | .imp Q N => "(" ++ ppPos Q ++ "⊃" ++ ppNeg N ++ ")"
  | .and M N => "(" ++ ppNeg M ++ "∧" ++ ppNeg N ++ ")"
  | .circ P => "◯" ++ ppPos P

end

def ppCtx (Γ : List Neg) : String :=
  if Γ.isEmpty then "·" else String.intercalate ", " (Γ.map ppNeg)

def ppJD : JD → String
  | .tru => " ⊢ "
  | .lax => " ⊢lax "

def ppSeq (Γ : List Neg) (j : JD) (ψ : Neg) : String :=
  ppCtx Γ ++ ppJD j ++ ppNeg ψ

mutual

def sizePos : Pos → Nat
  | .atom _ => 1
  | .fls => 1
  | .or P Q => sizePos P + sizePos Q + 1
  | .down N => sizeNeg N + 1

def sizeNeg : Neg → Nat
  | .up P => sizePos P + 1
  | .imp Q N => sizePos Q + sizeNeg N + 1
  | .and M N => sizeNeg M + sizeNeg N + 1
  | .circ P => sizePos P + 1

end

def sizeCell (Γ : List Neg) (ψ : Neg) : Nat :=
  (Γ.map sizeNeg).foldr (· + ·) 0 + sizeNeg ψ

/-! ## 2. The two oracles -/

/-- The erasure of the cell, closed as one formula: `⌊Γ⌋ ⊃ … ⊃ goal j ⌊ψ⌋`.
`LaxND` has `impIntro`/`impElim`, so this is provable in the empty context
exactly when `eraseCtx Γ ⊢ goal j (eraseNeg ψ)` is. -/
def closeErasure (Γ : List Neg) (j : JD) (ψ : Neg) : PLLFormula :=
  (eraseCtx Γ).foldr PLLFormula.ifThen (goal j (eraseNeg ψ))

/-- **Oracle 1** — PLL provability of the erasure, by the FRJW decision
procedure.  Used as a computation: this is a screen, untrusted-but-safe;
the verdict it produces is `unprov` (no claim) or a licence to search. -/
def erasureProvable (φ : PLLFormula) : Bool :=
  match FRJ.Gbu.W.decideLaxND φ with
  | isTrue _ => true
  | isFalse _ => false

/-- **Oracle 2** — the focused kernel search.  `true` is certified by
`LSeq.search_sound`; `false` says only "no derivation of height ≤ n"
(`LSeq.search_complete_h`). -/
def invSearch (n : Nat) (Γ : List Neg) (j : JD) (ψ : Neg) : Bool :=
  LSeq.search n (.inv Γ [] j ψ)

/-- **Certified emptiness.**  When the goal sequent has NO backward rule
instance at all, `search n = false` at every `n`, so completeness at
fuel = height makes `Inv Γ [] j ψ` empty outright.  This is the one
place the screen may say `fail`. -/
def noRuleAtAll (Γ : List Neg) (j : JD) (ψ : Neg) : Bool :=
  (LSeq.succs (.inv Γ [] j ψ)).isEmpty

/-! ## 3. Cells -/

structure Cell where
  stratum : String
  ctx : List Neg
  jd : JD
  goal : Neg
  note : String := ""

/-! ## 4. Enumeration

### 4.1 PLL formulas by size, and the `negOfO` image (stratum i) -/

def atomsL : List String := ["a", "b", "c"]

/-- `pllTable k` is a list indexed by size: entry `s` holds every PLL
formula with exactly `s` nodes over `atomsL ∪ {⊥}`. -/
def pllTable : Nat → List (List PLLFormula)
  | 0 => [[]]
  | n + 1 =>
    let prev := pllTable n
    let sz := n + 1
    let here : List PLLFormula :=
      if sz == 1 then PLLFormula.falsePLL :: atomsL.map PLLFormula.prop
      else
        (prev.getD n []).map PLLFormula.somehow ++
        ((List.range (sz - 2)).map (· + 1)).flatMap (fun a =>
          let A := prev.getD a []
          let B := prev.getD (sz - 1 - a) []
          A.flatMap (fun x => B.flatMap (fun y =>
            [PLLFormula.and x y, PLLFormula.or x y, PLLFormula.ifThen x y])))
    prev ++ [here]

def pllUpTo (k : Nat) : List PLLFormula := (pllTable k).flatten

/-! ### 4.2 Double-shift insertion (strata ii, iii)

`↑↓` at a negative position, `↓↑` at a positive one — the two shapes
that take a formula OUT of the image of `negOfO`/`posOfO`. -/

mutual

/-- Every way of inserting ONE double shift into a negative. -/
def insN : Neg → List Neg
  | .up P => Neg.up (.down (.up P)) :: (insP P).map Neg.up
  | .imp Q N =>
      Neg.up (.down (.imp Q N)) ::
        ((insP Q).map (fun Q' => Neg.imp Q' N) ++
         (insN N).map (fun N' => Neg.imp Q N'))
  | .and M N =>
      Neg.up (.down (.and M N)) ::
        ((insN M).map (fun M' => Neg.and M' N) ++
         (insN N).map (fun N' => Neg.and M N'))
  | .circ P => Neg.up (.down (.circ P)) :: (insP P).map Neg.circ

/-- Every way of inserting ONE double shift into a positive. -/
def insP : Pos → List Pos
  | .atom a => [Pos.down (.up (.atom a))]
  | .fls => [Pos.down (.up .fls)]
  | .or P Q =>
      Pos.down (.up (.or P Q)) ::
        ((insP P).map (fun P' => Pos.or P' Q) ++
         (insP Q).map (fun Q' => Pos.or P Q'))
  | .down N =>
      Pos.down (.up (.down N)) :: (insN N).map Pos.down

end

def insN2 (N : Neg) : List Neg := (insN N).flatMap insN

/-! ### 4.3 The route-(B) shapes (stratum iv) -/

def pA : Pos := .atom "a"
def pB : Pos := .atom "b"
def pC : Pos := .atom "c"
def nA : Neg := .up pA
def nB : Neg := .up pB
def nC : Neg := .up pC

/-- Small negatives used to fill the route-(B) shape templates. -/
def smallNeg : List Neg :=
  [ nA, nB, .up .fls, .circ pA, .imp pB nA, .and nA nB
  , .up (.down (.circ pA)), .up (.or pA pB) ]

/-- Small positives used to fill the route-(B) shape templates. -/
def smallPos : List Pos :=
  [ pA, pB, .fls, .or pA pB, .down (.circ pA), .down (.imp pB nA)
  , .down (.up pA) ]

/-- The eight `ParkedNP` shapes, instantiated small.  These are exactly
the hypotheses a saturated route-(B) station may carry
(`LJF/OFuelP.lean`, `ParkedNP`). -/
def parkedShapes : List Neg :=
  [ .up (.atom "a")                                             -- atom
  , .imp (.atom "c") nA                                         -- qimp
  , .imp (.down (.imp pC nA)) nB                                -- dyk
  , .circ pA                                                    -- box
  , .imp (.down (.circ pC)) nA                                  -- cimp
  , .imp (.or pA pB) nC                                         -- oimp
  , .imp (.down (.up pA)) nB                                    -- simp
  , .imp (.down (.and nA nB)) nC                                -- aimp
  , .imp (.down (.circ (.down (.imp (.atom "d") nA)))) (.up (.atom "e"))
                                                                -- the S1 ◯-implication
  ]

/-- The goal shapes route (B) actually presents to `CutInv`: `◯↓↑P`,
`↓↑P ⊃ N`, the `∃p`/`∀p` row forms `(↓X ⊃ Y) ∧ Z` and `◯↓(X ∨ Y)`. -/
def routeBGoals : List Neg :=
  (smallPos.map (fun P => Neg.circ (.down (.up P)))) ++
  (smallPos.flatMap (fun P => smallNeg.map (fun N => Neg.imp (.down (.up P)) N))) ++
  (smallNeg.flatMap (fun X => smallNeg.flatMap (fun Y =>
      [Neg.and (.imp (.down X) Y) nC, Neg.and (.imp (.down X) Y) (.circ pA)]))) ++
  (smallPos.flatMap (fun X => smallPos.map (fun Y =>
      Neg.circ (.down (.up (.or X Y))))))

/-! ### 4.4 The corpus (stratum v): the stations and the interpolants -/

def stations : List (String × List Neg × List Neg) :=
  [ ("s1", s1Station, [.up (.atom "e"), .circ (.atom "g"), nA])
  , ("dyk", dykStation, [.up (.atom "e"), nA, .circ pA])
  , ("strip", sStripStation, [.up (.atom "e"), nA])
  , ("or", sOrStation, [.up (.atom "e"), nA])
  , ("and", sAndStation, [.up (.atom "e"), nA])
  ]

/-! ## 5. The strata -/

def stratumI (gsz csz clen : Nat) : List Cell :=
  let goals := pllUpTo gsz
  let ctxF := pllUpTo csz
  let ctxs : List (List PLLFormula) :=
    [[]] ++ (if clen ≥ 1 then ctxF.map (fun x => [x]) else []) ++
    (if clen ≥ 2 then ctxF.flatMap (fun x => ctxF.map (fun y => [x, y])) else [])
  ctxs.flatMap (fun Γ0 => goals.map (fun φ =>
    { stratum := "i", ctx := Γ0.map negOfO, jd := .tru, goal := negOfO φ
    , note := "negOfO image" }))

/-- The same image at the LAX flag.  `FocalizationPLL` says nothing here
— `Inv Γ [] .lax C` has rules only for `C = ↑P` and `C = ◯P` — so this is
a stratum in its own right, not part of the positive control. -/
def stratumILax (gsz csz clen : Nat) : List Cell :=
  let goals := pllUpTo gsz
  let ctxF := pllUpTo csz
  let ctxs : List (List PLLFormula) :=
    [[]] ++ (if clen ≥ 1 then ctxF.map (fun x => [x]) else []) ++
    (if clen ≥ 2 then ctxF.flatMap (fun x => ctxF.map (fun y => [x, y])) else [])
  ctxs.flatMap (fun Γ0 => goals.map (fun φ =>
    { stratum := "i-lax", ctx := Γ0.map negOfO, jd := .lax, goal := negOfO φ
    , note := "negOfO image, lax flag" }))

/-- One double shift, at every admissible position, in the goal and in
each context formula. -/
def stratumII (gsz csz : Nat) (js : List JD) : List Cell :=
  let goals := pllUpTo gsz
  let ctxF := pllUpTo csz
  let goalIns : List Cell :=
    js.flatMap (fun j => goals.flatMap (fun φ =>
      (insN (negOfO φ)).flatMap (fun ψ =>
        ([] :: ctxF.map (fun x => [negOfO x])).map (fun Γ =>
          { stratum := "ii", ctx := Γ, jd := j, goal := ψ
          , note := "one ↑↓/↓↑ in the goal" }))))
  let ctxIns : List Cell :=
    js.flatMap (fun j => goals.flatMap (fun φ =>
      ctxF.flatMap (fun x => (insN (negOfO x)).map (fun X =>
        { stratum := "ii", ctx := [X], jd := j, goal := negOfO φ
        , note := "one ↑↓/↓↑ in the hypothesis" }))))
  goalIns ++ ctxIns

def stratumIII (gsz csz : Nat) (js : List JD) : List Cell :=
  let goals := pllUpTo gsz
  let ctxF := pllUpTo csz
  js.flatMap (fun j => goals.flatMap (fun φ =>
    (insN2 (negOfO φ)).flatMap (fun ψ =>
      ([] :: ctxF.map (fun x => [negOfO x])).map (fun Γ =>
        { stratum := "iii", ctx := Γ, jd := j, goal := ψ
        , note := "two ↑↓/↓↑ in the goal" })))) ++
  js.flatMap (fun j => goals.flatMap (fun φ =>
    ctxF.flatMap (fun x => (insN2 (negOfO x)).map (fun X =>
      { stratum := "iii", ctx := [X], jd := j, goal := negOfO φ
      , note := "two ↑↓/↓↑ in the hypothesis" }))))

def stratumIV (js : List JD) : List Cell :=
  js.flatMap (fun j =>
    parkedShapes.flatMap (fun H => routeBGoals.map (fun G =>
      { stratum := "iv", ctx := [H], jd := j, goal := G
      , note := "ParkedNP hypothesis × route-(B) goal" }))) ++
  js.flatMap (fun j =>
    parkedShapes.flatMap (fun H1 => parkedShapes.flatMap (fun H2 =>
      routeBGoals.take 8 |>.map (fun G =>
        { stratum := "iv", ctx := [H1, H2], jd := j, goal := G
        , note := "two ParkedNP hypotheses × route-(B) goal" }))))

def stratumV (fuels : List Nat) (js : List JD) : List Cell :=
  -- the stations with their own goals
  (stations.flatMap (fun (nm, done, gs) =>
    js.flatMap (fun j => gs.map (fun G =>
      { stratum := "v", ctx := done, jd := j, goal := G
      , note := "station " ++ nm })))) ++
  -- the interpolants as GOALS at a station
  (stations.flatMap (fun (nm, done, gs) =>
    fuels.flatMap (fun f =>
      [ { stratum := "v", ctx := done, jd := JD.tru
        , goal := interpP "p" f [] done none
        , note := "station " ++ nm ++ " ⊢ E_" ++ toString f : Cell }
      , { stratum := "v", ctx := done, jd := JD.tru
        , goal := interpP "p" f [] done (some (gs.headD nA))
        , note := "station " ++ nm ++ " ⊢ A_" ++ toString f } ]))) ++
  -- the interpolants as HYPOTHESES: `E_f ⊢ E_f` and `E_f, A_f ⊢ goal`
  (stations.flatMap (fun (nm, done, gs) =>
    fuels.flatMap (fun f =>
      let E := interpP "p" f [] done none
      let A := interpP "p" f [] done (some (gs.headD nA))
      [ { stratum := "v", ctx := [E], jd := JD.tru, goal := E
        , note := "E_" ++ toString f ++ " ⊢ E_" ++ toString f ++ " at " ++ nm : Cell }
      , { stratum := "v", ctx := [A], jd := JD.tru, goal := gs.headD nA
        , note := "A_" ++ toString f ++ " ⊢ G at " ++ nm }
      , { stratum := "v", ctx := [E, A], jd := JD.tru, goal := gs.headD nA
        , note := "E_" ++ toString f ++ ", A_" ++ toString f ++ " ⊢ G at " ++ nm } ])))

def strataOf (name : String) : List Cell :=
  match name with
  | "i" => stratumI 3 2 2
  | "i-lax" => stratumILax 3 2 1
  | "ii" => stratumII 2 2 [.tru, .lax]
  | "iii" => stratumIII 2 1 [.tru, .lax]
  | "iv" => stratumIV [.tru, .lax]
  | "v" => stratumV [1, 2, 3, 4] [.tru, .lax]
  | "i-big" => stratumI 4 2 2
  | _ => []

/-! ## 6. The direct `CutInv` screen (stratum vi)

Enumerate `(Γ, Δ, N, j, ψ)` directly and search for BOTH premises.  Only
when both are found is the conclusion searched — so a `flag` here is a
candidate refutation of `CutInv` itself, not merely of `PolInv`. -/

structure CutCell where
  ctx1 : List Neg          -- Γ
  cut : Neg                -- N
  ctx2 : List Neg          -- Δ
  jd : JD
  goal : Neg               -- ψ
  note : String := ""

/-- Cut formulas: the shapes route (B) cuts at — an interpolant, hence a
conjunction of guarded implications — plus the shift shapes. -/
def cutFormulas : List Neg :=
  [ nA, nB, .up .fls, .circ pA, .up (.down (.circ pA))
  , .imp pB nA, .and nA nB, .up (.down (.imp pB nA))
  , .up (.or pA pB), .and (.imp (.down nA) nB) nC
  , .imp (.down (.up pA)) nB, .circ (.down (.up pA))
  , .and (.imp (.down (.circ pA)) nB) (.circ pC)
  ]

def stratumVI (js : List JD) : List CutCell :=
  let ctx1s : List (List Neg) := [[], [nA], [.circ pA], [.imp pA nB], [nA, nB]]
  let ctx2s : List (List Neg) := [[], [nB], [.imp pB nC], [.circ pB]]
  let goals : List Neg :=
    [ nC, nA, .up .fls, .circ pC, .up (.down (.circ pC))
    , .imp pA nC, .and nA nC, .up (.down (.imp pA nC))
    , .circ (.down (.up pC)), .imp (.down (.up pA)) nC ]
  js.flatMap (fun j =>
    ctx1s.flatMap (fun Γ =>
      cutFormulas.flatMap (fun N =>
        ctx2s.flatMap (fun Δ =>
          goals.map (fun ψ =>
            { ctx1 := Γ, cut := N, ctx2 := Δ, jd := j, goal := ψ
            , note := "direct cut" })))))

/-! ### 6b. Stratum vi-b — cut cells built so that BOTH premises hold

Stratum `vi` enumerates blindly and most of its cells lose a premise.
Here the two premises are built from templates that make them derivable
by construction — `Γ` derives `N` by `∧`-elimination, a shift round trip,
an `∨`-branch or modus ponens; `N, Δ ⊢ⱼ ψ` holds by identity, a shift, a
`∧`/`⊃`/`◯` introduction, or by firing an implication `↓N ⊃ Y` on `N`.
The conclusion `Γ, Δ ⊢ⱼ ψ` then needs an ACTUAL cut, so this is the
stratum where a refutation of `CutInv` would show up. -/

/-- Contexts that derive the cut formula `N`. -/
def leftTemplates (N : Neg) : List (String × List Neg) :=
  [ ("id", [N])
  , ("and1", [.and N nB])
  , ("and2", [.and nB N])
  , ("upDown", [.up (.down N)])
  , ("orBoth", [.up (.or (.down N) (.down N))])
  , ("mp", [.imp pA N, nA])
  , ("andShift", [.and (.up (.down N)) nB])
  , ("orMixed", [.up (.or (.down N) (.down (.and N nB)))])
  ]

/-- `(Δ, ψ)` such that `N, Δ ⊢ⱼ ψ` is derivable. -/
def rightTemplates (N : Neg) : List (String × List Neg × Neg) :=
  [ ("id", [], N)
  , ("upDown", [], .up (.down N))
  , ("and", [nB], .and N nB)
  , ("wkImp", [], .imp pA N)
  , ("circ", [], .circ (.down N))
  , ("fire", [.imp (.down N) nC], nC)
  , ("fireShift", [.imp (.down N) nC], .up (.down nC))
  , ("fireCirc", [.imp (.down N) (.circ pC)], .circ pC)
  , ("fireAnd", [.imp (.down N) (.and nB nC)], .and nB nC)
  , ("fireTwice", [.imp (.down N) (.imp (.down N) nC)], nC)
  ]

/-- The cut formulas: atoms and boxes, then every shift-carrying and
route-(B) shape (`↑↓M`, `↓↑P ⊃ N`, `◯↓↑P`, `(↓X ⊃ Y) ∧ Z`, the Dyckhoff
and ◯-implication parked shapes). -/
def coreCuts : List Neg :=
  [ nA
  , .circ pA
  , .imp pB nA
  , .and nA nB
  , .up (.or pA pB)
  , .up (.down (.imp pB nA))
  , .imp (.down (.up pA)) nB
  , .circ (.down (.up pA))
  , .and (.imp (.down nA) nB) nC
  , .up (.down (.circ pA))
  , .imp (.down (.circ pA)) nB
  , .imp (.down (.imp pC nA)) nB
  , .circ (.down (.up (.or pA pB)))
  ]

def stratumVIb (js : List JD) : List CutCell :=
  js.flatMap (fun j =>
    coreCuts.flatMap (fun N =>
      (leftTemplates N).flatMap (fun (ln, Γ) =>
        (rightTemplates N).map (fun (rn, Δ, ψ) =>
          { ctx1 := Γ, cut := N, ctx2 := Δ, jd := j, goal := ψ
          , note := ln ++ "/" ++ rn }))))

/-! ## 7. Running -/

def verdictLine (idx : Nat) (c : Cell) (verdict : String) (budget : String)
    (oracleMs searchMs : Nat) : String :=
  s!"{idx}\t{c.stratum}\t{verdict}\t{budget}\t{oracleMs}\t{searchMs}\t{sizeCell c.ctx c.goal}\t{c.note}\t{ppSeq c.ctx c.jd c.goal}"

/-- One cell.  `budgets` is tried in increasing order; the first hit
wins.  A miss at every budget is a `flag` (a frontier marker), unless the
sequent has no backward rule instance at all, in which case the search's
completeness at fuel = height makes it a certified `fail`. -/
def runCell (budgets : List Nat) (idx : Nat) (c : Cell) : IO Unit := do
  let φ := closeErasure c.ctx c.jd c.goal
  let t0 ← IO.monoMsNow
  let pv := erasureProvable φ
  let t1 ← IO.monoMsNow
  let out ← IO.getStdout
  if !pv then
    out.putStrLn (verdictLine idx c "unprov" "-" (t1 - t0) 0)
    out.flush
    return
  let mut hit : Option Nat := none
  let t2 ← IO.monoMsNow
  for n in budgets do
    if hit.isNone then
      if invSearch n c.ctx c.jd c.goal then hit := some n
  let t3 ← IO.monoMsNow
  match hit with
  | some n => out.putStrLn (verdictLine idx c "pass" (toString n) (t1 - t0) (t3 - t2))
  | none =>
      if noRuleAtAll c.ctx c.jd c.goal then
        out.putStrLn (verdictLine idx c "fail" "no-rule" (t1 - t0) (t3 - t2))
      else
        out.putStrLn
          (verdictLine idx c "flag" (toString (budgets.foldr Nat.max 0)) (t1 - t0) (t3 - t2))
  out.flush

def runStratum (name : String) (start : Nat) (budgets : List Nat) : IO Unit := do
  let cells := strataOf name
  let out ← IO.getStdout
  out.putStrLn s!"# stratum {name} cells={cells.length} start={start} budgets={budgets}"
  out.flush
  let mut i := start
  for c in cells.drop start do
    runCell budgets i c
    i := i + 1
  out.putStrLn s!"# END {name} {i}"
  out.flush

/-- One `CutInv` cell: search both premises, and only if both are found,
search the conclusion. -/
def runCutCell (st : String) (pb cb : Nat) (idx : Nat) (c : CutCell) : IO Unit := do
  let out ← IO.getStdout
  let seqTxt :=
    ppCtx c.ctx1 ++ " ⊢ " ++ ppNeg c.cut ++ "   |   " ++
    ppCtx (c.cut :: c.ctx2) ++ ppJD c.jd ++ ppNeg c.goal ++ "   ⟹   " ++
    ppCtx (c.ctx1 ++ c.ctx2) ++ ppJD c.jd ++ ppNeg c.goal
  let t0 ← IO.monoMsNow
  let p1 := invSearch pb c.ctx1 .tru c.cut
  if !p1 then
    let t1 ← IO.monoMsNow
    out.putStrLn s!"{idx}\t{st}\tprem1-miss\t{pb}\t0\t{t1 - t0}\t0\t{c.note}\t{seqTxt}"
    out.flush
    return
  let p2 := invSearch pb (c.cut :: c.ctx2) c.jd c.goal
  if !p2 then
    let t1 ← IO.monoMsNow
    out.putStrLn s!"{idx}\t{st}\tprem2-miss\t{pb}\t0\t{t1 - t0}\t0\t{c.note}\t{seqTxt}"
    out.flush
    return
  -- both premises inhabited (certified by `search_sound`): the conclusion must hold
  let concl := invSearch cb (c.ctx1 ++ c.ctx2) c.jd c.goal
  let t1 ← IO.monoMsNow
  let v := if concl then "pass" else "flag"
  out.putStrLn s!"{idx}\t{st}\t{v}\t{pb}/{cb}\t0\t{t1 - t0}\t0\t{c.note}\t{seqTxt}"
  out.flush

def runCut (which : String) (start pb cb : Nat) : IO Unit := do
  let cells := if which == "vi-b" then stratumVIb [.tru, .lax] else stratumVI [.tru, .lax]
  let out ← IO.getStdout
  out.putStrLn s!"# stratum {which} cells={cells.length} start={start} premBudget={pb} conclBudget={cb}"
  out.flush
  let mut i := start
  for c in cells.drop start do
    runCutCell which pb cb i c
    i := i + 1
  out.putStrLn s!"# END {which} {i}"
  out.flush

/-! ## 8. The gate

Two injected defects, each of which the screen must report, run by
`--gate`:

* `bad-oracle`: an oracle that answers `true` on an UNPROVABLE erasure.
  With a sound oracle the cell is `unprov`; with the defect it becomes a
  `flag` — a false alarm the stratum table would carry.
* `zero-budget`: a search budget of `0`.  `search 0 = false` always, so
  every provable cell becomes a `flag`.

Both are run on cells whose correct verdicts are known, and the honest
verdict is printed beside the defective one. -/
def gateCells : List Cell :=
  [ { stratum := "gate", ctx := [], jd := .tru, goal := negOfO (.prop "a")
    , note := "control: ⊢ a is NOT provable" }
  , { stratum := "gate", ctx := [nA], jd := .tru, goal := nA
    , note := "control: a ⊢ a is provable, height small" } ]

def runGate : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn "# GATE: injected defects, each must be visible in the verdict"
  for c in gateCells do
    let φ := closeErasure c.ctx c.jd c.goal
    let pv := erasureProvable φ
    let honest := if !pv then "unprov"
      else if invSearch 12 c.ctx c.jd c.goal then "pass" else "flag"
    -- defect 1: the oracle always says "provable"
    let badOracle := true
    let d1 := if !badOracle then "unprov"
      else if invSearch 12 c.ctx c.jd c.goal then "pass" else "flag"
    -- defect 2: budget 0
    let d2 := if !pv then "unprov"
      else if invSearch 0 c.ctx c.jd c.goal then "pass" else "flag"
    out.putStrLn s!"gate\thonest={honest}\tbad-oracle={d1}\tzero-budget={d2}\t{c.note}\t{ppSeq c.ctx c.jd c.goal}"
  out.flush

/-! ## 9. Probes -/

def runProbe : IO Unit := do
  let out ← IO.getStdout
  for (nm, done, gs) in stations do
    for f in [1, 2, 3, 4] do
      let E := interpP "p" f [] done none
      let A := interpP "p" f [] done (some (gs.headD nA))
      out.putStrLn s!"probe\tstation={nm}\tfuel={f}\t|E|={sizeNeg E}\t|A|={sizeNeg A}"
      out.flush
  for nm in ["i", "i-lax", "ii", "iii", "iv", "v"] do
    out.putStrLn s!"probe\tstratum={nm}\tcells={(strataOf nm).length}"
    out.flush
  out.putStrLn s!"probe\tstratum=vi\tcells={(stratumVI [.tru, .lax]).length}"
  out.putStrLn s!"probe\tstratum=vi-b\tcells={(stratumVIb [.tru, .lax]).length}"
  -- oracle and search timing on two known cells
  let t0 ← IO.monoMsNow
  let _ := erasureProvable (closeErasure [nA] .tru nA)
  let t1 ← IO.monoMsNow
  let _ := invSearch 12 [nA] .tru nA
  let t2 ← IO.monoMsNow
  out.putStrLn s!"probe\toracle_ms={t1 - t0}\tsearch12_ms={t2 - t1}"
  out.flush

def main (args : List String) : IO Unit := do
  match args with
  | ["--probe"] => runProbe
  | ["--gate"] => runGate
  | "--cut" :: rest =>
      let ns := rest.map String.toNat!
      runCut "vi" (ns.getD 0 0) (ns.getD 1 12) (ns.getD 2 16)
  | "--cut2" :: rest =>
      let ns := rest.map String.toNat!
      runCut "vi-b" (ns.getD 0 0) (ns.getD 1 12) (ns.getD 2 16)
  | name :: start :: budgets =>
      runStratum name start.toNat! (if budgets.isEmpty then [10, 14]
                                    else budgets.map String.toNat!)
  | [name] => runStratum name 0 [10, 14]
  | _ => runProbe

end CutInvScreen

def main (args : List String) : IO Unit := CutInvScreen.main args
