/-
The Kreisel–Putnam screen for candidate ◯-REJECTION RULES.

Context (docs/bilax-round3-plan.md, the literature report): a rejection
rule `⊣B₁ … ⊣Bₙ / ⊣C` characterises a logic `L` only if it is
Ł-SOUND for `L` (premises non-theorems ⟹ conclusion a non-theorem)
AND **Ł-UNSOUND for every proper extension** of `L`.  The second
condition is what killed Łukasiewicz's conjecture for IPC: his
Disjunction Rule is sound for Kreisel–Putnam logic ⊋ IPC, so it cannot
characterise IPC.  Goranko–Skura flag the same trap for the modal
case, and the analogous danger for PLL is that a candidate ◯-rule is
also sound for PCLL (= PLL + ◯-∨ distribution) or for PICLL
(+ ¬◯⊥) — both proper extensions we have calculi and certificates
for.

Verdicts, three-valued and certificate-only per repo doctrine:

* **KILL** — a certified Ł-soundness violation for PLL: every premise
  is refuted by a battery countermodel while the conclusion is PROVED
  by the searcher.  The rule is dead.
* **DISCRIM** — a certified discrimination witness against an
  extension: premises refuted (so non-theorems of the extension too,
  since a confluent countermodel refutes `DerivU`), while the
  conclusion is provable WITH distribution.  The rule is not sound for
  that extension — which is what we need.
* **FLAG** — no witness either way within budget.  A rule with no
  DISCRIM witness anywhere is the Kreisel–Putnam danger sign and is
  reported as such, never silently passed.

The corpus is the certified closed-fragment catalogue
(docs/pcll-closed-fragment-catalogue.md), which is exactly the set of
formulas whose separations we want a rejection calculus to derive.
-/
import LaxLogic.PLLCountermodelEmit
import LaxLogic.PLLSearchConf

open PLLND PLLND.FinCM

namespace RejScreen

abbrev F := PLLFormula

/-! ## The corpus: the catalogue's representatives -/

def bot : F := .falsePLL
def top : F := .ifThen bot bot
def oBot : F := .somehow bot
def nOBot : F := .ifThen oBot bot
def q4 : F := .or nOBot oBot
def nnOBot : F := .ifThen nOBot bot
def q7 : F := .or nnOBot nOBot
def q5 : F := .somehow nOBot
def q10 : F := .ifThen nnOBot oBot
def q9 : F := .or nnOBot q5
def q11 : F := .or q10 nnOBot
def q8 : F := .ifThen q5 q4
def q14 : F := .ifThen q10 q5
def w16 : F := .ifThen q9 q4

def pv : F := .prop "p"
def qv : F := .prop "q"
/-- The distribution axiom instance: a PCLL theorem, NOT a PLL one —
the canonical discriminator. -/
def distPQ : F := .ifThen (.somehow (.or pv qv))
  (.or (.somehow pv) (.somehow qv))

/-- The catalogue's crank-≤6 representatives, PLUS p-carrying cells.
The closed fragment alone is UNDER-POWERED for the extension test:
distribution's entire visible effect there is four merges
(docs/pcll-closed-fragment-catalogue.md), so PCLL ≈ PLL on it and no
discrimination witness can exist by construction.  The p,q cells are
where distribution actually bites. -/
def corpus : List (String × F) :=
  [("⊥", bot), ("⊤", top), ("◯⊥", oBot), ("¬◯⊥", nOBot),
   ("¬◯⊥∨◯⊥", q4), ("¬¬◯⊥", nnOBot), ("¬¬◯⊥∨¬◯⊥", q7),
   ("◯¬◯⊥", q5), ("¬¬◯⊥⊃◯⊥", q10), ("¬¬◯⊥∨◯¬◯⊥", q9),
   ("(¬¬◯⊥⊃◯⊥)∨¬¬◯⊥", q11), ("g1=◯¬◯⊥⊃(¬◯⊥∨◯⊥)", q8),
   ("r1", q14), ("w1", w16),
   ("p", pv), ("◯p", .somehow pv), ("p∨q", .or pv qv),
   ("◯(p∨q)", .somehow (.or pv qv)),
   ("◯p∨◯q", .or (.somehow pv) (.somehow qv)),
   ("dist(p,q)", distPQ),
   ("◯dist(p,q)", .somehow distPQ),
   ("¬¬dist(p,q)", .ifThen (.ifThen distPQ bot) bot)]

/-! ## The battery: well-formed confluent frames on ≤ 3 worlds -/

def mkFrame (n : Nat) (ri rm : List (Nat × Nat)) (fal : List Nat) : FinCM :=
  ⟨n, ri, rm, fal, []⟩

def wf (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all (fun x => M.riB x x && M.rmB x x) &&
  ws.all (fun x => ws.all fun y => ws.all fun z =>
    (!(M.riB x y && M.riB y z) || M.riB x z) &&
    (!(M.rmB x y && M.rmB y z) || M.rmB x z)) &&
  ws.all (fun x => ws.all fun y =>
    (!(M.rmB x y) || M.riB x y) &&
    (!(M.fallB x && M.riB x y) || M.fallB y))

def confl (M : FinCM) : Bool :=
  let ws := List.range M.n
  ws.all fun x => ws.all fun w => ws.all fun v =>
    !(M.rmB x w && M.riB x v) ||
      ws.any fun u => M.riB w u && M.rmB v u

def pairsOf (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun x => (List.range n).map fun y => (x, y)

def subsetOf (l : List (Nat × Nat)) (code : Nat) : List (Nat × Nat) :=
  (l.zipIdx.filter fun p => (code / 2 ^ p.2) % 2 = 1).map (·.1)

def framesN (n : Nat) : List FinCM :=
  let ps := pairsOf n
  let cap := 2 ^ ps.length
  (List.range cap).flatMap fun ci =>
    (List.range cap).flatMap fun cm =>
      (List.range (2 ^ n)).map fun cf =>
        mkFrame n
          (subsetOf ps ci ++ (List.range n).map fun x => (x, x))
          (subsetOf ps cm ++ (List.range n).map fun x => (x, x))
          ((List.range n).filter fun x => (cf / 2 ^ x) % 2 = 1)

def battery : List FinCM :=
  ((framesN 1 ++ framesN 2 ++ framesN 3).filter fun M => wf M && confl M)

/-- A battery countermodel certifies `⊬ φ` (and `⊬_DerivU φ`, since
the model is confluent). -/
def refutedSomewhere (φ : F) : Option (Nat × Nat) :=
  let rec go (i : Nat) : List FinCM → Option (Nat × Nat)
    | [] => none
    | M :: ms =>
        match (List.range M.n).find? (fun w => !(M.forceB w φ)) with
        | some w => some (i, w)
        | none => go (i + 1) ms
  go 0 battery

/-! ## Provability, PLL and PCLL -/

def provedPLL (b : Nat) (φ : F) : Bool :=
  match Search.decide { findBudget := some b, emitClosureCap := 0 } [] φ with
  | .proved _ => true
  | _ => false

/-- Provability using ONE distribution instance as a premise (the
PCLL tier of wip/rnc_probe: sound for `DerivU` by
`derivU_of_proved`). -/
def provedPCLL (b : Nat) (φ : F) : Bool :=
  provedPLL b φ ||
  ([(oBot, nOBot), (nOBot, oBot), (nnOBot, q5), (q5, nnOBot),
    (q10, nnOBot), (nnOBot, nOBot), (pv, qv), (qv, pv)].any fun p =>
    match Search.decide { findBudget := some b, emitClosureCap := 0 }
        [ConfluentU.distF p.1 p.2] φ with
    | .proved _ => true
    | _ => false)

/-! ## The candidate ◯-rejection rules -/

structure Rule where
  name : String
  shape : String
  /-- premises and conclusion, from one corpus formula -/
  inst : F → List F × F

def rules : List Rule :=
  [ { name := "R1", shape := "⊣φ / ⊣◯φ"
      inst := fun φ => ([φ], .somehow φ) },
    { name := "R2", shape := "⊣◯φ / ⊣φ"
      inst := fun φ => ([.somehow φ], φ) },
    { name := "R3", shape := "⊣φ / ⊣(◯φ ⊃ φ)"
      inst := fun φ => ([φ], .ifThen (.somehow φ) φ) },
    { name := "R4", shape := "⊣φ / ⊣¬¬◯φ"
      inst := fun φ => ([φ], .ifThen (.ifThen (.somehow φ) bot) bot) },
    { name := "R5(DR-lax)", shape := "⊣φ,⊣ψ / ⊣◯(φ∨ψ)"
      inst := fun φ => ([φ, nOBot], .somehow (.or φ nOBot)) } ]

/-! ## The screen -/

def screenRule (b : Nat) (R : Rule) : IO Unit := do
  let mut kills : List String := []
  let mut discrims : List String := []
  let mut checked := 0
  let mut premRefuted := 0
  for (nm, φ) in corpus do
    let (prems, concl) := R.inst φ
    -- every premise must be a certified non-theorem
    let cert := prems.all fun P => (refutedSomewhere P).isSome
    if cert then
      premRefuted := premRefuted + 1
      checked := checked + 1
      if provedPLL b concl then
        kills := s!"KILL {R.name} at φ={nm}: premises refuted, conclusion PROVED in PLL" :: kills
      else if provedPCLL b concl then
        discrims := s!"DISCRIM {R.name} at φ={nm}: conclusion provable WITH distribution (rule not sound for PCLL)" :: discrims
  IO.println s!"  {R.name}  [{R.shape}]"
  IO.println s!"    instances with all premises certified non-theorems: {premRefuted}/{corpus.length}"
  if kills.isEmpty then
    IO.println s!"    Ł-soundness for PLL: no certified violation ({checked} cells)"
  else
    IO.println s!"    Ł-soundness for PLL: {kills.length} CERTIFIED VIOLATIONS — RULE DEAD"
    for k in kills.take 3 do IO.println s!"      {k}"
  if discrims.isEmpty then
    IO.println s!"    PCLL discrimination: NO WITNESS — Kreisel-Putnam DANGER SIGN (may be sound for PCLL too)"
  else
    IO.println s!"    PCLL discrimination: {discrims.length} witnesses (good: not sound for PCLL)"
    for d in discrims.take 2 do IO.println s!"      {d}"
  (← IO.getStdout).flush

def main : IO Unit := do
  IO.println "Kreisel-Putnam screen for candidate ◯-rejection rules"
  IO.println s!"battery: {battery.length} well-formed confluent frames (≤3 worlds)"
  IO.println s!"corpus: {corpus.length} catalogue representatives"
  -- non-vacuity: how many corpus members are certified non-theorems?
  let nonThms := corpus.filter fun p => (refutedSomewhere p.2).isSome
  IO.println s!"corpus members certified NON-theorems: {nonThms.length} (non-vacuity)"
  IO.println ""
  for R in rules do
    screenRule 8000 R
  IO.println "REJECT-SCREEN-DONE"

end RejScreen

def main : IO Unit := RejScreen.main
