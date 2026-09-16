/-
WP12 Stage 0, R2 / R3 / R4: the decider stages for the pair-recording
recursion `interpR`.

Transfer and decider as `_probe/stage0.lean` / `_probe/stage0d.lean`: erase
to `PLLFormula`, normalise by `Rewrite.fullSetC`, decide by
`FRJ.Arity.decideByEngine` with in-process certificates.  Every run is under
the caller's deadline (`_probe/r_run.sh`).

Modes:
  control          the control batch (`p ⊢ ◯p` PROVED, `◯p ⊢ p` REFUTED)
  R2-ix  <f>       the escape property at cell (ix)'s SAME-station residue
  R2-iii <f>       a LARGER-station residue: no escape needed
  R2-vii <f>       ditto, cell (vii)
  R3     <f>       soundness at three cells
  R4-v1  <f>       {◯p ⊃ r, ◯q} ⇒ ◯p
  R4-v2  <f>       {◯p ⊃ r, s ⊃ ◯p} ⇒ r
  R4-s1  <f>       [◯(d ⊃ p) ⊃ a, c ⊃ ◯p] ⇒ a, Δ = c
-/
import wip.ui_routeB_r_cells
import wip.check_closed
import Rewrite
import FRJ.Bridge

set_option autoImplicit false
open LJFO FRJ FRJ.Arity FRJ.Search

def sizeF : PLLFormula → Nat
  | .prop _ => 1 | .falsePLL => 1
  | .and a b => sizeF a + sizeF b + 1 | .or a b => sizeF a + sizeF b + 1
  | .ifThen a b => sizeF a + sizeF b + 1 | .somehow a => sizeF a + 1

def cfgD : Config :=
  { rounds := 16, jmax := 3, pmax := 2, lamCap := 24, maxRS := 3000, maxIS := 3000 }

def nrm (φ : PLLFormula) : PLLFormula := Rewrite.simplifyWith Rewrite.fullSetC 200 φ

def verdict (φ : PLLFormula) (cfg : Config) : String :=
  match decideByEngine (FRJ.ofPLL φ) cfg with
  | some (.inl _) => "PROVED " | some (.inr _) => "REFUTED" | none => "FLAG(not-closed)"

def one (tag : String) (φ : PLLFormula) (cfg : Config) : IO Unit := do
  let n := nrm φ
  let t0 ← IO.monoMsNow
  let v := verdict n cfg
  let t1 ← IO.monoMsNow
  IO.println s!"    {tag}: nrm size {sizeF n}  {v}  ({t1-t0} ms)"
  (← IO.getStdout).flush

/-- The station as one erased conjunction (`⊤` for the empty station). -/
def ctxF : List Neg → PLLFormula
  | [] => .ifThen .falsePLL .falsePLL
  | [X] => eraseNeg X
  | X :: Γ => .and (eraseNeg X) (ctxF Γ)

def aOf (p : String) (f : Nat) (todo done : List Neg) (G : Neg) (seen : SeenR) : PLLFormula :=
  nrm (eraseNeg (interpR p f todo done (some G) seen))
def eOf (p : String) (f : Nat) (todo done : List Neg) (seen : SeenR) : PLLFormula :=
  nrm (eraseNeg (interpR p f todo done none seen))

/-! ## R2 · the escape property -/

/-- cell (ix): `done = [(a∨b) ⊃ ↑c, c ⊃ ↑a]`, guard antecedent `a∨b`.  The
residue state `r` is at the SAME station as the recorded pair, so the
re-attack IS cut and the escape is expected to be needed. -/
def r2ix (f : Nat) (cfg : Config) : IO Unit := do
  let seen : SeenR := [(qa9, cell9)]
  let aR := aOf "p" f [] cell9 goal9 seen
  let aG := aOf "p" f [] cell9 (.up qa9) seen
  IO.println s!"R2 cell(ix) f={f}  same-station residue  |A^R(r)|={sizeF aR} |A^R(g)|={sizeF aG}"
  (← IO.getStdout).flush
  one "datum b sufficient at r: b, done |- ↑a                " (.ifThen (.and (.prop "b") (ctxF cell9)) (.prop "a")) cfg
  one "NO escape:  b |- A^R(r)                (expect REFUTED)" (.ifThen (.prop "b") aR) cfg
  one "ESCAPE:     b |- A^R(r) ∨ A^R(g)       (expect PROVED) " (.ifThen (.prop "b") (.or aR aG)) cfg
  one "the escape lands at the guard: b |- A^R(g)             " (.ifThen (.prop "b") aG) cfg

/-- cell (iii): the residue `↑a :: cell3 ⇒ ↑b` with `(q3, cell3)` recorded.
The station is STRICTLY LARGER as a set, so the re-attack is NOT cut and
every sufficient datum should be reached with NO escape. -/
def r2iii (f : Nat) (cfg : Config) : IO Unit := do
  let q3 : Pos := .down dykBody
  let seen : SeenR := [(q3, cell3)]
  let st : List Neg := .up (.atom "a") :: cell3
  let aR := aOf "p" f [] st (.up (.atom "b")) seen
  let aP := nrm (eraseNeg (interpP "p" f [] st (some (.up (.atom "b")))))
  let eR := eOf "p" f [] st seen
  let d1 : PLLFormula := .prop "b"
  let d2 : PLLFormula := .ifThen (.prop "a") (.prop "b")
  IO.println s!"R2 cell(iii) f={f}  LARGER-station residue  |A^R|={sizeF aR} |A^P|={sizeF aP} |E^R|={sizeF eR}"
  (← IO.getStdout).flush
  one "sufficiency  b, station |- b                          " (.ifThen (.and d1 (ctxF st)) (.prop "b")) cfg
  one "sufficiency  (a⊃b), station |- b                      " (.ifThen (.and d2 (ctxF st)) (.prop "b")) cfg
  one "datum b     |- A^R                                    " (.ifThen d1 aR) cfg
  one "datum b     |- A^P    (interpP, the comparison)       " (.ifThen d1 aP) cfg
  one "datum (a⊃b) |- A^R                                    " (.ifThen d2 aR) cfg
  one "datum (a⊃b) |- A^P    (interpP, the comparison)       " (.ifThen d2 aP) cfg
  one "R ⊢ P  and  P ⊢ R at this state:  A^R |- A^P          " (.ifThen aR aP) cfg
  one "                                  A^P |- A^R          " (.ifThen aP aR) cfg

/-- cell (vii): the residue `↑a :: cell7 ⇒ ↑c` with `(q7, cell7)` recorded. -/
def r2vii (f : Nat) (cfg : Config) : IO Unit := do
  let seen : SeenR := [(q7, cell7)]
  let st : List Neg := .up (.atom "a") :: cell7
  let aR := aOf "p" f [] st (.up (.atom "c")) seen
  let aP := nrm (eraseNeg (interpP "p" f [] st (some (.up (.atom "c")))))
  let d1 : PLLFormula := .prop "c"
  let d2 : PLLFormula := .and (.ifThen (.prop "a") (.prop "c")) (.ifThen (.prop "b") (.prop "c"))
  IO.println s!"R2 cell(vii) f={f}  LARGER-station residue  |A^R|={sizeF aR} |A^P|={sizeF aP}"
  (← IO.getStdout).flush
  one "datum c            |- A^R                             " (.ifThen d1 aR) cfg
  one "datum c            |- A^P   (the comparison)          " (.ifThen d1 aP) cfg
  one "datum (a⊃c)∧(b⊃c)  |- A^R                             " (.ifThen d2 aR) cfg
  one "datum (a⊃c)∧(b⊃c)  |- A^P   (the comparison)          " (.ifThen d2 aP) cfg
  one "A^R |- A^P                                            " (.ifThen aR aP) cfg
  one "A^P |- A^R                                            " (.ifThen aP aR) cfg

/-! ## R3 · soundness -/

def r3one (nm : String) (done : List Neg) (G : Neg) (f : Nat) (cfg : Config) : IO Unit := do
  let aR := aOf "p" f [] done G []
  let eR := eOf "p" f [] done []
  IO.println s!"R3 {nm} f={f}  |A^R|={sizeF aR} |E^R|={sizeF eR}"
  (← IO.getStdout).flush
  one "∃p sound:  done |- E^R                             " (.ifThen (ctxF done) eR) cfg
  one "∀p sound:  A^R ∧ done |- G                         " (.ifThen (.and aR (ctxF done)) (eraseNeg G)) cfg

def r3 (f : Nat) (cfg : Config) : IO Unit := do
  r3one "(i)  cell1 ⇒ ↑(a∨b)" cell1 goal1 f cfg
  r3one "(ix) cell9 ⇒ ↑a    " cell9 goal9 f cfg
  r3one "(m1) [◯a] ⇒ ◯b     " m1 (.circ (.atom "b")) f cfg

/-! ## R4 · top-level cofinality on the recorded validation cells -/

/-- `{◯p ⊃ r, ◯q} ⇒ ◯p`, the χ = ⊥ cell (`docs/ui-ljfo-clause-table.md` §4.10). -/
def v1 : List Neg :=
  [.imp (.down (.circ (.atom "p"))) (.up (.atom "r")), .circ (.atom "q")]
def v1goal : Neg := .circ (.atom "p")

/-- `{◯p ⊃ r, s ⊃ ◯p} ⇒ r`, the χ = s cell. -/
def v2 : List Neg :=
  [.imp (.down (.circ (.atom "p"))) (.up (.atom "r")), .imp (.atom "s") (.circ (.atom "p"))]
def v2goal : Neg := .up (.atom "r")

/-- S1 in its blueprint form `[◯(d ⊃ p) ⊃ a, c ⊃ ◯p] ⇒ a`, Δ = c. -/
def s1b : List Neg :=
  [ .imp (.down (.circ (.down (.imp (.atom "d") (.up (.atom "p")))))) (.up (.atom "a"))
  , .imp (.atom "c") (.circ (.atom "p")) ]
def s1bgoal : Neg := .up (.atom "a")

def r4v1 (f : Nat) (cfg : Config) : IO Unit := do
  let aR := aOf "p" f [] v1 v1goal []
  let eR := eOf "p" f [] v1 []
  let boxBot : PLLFormula := .somehow .falsePLL
  let thetaMax : PLLFormula :=
    .ifThen (.and (.ifThen boxBot (.prop "r")) (.somehow (.prop "q"))) boxBot
  IO.println s!"R4 v1  [◯p ⊃ r, ◯q] ⇒ ◯p  f={f}  |A^R|={sizeF aR} |E^R|={sizeF eR}"
  (← IO.getStdout).flush
  one "(d) ◯⊥ |- A^R                (A^R is ◯⊥-absorbing)  " (.ifThen boxBot aR) cfg
  one "(b) E^R |- (◯⊥ ⊃ r) ∧ ◯q     (E^R is ≥ the ⊥-instance)"
    (.ifThen eR (.and (.ifThen boxBot (.prop "r")) (.somehow (.prop "q")))) cfg
  one "the reduction: (◯⊥⊃r) ∧ ◯q ∧ θmax |- ◯⊥              "
    (.ifThen (.and (.and (.ifThen boxBot (.prop "r")) (.somehow (.prop "q"))) thetaMax) boxBot) cfg

def r4v2 (f : Nat) (cfg : Config) : IO Unit := do
  let aR := aOf "p" f [] v2 v2goal []
  let eR := eOf "p" f [] v2 []
  let T : PLLFormula := .ifThen (.ifThen (.somehow (.prop "s")) (.prop "r")) (.prop "r")
  IO.println s!"R4 v2  [◯p ⊃ r, s ⊃ ◯p] ⇒ r  f={f}  |A^R|={sizeF aR} |E^R|={sizeF eR}"
  (← IO.getStdout).flush
  one "soundness cross-check:  A^R |- T        (T = (◯s⊃r)⊃r)" (.ifThen aR T) cfg
  one "the datum unrelativised:  T |- A^R                     " (.ifThen T aR) cfg
  one "ACofinal instance:  E^R ∧ T |- A^R                      " (.ifThen (.and eR T) aR) cfg

def r4s1 (f : Nat) (cfg : Config) : IO Unit := do
  let aR := aOf "p" f [] s1b s1bgoal []
  let eR := eOf "p" f [] s1b []
  IO.println s!"R4 S1 [◯(d⊃p)⊃a, c⊃◯p] ⇒ a  f={f}  |A^R|={sizeF aR} |E^R|={sizeF eR}"
  (← IO.getStdout).flush
  one "Δ = c sufficient:  c, Γ |- a                           "
    (.ifThen (.and (.prop "c") (ctxF s1b)) (.prop "a")) cfg
  one "the datum unrelativised:  c |- A^R                     " (.ifThen (.prop "c") aR) cfg
  one "ACofinal instance:  E^R ∧ c |- A^R                     " (.ifThen (.and eR (.prop "c")) aR) cfg

def main (args : List String) : IO Unit := do
  match args with
  | ["control"] => do
      one "ctl p |- ◯p  (must be PROVED) " (.ifThen (.prop "p") (.somehow (.prop "p"))) cfgD
      one "ctl ◯p |- p  (must be REFUTED)" (.ifThen (.somehow (.prop "p")) (.prop "p")) cfgD
  | [mode, fs] =>
      let f := fs.toNat!
      match mode with
      | "R2-ix" => r2ix f cfgD
      | "R2-iii" => r2iii f cfgD
      | "R2-vii" => r2vii f cfgD
      | "R3" => r3 f cfgD
      | "R4-v1" => r4v1 f cfgD
      | "R4-v2" => r4v2 f cfgD
      | "R4-s1" => r4s1 f cfgD
      | _ => IO.println "unknown mode"
  | _ => IO.println "usage: r_stage0 <mode> <fuel> | control"
