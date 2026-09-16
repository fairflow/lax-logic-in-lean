/-
# Seam 1 at a genuine ATOM — the test the ρ-corpus cannot run

    lake env lean --run wip/gbu_seam1_probe.lean

The 462-cell ρ-corpus is CLOSED (`◯`/`⊥` only, no propositional
variables), so its only prime formula is `⊥`.  Seam 1 of
`docs/gbu-circ-seams.md` is the configuration

    Ω ⇒g F      F prime,   ◯Y ∈ Ω,   Ω ⊆ Ĝ

and at `F = ⊥` it is easy: refuting `Ω ⇒ ⊥` only asks for an
infallible root.  At a genuine atom it is not, and the corpus contains
no instance.  This bank supplies them.

The critical sub-case is `Y = F`, i.e. `◯p ∈ Ω` with goal `p`.  Then the
promise join's

    hJ5 : ∀ Y, ◯Y ∈ ⋃ⱼ (Σⱼ)^◯ → ∃ i, Y ∈ Cl(Δ_i)     (Δ_i ⇒ F)

asks for a row REFUTING `p` whose context CLOSES `p`, which soundness
forbids.  So the prediction is that `◯p ⊃ p` — the counit, which is
PLL-invalid — is not reachable, while `◯p ⊃ q` (a DIFFERENT atom, where
`Ax^R`'s own context `Ĝ_at ∖ {q} = {p}` closes `p`) is.

Verdicts are three-valued and untrusted: `HIT` is an engine claim, not a
certificate; `none` at a stated budget is a LEAD, never a refutation.
Every cell reports its budget and whether a cap was binding, so nothing
is silently truncated.
-/
import wip.frjx
import FRJ.Bridge

namespace FRJ.Seam1

open FRJ Form

def pA : Form := .atom "p"
def qA : Form := .atom "q"

/-- name, formula, PLL status (hand-checked, stated for the reader). -/
def bank : List (String × Form × String) :=
  [ ("counit    ◯p ⊃ p",        .imp (.circ pA) pA,                "INVALID — must be refutable"),
    ("cross     ◯p ⊃ q",        .imp (.circ pA) qA,                "INVALID — must be refutable"),
    ("counit⊥   ◯⊥ ⊃ ⊥",        .imp (.circ .bot) .bot,            "INVALID — the corpus's own shape"),
    ("disj      ◯p ⊃ (p ∨ q)",  .imp (.circ pA) (.or pA qA),       "INVALID — must be refutable"),
    ("neg       ◯p ⊃ ⊥",        .imp (.circ pA) .bot,              "INVALID — must be refutable"),
    ("nested    (◯p ⊃ p) ⊃ p",  .imp (.imp (.circ pA) pA) pA,      "INVALID — must be refutable"),
    ("unit      p ⊃ ◯p",        .imp pA (.circ pA),                "VALID — ALARM if HIT"),
    ("id        ◯p ⊃ ◯p",       .imp (.circ pA) (.circ pA),        "VALID — ALARM if HIT"),
    ("mult      ◯◯p ⊃ ◯p",      .imp (.circ (.circ pA)) (.circ pA), "VALID — ALARM if HIT") ]

def runOne (cfg : Search.Config) (nm : String) (G : Form) (status : String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let (db, st) := FRJX.saturate true G cfg
  let hit := FRJX.derivable G db
  let t1 ← IO.monoMsNow
  let caps :=
    (if st.dbCapped then " DBCAP" else "") ++ (if st.lamCapped then " LAMCAP" else "") ++
    (if st.jmaxBinding then " JMAX" else "") ++ (if st.pmaxBinding then " PMAX" else "")
  IO.println s!"{nm}\t{if hit then "HIT" else "none"}\t{t1 - t0}ms\tr={st.roundsUsed} RS={st.rsSize} IS={st.isSize}{caps}\t| Ĝat={(gAt G).length} Ĝimp={(gImp G).length} Ĝcirc={(gCirc G).length}\t| {status}"

/-- Dump every row the engine derived, so the DISCHARGE can be read off
rather than guessed. -/
def dumpOne (cfg : Search.Config) (nm : String) (G : Form) : IO Unit := do
  let (db, _) := FRJX.saturate true G cfg
  IO.println s!"== {nm}   sfR={reprStr (sfR G)}   Ĝ={reprStr (gHat G)}"
  IO.println "  regular rows (tag | ctx => rhs):"
  for r in db.rs do
    IO.println s!"    {reprStr r.t} | {reprStr r.ctx} => {reprStr r.rhs}"
  IO.println "  irregular rows (stab ; th -> rhs):"
  for i in db.is do
    IO.println s!"    {reprStr i.stab} ; {reprStr i.th} -> {reprStr i.rhs}"

def main : IO Unit := do
  let cfg : Search.Config :=
    { rounds := 14, lamCap := 24, maxRS := 6000, maxIS := 6000, jmax := 4, pmax := 3 }
  IO.println s!"-- FRJX (patched) budget: rounds=14 lamCap=24 maxRS=6000 maxIS=6000 jmax=4 pmax=3"
  for (nm, G, status) in bank do
    runOne cfg nm G status
  IO.println ""
  dumpOne cfg "counit  ◯p ⊃ p" (.imp (.circ pA) pA)
  IO.println "-- SEAM1-DONE"

end FRJ.Seam1

def main : IO Unit := FRJ.Seam1.main
