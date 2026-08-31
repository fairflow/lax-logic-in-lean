/-
# The `◯` rules of SC/LaxND inside `Gbu◯(G)` — the derivable half

Check requested 2026-08-31, before stage W5: are SC's `laxL`/`laxR`
(`LaxLogic/PLLSequent.lean`, F&M Figure 2) derivable in `Gbu◯(G)`
(`wip/gbu_circ.lean` §11b)?  `LaxND ↔ SC` is mechanised (`SC_to_ND`,
`ND_to_SC`, with `cutElimination`), so cut-free SC is the right source:
if every SC rule is admissible in `GbuRC` then `Gbu◯(G)` is complete in
itself, with no route through the FRJ database.

This file machine-checks the half that is derivable OUTRIGHT — each
lemma is a single constructor application, so the rules below are
DERIVED RULES of `Gbu◯(G)`, not admissibilities:

* `L◯` (SC `laxL`), regular and irregular:  `lcirc` / `lcircI`;
* `R◯` with an IRREGULAR premise:           `rcirc` / `rcircI`.

What is NOT here, and is OPEN (recorded as data, no declaration): SC's
`laxR` at the REGULAR judgment,

    Ψ ⇒g Z   ⟹   Ψ ⇒g ◯Z        (◯Z ∈ Sf^R(G)),

whose only Gbu◯ route is `rcirc` over an irregular premise.  The direct
induction on `Ψ ⇒g Z` closes every case EXCEPT `R∧` (`randR`) and
`R⊃ᵢ` (`rimpI`), whose premises are regular where `randI`/`rimpII`
demand irregular ones; the irregular-target variant closes those and
sticks instead at `L⊃` (`limpL`), whose `limpLI` mirror carries the
size condition `A.hasCirc = false ∨ |A| < |◯C|`.  Those obligations are
precisely the focalization content of Gbu◯ completeness (the proof-side
mirrors of stage W5's database clauses `(∨-inv)` and `(★)`), and the
same holds for SC's `R∨` against `rorR1`/`rorR2`.  They are not rule
derivabilities and are not attempted here.
-/
import wip.gbu_circ

namespace FRJ.Gbu

open Form

/-- `Ψ ≐ ◯Z :: Ψ` when `◯Z ∈ Ψ` — the contraction reading of `≐` that
lets `lcirc` consume a `◯`-hypothesis SC's `laxL` keeps. -/
private theorem ctxEq_cons_self {Ψ : List Form} {X : Form} (h : X ∈ Ψ) :
    Ψ ≐ X :: Ψ :=
  fun _x => ⟨List.mem_cons_of_mem _,
    fun hx => (List.mem_cons.mp hx).elim (fun e => e ▸ h) id⟩

/-- **SC's `laxL` is a derived rule of `Gbu◯(G)`, regular judgment.**

    ◯Z ∈ Ψ      Ψ, Z ⇒g ◯C
    ───────────────────────      (= `lcirc` + contraction-by-`≐`)
           Ψ ⇒g ◯C
-/
def scLaxL {G : Form} {Ψ : List Form} {Z C : Form}
    (hmem : Form.circ Z ∈ Ψ) (d : GbuRC G (Z :: Ψ) (.circ C))
    (hprin : Form.circ Z ∈ sfL G) :
    GbuRC G Ψ (.circ C) :=
  .lcirc d hprin (ctxEq_cons_self hmem)

/-- **SC's `laxL` is a derived rule of `Gbu◯(G)`, irregular judgment.** -/
def scLaxL_irr {G : Form} {Ψ : List Form} {Z C : Form}
    (hmem : Form.circ Z ∈ Ψ) (d : GbuIC G (Z :: Ψ) (.circ C))
    (hprin : Form.circ Z ∈ sfL G) :
    GbuIC G Ψ (.circ C) :=
  .lcircI d hprin (ctxEq_cons_self hmem)

/-- **SC's `laxR`, irregular premise, regular conclusion** — `rcirc`
verbatim.

    Ψ →g Z
    ─────────
    Ψ ⇒g ◯Z
-/
def scLaxR_of_irr {G : Form} {Ψ : List Form} {Z : Form}
    (d : GbuIC G Ψ Z) (hgoal : Form.circ Z ∈ sfR G) :
    GbuRC G Ψ (.circ Z) :=
  .rcirc d hgoal

/-- **SC's `laxR`, irregular judgment throughout** — `rcircI` verbatim. -/
def scLaxR_irr {G : Form} {Ψ : List Form} {Z : Form}
    (d : GbuIC G Ψ Z) (hgoal : Form.circ Z ∈ sfR G) :
    GbuIC G Ψ (.circ Z) :=
  .rcircI d hgoal

/-! ## Axiom pins

`soundRC`/`soundIC` are pinned here as the audit anchor for the FRJW
mirror question: both Gbu◯ judgments are sound against the same Kripke
semantics as `soundnessW`, so no FRJW disproof can ever coexist with a
Gbu◯ proof of the same sequent — whatever `lift` adds. -/

/-- info: 'FRJ.Gbu.soundRC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms soundRC

/-- info: 'FRJ.Gbu.soundIC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms soundIC

/-- info: 'FRJ.Gbu.scLaxL' depends on axioms: [propext] -/
#guard_msgs in
#print axioms scLaxL

/-- info: 'FRJ.Gbu.scLaxL_irr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms scLaxL_irr

/-- info: 'FRJ.Gbu.scLaxR_of_irr' does not depend on any axioms -/
#guard_msgs in
#print axioms scLaxR_of_irr

/-- info: 'FRJ.Gbu.scLaxR_irr' does not depend on any axioms -/
#guard_msgs in
#print axioms scLaxR_irr

end FRJ.Gbu
