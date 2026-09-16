import LaxLogic.PLL.Search.Decide
import LaxLogic.PLL.UI.G4UI
import LaxLogic.PLL.G4.G4Gap
/-!
# g4ill_probe: per-instance decidable probe of Iemhoff-UI statements for G4iLL (task follow-on to #13)

QUESTION: does UI *as a statement* hold for G4iLL-derivability (PLLND.G4) with her
tables (iemE/iemA of wip/g4ill_ui.lean), despite the two broken proof steps?
METHOD: iemE/iemA copied verbatim below; probes decided by (a) `instDecidableG4`
(library, decision-grade, PLLDecide.lean) for small instances, (b) `g4B` — an
exact memoized reimplementation of the same `succs` recursion (sound+complete by
succs_sound/succs_complete + G4.perm; multiset keys, duplicates kept), (c) `g4bud`
— budgeted variant, `some false` only on FULL exhaustion (decision-equivalent),
`none` = honest skip.  g4B validated against library decide on canonical battery
(◯-unit T, ◯◯→◯ T, refl F, EM F, gap sequent F, cut-left T, two-copies T): all agree.

== RESULTS RECORDED (scratch runs, this toolchain, 2026-07-12; STOPPED EARLY on budget call) ==
* (∃r)  `G4 Γ (iemE p (seqMeasure Γ C) Γ C)`: famSound sweep 1166/1166 PASS, 0 fail
  (Γ ⊆ 14-formula p/q/r pool ≤2 elems, C over 11 goals; ~ms/instance — iemE on the
  RIGHT is cheap: deterministic andR decomposition).
* (∃r)-L4→-(i) sorried conjunct `Γ ⊢ ∃p(B→D, Γ∖F ⇒ A→B)`, F=(A→B)→D ∈ Γ:
  famL4 sweep 1080/1080 PASS, 0 fail (A∈6,B∈5,D∈6 shapes × 6 context pads; includes
  the gap-shaped F = (◯p→r)→◯p).  HER BROKEN STEP'S STATEMENT SURVIVES EVERYWHERE PROBED.
* (∀l)  `G4 (iemA p _ Γ C :: Γ) C`: chunk 1/4 (300/300, 1-elem contexts) PASS;
  chunks 2-4 (2-elem contexts, aVal up to ~11K nodes in context) TIMED OUT — no verdicts,
  no failures seen.
* Adequacy (∀∃), (A)-half `iemE p F Γ C, Δ ⊢ iemA p F Γ C` (gate: G4 (Γ++Δ) C):
  hand DPN instances: ([q→p],[◯q],◯p) PASS (the exact flawed-case shape: Δ-side box,
  i-side circle succedent — rescued by selecting the R◯-disjunct ◯∀p(Γ⇒W) FIRST, then
  opening the Δ-box under the then-circle succedent).  famDPN (616 sharp instances)
  defined below; full sweep TIMED OUT at 60K-expansion budget × 616.  Hard unresolved
  instance isolated: ([◯q→p], [◯q], ◯p) — `none` at 1M expansions (~8 min): the
  jump-implication γ-form case.  NO `some false` (violation) seen on ANY adequacy probe.
* Adequacy (E)-half: NOT run (stopped).
* Stability: iemE/iemA values verified fuel-stable at seqMeasure vs +5/+7 on samples.

== VERDICT SO FAR: (P) honest partial, evidence leaning (S) ==
~2550 decided probes, ZERO violations.  Both flawed-proof-step targets: L4→ statement
fully survives its swept family; (DPN)-L◯ target family survives every instance decided
(coverage partial; one genuinely hard instance unresolved).
Throughput: plain small sequents ms; interpolant-in-context searches ~2K expansions/s,
48 s per 100K-budget instance; library WF decider (no memo) infeasible beyond ~40-node
contexts — use g4bud for sweeps, library `decide` to confirm any violation candidate.

Provenance: all defs below iemE/iemA etc. copied verbatim from wip/g4ill_ui.lean
lines 66-318 (task #13).  Sweep/searcher code compiled green as of last scratch run
(hdr = this file minus this docstring); results above are from `lake env lean` runs
of exactly these definitions with the recorded #eval lines (in comments at EOF).
-/

open PLLFormula

namespace PLLND
namespace G4Probe

-- ===== Definitions copied verbatim from wip/g4ill_ui.lean (lines 66-318) =====
/-! ### The measure (her ≪, linearised) -/

/-- `4^weight`: the Dershowitz–Manna order on weight-multisets embeds
into `Nat` by summing these, because every G4iLL premise replaces one
formula by at most two strictly lighter ones. -/
def fwt (φ : PLLFormula) : Nat := 4 ^ φ.weight

/-- Antecedent measure. -/
def ctxMeasure (Γ : List PLLFormula) : Nat := (Γ.map fwt).sum

/-- Sequent measure; `⊥` models her empty succedent and counts `0`. -/
def seqMeasure (Γ : List PLLFormula) (C : PLLFormula) : Nat :=
  ctxMeasure Γ + (if C = falsePLL then 0 else fwt C)

/-! ### The quantifier pair

Clause tables verbatim from her papers (see the module docstring for
the source of each family).  Layout of `iemE p (fuel+1) Γ C`, a big
conjunction:

* `∃ᵃᵗ` part 1 — atoms `q ≠ p` of `Γ`, and `⊥` if `⊥ ∈ Γ`;
* axiom instances — if `S` is an `At`- or `L⊥`-instance, the
  conjunction of the p-free members of `Γ`;
* per context formula `F ∈ Γ` with `Γ' = Γ.erase F` (rule instances
  with `F` principal, plus the `∃ᵃᵗ` implication family):
  - `F = A∧B` (L∧): `E(A,B,Γ' ⇒ C)`
  - `F = A∨B` (L∨): `E(A,Γ' ⇒ C) ∨ E(B,Γ' ⇒ C)`
  - `F = q→B`: if `q ∈ Γ'` the `L1→` instance conjunct
    (`q = p`: `E(B,Γ' ⇒ C)`; else `q ∧ E(B,Γ' ⇒ C)`), and always
    (for `q ≠ p`) the `∃ᵃᵗ` conjunct `q → E(B,Γ' ⇒ C)`
  - `F = ⊥→B` (repo `impLBot`, flagged extension): `E(Γ' ⇒ C)`
  - `F = (A∧B)→D` (L2→): `E(A→(B→D),Γ' ⇒ C)`
  - `F = (A∨B)→D` (L3→): `E(A→D,B→D,Γ' ⇒ C)`
  - `F = (A→B)→D` (L4→): `E(B→D,Γ' ⇒ A→B) ∧ (A(B→D,Γ' ⇒ A→B) → E(D,Γ' ⇒ C))`
  - `F = ◯A→B` (R◯→): `E(Γ' ⇒ A) ∧ (A(Γ' ⇒ A) → E(B,Γ' ⇒ C))`;
    (L◯→, one per witness box `◯x ∈ Γ'`, `Γ'' = Γ'.erase ◯x`):
    `◯E(x,Γ'' ⇒ ◯A) ∧ (◯A(x,Γ'' ⇒ ◯A) → E(B,Γ' ⇒ C))`
  - `F = ◯χ` (L◯ instance, only for `C = ◯ψ`): `◯E(χ,Γ' ⇒ C)`
* right-rule instances, by the shape of `C`:
  - `C = A∧B` (R∧): `E(Γ ⇒ A) ∨ E(Γ ⇒ B)`
  - `C = A∨B` (R∨, two instances): `E(Γ ⇒ A)` and `E(Γ ⇒ B)`
  - `C = A→B` (R→): `A → E(A,Γ ⇒ B)` if `p ∉ A`, else nothing (her `⊤`)
  - `C = ◯D` (R◯): `◯E(Γ ⇒ D)`
* `L◯→`-nonprincipal (her `S^γ`, every sequent):
  - box openers, one per `◯α ∈ Γ`: `◯E(α, Γ.erase ◯α ⇒ ∅)`
  - γ-forms, one per `γ = ◯α→β ∈ Γ`:
    `E(Γ.erase γ ⇒ ◯α) ∧ (◯A(Γ.erase γ ⇒ ◯α) → E(β, Γ.erase γ ⇒ C))`
* succedent plumbing (only for `C ≠ ⊥`; her `R◯→`/`L4→`-nonprincipal
  `⋀{∃p(Π⇒) | Π ⊆ Sᵃ}`): `E(Π ⇒ ∅)` for every sublist `Π` of `Γ`.

`iemA p (fuel+1) Γ C`, a big disjunction:

* `∀ᵃᵗ` — `C = q ≠ p`: disjunct `q`; and per `q→B ∈ Γ` (`q ≠ p`):
  `q ∧ A(B, Γ.erase (q→B) ⇒ C)`;
* axiom instances — `⊤` if (`C = q` and `q ∈ Γ`) or `⊥ ∈ Γ`;
* right-rule instances (goal clauses):
  - `C = A∧B` (R∧): `(E(Γ⇒A) → A(Γ⇒A)) ∧ (E(Γ⇒B) → A(Γ⇒B))`
  - `C = A∨B` (R∨, two): `E(Γ⇒A) → A(Γ⇒A)` and `E(Γ⇒B) → A(Γ⇒B)`
  - `C = A→B` (R→): `A → A(A,Γ ⇒ B)` if `p ∉ A`, else
    `E(A,Γ ⇒ B) → A(A,Γ ⇒ B)`
  - `C = ◯D` (R◯): `◯A(Γ ⇒ D)`
* per context formula `F ∈ Γ`, `Γ' = Γ.erase F`:
  - `F = A∧B` (L∧): `E(A,B,Γ'⇒C) → A(A,B,Γ'⇒C)`
  - `F = A∨B` (L∨): `(E(A,Γ'⇒C) → A(A,Γ'⇒C)) ∧ (E(B,Γ'⇒C) → A(B,Γ'⇒C))`
  - `F = q→B`, `q ∈ Γ'` (L1→): `q = p`: `A(B,Γ'⇒C)`, else `q → A(B,Γ'⇒C)`
  - `F = ⊥→B` (flagged): `E(Γ'⇒C) → A(Γ'⇒C)`
  - `F = (A∧B)→D` (L2→): `E(σ⇒C) → A(σ⇒C)`, `σ = A→(B→D),Γ'`
  - `F = (A∨B)→D` (L3→): likewise at `A→D,B→D,Γ'`
  - `F = (A→B)→D` (L4→): `(E(B→D,Γ'⇒A→B) → A(B→D,Γ'⇒A→B)) ∧ (E(D,Γ'⇒C) → A(D,Γ'⇒C))`
  - `F = ◯A→B` (R◯→, note: *unguarded*, her ι∀ᴿ = ∀pS₁ ∧ ∀pS₂):
    `A(Γ'⇒A) ∧ A(B,Γ'⇒C)`; (L◯→ per witness `◯x ∈ Γ'`):
    `◯A(x,Γ''⇒◯A) ∧ A(B,Γ'⇒C)`
  - `F = ◯χ` (L◯, only for `C = ◯ψ`): `◯A(χ,Γ'⇒C)`
* `L◯→`-nonprincipal γ-disjuncts, one per `γ = ◯α→β ∈ Γ`:
  `◯A(Γ.erase γ ⇒ ◯α) ∧ A(β, Γ.erase γ ⇒ C)`.
-/

/-- Is `S = (Γ ⇒ C)` an instance of one of her axioms (`At`, `L⊥`)? -/
def isAxInst (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  Γ.contains falsePLL ||
    (match C with | .prop _ => Γ.contains C | _ => false)

/-! #### Clause families

Each family is a plain (non-recursive) definition taking the
one-level-down quantifier values `E A` as parameters (the UIML
`e_rule`/`a_rule` architecture); the fueled pair below ties the knot.
All clause-membership reasoning happens on these, where the equation
lemmas reduce cleanly on constructor shapes. -/

section Clauses

variable (p : String) (E A : List PLLFormula → PLLFormula → PLLFormula)

/-- `∃ᵃᵗ` part 1: atoms `≠ p` of `Γ`, and `⊥` if present. -/
def eAtomList (Γ : List PLLFormula) : List PLLFormula :=
  Γ.filterMap (fun F => match F with
    | .prop q => if q = p then none else some (prop q)
    | .falsePLL => some falsePLL
    | _ => none)

/-- Left-rule instance clauses (plus the `∃ᵃᵗ` implication family) for
one context formula `F ∈ Γ`, E-side. -/
def eCtxClauses (Γ : List PLLFormula) (C F : PLLFormula) : List PLLFormula :=
  let Γ' := Γ.erase F
  match F with
  | .and A₁ B₁ => [E (A₁ :: B₁ :: Γ') C]
  | .or A₁ B₁ => [(E (A₁ :: Γ') C).or (E (B₁ :: Γ') C)]
  | .ifThen (.prop q) B₁ =>
      (if prop q ∈ Γ' then
        [if q = p then E (B₁ :: Γ') C
         else (prop q).and (E (B₁ :: Γ') C)] else [])
      ++ (if q = p then [] else [(prop q).ifThen (E (B₁ :: Γ') C)])
  | .ifThen .falsePLL _ => [E Γ' C]
  | .ifThen (.and A₁ B₁) D => [E (A₁.ifThen (B₁.ifThen D) :: Γ') C]
  | .ifThen (.or A₁ B₁) D => [E (A₁.ifThen D :: B₁.ifThen D :: Γ') C]
  | .ifThen (.ifThen A₁ B₁) D =>
      [(E (B₁.ifThen D :: Γ') (A₁.ifThen B₁)).and
        ((A (B₁.ifThen D :: Γ') (A₁.ifThen B₁)).ifThen (E (D :: Γ') C))]
  | .ifThen (.somehow A₁) B₁ =>
      ((E Γ' A₁).and ((A Γ' A₁).ifThen (E (B₁ :: Γ') C)))
      :: Γ'.filterMap (fun X => match X with
          | .somehow x =>
              let Γ'' := Γ'.erase (somehow x)
              some (((E (x :: Γ'') A₁.somehow).somehow).and
                (((A (x :: Γ'') A₁.somehow).somehow).ifThen (E (B₁ :: Γ') C)))
          | _ => none)
  | .somehow χ =>
      (match C with
        | .somehow _ => [(E (χ :: Γ') C).somehow]
        | _ => [])
  | _ => []

/-- Right-rule instance clauses, E-side, by the shape of `C`. -/
def eGoalClauses (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  match C with
  | .and A₁ B₁ => [(E Γ A₁).or (E Γ B₁)]
  | .or A₁ B₁ => [E Γ A₁, E Γ B₁]
  | .ifThen A₁ B₁ =>
      if p ∈ A₁.atoms then [] else [A₁.ifThen (E (A₁ :: Γ) B₁)]
  | .somehow D => [(E Γ D).somehow]
  | _ => []

/-- `L◯→`-nonprincipal box openers, one per `◯α ∈ Γ`. -/
def eOpenClauses (Γ : List PLLFormula) (F : PLLFormula) : List PLLFormula :=
  match F with
  | .somehow α => [(E (α :: Γ.erase (somehow α)) falsePLL).somehow]
  | _ => []

/-- `L◯→`-nonprincipal γ-forms, one per `γ = ◯α→β ∈ Γ`. -/
def eGammaClauses (Γ : List PLLFormula) (C F : PLLFormula) : List PLLFormula :=
  match F with
  | .ifThen (.somehow α) β =>
      let Γ' := Γ.erase F
      [(E Γ' α.somehow).and
        (((A Γ' α.somehow).somehow).ifThen (E (β :: Γ') C))]
  | _ => []

/-- Succedent plumbing `⋀{∃p(Θ⇒) | Θ ⊆ Γ}` (`C ≠ ⊥` only). -/
def ePlumbClauses (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  if C = falsePLL then [] else Γ.sublists.map (fun Θ => E Θ falsePLL)

/-- Goal-directed disjuncts, A-side. -/
def aGoalClauses (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  match C with
  | .prop q => if q = p then [] else [prop q]
  | .and A₁ B₁ =>
      [((E Γ A₁).ifThen (A Γ A₁)).and ((E Γ B₁).ifThen (A Γ B₁))]
  | .or A₁ B₁ =>
      [(E Γ A₁).ifThen (A Γ A₁), (E Γ B₁).ifThen (A Γ B₁)]
  | .ifThen A₁ B₁ =>
      if p ∈ A₁.atoms then [(E (A₁ :: Γ) B₁).ifThen (A (A₁ :: Γ) B₁)]
      else [A₁.ifThen (A (A₁ :: Γ) B₁)]
  | .somehow D => [(A Γ D).somehow]
  | _ => []

/-- Context-directed disjuncts for one `F ∈ Γ`, A-side. -/
def aCtxClauses (Γ : List PLLFormula) (C F : PLLFormula) : List PLLFormula :=
  let Γ' := Γ.erase F
  match F with
  | .and A₁ B₁ =>
      [(E (A₁ :: B₁ :: Γ') C).ifThen (A (A₁ :: B₁ :: Γ') C)]
  | .or A₁ B₁ =>
      [((E (A₁ :: Γ') C).ifThen (A (A₁ :: Γ') C)).and
        ((E (B₁ :: Γ') C).ifThen (A (B₁ :: Γ') C))]
  | .ifThen (.prop q) B₁ =>
      (if prop q ∈ Γ' then
        [if q = p then A (B₁ :: Γ') C
         else (prop q).ifThen (A (B₁ :: Γ') C)] else [])
      ++ (if q = p then [] else [(prop q).and (A (B₁ :: Γ') C)])
  | .ifThen .falsePLL _ => [(E Γ' C).ifThen (A Γ' C)]
  | .ifThen (.and A₁ B₁) D =>
      [(E (A₁.ifThen (B₁.ifThen D) :: Γ') C).ifThen
        (A (A₁.ifThen (B₁.ifThen D) :: Γ') C)]
  | .ifThen (.or A₁ B₁) D =>
      [(E (A₁.ifThen D :: B₁.ifThen D :: Γ') C).ifThen
        (A (A₁.ifThen D :: B₁.ifThen D :: Γ') C)]
  | .ifThen (.ifThen A₁ B₁) D =>
      [((E (B₁.ifThen D :: Γ') (A₁.ifThen B₁)).ifThen
          (A (B₁.ifThen D :: Γ') (A₁.ifThen B₁))).and
        ((E (D :: Γ') C).ifThen (A (D :: Γ') C))]
  | .ifThen (.somehow A₁) B₁ =>
      ((A Γ' A₁).and (A (B₁ :: Γ') C))
      :: Γ'.filterMap (fun X => match X with
          | .somehow x =>
              let Γ'' := Γ'.erase (somehow x)
              some (((A (x :: Γ'') A₁.somehow).somehow).and
                (A (B₁ :: Γ') C))
          | _ => none)
  | .somehow χ =>
      (match C with
        | .somehow _ => [(A (χ :: Γ') C).somehow]
        | _ => [])
  | _ => []

/-- `L◯→`-nonprincipal γ-disjuncts, A-side. -/
def aGammaClauses (Γ : List PLLFormula) (C F : PLLFormula) : List PLLFormula :=
  match F with
  | .ifThen (.somehow α) β =>
      let Γ' := Γ.erase F
      [((A Γ' α.somehow).somehow).and (A (β :: Γ') C)]
  | _ => []

end Clauses

mutual

/-- Iemhoff's `∃pS`, sequent-indexed, fueled. -/
def iemE (p : String) : Nat → List PLLFormula → PLLFormula → PLLFormula
  | 0, _, _ => truePLL
  | fuel + 1, Γ, C =>
      andAll (
        eAtomList p Γ
        ++ (if isAxInst Γ C then
              [andAll (Γ.filter (fun φ => p ∉ φ.atoms))] else [])
        ++ Γ.flatMap (eCtxClauses p (iemE p fuel) (iemA p fuel) Γ C)
        ++ eGoalClauses p (iemE p fuel) Γ C
        ++ Γ.flatMap (eOpenClauses (iemE p fuel) Γ)
        ++ Γ.flatMap (eGammaClauses (iemE p fuel) (iemA p fuel) Γ C)
        ++ ePlumbClauses (iemE p fuel) Γ C)

/-- Iemhoff's `∀pS`, sequent-indexed, fueled. -/
def iemA (p : String) : Nat → List PLLFormula → PLLFormula → PLLFormula
  | 0, _, _ => falsePLL
  | fuel + 1, Γ, C =>
      orAll (
        (if isAxInst Γ C then [truePLL] else [])
        ++ aGoalClauses p (iemE p fuel) (iemA p fuel) Γ C
        ++ Γ.flatMap (aCtxClauses p (iemE p fuel) (iemA p fuel) Γ C)
        ++ Γ.flatMap (aGammaClauses (iemA p fuel) Γ C))

end


end G4Probe
end PLLND
-- ===== Instruments =====
namespace PLLND
namespace G4Probe
open PLLFormula

/-- Node count of a formula. -/
def fsize : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and A B => fsize A + fsize B + 1
  | .or A B => fsize A + fsize B + 1
  | .ifThen A B => fsize A + fsize B + 1
  | .somehow A => fsize A + 1

/-- Canonical fuel: the documented sufficient bound. -/
def cfuel (Γ : List PLLFormula) (C : PLLFormula) : Nat := seqMeasure Γ C

def eVal (p : String) (Γ : List PLLFormula) (C : PLLFormula) : PLLFormula :=
  iemE p (cfuel Γ C) Γ C
def aVal (p : String) (Γ : List PLLFormula) (C : PLLFormula) : PLLFormula :=
  iemA p (cfuel Γ C) Γ C

-- shorthands
def pp : PLLFormula := prop "p"
def qq : PLLFormula := prop "q"
def rr : PLLFormula := prop "r"

end G4Probe
end PLLND

open PLLFormula PLLND PLLND.G4Probe

-- ===== Memoized G4 search (mirrors PLLDecide.succs exactly) =====
namespace PLLND
namespace G4Probe
open PLLFormula

/-- Canonical string encoding (injective). -/
def enc : PLLFormula → String
  | .prop a => "P" ++ a
  | .falsePLL => "F"
  | .and A B => "(" ++ enc A ++ "&" ++ enc B ++ ")"
  | .or A B => "(" ++ enc A ++ "|" ++ enc B ++ ")"
  | .ifThen A B => "(" ++ enc A ++ ">" ++ enc B ++ ")"
  | .somehow A => "O" ++ enc A

/-- Permutation-canonical sequent key (multiset: sorted WITH duplicates —
contraction is not admissible in G4, so duplicates matter). -/
def skey (Γ : List PLLFormula) (C : PLLFormula) : String :=
  String.intercalate "," ((Γ.map enc).mergeSort (· ≤ ·)) ++ "⊢" ++ enc C

/-- Memoized backward search over `PLLDecide.succs` — the same recursion as
the library's `decideG4` (`G4 Γ C ↔ ∃ inst ∈ succs Γ C, ∀ s ∈ inst, G4 s.1 s.2`
by `succs_sound`/`succs_complete`), plus memoization on the
permutation-canonical key (sound by `G4.perm`).  Terminates because every
`succs` premise strictly DM-descends (`succs_dec`); `partial` only because
we do not replay that proof. -/
partial def g4mM (Γ : List PLLFormula) (C : PLLFormula) :
    StateM (Std.HashMap String Bool) Bool := do
  let k := skey Γ C
  match (← get).get? k with
  | some b => pure b
  | none => do
      let r ← (succs Γ C).anyM (fun inst => inst.allM fun s => g4mM s.1 s.2)
      modify (fun m => m.insert k r)
      pure r

/-- Fresh-memo entry point. -/
def g4B (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  (g4mM Γ C).run' ∅

end G4Probe
end PLLND
-- ===== Budgeted memoized search: `none` = budget out (honest skip) =====
namespace PLLND
namespace G4Probe
open PLLFormula

deriving instance Hashable for PLLFormula

/-- Permutation-canonical key: context sorted by hash (ties by any
consistent order are unnecessary — a tie-order difference only costs a
memo miss, never soundness, since map equality is full structural
equality). Multiset-faithful: duplicates kept (no contraction in G4). -/
def hkey (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula × PLLFormula :=
  (Γ.mergeSort (fun a b => hash a ≤ hash b), C)

abbrev BS := Std.HashMap (List PLLFormula × PLLFormula) Bool × Nat

/-- Budgeted search.  Result semantics:
* `some true`  — derivable (an instance with all premises `some true`);
* `some false` — **exhaustively** underivable (every instance refuted with
  no budget interference) — decision-equivalent to `decide (G4 Γ C)` = false;
* `none`       — expansion budget hit somewhere relevant: NO verdict.
Only definitive verdicts are memoized. -/
partial def g4bM (Γ : List PLLFormula) (C : PLLFormula) :
    StateM BS (Option Bool) := do
  let k := hkey Γ C
  match (← get).1.get? k with
  | some b => pure (some b)
  | none =>
      if (← get).2 = 0 then pure none else do
      modify (fun s => (s.1, s.2 - 1))
      -- fold over instances: some true short-circuits; none taints a
      -- final negative; some false on an instance is definitive for it.
      let rec instLoop : List (List Sequent) → Bool → StateM BS (Option Bool)
        | [], tainted => pure (if tainted then none else some false)
        | inst :: rest, tainted => do
            let rec premLoop : List Sequent → StateM BS (Option Bool)
              | [] => pure (some true)
              | s :: ss => do
                  match ← g4bM s.1 s.2 with
                  | some true => premLoop ss
                  | some false => pure (some false)
                  | none => pure none
            match ← premLoop inst with
            | some true => pure (some true)
            | some false => instLoop rest tainted
            | none => instLoop rest true
      let r ← instLoop (succs Γ C) false
      match r with
      | some b => modify (fun s => (s.1.insert k b, s.2)); pure (some b)
      | none => pure none

/-- Fresh run with budget `n` expansions. -/
def g4bud (n : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Option Bool :=
  (g4bM Γ C).run' (∅, n)

end G4Probe
end PLLND
-- ===== Sweep infrastructure =====
namespace PLLND
namespace G4Probe
open PLLFormula

abbrev M := StateM (Std.HashMap String Bool)

/-- (∃r) probe: `⊢ Γ ⇒ ∃p(Γ ⇒ C)`. -/
def probeEm (p : String) (Γ : List PLLFormula) (C : PLLFormula) : M Bool :=
  g4mM Γ (iemE p (cfuel Γ C) Γ C)

/-- (∀l) probe: `⊢ ∀p(Γ ⇒ C), Γ ⇒ C`. -/
def probeAm (p : String) (Γ : List PLLFormula) (C : PLLFormula) : M Bool :=
  g4mM (iemA p (cfuel Γ C) Γ C :: Γ) C

/-- (∃r)-L4→-(i) conjunct probe at `F = (A→B)→D ∈ Γ`:
`⊢ Γ ⇒ ∃p(B→D, Γ∖F ⇒ A→B)` — the sorried step of `eSound`. -/
def probeL4m (p : String) (Γ : List PLLFormula) : PLLFormula → M (Option Bool)
  | F@(.ifThen (.ifThen A B) D) =>
      if F ∈ Γ then do
        let S₁Γ := B.ifThen D :: Γ.erase F
        let S₁C := A.ifThen B
        let r ← g4mM Γ (iemE p (cfuel S₁Γ S₁C) S₁Γ S₁C)
        pure (some r)
      else pure none
  | _ => pure none

/-- Adequacy probes; `none` = gate failed (premise sequent underivable). -/
def probeAdqAm (p : String) (Γ Δ : List PLLFormula) (C : PLLFormula) :
    M (Option Bool) := do
  let gate ← g4mM (Γ ++ Δ) C
  if gate then
    let F := cfuel Γ C + 1
    let r ← g4mM (iemE p F Γ C :: Δ) (iemA p F Γ C)
    pure (some r)
  else pure none

def probeAdqEm (p : String) (Γ Δ : List PLLFormula) (C : PLLFormula) :
    M (Option Bool) := do
  if p ∈ C.atoms then pure none else do
  let gate ← g4mM (Γ ++ Δ) C
  if gate then
    let F := cfuel Γ C + 1
    let r ← g4mM (iemE p F Γ falsePLL :: Δ) C
    pure (some r)
  else pure none

/-- Run one family: returns (tested, gated-out/skipped, failures). -/
def runFam {α : Type} (jobs : List α) (probe : α → M (Option Bool)) :
    Nat × Nat × List α :=
  (jobs.foldlM (fun (acc : Nat × Nat × List α) j => do
      match ← probe j with
      | none => pure (acc.1, acc.2.1 + 1, acc.2.2)
      | some true => pure (acc.1 + 1, acc.2.1, acc.2.2)
      | some false => pure (acc.1 + 1, acc.2.1, acc.2.2 ++ [j])
    ) (0, 0, [])).run' ∅

end G4Probe
end PLLND
-- ===== Instance generators =====
namespace PLLND
namespace G4Probe
open PLLFormula

/-- p-side pool: small formulas mentioning `p` (plus a few mixed). -/
def pPool : List PLLFormula :=
  [pp, pp.somehow, qq.ifThen pp, qq.ifThen pp.somehow, qq.somehow.ifThen pp,
   pp.ifThen qq, pp.somehow.ifThen qq, (qq.ifThen pp).somehow, pp.and qq,
   pp.or qq]

/-- p-free pool (for Δ). -/
def dPool : List PLLFormula := [qq.somehow, qq, qq.somehow.somehow, qq.ifThen rr]

/-- goal pool. -/
def cPool : List PLLFormula :=
  [pp, qq, rr, falsePLL, pp.somehow, qq.somehow, pp.ifThen qq, qq.ifThen pp,
   (qq.ifThen pp).somehow, pp.or qq, pp.and qq]

/-- sublists of length ≤ n. -/
def subsLe (n : Nat) (l : List PLLFormula) : List (List PLLFormula) :=
  l.sublists.filter (fun s => s.length ≤ n)

/-- (∃r)/(∀l) instance family: Γ ⊆ pPool∪dPool (≤2), C ∈ cPool. -/
def famSound : List (List PLLFormula × PLLFormula) :=
  (subsLe 2 (pPool ++ dPool)).flatMap (fun Γ => cPool.map (fun C => (Γ, C)))

/-- L4→ family: `F = (A→B)→D`, Γ = [F] or [F, X]. -/
def famL4 : List (List PLLFormula × PLLFormula) :=
  let As : List PLLFormula := [qq, pp, pp.somehow, qq.somehow, pp.ifThen qq, qq.ifThen pp]
  let Bs : List PLLFormula := [pp, qq, pp.somehow, qq.somehow, rr]
  let Ds : List PLLFormula := [pp, qq, rr, falsePLL, pp.somehow, qq.somehow]
  let Xs : List (List PLLFormula) := [[], [qq], [qq.somehow], [pp], [pp.somehow], [qq.ifThen pp]]
  (As.flatMap fun A => Bs.flatMap fun B => Ds.flatMap fun D =>
    Xs.map fun X => ((A.ifThen B).ifThen D :: X, (A.ifThen B).ifThen D))

/-- Adequacy family: (Γ, Δ, C) with Δ p-free. -/
def famAdq : List (List PLLFormula × List PLLFormula × PLLFormula) :=
  (subsLe 2 pPool).flatMap fun Γ =>
    (subsLe 2 dPool).flatMap fun Δ =>
      cPool.map fun C => (Γ, Δ, C)

end G4Probe
end PLLND
-- ===== DPN-targeted family: Δ-side box, i-side succedent =====
namespace PLLND
namespace G4Probe
open PLLFormula

/-- Γ-parts with p-content, small. -/
def dpnG : List (List PLLFormula) :=
  [[pp], [pp.somehow], [qq.ifThen pp], [qq.ifThen pp.somehow],
   [qq.somehow.ifThen pp], [qq.somehow.ifThen pp.somehow],
   [pp.ifThen qq], [(qq.ifThen pp).somehow], [pp, pp.ifThen qq],
   [qq.ifThen pp, pp.ifThen qq.somehow], [pp.somehow.ifThen qq]]

/-- p-free Δ-parts, each containing a box. -/
def dpnD : List (List PLLFormula) :=
  [[qq.somehow], [qq, qq.somehow], [qq.somehow.somehow], [rr.somehow],
   [qq.somehow, rr.somehow], [(qq.ifThen rr).somehow], [qq.ifThen rr, qq.somehow]]

/-- circle succedents (i-side: mostly p-containing). -/
def dpnC : List PLLFormula :=
  [pp.somehow, qq.somehow, (qq.ifThen pp).somehow, (pp.ifThen qq).somehow,
   pp.somehow.somehow, (pp.and qq).somehow, (pp.or qq).somehow, rr.somehow]

def famDPN : List (List PLLFormula × List PLLFormula × PLLFormula) :=
  dpnG.flatMap fun Γ => dpnD.flatMap fun Δ => dpnC.map fun C => (Γ, Δ, C)

end G4Probe
end PLLND
-- ===== Budgeted family runners =====
namespace PLLND
namespace G4Probe
open PLLFormula

/-- Outcome tally: (passes, violations, budget-outs, gate-outs) plus the
violation and budget-out instance lists. -/
structure Tally (α : Type) where
  pass : Nat := 0
  viol : Nat := 0
  bud : Nat := 0
  gate : Nat := 0
  violL : List α := []
  budL : List α := []
deriving Repr

/-- Budgeted run; each instance gets a fresh budget but the memo is shared
across the family (only definitive entries are stored, so sharing is sound). -/
def runB {α : Type} (jobs : List α)
    (probe : α → StateM BS (Option (Option Bool))) (budget : Nat) : Tally α :=
  (jobs.foldlM (fun (t : Tally α) j => do
      modify (fun s => (s.1, budget))  -- refill budget
      match ← probe j with
      | none => pure { t with gate := t.gate + 1 }
      | some none => pure { t with bud := t.bud + 1, budL := t.budL ++ [j] }
      | some (some true) => pure { t with pass := t.pass + 1 }
      | some (some false) => pure { t with viol := t.viol + 1, violL := t.violL ++ [j] }
    ) {}).run' (∅, budget)

/-- Budgeted probes.  Outer `none` = gate failed (or gate budget-out). -/
def probeEb (p : String) (j : List PLLFormula × PLLFormula) :
    StateM BS (Option (Option Bool)) := do
  pure (some (← g4bM j.1 (iemE p (cfuel j.1 j.2) j.1 j.2)))

def probeAb (p : String) (j : List PLLFormula × PLLFormula) :
    StateM BS (Option (Option Bool)) := do
  pure (some (← g4bM (iemA p (cfuel j.1 j.2) j.1 j.2 :: j.1) j.2))

def probeL4b (p : String) (j : List PLLFormula × PLLFormula) :
    StateM BS (Option (Option Bool)) :=
  match j.2 with
  | .ifThen (.ifThen A B) D =>
      if (A.ifThen B).ifThen D ∈ j.1 then do
        let S₁Γ := B.ifThen D :: j.1.erase ((A.ifThen B).ifThen D)
        let S₁C := A.ifThen B
        pure (some (← g4bM j.1 (iemE p (cfuel S₁Γ S₁C) S₁Γ S₁C)))
      else pure none
  | _ => pure none

def probeAdqAb (p : String) (j : List PLLFormula × List PLLFormula × PLLFormula) :
    StateM BS (Option (Option Bool)) := do
  match ← g4bM (j.1 ++ j.2.1) j.2.2 with
  | some true =>
      let F := cfuel j.1 j.2.2 + 1
      pure (some (← g4bM (iemE p F j.1 j.2.2 :: j.2.1) (iemA p F j.1 j.2.2)))
  | _ => pure none

def probeAdqEb (p : String) (j : List PLLFormula × List PLLFormula × PLLFormula) :
    StateM BS (Option (Option Bool)) := do
  if p ∈ j.2.2.atoms then pure none else
  match ← g4bM (j.1 ++ j.2.1) j.2.2 with
  | some true =>
      let F := cfuel j.1 j.2.2 + 1
      pure (some (← g4bM (iemE p F j.1 falsePLL :: j.2.1) j.2.2))
  | _ => pure none

end G4Probe
end PLLND

/-! ## Reproduction lines (each was run as a separate `#eval`; results inline above)
* `#eval runFam famSound (fun j => do pure (some (← probeEm "p" j.1 j.2)))` → `(1166, 0, [])`
* `#eval runFam famL4 (fun j => probeL4m "p" j.1 j.2)` → `(1080, 0, [])`
* `#eval runFam (famSound.take 300) (fun j => do pure (some (← probeAm "p" j.1 j.2)))` → `(300, 0, [])`
* `#eval g4B (eVal "p" [qq.ifThen pp] pp.somehow :: [qq.somehow]) (aVal "p" [qq.ifThen pp] pp.somehow)` → `true`
* `#eval g4bud 1000000 (eVal "p" [qq.somehow.ifThen pp] pp.somehow :: [qq.somehow]) (aVal "p" [qq.somehow.ifThen pp] pp.somehow)` → unresolved (killed ~8 min)
* validation: `[g4B ..., decide (G4 ...)]` agreed on ◯-unit/◯◯→◯/refl/EM/gap/cut-left/two-copies.
-/
