/-
# The FRJ(◯) forward-saturation engine, as a library

Ported verbatim from `wip/frj_sat.lean` (namespace `FRJSat`), which stays
in place as the FROZEN reference implementation: it is the differential
oracle for everything built here, and the two are expected to agree on
every goal both settle.

Nothing in this module is used by a proof.  Its output is a typed
derivation (`FRJr G t Γ G`), so a hit inhabits `Provable G` and can be
turned into a kernel-checkable certificate by extracting the model
(`FRJ.modR`) and `decide`-ing the refutation; discovery stays untrusted,
as the repo's discover-then-pin discipline requires.

**Derivation-carrying.**  Every database row packs its own `FRJr`/`FRJi`
term: rule side conditions are discharged by `Decidable` instances at
insertion time, so the engine cannot misapply a rule — a faithfulness bug
is a type error, and a hit IS a derivation.

Caps are reported, never silent: joins are bounded in premise arity,
promise arity, and `Λ`-split width; each cap prints with the verdict.
-/
import FRJ.Calculus

namespace FRJ.Search

open Form

open FRJ Form

/-! ## Rows: sequents carrying their derivations -/

/-- A regular row `Γ ⇒ C` with its tag and derivation. -/
structure RS (G : Form) where
  t : Tag
  ctx : List Form
  rhs : Form
  der : FRJr G t ctx rhs

/-- An irregular row `Σ ; Θ → C` with its derivation.  No canonicality
invariant: since the deslime the `⊃∈` zone split is EXTENSIONAL
(`Θ ≐ (Θ \ Λ) ++ Λ`), so any zone splits. -/
structure IS (G : Form) where
  stab : List Form
  th : List Form
  rhs : Form
  der : FRJi G stab th rhs

/-! ## Decidable plumbing -/

instance decSubset (l m : List Form) : Decidable (l ⊆ m) :=
  decidable_of_iff (∀ x ∈ l, x ∈ m) (by
    constructor
    · intro h a ha; exact h a ha
    · intro h a ha; exact h ha)

/-- The `hJ2` check, phrased boundedly: every implication among the
stable parts has its antecedent in `Υ`. -/
def ImpAnteOk (Υ : List Form) : Form → Prop
  | .imp A _ => A ∈ Υ
  | _ => True

instance (Υ : List Form) (X : Form) : Decidable (ImpAnteOk Υ X) := by
  cases X <;> simp [ImpAnteOk] <;> infer_instance

/-- The `hJ5` check, phrased boundedly. -/
def CircBodyOk {k : Nat} (Δs : Fin (k + 1) → List Form) : Form → Prop
  | .circ Y => ∃ i, Clo (Δs i) Y
  | _ => True

instance {k : Nat} (Δs : Fin (k + 1) → List Form) (X : Form) :
    Decidable (CircBodyOk Δs X) := by
  cases X <;> simp [CircBodyOk] <;> infer_instance

/-! ## Zone-split helper for `⊃∈` -/

/-- The `⊃∈` zone split, extensionally: for `Λ ⊆ Θ`, `Θ` denotes the same
set as `(Θ \ Λ) ++ Λ`.  This is the whole content of the split now — no
normal form and no transport of the premise derivation. -/
theorem zone_split {Θ Λ : List Form} (hΛ : ∀ x ∈ Λ, x ∈ Θ) :
    Θ ≐ FRJ.sdiff Θ Λ ++ Λ := by
  intro x
  constructor
  · intro h
    by_cases hl : x ∈ Λ
    · exact List.mem_append_right _ hl
    · exact List.mem_append_left _ (mem_sdiff.mpr ⟨h, hl⟩)
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact (mem_sdiff.mp h).1
    · exact hΛ _ h

/-! ## Seeds -/

def seedsR (G : Form) : List (RS G) :=
  (sfR G).filterMap (fun F =>
    if hF : F.isPrime then
      if hg : F ∈ sfR G then
        some ⟨.barren, rm (gAt G) F, F, .axR F hF hg (CtxEq.refl _)⟩
      else none
    else none)

def seedsI (G : Form) : List (IS G) :=
  (sfR G).filterMap (fun F =>
    if hF : F.isPrime then
      if hg : F ∈ sfR G then
        some ⟨[], (rm (gAt G) F) ++ gImp G ++ gCirc G, F,
          .axI F hF hg (CtxEq.refl _)⟩
      else none
    else none)

/-- The `Ax^I◯` seeds (round-2 general form): for every `F` with
`◯F ∈ sfR G` and every classical valuation `ats ⊆ Ĝ_at` refuting `F`, the
mounted bare-final-world axiom `[] ; vacZoneA G ats → ◯F`.  Valuations
are the full subset lattice when `Ĝ_at` is small; above the cap only the
empty, the full, and the `F`-removed valuation are tried (reported in the
banner). -/
def seedsIC (G : Form) : List (IS G) :=
  (sfR G).flatMap (fun C =>
    match C with
    | .circ F =>
      if hg : Form.circ F ∈ sfR G then
        let vals := if (gAt G).length ≤ 4 then (gAt G).sublists
          else [[], gAt G, rm (gAt G) F]
        vals.filterMap (fun ats =>
          if hats : ats ⊆ gAt G then
            if hFf : classForce ats F = false then
              some ⟨[], vacZoneA G ats, .circ F,
                .axIC F ats hats hFf hg (CtxEq.refl _)⟩
            else none
          else none)
      else []
    | _ => [])

/-! ## Single-premise regular rules -/

/-- `∧`, `⊃∈`, `◯∈` applied to one regular row, against every right
subformula target. -/
def stepR1 (G : Form) (r : RS G) : List (RS G) :=
  (sfR G).filterMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .and A B, hg =>
          if h1 : r.rhs = A then
            some ⟨r.t, r.ctx, .and A B, .andR1 (h1 ▸ r.der) hg⟩
          else if h2 : r.rhs = B then
            some ⟨r.t, r.ctx, .and A B, .andR2 (h2 ▸ r.der) hg⟩
          else none
      | .imp A B, hg =>
          if h : r.rhs = B then
            if hA : Clo r.ctx A then
              some ⟨r.t, r.ctx, .imp A B, .impIn (h ▸ r.der) hA hg⟩
            else none
          else none
      | .circ Z, hg =>
          if h : r.rhs = Z then
            if ht : r.t = .barren ∨ ∃ W, r.t = .chain W ∧ Covers r.ctx W Z then
              some ⟨r.t, r.ctx, .circ Z, .circIn (h ▸ r.der) ht hg⟩
            else none
          else none
      | _, _ => none
    else none)

/-! ## Single- and double-premise irregular rules -/

/-- `∧` (irregular). -/
def stepI1 (G : Form) (i : IS G) : List (IS G) :=
  (sfR G).filterMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .and A B, hg =>
          if h1 : i.rhs = A then
            some ⟨i.stab, i.th, .and A B, .andI1 (h1 ▸ i.der) hg⟩
          else if h2 : i.rhs = B then
            some ⟨i.stab, i.th, .and A B, .andI2 (h2 ▸ i.der) hg⟩
          else none
      | _, _ => none
    else none)

/-- `∨` (irregular), on an ordered pair of rows. -/
def stepOrI (G : Form) (i1 i2 : IS G) : List (IS G) :=
  (sfR G).filterMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .or C₁ C₂, hg =>
          if h1 : i1.rhs = C₁ then
            if h2 : i2.rhs = C₂ then
              if hs1 : i1.stab ⊆ i2.stab ++ i2.th then
                if hs2 : i2.stab ⊆ i1.stab ++ i1.th then
                  some ⟨i1.stab ++ i2.stab, cap i1.th i2.th, .or C₁ C₂,
                    .orI (h1 ▸ i1.der) (h2 ▸ i2.der) hs1 hs2 hg
                      (CtxEq.refl _) (CtxEq.refl _)⟩
                else none
              else none
            else none
          else none
      | _, _ => none
    else none)

/-- The `Λ`-candidates for the `⊃∈` zone split: full enumeration below
the width cap, a pragmatic list above it (reported). -/
def lamCandidates (th : List Form) (cap : Nat) : List (List Form) × Bool :=
  if th.length ≤ cap then (th.sublists, false)
  else (([] : List Form) :: th :: th.map (fun x => [x]), true)

/-- `⊃∈` (irregular): enumerate zone splits. -/
def stepImpInI (G : Form) (lamCap : Nat) (i : IS G) : List (IS G) × Bool :=
  let (lams, capped) := lamCandidates i.th lamCap
  (((sfR G).flatMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .imp A B, hg =>
          if h : i.rhs = B then
            lams.filterMap (fun Λ =>
              if hΛ : ∀ x ∈ Λ, x ∈ i.th then
                if hA : Clo (i.stab ++ Λ) A then
                  some ⟨i.stab ++ Λ, FRJ.sdiff i.th Λ, .imp A B,
                    .impInI (h ▸ i.der) (zone_split hΛ) cap_sdiff_eq_nil hA hg
                      (CtxEq.refl _) (CtxEq.refl _)⟩
                else none
              else none)
          else []
      | _, _ => []
    else [])), capped)

/-- The canonical maximal `Θ` for the world-changing irregular rules. -/
def thetaMax (G : Form) (Γ : List Form) : List Form :=
  (gHat G).filter (fun X => cloB Γ X)

/-! ### The `⊃∉` zone candidates

`⊃∉` needs `Θ ⊆ Cl(Γ) ∩ Ĝ` with `A ∉ Cl(Θ)`.  The admissible zones form a
down-set (`Clo` is monotone in the zone), and every irregular consumer
accepts a larger second zone wherever it accepts a smaller one, so the
⊆-MAXIMAL admissible zones suffice.  They are read off the grammar of
`Cl`: `A ∉ Cl(Θ)` iff `A ∉ Θ` and, by the shape of `A`, its generators
are absent — `∧`: SOME conjunct absent; `∨`: BOTH disjuncts absent;
`⊃`, `◯`: the consequent/body absent.  `removalSets Θ A` lists the
⊆-minimal `R ⊆ Θ` with `A ∉ Cl(Θ \ R)`; the candidates are `Θmax \ R`.

History (2026-08-17): the previous enumeration offered only `Θmax` and
`Θmax` purged of the SINGLE generators of `A` (`X` with `A ∈ Cl({X})`),
which misses every `A` generated JOINTLY.  Erasure of `dn_circ_and`,
`G = ¬¬(p∧q) ⊃ (p∧q)`, `A = p∧q`, `Θmax = {p, q, ¬¬(p∧q)}`: no single
member generates `p∧q`, both candidates were `Θmax` itself, `hAnot`
failed on both, and the zone `{¬¬(p∧q)}` (= `Λ*` of the countermodel's
root, the zone the completeness construction uses) was never offered —
so `[] ; ¬¬(p∧q) → ¬(p∧q)`, hence `¬¬(p∧q) ⇒ p` by `⋈^At`, was never
derived, and the engine reported a rule-closure fixpoint without the
goal.  With the maximal admissible zones `{p, ¬¬(p∧q)}`, `{q, ¬¬(p∧q)}`
the derivation is found.

Side effect: `⊃∉` is now MONOTONE in the regular premise's context — for
`Γ ⊆ Γ'` every maximal admissible zone over `Γ` extends to one over `Γ'`
(admissible zones over `Γ` are admissible over `Γ'`, `Θmax` grows, `hA`
is monotone) — so the RS subsumption's former exception (the `hAnot`
gate) is gone. -/

/-- Set inclusion of contexts, as a `Bool` (shared with the subsumption
layer below). -/
def subB (l m : List Form) : Bool := l.all (fun x => decide (x ∈ m))

/-- The ⊆-minimal members of a family of sets (deduplicated up to set
equality). -/
def minimalSets (l : List (List Form)) : List (List Form) :=
  l.foldl (fun acc R =>
    if acc.any (fun R' => subB R' R) then acc
    else R :: acc.filter (fun R' => !(subB R R'))) []

/-- The ⊆-minimal `R ⊆ Θ` with `A ∉ Cl(Θ \ R)`, by the grammar of `Cl`. -/
def removalSets (Θ : List Form) : Form → List (List Form)
  | .atom p => [if Form.atom p ∈ Θ then [Form.atom p] else []]
  | .bot => [if Form.bot ∈ Θ then [Form.bot] else []]
  | .and X Y =>
      let s := if Form.and X Y ∈ Θ then [Form.and X Y] else []
      minimalSets ((removalSets Θ X ++ removalSets Θ Y).map (s ++ ·))
  | .or X Y =>
      let s := if Form.or X Y ∈ Θ then [Form.or X Y] else []
      minimalSets ((removalSets Θ X).flatMap (fun R₁ =>
        (removalSets Θ Y).map (fun R₂ => s ++ R₁ ++ R₂)))
  | .imp A X =>
      let s := if Form.imp A X ∈ Θ then [Form.imp A X] else []
      minimalSets ((removalSets Θ X).map (s ++ ·))
  | .circ X =>
      let s := if Form.circ X ∈ Θ then [Form.circ X] else []
      minimalSets ((removalSets Θ X).map (s ++ ·))

/-- The `⊃∉` zone candidates: the ⊆-maximal `Θ ⊆ Θmax(Γ) = Cl(Γ) ∩ Ĝ`
with `A ∉ Cl(Θ)` (pre-`nf`; `stepNotIn` canonicalises).  Untrusted:
`hAnot` is still decided at insertion, so a defect here can only lose
rows, never admit one. -/
def thetaCandidates (G : Form) (Γ : List Form) (A : Form) : List (List Form) :=
  let Θmax := thetaMax G Γ
  (removalSets Θmax A).map (fun R => FRJ.sdiff Θmax R)

/-- `⊃∉` and `◯∉` from one regular row.  The `Θ`-candidates are cut down
to `Ĝ` by construction, which is what the rules' own `hTh` field asks
for. -/
def stepNotIn (G : Form) (r : RS G) : List (IS G) :=
  (sfR G).flatMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .imp A B, hg =>
          if h : r.rhs = B then
            if hA : Clo r.ctx A then
              (thetaCandidates G r.ctx A).filterMap (fun l =>
                let Θ := l.filter (fun x => decide (x ∈ gHat G))
                if hTh : ∀ X ∈ Θ, Clo r.ctx X ∧ X ∈ gHat G then
                  if hAnot : ¬ Clo Θ A then
                    some ⟨[], Θ, .imp A B,
                      .impNotIn (h ▸ r.der) hTh hA hAnot hg⟩
                  else none
                else none)
            else []
          else []
      | .circ Z, hg =>
          if h : r.rhs = Z then
            if ht : r.t = .barren ∨ ∃ W, r.t = .chain W ∧ Covers r.ctx W Z then
              let Θ := (gHat G).filter (fun X => cloB r.ctx X)
              if hTh : ∀ X ∈ Θ, Clo r.ctx X ∧ X ∈ gHat G then
                [⟨[], Θ, .circ Z, .circNotIn (h ▸ r.der) ht hTh hg⟩]
              else []
            else []
          else []
      | _, _ => []
    else [])

/-! ## The joins

Premises are packed as a head-and-rest pair so the `Fin (n+1)` indexing
of the constructors is definitional (`(a :: rest).length = rest.length + 1`).
-/

section Joins

variable {G : Form}

/-- The zone functions of a premise family. -/
def stabF (a : IS G) (rest : List (IS G)) : Fin (rest.length + 1) → List Form :=
  fun j => ((a :: rest).get j).stab

def thF (a : IS G) (rest : List (IS G)) : Fin (rest.length + 1) → List Form :=
  fun j => ((a :: rest).get j).th

def rhsF (a : IS G) (rest : List (IS G)) : Fin (rest.length + 1) → Form :=
  fun j => ((a :: rest).get j).rhs

def premF (a : IS G) (rest : List (IS G)) :
    ∀ j, FRJi G (stabF a rest j) (thF a rest j) (rhsF a rest j) :=
  fun j => ((a :: rest).get j).der

/-- The promise-family functions. -/
def dctxF (p : RS G) (prest : List (RS G)) : Fin (prest.length + 1) → List Form :=
  fun i => ((p :: prest).get i).ctx

def drhsF (p : RS G) (prest : List (RS G)) : Fin (prest.length + 1) → Form :=
  fun i => ((p :: prest).get i).rhs

def dtagF (p : RS G) (prest : List (RS G)) : Fin (prest.length + 1) → Tag :=
  fun i => ((p :: prest).get i).t

def dpsF (p : RS G) (prest : List (RS G)) :
    ∀ i, FRJr G (dtagF p prest i) (dctxF p prest i) (drhsF p prest i) :=
  fun i => ((p :: prest).get i).der

/-- The shared (J1) and `Υ`-antecedent checks. -/
def j1j2Check (a : IS G) (rest : List (IS G)) :
    Option (PLift ((∀ i j, i ≠ j → stabF a rest i ⊆ stabF a rest j ++ thF a rest j) ∧
      (∀ X ∈ unionAll (fun j => impPart (stabF a rest j)), ImpAnteOk (upsilon (rhsF a rest)) X))) :=
  if h1 : ∀ i j, i ≠ j → stabF a rest i ⊆ stabF a rest j ++ thF a rest j then
    if h2 : ∀ X ∈ unionAll (fun j => impPart (stabF a rest j)),
        ImpAnteOk (upsilon (rhsF a rest)) X then
      some ⟨h1, h2⟩
    else none
  else none

/-- Convert the bounded `Υ`-check into the rule's `hJ2` form. -/
theorem hJ2_of_check {a : IS G} {rest : List (IS G)}
    (h : ∀ X ∈ unionAll (fun j => impPart (stabF a rest j)),
      ImpAnteOk (upsilon (rhsF a rest)) X) :
    ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stabF a rest j)) →
      A ∈ upsilon (rhsF a rest) :=
  fun _ _ hm => h _ hm

/-- The barren joins (`⋈^At`, `⋈^∨`) on one premise family. -/
def mkJoinBarren (a : IS G) (rest : List (IS G)) : List (RS G) :=
  match j1j2Check a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    if hcirc : unionAll (fun j => circPart (stabF a rest j)) = [] then
      -- ⋈^At over prime targets
      ((sfR G).filterMap (fun F =>
        if hF : F.isPrime then
          if hFnot : F ∉ unionAll (fun j => atPart (stabF a rest j)) then
            if hg : F ∈ sfR G then
              some ⟨.barren, joinCtxAt (stabF a rest) (thF a rest) (rhsF a rest) F, F,
                .joinAt (premF a rest) h1 (hJ2_of_check h2) hcirc hF hFnot hg (CtxEq.refl _)⟩
            else none
          else none
        else none)) ++
      -- ⋈^∨ over disjunction targets
      ((sfR G).filterMap (fun T =>
        if hg : T ∈ sfR G then
          match T, hg with
          | .or C₁ C₂, hg =>
              if hC : C₁ ∈ upsilon (rhsF a rest) ∧ C₂ ∈ upsilon (rhsF a rest) then
                some ⟨.barren, joinCtxOr (stabF a rest) (thF a rest) (rhsF a rest),
                  .or C₁ C₂,
                  .joinOr (premF a rest) h1 (hJ2_of_check h2) hcirc hC hg (CtxEq.refl _)⟩
              else none
          | .circ Z, hg =>
              if hZ : Z ∈ upsilon (rhsF a rest) then
                some ⟨.barren, joinCtxOr (stabF a rest) (thF a rest) (rhsF a rest),
                  .circ Z,
                  .joinCirc (premF a rest) h1 (hJ2_of_check h2) hcirc hZ hg (CtxEq.refl _)⟩
              else none
          | _, _ => none
        else none))
    else []

/-- The fallible joins (`⋈^At,⊥`, `⋈^∨,⊥`) on one premise family. -/
def mkJoinF (a : IS G) (rest : List (IS G)) : List (RS G) :=
  match j1j2Check a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    ((sfR G).filterMap (fun F =>
      if hF : F.isPrime then
        if hFnot : F ∉ unionAll (fun j => atPart (stabF a rest j)) then
          if hg : F ∈ sfR G then
            some ⟨.blocked, joinCtxAtF (stabF a rest) (thF a rest) (rhsF a rest) F, F,
              .joinAtF (premF a rest) h1 (hJ2_of_check h2) hF hFnot hg (CtxEq.refl _)⟩
          else none
        else none
      else none)) ++
    ((sfR G).filterMap (fun T =>
      if hg : T ∈ sfR G then
        match T, hg with
        | .or C₁ C₂, hg =>
            if hC : C₁ ∈ upsilon (rhsF a rest) ∧ C₂ ∈ upsilon (rhsF a rest) then
              some ⟨.blocked, joinCtxOrF (stabF a rest) (thF a rest) (rhsF a rest),
                .or C₁ C₂,
                .joinOrF (premF a rest) h1 (hJ2_of_check h2) hC hg (CtxEq.refl _)⟩
            else none
        | _, _ => none
      else none))

/-- The promise joins on one premise family and one promise family.
Emits the `chain`-tagged row when the family is unanimous, and the
`blocked`-tagged row always. -/
def mkJoinP (a : IS G) (rest : List (IS G)) (p : RS G) (prest : List (RS G)) :
    List (RS G) :=
  match j1j2Check a rest with
  | none => []
  | some ⟨h1, h2⟩ =>
    if h5 : ∀ X ∈ unionAll (fun j => circPart (stabF a rest j)),
        CircBodyOk (dctxF p prest) X then
      let hJ5 : ∀ Y : Form,
          Form.circ Y ∈ unionAll (fun j => circPart (stabF a rest j)) →
          ∃ i, Clo (dctxF p prest i) Y := fun _ hm => h5 _ hm
      if h7 : ∀ i j, ∀ X ∈ stabF a rest j, Clo (dctxF p prest i) X then
      -- the two tag options
      let tags : List ((t' : Tag) ×'
          (t' = .blocked ∨ (t' = .chain (drhsF p prest 0) ∧ ∀ i,
            drhsF p prest i = drhsF p prest 0 ∧
            (dtagF p prest i = .barren ∨ ∃ W, dtagF p prest i = .chain W ∧
              Covers (dctxF p prest i) W (drhsF p prest 0))))) :=
        ⟨.blocked, Or.inl rfl⟩ ::
        (if hch : ∀ i, drhsF p prest i = drhsF p prest 0 ∧
            (dtagF p prest i = .barren ∨ ∃ W, dtagF p prest i = .chain W ∧
              Covers (dctxF p prest i) W (drhsF p prest 0)) then
          [⟨.chain (drhsF p prest 0), Or.inr ⟨rfl, hch⟩⟩]
        else [])
      (tags.flatMap (fun tg =>
        -- ⋈^At,p over prime targets
        ((sfR G).filterMap (fun F =>
          if hF : F.isPrime then
            if hFnot : F ∉ unionAll (fun j => atPart (stabF a rest j)) then
              if hg : F ∈ sfR G then
                some ⟨tg.1,
                  joinCtxAtP (stabF a rest) (thF a rest) (rhsF a rest) F (dctxF p prest), F,
                  .joinAtP (premF a rest) (dpsF p prest) h1 (hJ2_of_check h2)
                    hJ5 h7 tg.2 hF hFnot hg (CtxEq.refl _)⟩
              else none
            else none
          else none)) ++
        -- ⋈^∨,p over disjunction targets
        ((sfR G).filterMap (fun T =>
          if hg : T ∈ sfR G then
            match T, hg with
            | .or C₁ C₂, hg =>
                if hC : C₁ ∈ upsilon (rhsF a rest) ∧ C₂ ∈ upsilon (rhsF a rest) then
                  some ⟨tg.1,
                    joinCtxOrP (stabF a rest) (thF a rest) (rhsF a rest) (dctxF p prest),
                    .or C₁ C₂,
                    .joinOrP (premF a rest) (dpsF p prest) h1 (hJ2_of_check h2)
                      hJ5 h7 tg.2 hC hg (CtxEq.refl _)⟩
                else none
            | _, _ => none
          else none)))) ++
      -- ⋈^◯,p over modal targets: components pledge the body
      ((sfR G).filterMap (fun T =>
        if hg : T ∈ sfR G then
          match T, hg with
          | .circ Z, hg =>
              if hZ : Z ∈ upsilon (rhsF a rest) then
                if hDs : ∀ i, drhsF p prest i = Z ∧
                    (dtagF p prest i = .barren ∨ ∃ W, dtagF p prest i = .chain W ∧
                      Covers (dctxF p prest i) W Z) then
                  some ⟨.chain Z,
                    joinCtxOrP (stabF a rest) (thF a rest) (rhsF a rest) (dctxF p prest),
                    .circ Z,
                    .joinCircP (premF a rest) (dpsF p prest) h1 (hJ2_of_check h2)
                      hJ5 h7 hDs hZ hg (CtxEq.refl _)⟩
                else none
              else none
          | _, _ => none
        else none))
      else []
    else []

end Joins

/-! ## Subsumption and the database

Regular rows are kept maximal in (tag, context): `barren` dominates
`chain D` dominates `blocked` (each is accepted wherever the smaller is),
and a superset context is accepted wherever a subset is by every
consumer.  (Until 2026-08-17 the `hAnot` gate of `⊃∉` was the one
exception — it can hold for a smaller context and fail for a larger —
because only two `Θ`-candidates were tried; with the maximal admissible
zones enumerated, `thetaCandidates`, the rule is monotone in the context
and the exception is gone.)  Irregular rows are kept maximal in the
second zone at set-equal stable zones. -/

def tagLeB : Tag → Tag → Bool
  | .blocked, _ => true
  | .chain D, .chain D' => decide (D = D')
  | .chain _, .barren => true
  | .barren, .barren => true
  | _, _ => false

def rsLe {G : Form} (r r' : RS G) : Bool :=
  decide (r.rhs = r'.rhs) && tagLeB r.t r'.t && subB r.ctx r'.ctx

def isLe {G : Form} (i i' : IS G) : Bool :=
  decide (i.rhs = i'.rhs) && subB i.stab i'.stab && subB i'.stab i.stab
    && subB i.th i'.th

structure DB (G : Form) where
  rs : List (RS G)
  is : List (IS G)

/-- Insert with forward and backward subsumption.  Returns `true` when
the row was genuinely new. -/
def insertR {G : Form} (db : DB G) (r : RS G) : DB G × Bool :=
  if db.rs.any (fun e => rsLe r e) then (db, false)
  else ({ db with rs := r :: db.rs.filter (fun e => !(rsLe e r)) }, true)

def insertI {G : Form} (db : DB G) (i : IS G) : DB G × Bool :=
  if db.is.any (fun e => isLe i e) then (db, false)
  else ({ db with is := i :: db.is.filter (fun e => !(isLe e i)) }, true)

def insertAllR {G : Form} (db : DB G) (l : List (RS G)) : DB G × Nat :=
  l.foldl (fun (acc : DB G × Nat) r =>
    let (db', new) := insertR acc.1 r
    (db', acc.2 + (if new then 1 else 0))) (db, 0)

def insertAllI {G : Form} (db : DB G) (l : List (IS G)) : DB G × Nat :=
  l.foldl (fun (acc : DB G × Nat) i =>
    let (db', new) := insertI acc.1 i
    (db', acc.2 + (if new then 1 else 0))) (db, 0)

/-! ## Family enumeration -/

/-- All sublists of length `≤ k`, preserving order. -/
def combosLe {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _, [] => [[]]
  | k + 1, a :: as => combosLe (k + 1) as ++ (combosLe k as).map (a :: ·)

/-- Head-and-rest families of total size `≤ k`, each subset once. -/
def famsUpTo {α : Type} (l : List α) (k : Nat) : List (α × List α) :=
  match l with
  | [] => []
  | a :: as => ((combosLe (k - 1) as).map (fun rest => (a, rest))) ++ famsUpTo as k

/-- **The differential of `famsUpTo`**: the families of total size `≤ k`
over `new ++ old` that CONTAIN AT LEAST ONE element of `new`.  A family
is split as `s ⊆ new` (nonempty) and `t ⊆ old`, headed by `s`'s first
element — which is exactly the head `famsUpTo (new ++ old) k` gives that
subset, `new` coming first.  Hence

    famsDeltaUpTo new old k ++ famsUpTo old k  =  famsUpTo (new ++ old) k

as sets of families — `#guard`ed below on eight shapes, both degenerate
ends included, together with the ONE shape (`k = 0`) where it fails and
the `max k 1` that callers owe it.  This is the enumerator semi-naive
evaluation runs on
(`Config.semiNaive`, `FRJ/Search/Core.lean`): a family drawn entirely
from `old` was fired in an earlier round and cannot yield a fresh row. -/
def famsDeltaUpTo {α : Type} (new old : List α) (k : Nat) : List (α × List α) :=
  (combosLe k new).flatMap (fun s =>
    match s with
    | [] => []
    | a :: srest => (combosLe (k - s.length) old).map (fun t => (a, srest ++ t)))

section FamsDeltaCheck

/-- A family as a plain list, for the set comparison below. -/
private def famList (f : Nat × List Nat) : List Nat := f.1 :: f.2

private def famSubsetB (a b : List (Nat × List Nat)) : Bool :=
  a.all (fun f => b.any (fun g =>
    let l := famList f; let m := famList g
    l.all (· ∈ m) && m.all (· ∈ l)))

/-- `famsDeltaUpTo new old k ++ famsUpTo old k = famsUpTo (new ++ old) k`,
as sets of families. -/
private def deltaOK (new old : List Nat) (k : Nat) : Bool :=
  let lhs := famsDeltaUpTo new old k ++ famsUpTo old k
  let rhs := famsUpTo (new ++ old) k
  famSubsetB lhs rhs && famSubsetB rhs lhs
    && decide (lhs.length = rhs.length)

-- both degenerate ends, and the shapes the engine actually meets
#guard deltaOK [] [] 3
#guard deltaOK [] [1, 2, 3] 3
#guard deltaOK [1, 2, 3] [] 3
#guard deltaOK [1] [2, 3, 4, 5] 2
#guard deltaOK [1, 2] [3, 4, 5, 6, 7] 3
#guard deltaOK [1, 2, 3] [4, 5, 6] 1
#guard deltaOK [1, 2, 3, 4] [5, 6, 7, 8] 4
-- `k` past the total length: nothing truncates on either side
#guard deltaOK [1, 2] [3] 5

/-! `k = 0` is the ONE shape where the identity fails, and it fails in
the unsafe direction — the differential is EMPTY while `famsUpTo` is
not.  `famsUpTo` reaches `combosLe (k - 1)` with `k = 0` truncating to
`0`, so `famsUpTo l 0 = famsUpTo l 1` = all singletons, whereas
`combosLe 0 new = [[]]` makes every `s` empty and `famsDeltaUpTo _ _ 0 =
[]`.  Callers must therefore pass `max k 1`; `roundStepG` does. -/
#guard !(deltaOK [1, 2] [3, 4, 5] 0)
#guard deltaOK [1, 2] [3, 4, 5] 1
#guard decide (famsUpTo [1, 2, 3] 0 = famsUpTo [1, 2, 3] 1)

/-- **The shape `roundStepG` actually calls**: the differential at
`max k 1`, the old-only half and the naive reference at the caller's
RAW `k`.  `deltaOK` above states the identity at a single `k` and so
does not cover the `max` compensation at all — until this was added the
compensation was asserted only in the prose above it, and `k = 0` is
precisely where the two enumerators disagree.  `jmax = 0` and
`pmax = 0` are admissible `Config` values, so the corner is reachable,
not hypothetical. -/
private def deltaOKmax (new old : List Nat) (k : Nat) : Bool :=
  let lhs := famsDeltaUpTo new old (max k 1) ++ famsUpTo old k
  let rhs := famsUpTo (new ++ old) k
  famSubsetB lhs rhs && famSubsetB rhs lhs
    && decide (lhs.length = rhs.length)

-- the corner the compensation exists for, at every delta shape
-- (GATE WATCHED 2026-09-04: `max k 1` → `k` here turns the two `k = 0`
-- lines with a NON-EMPTY delta red, and only those.)
#guard deltaOKmax [1, 2] [3, 4, 5] 0
#guard deltaOKmax [] [1, 2, 3] 0
#guard deltaOKmax [1, 2, 3] [] 0
#guard deltaOKmax [] [] 0
-- and the budgets the engine runs on (`pmax = 2`, `jmax = 3`)
#guard deltaOKmax [1, 2] [3, 4, 5] 1
#guard deltaOKmax [1] [2, 3, 4, 5] 2
#guard deltaOKmax [1, 2] [3, 4, 5, 6, 7] 3

end FamsDeltaCheck

/-- Does a premise family carry any modal content for a `P`/`F` join to
keep? -/
def modalContent {G : Form} (a : IS G) (rest : List (IS G)) : Bool :=
  !(unionAll (fun j => circPart (stabF a rest j))).isEmpty
    || !(interAll (fun j => circPart (thF a rest j))).isEmpty

/-! ## The saturation loop -/

structure Config where
  rounds : Nat := 10
  jmax : Nat := 3
  pmax : Nat := 2
  lamCap : Nat := 10
  maxRS : Nat := 800
  maxIS : Nat := 800
  /-- **Semi-naive (differential) evaluation**, in the `Ops` loop only
  (`saturateO`, `FRJ/Search/Core.lean`): fire a rule instance only when
  one of its premises is a row NEW since the previous round.

  DEFAULT `false`, and every other engine ignores the field entirely —
  the legacy `saturate`/`roundStep` here, `saturateFast`, `saturateProf`.
  With `false` the `Ops` loop is what it was, candidate for candidate and
  row for row, so `paperOps` (checked against `saturate` by
  `lake exe frjvrun diff`) and `vOps` are untouched.

  With `true` the FIXPOINT is the same but the ROW ORDER need not be:
  insertion keeps `rsLeO`/`isLeO`-maximal rows, and among rows that
  subsume each other mutually the one that survives is the one offered
  first.  Semi-naive offers the same candidates in a different order, so
  a different representative of a mutual-subsumption class may be the
  one stored.  `lake exe wscreen snd` compares the two stores per cell
  and is what licenses turning this on. -/
  semiNaive : Bool := false

structure Stats where
  roundsUsed : Nat := 0
  lamCapped : Bool := false
  dbCapped : Bool := false
  rsSize : Nat := 0
  isSize : Nat := 0
  /-- Did the join ARITY cap `jmax` omit a premise family in some round?

  `famsUpTo l k` enumerates families of total size `≤ k`, so a family it
  never formed exists exactly when `l.length > k`.  This records
  `db.is.length > cfg.jmax` at the start of each round, disjunctively.

  Added 2026-08-21.  `Stats` previously recorded `lamCapped` and
  `dbCapped` but NOT the two arity caps, and `roundStep` truncates on both
  — so a caller could see every recorded cap unset while `jmax` had
  silently cut the enumeration.  Anything reading "no cap was hit" off
  this structure was reading three of the five. -/
  jmaxBinding : Bool := false
  /-- Did the promise-family arity cap `pmax` omit a family in some round?
  `db.rs.length > cfg.pmax` at the start of each round, disjunctively.

  CONSERVATIVE in `saturateFast`, which enumerates promise families over a
  FILTERED `db.rs` (the `J7` survivors), so this can report binding when
  the filtered list was in fact short enough.  That asymmetry is
  deliberate: a false "possibly binding" costs a re-run, a false "not
  binding" is the failure this field exists to prevent. -/
  pmaxBinding : Bool := false

/-- One saturation round: every rule against the current database. -/
def roundStep (G : Form) (cfg : Config) (db : DB G) :
    DB G × Nat × Bool :=
  -- single-premise regular and world-changing rules
  let newR1 := db.rs.flatMap (fun r => stepR1 G r)
  let newI1 := db.rs.flatMap (fun r => stepNotIn G r)
  let newI2 := db.is.flatMap (fun i => stepI1 G i)
  let newI3 := db.is.flatMap (fun i1 => db.is.flatMap (fun i2 => stepOrI G i1 i2))
  let impRes := db.is.map (fun i => stepImpInI G cfg.lamCap i)
  let newI4 := impRes.flatMap (·.1)
  let lamCapped := impRes.any (·.2)
  -- joins
  let fams := famsUpTo db.is cfg.jmax
  let newJB := fams.flatMap (fun (a, rest) => mkJoinBarren a rest)
  let newJF := fams.flatMap (fun (a, rest) =>
    if modalContent a rest then mkJoinF a rest else [])
  let pfams := famsUpTo db.rs cfg.pmax
  let newJP := fams.flatMap (fun (a, rest) =>
    if modalContent a rest then
      pfams.flatMap (fun (p, prest) => mkJoinP a rest p prest)
    else [])
  let (db1, n1) := insertAllR db (newR1 ++ newJB ++ newJF ++ newJP)
  let (db2, n2) := insertAllI db1 (newI1 ++ newI2 ++ newI3 ++ newI4)
  (db2, n1 + n2, lamCapped)

def saturate (G : Form) (cfg : Config) : DB G × Stats :=
  let db0 : DB G := { rs := seedsR G, is := seedsI G ++ seedsIC G }
  let rec go : Nat → DB G → Stats → DB G × Stats
    | 0, db, st => (db, { st with dbCapped := st.dbCapped })
    | fuel + 1, db, st =>
        if db.rs.length > cfg.maxRS || db.is.length > cfg.maxIS then
          (db, { st with dbCapped := true })
        else
          let (db', fresh, lc) := roundStep G cfg db
          let st' := { st with
            roundsUsed := st.roundsUsed + 1,
            lamCapped := st.lamCapped || lc,
            jmaxBinding := st.jmaxBinding || decide (db.is.length > cfg.jmax),
            pmaxBinding := st.pmaxBinding || decide (db.rs.length > cfg.pmax) }
          if fresh == 0 then (db', st')
          else go fuel db' st'
  let (db, st) := go cfg.rounds db0 {}
  (db, { st with rsSize := db.rs.length, isSize := db.is.length })

/-- The headline: is the goal derivable? -/
def derivable (G : Form) (db : DB G) : Bool :=
  db.rs.any (fun r => decide (r.rhs = G))


end FRJ.Search
