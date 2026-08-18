/-
# The FRJ◯ forward-saturation engine — W4 (T2)

Bounded forward saturation for `FRJ(G)` with the modal rules, run over a
corpus whose PLL-verdicts are known from pinned repo results.  The test:
every PLL-underivable corpus formula must become `Provable` at budget;
no PLL-derivable one may (that direction is guaranteed by the PROVED
soundness theorem plus the typing below, so the controls exercise
engine behaviour, not logic).

**Derivation-carrying.**  Every database row packs its own `FRJr`/`FRJi`
term: rule side conditions are discharged by `Decidable` instances at
insertion time, so the engine cannot misapply a rule — a faithfulness
bug is a type error, and a hit IS a derivation (`Provable G` inhabited).
This is the repo's discover-then-pin oracle pattern with the discovery
itself typed.

Caps are reported, never silent: joins are bounded in premise arity,
promise arity, and `Λ`-split width; each cap prints with the verdict.

Verdict discipline (repo standard): `pass` = expected-underivable and
derived; `flag` = expected-underivable, not reached at budget (frontier
marker — raise the budget, never drop silently); `FAIL` only ever on a
certificate.  A `control` line reports a PLL-derivable formula staying
underived, as expected.
-/
import FRJ.Calculus
import FRJ.Erase

namespace FRJSat

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
  /-- ABLATION (2026-08-18): switch off the PROMISE joins `⋈^At,p`,
  `⋈^∨,p`, `⋈^◯,p`.  These are the rules whose completeness-side supply
  is `PledgeSupply` — the last open condition on `Rm = ≤` frames.  If the
  corpus still derives without them, the promise machinery is not needed
  for these goals, and `PledgeSupply` is an artefact of the construction
  rather than of the calculus. -/
  usePromise : Bool := true
  /-- ABLATION: switch off the FALLIBLE joins `⋈^At,f`, `⋈^∨,f`. -/
  useFallible : Bool := true

structure Stats where
  roundsUsed : Nat := 0
  lamCapped : Bool := false
  dbCapped : Bool := false
  rsSize : Nat := 0
  isSize : Nat := 0

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
  let newJF := if !cfg.useFallible then [] else fams.flatMap (fun (a, rest) =>
    if modalContent a rest then mkJoinF a rest else [])
  let pfams := famsUpTo db.rs cfg.pmax
  let newJP := if !cfg.usePromise then [] else fams.flatMap (fun (a, rest) =>
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
            lamCapped := st.lamCapped || lc }
          if fresh == 0 then (db', st')
          else go fuel db' st'
  let (db, st) := go cfg.rounds db0 {}
  (db, { st with rsSize := db.rs.length, isSize := db.is.length })

/-- The headline: is the goal derivable? -/
def derivable (G : Form) (db : DB G) : Bool :=
  db.rs.any (fun r => decide (r.rhs = G))

/-! ## The corpus

Verdict provenance, per formula, in the comments.  `expectDerivable`
refers to PLL-derivability: `false` = PLL-underivable, the engine must
reach it; `true` = PLL-derivable (control), the engine cannot reach it
(soundness is a PROVED theorem and the rows are typed derivations). -/

def fp : Form := .atom "p"
def fq : Form := .atom "q"
def fw : Form := .atom "w"
def fz : Form := .atom "z"
def fr : Form := .atom "r"

structure Cell where
  name : String
  form : Form
  expectDerivable : Bool
  provenance : String

def corpus : List Cell := [
  -- PLL-underivable: the engine must derive these
  ⟨"neg_circ_bot", .imp (.circ .bot) .bot, false,
    "pinned: provable_neg_circ_bot / not_PLL_neg_circ_bot"⟩,
  ⟨"circ_imp", .imp (.circ fp) fp, false,
    "pinned: provable_circ_imp"⟩,
  ⟨"circ_peirce", .imp (.imp (.circ fp) fq) fq, false,
    "pinned: provable_circ_peirce (the ◯∉ witness)"⟩,
  ⟨"nn_circ_bot", .imp (.imp (.circ .bot) .bot) .bot, false,
    "the Ax^I◯ witness: was the standing flag (the ◯∉ cycle); the bare-final-world seed unlocks it; pinned hand cell provable_nn_circ_bot"⟩,
  ⟨"nnn_circ_bot", .imp (.imp (.imp (.circ .bot) .bot) .bot) .bot, false,
    "≡ ¬◯⊥ intuitionistically; the deeper-nesting twin"⟩,
  ⟨"circ_or_split", .imp (.circ (.or fp fq)) (.or (.circ fp) (.circ fq)), false,
    "Screen 2 (FRJ/Modal.lean): branch refutes it"⟩,
  -- W4 pledge-stress cells (2026-08-17): ◯-goals with compound bodies,
  -- probing the pledged-visit shapes BEFORE the minMod build is scoped
  ⟨"circ_circ_imp", .circ (.imp (.circ fp) fp), false,
    "pledge stress: ◯-goal, ⊃-body with MODAL antecedent; refuter v0 has the (◯p⊃p)-witness strictly above"⟩,
  ⟨"neg_circ_circ_imp", .imp (.circ (.imp (.circ fp) fp)) .bot, false,
    "pledge stress: the same body through the irregular route (Υ ∋ ◯(◯p⊃p))"⟩,
  ⟨"lob_circ", .imp (.circ (.imp (.circ fp) fp)) (.circ fp), false,
    "pledge stress: promise join must absorb ◯p while pledging p"⟩,
  ⟨"circ_and_pledge", .circ (.and fp fq), false,
    "pledge stress: ∧-body; one-world refuter"⟩,
  ⟨"peirce_compound", .imp (.imp (.circ (.imp fq fp)) fp) fp, false,
    "corner probe: Y-cell for ◯(q⊃p) inside a Peirce shell — the t0-◯Z demand with compound body"⟩,
  ⟨"circ_ante_circ_goal", .imp (.circ fq) (.circ (.imp (.circ fp) fp)), false,
    "corner probe: modal-left signature + ◯-goal with modal-antecedent body — the pledged ⊃-float shape"⟩,
  ⟨"corner_disj_atom", .imp (.imp (.circ (.imp fq fp)) fw) (.or fw fq), false,
    "§9 stratum: modal-antecedent imp in sfL + atomic disjunctive goal"⟩,
  ⟨"corner_disj_imp", .imp (.imp (.circ (.imp fq fp)) fw) (.or fw (.imp fq fp)), false,
    "§9 stratum: modal-antecedent imp + the modal body itself as goal disjunct"⟩,
  ⟨"corner_disj_circ", .imp (.imp (.circ fz) fw) (.or fw (.circ fz)), false,
    "§9 stratum: ◯-disjunct or-cell + Υ-demand for the same ◯z — the I/R mutual-demand shape"⟩,
  ⟨"corner_poisoned_axic", .imp (.imp (.or fp (.imp fp fq)) fw) (.or fw (.circ fz)), false,
    "§9 CRITICAL: A := p∨(p⊃q) is classForce-true at ∅ but unforced, so A⊃w escapes every vacZone; sole ◯z-candidate is cone-trivial — all known suppliers of the irregular ◯z-cell fail"⟩,
  ⟨"corner_poisoned_ups", .imp (.imp (.or fp (.imp fp fq)) fw) (.imp (.imp (.circ fz) fw) (.or fw fz)), false,
    "§9 CRITICAL twin: the poisoned antecedent + a Υ-demand (◯z⊃w in sfL) instead of an or-disjunct"⟩,
  ⟨"corner_residue", .imp (.imp (.atom "x") fz) (.imp (.imp (.circ fz) fw) (.or fw (.circ fz))), false,
    "§11 residue probe: non-maximal corner world (a < b, b forces z) with the consequent-z implication x⊃z in Λ*_a — the shape where Clo-grounding of the syn-route fails"⟩,
  ⟨"corner_residue_poisoned", .imp (.imp (.or fp (.imp fp fq)) fz) (.imp (.imp (.circ fz) fw) (.or fw (.circ fz))), false,
    "§11 residue probe, poisoned: antecedent A=p∨(p⊃q) classically true at ∅, consequent z — blocks BOTH the vacZone and the Clo-grounding routes at once"⟩,
  ⟨"corner_selfloop", .imp (.imp (.circ fz) fz) (.or fw (.circ fz)), false,
    "§11 self-loop probe: (◯z⊃z) ∈ Λ* with ungroundable consequent z — the retained imp re-demands its own ◯z-cell inside the supply row"⟩,
  ⟨"corner_taut_body", .imp (.imp (.circ (.or fq (.imp fq fp))) (.or fp (.imp fp fq))) (.or fw (.circ (.or fq (.imp fq fp)))), false,
    "§11 killer attempt: tautologous ◯-body Z'=q∨(q⊃p) (blocks every-ats axIC) with tautologous-but-unforced consequent W=p∨(p⊃q); 3-world model a<b{p,q},c{p}"⟩,
  ⟨"nn_circ_circ_bot", .imp (.imp (.circ (.circ .bot)) .bot) .bot, false,
    "pledge stress: nested ◯-body through the irregular route (¬¬◯◯⊥)"⟩,
  ⟨"excluded_middle", .or fp (.imp fp .bot), false,
    "IPL classic; two-world chain refutes"⟩,
  ⟨"circ_and_goal", .circ (.and fp fq), false,
    "one infallible world with p false refutes"⟩,
  ⟨"circ_imp_goal", .circ (.imp fp fq), false,
    "one world forcing p, refuting q (the compound-◯ family)"⟩,
  ⟨"circ_mono_atoms", .imp (.circ fp) (.circ fq), false,
    "one world forcing p, refuting q"⟩,
  ⟨"godel_dummett", .or (.imp fp fq) (.imp fq fp), false,
    "IPL classic; branching model refutes"⟩,
  -- PLL-derivable controls: the engine cannot reach these
  ⟨"unit_inst", .imp fp (.circ fp), true,
    "the unit A ⊃ ◯A"⟩,
  ⟨"mult_inst", .imp (.circ (.circ fp)) (.circ fp), true,
    "the multiplication ◯◯A ⊃ ◯A"⟩,
  ⟨"circ_taut", .circ (.imp fp fp), true,
    "control for the modal join: ◯(p⊃p) is PLL-derivable (unit), so no ⋈^◯ instance may reach it"⟩,
  ⟨"top", .imp .bot .bot, true,
    "⊤"⟩,
  ⟨"g4ill_blocker", .imp (.circ (.imp (.imp (.circ fp) fr) (.circ fp)))
      (.imp (.imp (.circ fp) fr) fr), true,
    "PLL-derivable (the sequent G4iLL misses; g4ill campaign, pinned)"⟩
]


/-! ## Erasure-transfer attack (2026-08-17)

Statement under attack, BEFORE any proof build (standing mandate):

    (E)    Provable (erase G) → Provable G

Cells: ◯-decorations of intuitionistic refuters whose erasures are
IPC-underivable — several classically VALID, hence beyond the discrete/
classical-shadow corner.  Each cell also records its hand-checked
TRANSPARENT countermodel (`Rm = id`), so (E) failing at a derivable
erasure would exhibit FRJ◯ incompleteness on a transparent model.

Verdicts: `transfer:pass` (both derived); `transfer:vacuous*` (erasure
not derived — budget, or engine-certain mis-scoped cell);
`transfer:flag` (erasure derived, G not reached, caps hit);
`transfer:FAIL-CANDIDATE` (erasure derived, G-saturation COMPLETE below
every cap with no derivation — an engine-certain counterexample to (E)
modulo engine faithfulness: minimise and escalate to kernel).

"Engine-certain" is relative to the COMPLETENESS of the enumeration
layer, not only its faithfulness: a rule-closure fixpoint below every
cap says nothing when a rule's instances are under-enumerated.  The
`dn_circ_and` erasure showed exactly that (2026-08-17): reported
`vacuous-CERTAIN` at both bounds while `FRJ.completeness` derives it —
the `⊃∉` zone enumeration was the gap (`thetaCandidates`).  Any future
`vacuous-CERTAIN`/`FAIL-CANDIDATE` on a cell with a known countermodel
is to be read the same way: check the enumeration before the
statement. -/

structure EPair where
  name : String
  form : Form
  note : String

def ePairs : List EPair := [
  ⟨"dn_circ", .imp (.imp (.imp (.circ fp) .bot) .bot) (.circ fp),
    "¬¬◯p⊃◯p; erase = ¬¬p⊃p; 2-chain r<b{p} transparent refuter"⟩,
  ⟨"peirce_circ", .imp (.imp (.imp (.circ fp) (.circ fq)) (.circ fp)) (.circ fp),
    "◯-Peirce; erase classically VALID; 2-chain r<b{p} refutes"⟩,
  ⟨"wem_circ", .or (.imp (.circ fp) .bot) (.imp (.imp (.circ fp) .bot) .bot),
    "¬◯p∨¬¬◯p; erase = weak EM, classically VALID; branch r<b1{p},b2{}"⟩,
  ⟨"dummett_circ", .or (.imp (.circ fp) (.circ fq)) (.imp (.circ fq) (.circ fp)),
    "◯-Dummett; erase classically VALID; branch r<b1{p},b2{q}"⟩,
  ⟨"dn_mixed", .imp (.imp (.imp fp .bot) .bot) (.circ fp),
    "¬¬p⊃◯p; decoration in consequent only; 2-chain r<b{p}"⟩,
  ⟨"orshift_circ", .or (.circ fp) (.imp (.circ fp) fq),
    "◯p∨(◯p⊃q); erase classically VALID; 2-chain r<b{p}, q nowhere"⟩,
  ⟨"dn_circ_and", .imp (.imp (.imp (.circ (.and fp fq)) .bot) .bot) (.circ (.and fp fq)),
    "compound ◯-body A=p∧q: the zone-shift stress; 2-chain r<b{p,q}"⟩,
  ⟨"dn_circ_nested", .imp (.imp (.imp (.circ (.circ fp)) .bot) .bot) (.circ (.circ fp)),
    "nested ◯◯-decoration; erase = ¬¬p⊃p; 2-chain r<b{p}"⟩
]

def runEPair (cfg : Config) (c : EPair) : IO Unit := do
  let e := FRJ.erase c.form
  let (dbE, stE) := saturate e cfg
  let hitE := derivable e dbE
  let (dbG, stG) := saturate c.form cfg
  let hitG := derivable c.form dbG
  let fixE := !stE.lamCapped && !stE.dbCapped && stE.roundsUsed < cfg.rounds
  let fixG := !stG.lamCapped && !stG.dbCapped && stG.roundsUsed < cfg.rounds
  let v :=
    if !hitE then
      if fixE then "transfer:vacuous-CERTAIN (erasure underivable — cell mis-scoped?)"
      else "transfer:vacuous (erasure not reached at budget — raise)"
    else if hitG then "transfer:pass"
    else if fixG then "transfer:FAIL-CANDIDATE (G-saturation complete, no derivation!)"
    else "transfer:flag (G not reached at budget — raise)"
  IO.println s!"{c.name}: {v} | erase[hit={hitE} r={stE.roundsUsed} RS={stE.rsSize} IS={stE.isSize}{if stE.lamCapped then " Λcap" else ""}{if stE.dbCapped then " DBcap" else ""}] G[hit={hitG} r={stG.roundsUsed} RS={stG.rsSize} IS={stG.isSize}{if stG.lamCapped then " Λcap" else ""}{if stG.dbCapped then " DBcap" else ""}] | {c.note}"
  (← IO.getStdout).flush

def verdict (c : Cell) (hit : Bool) : String :=
  match c.expectDerivable, hit with
  | false, true => "pass"
  | false, false => "flag (not reached at budget — raise budget)"
  | true, false => "control-ok"
  | true, true => "FAIL (typed derivation of a PLL-derivable formula!)"

def runCell (cfg : Config) (c : Cell) : IO Unit := do
  let (db, st) := saturate c.form cfg
  let hit := derivable c.form db
  let caps :=
    (if st.lamCapped then " [Λ-cap]" else "") ++
    (if st.dbCapped then " [DB-cap]" else "")
  IO.println s!"{c.name}: {verdict c hit} | rounds={st.roundsUsed} RS={st.rsSize} IS={st.isSize}{caps} | {c.provenance}"
  (← IO.getStdout).flush

def main : IO Unit := do
  let cfg : Config := {}
  IO.println s!"FRJ◯ saturation — jmax={cfg.jmax} pmax={cfg.pmax} rounds={cfg.rounds} lamCap={cfg.lamCap} (subsumption: RS by tag-and-context dominance, IS by second-zone dominance; ⊃∉ enumerates the maximal admissible zones, so every consumer is monotone)"
  for c in corpus do
    runCell cfg c
  let cfgHigh : Config := { rounds := 16, jmax := 4, pmax := 3, lamCap := 16, maxRS := 1500, maxIS := 1500 }
  IO.println s!"-- raised-budget re-run (jmax={cfgHigh.jmax} pmax={cfgHigh.pmax} lamCap={cfgHigh.lamCap}) --"
  for c in corpus do
    if c.name == "corner_poisoned_ups" || c.name == "corner_residue" || c.name == "corner_residue_poisoned" || c.name == "corner_selfloop" || c.name == "corner_taut_body" then
      runCell cfgHigh c
  IO.println s!"-- ABLATION: are the PROMISE joins ever needed? (PledgeSupply screen) --"
  let cfgNoP : Config := { usePromise := false }
  let cfgNoPF : Config := { usePromise := false, useFallible := false }
  let cfgHiNoP : Config := { cfgHigh with usePromise := false }
  let mut base : List (String × Bool) := []
  for c in corpus do
    base := base ++ [(c.name, derivable c.form (saturate c.form cfg).1)]
  let runAbl (label : String) (k : Config) : IO Unit := do
    let mut lost : List String := []
    let mut hits := 0
    for c in corpus do
      let hit := derivable c.form (saturate c.form k).1
      if hit then hits := hits + 1
      let wasHit := (base.find? (fun q => q.1 == c.name)).map (·.2) |>.getD false
      if wasHit && !hit then lost := lost ++ [c.name]
    IO.println s!"{label}: derived {hits}/{corpus.length}; lost vs baseline: {if lost.isEmpty then "NONE" else String.intercalate ", " lost}"
    (← IO.getStdout).flush
  runAbl "no promise joins            " cfgNoP
  runAbl "no promise, no fallible     " cfgNoPF
  runAbl "no promise, raised budget   " cfgHiNoP
  IO.println s!"-- erasure-transfer attack (E): Provable (erase G) → Provable G --"
  for c in ePairs do
    runEPair cfg c
  IO.println s!"-- erasure re-run at raised bounds (fixpoint is jmax/pmax-relative) --"
  for c in ePairs do
    if c.name == "dn_circ_and" then
      runEPair cfgHigh c
  IO.println "done."

end FRJSat

def main : IO Unit := FRJSat.main
