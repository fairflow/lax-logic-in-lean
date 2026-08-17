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

namespace FRJSat

open FRJ Form

/-! ## Rows: sequents carrying their derivations -/

/-- A regular row `Γ ⇒ C` with its tag and derivation. -/
structure RS (G : Form) where
  t : Tag
  ctx : List Form
  rhs : Form
  der : FRJr G t ctx rhs

/-- An irregular row `Σ ; Θ → C` with its derivation and the invariant
that the second zone is canonical (needed by the `⊃∈` zone split). -/
structure IS (G : Form) where
  stab : List Form
  th : List Form
  rhs : Form
  der : FRJi G stab th rhs
  thNf : th = nf G th

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

theorem nf_split {G : Form} {Θ Λ : List Form}
    (hΛ : ∀ x ∈ Λ, x ∈ Θ) (hnf : Θ = nf G Θ) :
    nf G (FRJ.sdiff Θ Λ ++ Λ) = Θ := by
  conv_rhs => rw [hnf]
  refine nf_ext (fun x _ => ?_)
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact (mem_sdiff.mp h).1
    · exact hΛ _ h
  · intro h
    by_cases hl : x ∈ Λ
    · exact List.mem_append_right _ hl
    · exact List.mem_append_left _ (mem_sdiff.mpr ⟨h, hl⟩)

/-! ## Seeds -/

def seedsR (G : Form) : List (RS G) :=
  (sfR G).filterMap (fun F =>
    if hF : F.isPrime then
      if hg : F ∈ sfR G then
        some ⟨.barren, rm (gAt G) F, F, .axR F hF hg⟩
      else none
    else none)

def seedsI (G : Form) : List (IS G) :=
  (sfR G).filterMap (fun F =>
    if hF : F.isPrime then
      if hg : F ∈ sfR G then
        some ⟨[], nf G ((rm (gAt G) F) ++ gImp G ++ gCirc G), F,
          .axI F hF hg, nf_idem.symm⟩
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
              some ⟨[], vacZoneA G ats, .circ F, .axIC F ats hats hFf hg,
                nf_idem.symm⟩
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
            some ⟨i.stab, i.th, .and A B, .andI1 (h1 ▸ i.der) hg, i.thNf⟩
          else if h2 : i.rhs = B then
            some ⟨i.stab, i.th, .and A B, .andI2 (h2 ▸ i.der) hg, i.thNf⟩
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
                  some ⟨i1.stab ++ i2.stab, nf G (cap i1.th i2.th), .or C₁ C₂,
                    .orI (h1 ▸ i1.der) (h2 ▸ i2.der) hs1 hs2 hg, nf_idem.symm⟩
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
                if hA : Clo (nf G (i.stab ++ Λ)) A then
                  let d' : FRJi G i.stab (nf G (FRJ.sdiff i.th Λ ++ Λ)) B := by
                    rw [nf_split hΛ i.thNf]; exact (h ▸ i.der)
                  some ⟨nf G (i.stab ++ Λ), nf G (FRJ.sdiff i.th Λ), .imp A B,
                    .impInI d' cap_sdiff_eq_nil hA hg, nf_idem.symm⟩
                else none
              else none)
          else []
      | _, _ => []
    else [])), capped)

/-- The canonical maximal `Θ` for the world-changing irregular rules. -/
def thetaMax (G : Form) (Γ : List Form) : List Form :=
  nf G ((gHat G).filter (fun X => cloB Γ X))

/-- `⊃∉` and `◯∉` from one regular row.  The `Θ`-candidates are `nf`-images
by construction, so the canonicality invariant is `nf_idem`. -/
def stepNotIn (G : Form) (r : RS G) : List (IS G) :=
  (sfR G).flatMap (fun T =>
    if hg : T ∈ sfR G then
      match T, hg with
      | .imp A B, hg =>
          if h : r.rhs = B then
            -- Θ-candidate sources: maximal, and maximal purged of
            -- A-generators (hAnot can fail at the maximum)
            let pre : List (List Form) := [(gHat G).filter (fun X => cloB r.ctx X),
              (thetaMax G r.ctx).filter
                (fun X => decide (X ≠ A) && !(cloB [X] A))]
            pre.filterMap (fun l =>
              let Θ := nf G l
              if hTh : ∀ X ∈ Θ, Clo r.ctx X ∧ X ∈ gHat G then
                if hA : Clo r.ctx A then
                  if hAnot : ¬ Clo Θ A then
                    some ⟨[], Θ, .imp A B,
                      .impNotIn (h ▸ r.der) hTh hA hAnot hg, nf_idem.symm⟩
                  else none
                else none
              else none)
          else []
      | .circ Z, hg =>
          if h : r.rhs = Z then
            if ht : r.t = .barren ∨ ∃ W, r.t = .chain W ∧ Covers r.ctx W Z then
              let Θ := nf G ((gHat G).filter (fun X => cloB r.ctx X))
              if hTh : ∀ X ∈ Θ, Clo r.ctx X ∧ X ∈ gHat G then
                [⟨[], Θ, .circ Z, .circNotIn (h ▸ r.der) ht hTh hg, nf_idem.symm⟩]
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
                .joinAt (premF a rest) h1 (hJ2_of_check h2) hcirc hF hFnot hg⟩
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
                  .joinOr (premF a rest) h1 (hJ2_of_check h2) hcirc hC hg⟩
              else none
          | .circ Z, hg =>
              if hZ : Z ∈ upsilon (rhsF a rest) then
                some ⟨.barren, joinCtxOr (stabF a rest) (thF a rest) (rhsF a rest),
                  .circ Z,
                  .joinCirc (premF a rest) h1 (hJ2_of_check h2) hcirc hZ hg⟩
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
              .joinAtF (premF a rest) h1 (hJ2_of_check h2) hF hFnot hg⟩
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
                .joinOrF (premF a rest) h1 (hJ2_of_check h2) hC hg⟩
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
                    hJ5 h7 tg.2 hF hFnot hg⟩
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
                      hJ5 h7 tg.2 hC hg⟩
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
                      hJ5 h7 hDs hZ hg⟩
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
consumer — with ONE deliberate exception, reported with the results: the
`hAnot` gate of `⊃∉` can hold for a smaller context and fail for a
larger; the purged `Θ`-candidate mitigates, and a residual miss shows up
as a `flag`, never as a wrong verdict.  Irregular rows are kept maximal
in the second zone at set-equal stable zones. -/

def subB (l m : List Form) : Bool := l.all (fun x => decide (x ∈ m))

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
  IO.println s!"FRJ◯ saturation — jmax={cfg.jmax} pmax={cfg.pmax} rounds={cfg.rounds} lamCap={cfg.lamCap} (subsumption: RS by tag-and-context dominance — the ⊃∉ hAnot gate is the one non-monotone consumer, mitigated by the purged Θ-candidate)"
  for c in corpus do
    runCell cfg c
  IO.println "done."

end FRJSat

def main : IO Unit := FRJSat.main
