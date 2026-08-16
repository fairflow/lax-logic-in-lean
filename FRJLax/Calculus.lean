/-
# FRJ◯ — the calculus, `◯`-free rules

Section 3 and Figure 1 of Fiorentini–Ferrari (ACM TOCL 21(3), Article 22,
2020), transcribed rule by rule.  **The `◯`-free rules only**: the modal
rules are W5, they are new mathematics, and their statements are
Matthew's.  `◯` is present in the language (`FRJLax/Core.lean`) but no
rule below mentions it.

Two properties this file is written to have, both checkable by
inspection:

* **Every index in a constructor's return type is a variable or a
  constructor form** (McBride's no-green-slime rule).  Every computed
  context enters through the membership-equality relation `≐` as a
  hypothesis, never as an index.  Compare the corresponding constructors
  of `FRJ/Calculus.lean`, whose return types read
  `FRJr G ((gAt G).erase F) F` and
  `FRJi G (St₁ ∪ St₂) (Th₁ ∩ Th₂) (C₁ ∨ C₂)`; that is the concrete reason
  its `Extract.lean` fights the kernel.
* **Every side condition is decidable**, so a rule application can be
  discharged by `decide` and the W6 searcher has something to compute.
  `Clo` is decided by `cloB`, `≐` and `⊆` by `decEqv`/`decSubset`, and
  (J2) is stated through the `Bool` test `suppB` rather than as a
  quantifier over all formulas.

The judgments are `Type`-valued: a refutation is data, not an existence
claim.  The completeness construction of W4 has to *return* one.

NAMING.  `Σ` is reserved notation in Lean (sigma types), so the paper's
`Σ` is written `St` — "stable", the paper's own word for that zone — and
its `Θ` is written `Th` in binder positions for symmetry.  `Γ`, `Λ`, `Υ`
keep the paper's letters.

Imports: `FRJLax.Core` and nothing else.
-/
import FRJLax.Core

namespace FRJLax

/-! ## Sequents

"There are two types of `FRJ(G)`-sequents, we call *regular* (arrow `⇒`)
and *irregular* (arrow `→`):

* regular sequents have the form `Γ ⇒ C`, where `Γ ⊆ Ĝ` and `C ∈ Sf^R(G)`;
* irregular sequents have the form `Σ ; Θ → C`, where `Σ ∪ Θ ⊆ Ĝ` and
  `C ∈ Sf^R(G)`."

"Given a sequent `σ`, the set `Lhs(σ)` of *left* formulas of `σ` and the
*right* formula of `σ` are defined as follows: `Lhs(σ) = Γ` if `σ` is
regular, `Σ ∪ Θ` if `σ` is irregular; `Rhs(σ) = C`."

DIVERGENCE (the paper's constraints are a lemma, not a type).  The paper
defines the sequent *set* by the constraints `Γ ⊆ Ĝ`, `Σ ∪ Θ ⊆ Ĝ`,
`C ∈ Sf^R(G)`.  The figure's blanket condition `Rhs(σ) ∈ Sf^R(G)` is
carried as a field `hg` on every constructor; the context constraints are
not indices but propagate from the axioms, and are the well-formedness
lemma of W3.  This is what keeps the inductive family free of proof
indices.  (The constraints exist to give the Finite Rule Property, needed
for refutation-search, not for the two theorems in scope.) -/

/-- A sequent, as data.  Used by `↦` in W3; the judgments below are
indexed by the components rather than by a sequent, so that the indices
stay variables. -/
inductive Sequent where
  | reg : List Form → Form → Sequent
  | irr : List Form → List Form → Form → Sequent
  deriving DecidableEq, Repr

namespace Sequent

/-- `Lhs(σ)`. -/
def lhs : Sequent → List Form
  | .reg Γ _ => Γ
  | .irr St Th _ => St ++ Th

/-- `Rhs(σ)`. -/
def rhs : Sequent → Form
  | .reg _ C => C
  | .irr _ _ C => C

/-- Whether `σ` is regular.  The paper's `tp(σ)`, used by the weight
function; here it just names the two arrows. -/
def isReg : Sequent → Bool
  | .reg _ _ => true
  | .irr _ _ _ => false

end Sequent

/-! ## The premises of a join rule

"The *join* rules `⋈^At` and `⋈^∨` apply to `n ≥ 1` irregular sequents
`σ₁ = Σ₁;Θ₁ → A₁, …, σₙ = Σₙ;Θₙ → Aₙ` and yield a regular sequent
`σ = Γ ⇒ C`; this is the only way to obtain a regular sequent from
irregular ones."

The `n ≥ 1` is carried structurally, by a premise vector whose index list
is nonempty by construction (`Prems.one` starts it, `Prems.cons` extends
it).  This avoids a `Fin (n+1)`-indexed family and any need for a
decidable quantifier over `Fin`; the zone operations are then ordinary
list operations, and induction over the premises is structural. -/

/-- One premise of a join: its stable set `Σ_j`, its `Θ_j`, and its right
formula `A_j`. -/
structure Prem where
  /-- `Σ_j`, the stable set of the premise. -/
  stab : List Form
  /-- `Θ_j`. -/
  theta : List Form
  /-- `A_j`, the right formula of the premise. -/
  goal : Form
  deriving DecidableEq, Repr

/-- Intersection of a list of lists.  Only ever applied to the nonempty
index list of a `Prems`; the empty case is a junk value, and
`mem_interAll` carries the nonemptiness hypothesis. -/
def interAll : List (List Form) → List Form
  | [] => []
  | [x] => x
  | x :: y :: xs => cap x (interAll (y :: xs))

theorem mem_interAll : ∀ {ls : List (List Form)}, ls ≠ [] → ∀ {y : Form},
    (y ∈ interAll ls ↔ ∀ l ∈ ls, y ∈ l) := by
  intro ls
  induction ls with
  | nil => intro h; exact absurd rfl h
  | cons x xs ih =>
      cases xs with
      | nil => intro _ y; simp [interAll]
      | cons z zs =>
          intro _ y
          have ihz := ih (by simp) (y := y)
          show y ∈ cap x (interAll (z :: zs)) ↔ _
          constructor
          · intro h l hl
            rcases List.mem_cons.mp hl with rfl | hl'
            · exact (mem_cap.mp h).1
            · exact ihz.mp (mem_cap.mp h).2 l hl'
          · intro h
            exact mem_cap.mpr ⟨h x (by simp),
              ihz.mpr (fun l hl => h l (List.mem_cons_of_mem _ hl))⟩

/-! ### The zones

"Let `Σ^At = ⋃_j Σ^At_j`, `Σ^⊃ = ⋃_j Σ^⊃_j`, `Θ^At = ⋂_j Θ^At_j`,
`Θ^⊃ = (⋂_j Θ^⊃_j)/Υ`, where `Υ = {A₁, …, Aₙ}`", and

"given a set of `⊃`-formulas `Γ^⊃` and a set of formulas `Υ`, let
`Γ^⊃/Υ = { Y ⊃ Z ∈ Γ^⊃ | Y ∈ Υ }`; we call `Γ^⊃/Υ` the *restriction* of
`Γ^⊃` to `Υ`."

Factored out once here, so that the `↦` relation of W3 refers to the same
functions as the rules and cannot drift from them. -/

/-- `Υ = {A₁, …, Aₙ}`, the right formulas of the premises. -/
def ups (l : List Prem) : List Form := l.map Prem.goal

/-- `Σ^At = ⋃_j Σ^At_j`. -/
def sigAt (l : List Prem) : List Form := l.flatMap (fun p => atPart p.stab)

/-- `Σ^⊃ = ⋃_j Σ^⊃_j`. -/
def sigImp (l : List Prem) : List Form := l.flatMap (fun p => impPart p.stab)

/-- `Θ^At = ⋂_j Θ^At_j`. -/
def thAt (l : List Prem) : List Form := interAll (l.map (fun p => atPart p.theta))

/-- The membership test of the restriction operator. -/
def inRestrict (Υ : List Form) : Form → Bool
  | .imp Y _ => decide (Y ∈ Υ)
  | _ => false

/-- `Γ^⊃/Υ = { Y ⊃ Z ∈ Γ^⊃ | Y ∈ Υ }`. -/
def restrict (X Υ : List Form) : List Form := X.filter (inRestrict Υ)

theorem mem_restrict {X Υ : List Form} {Y Z : Form} :
    Form.imp Y Z ∈ restrict X Υ ↔ (Form.imp Y Z ∈ X ∧ Y ∈ Υ) := by
  simp [restrict, List.mem_filter, inRestrict]

theorem restrict_subset {X Υ : List Form} : restrict X Υ ⊆ X :=
  fun _ h => (List.mem_filter.mp h).1

/-- `Θ^⊃ = (⋂_j Θ^⊃_j)/Υ`. -/
def thImp (l : List Prem) : List Form :=
  restrict (interAll (l.map (fun p => impPart p.theta))) (ups l)

/-- The conclusion context of `⋈^At`: `Σ^At, Θ^At \ {F}, Σ^⊃, Θ^⊃`. -/
def joinCtxAt (l : List Prem) (F : Form) : List Form :=
  sigAt l ++ rm (thAt l) F ++ sigImp l ++ thImp l

/-- The conclusion context of `⋈^∨`: `Σ^At, Θ^At, Σ^⊃, Θ^⊃`. -/
def joinCtxOr (l : List Prem) : List Form :=
  sigAt l ++ thAt l ++ sigImp l ++ thImp l

/-- The support test of side condition (J2): "`Y ⊃ Z ∈ Σ^⊃` implies
`Y ∈ Υ`".  A `Bool`, so that (J2) is a decidable field; formulas that are
not implications cannot occur in `Σ^⊃` and the test is vacuous on them. -/
def suppB (Υ : List Form) : Form → Bool
  | .imp Y _ => decide (Y ∈ Υ)
  | _ => true

/-- `Σ^◯ = ⋃_j Σ^◯_j`. -/
def sigCirc (l : List Prem) : List Form := l.flatMap (fun p => circPart p.stab)

/-- `Θ^◯ = ⋂_j Θ^◯_j`. -/
def thCirc (l : List Prem) : List Form := interAll (l.map (fun p => circPart p.theta))

/-- The `◯`-formulas a promise join keeps in its conclusion. -/
def joinCirc (l : List Prem) : List Form := sigCirc l ++ thCirc l

/-- The argument of a `◯`-formula; the identity elsewhere.  Used to state
the modal witness condition (J5) without quantifying over all formulas. -/
def circArg : Form → Form
  | .circ Y => Y
  | X => X

/-- The conclusion context of a promise `⋈^At`. -/
def joinCtxAtP (l : List Prem) (F : Form) : List Form :=
  joinCtxAt l F ++ joinCirc l

/-- The conclusion context of a promise `⋈^∨`. -/
def joinCtxOrP (l : List Prem) : List Form :=
  joinCtxOr l ++ joinCirc l

/-- (J5): every `◯Y` kept in the conclusion has its argument forced at the
promise world — `Y ∈ Cl(Δ)`.  This is the witness that `Model.circ_intro`
consumes. -/
def J5 (l : List Prem) (Δ : List Form) : Prop :=
  ∀ X ∈ joinCirc l, Clo Δ (circArg X)

/-- (J6): every `◯Y` kept in the conclusion is itself forced at the
promise world.  This is the "strictly above" half of `circ_intro` at the
promise world; at the irregular premises' worlds it comes from the same
closure argument that (P2) uses for `⊃`. -/
def J6 (l : List Prem) (Δ : List Form) : Prop := ∀ X ∈ joinCirc l, Clo Δ X

/-- (J7): the conclusion context is forced at the promise world, which is
above the new world.  Monotonicity. -/
def J7 (Γ Δ : List Form) : Prop := ∀ X ∈ Γ, Clo Δ X

instance decJ5 (l : List Prem) (Δ : List Form) : Decidable (J5 l Δ) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance decJ6 (l : List Prem) (Δ : List Form) : Decidable (J6 l Δ) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance decJ7 (Γ Δ : List Form) : Decidable (J7 Γ Δ) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- (J1): "`Σ_i ⊆ Σ_j ∪ Θ_j` for every `i ≠ j`".  Stated over all pairs,
including `i = j`, where it holds trivially. -/
def J1 (l : List Prem) : Prop := ∀ p ∈ l, ∀ q ∈ l, p.stab ⊆ q.stab ++ q.theta

/-- (J2): "`Y ⊃ Z ∈ Σ^⊃` implies `Y ∈ Υ`". -/
def J2 (l : List Prem) : Prop := ∀ X ∈ sigImp l, suppB (ups l) X = true

instance decJ1 (l : List Prem) : Decidable (J1 l) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

instance decJ2 (l : List Prem) : Decidable (J2 l) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ## The calculus

Figure 1, every rule, with every side condition present as a field.  The
figure's blanket condition — "in the conclusion `σ` of each rule,
`Rhs(σ) ∈ Sf^R(G)`" — is the field `hg`. -/

mutual

/-- Refutations of regular sequents `Γ ⇒ C`.

The `Bool` index is **barrenness**: `true` says the world this refutation
builds has no proper modal successor, so that `◯Z` fails there as soon as
`Z` does (`Model.not_force_circ_of_no_promise`).  A join that declares a
promise sets it to `false`; every other rule passes it through, because
every other rule builds no new world. -/
inductive FRJr (G : Form) : Bool → List Form → Form → Type
  /-- `Ax^⇒`: `⊢ Ĝ_at \ {F} ⇒ F`, `F ∈ Prime`. -/
  | axR {Γ F} (hF : F.isPrime = true) (hg : F ∈ sfR G)
      (hΓ : Γ ≐ rm (gAt G) F) : FRJr G true Γ F
  /-- `∧` regular, `k = 1`. -/
  | andR₁ {b Γ A₁ A₂} (d : FRJr G b Γ A₁) (hg : Form.and A₁ A₂ ∈ sfR G) :
      FRJr G b Γ (.and A₁ A₂)
  /-- `∧` regular, `k = 2`. -/
  | andR₂ {b Γ A₁ A₂} (d : FRJr G b Γ A₂) (hg : Form.and A₁ A₂ ∈ sfR G) :
      FRJr G b Γ (.and A₁ A₂)
  /-- `⊃∈` regular, side condition `A ∈ Cl(Γ)`. -/
  | impInR {b Γ A B} (d : FRJr G b Γ B) (hA : Clo Γ A)
      (hg : Form.imp A B ∈ sfR G) : FRJr G b Γ (.imp A B)
  /-- `⋈^At`, with (J1), (J2) and (J3) `F ∈ Prime \ Σ^At`. -/
  | joinAt {l Γ F} (ps : Prems G l) (j1 : J1 l) (j2 : J2 l)
      (hF : F.isPrime = true) (j3 : F ∉ sigAt l) (hg : F ∈ sfR G)
      (hc : joinCirc l = []) (hΓ : Γ ≐ joinCtxAt l F) : FRJr G true Γ F
  /-- `⋈^∨`, with (J1), (J2) and (J4) `{C₁,C₂} ⊆ Υ`. -/
  | joinOr {l Γ C₁ C₂} (ps : Prems G l) (j1 : J1 l) (j2 : J2 l)
      (j4₁ : C₁ ∈ ups l) (j4₂ : C₂ ∈ ups l) (hg : Form.or C₁ C₂ ∈ sfR G)
      (hc : joinCirc l = []) (hΓ : Γ ≐ joinCtxOr l) : FRJr G true Γ (.or C₁ C₂)
  /-- `◯∈`: from `Γ ⇒ Z` at a BARREN world infer `Γ ⇒ ◯Z`.  Justified by
  `Model.not_force_circ_of_no_promise`: a world with no proper modal
  successor refutes `◯Z` as soon as it refutes `Z`. -/
  | circIn {Γ Z} (d : FRJr G true Γ Z) (hg : Form.circ Z ∈ sfR G) :
      FRJr G true Γ (.circ Z)
  /-- `⋈^At,p`: a `⋈^At` carrying a PROMISE PREMISE `Δ ⇒ D`, whose world
  becomes the modal successor of the new world.  (J5) supplies the modal
  witness, (J6) and (J7) the "strictly above" half; justified by
  `Model.circ_intro`.  The conclusion's world is not barren. -/
  | joinAtP {l Γ F Δ D bp} (ps : Prems G l) (pr : FRJr G bp Δ D)
      (j1 : J1 l) (j2 : J2 l) (hF : F.isPrime = true) (j3 : F ∉ sigAt l)
      (j5 : J5 l Δ) (j6 : J6 l Δ) (j7 : J7 Γ Δ) (hg : F ∈ sfR G)
      (hΓ : Γ ≐ joinCtxAtP l F) : FRJr G false Γ F
  /-- `⋈^At,⊥`: a `⋈^At` whose modal successor is a FALLIBLE world.

  A fallible world forces every formula, so no (J5)/(J6)/(J7) is needed —
  but by `Model.circ_of_fallible_cone` the witness must cover the whole
  cone above the new world, so the fallible world is a maximum of the
  model, modally accessible from every world.  Consequently NO world of
  such a model is barren, which is why the conclusion's flag is `false`
  and `◯∈` can never be applied above it. -/
  | joinAtF {l Γ F} (ps : Prems G l) (j1 : J1 l) (j2 : J2 l)
      (hF : F.isPrime = true) (j3 : F ∉ sigAt l) (hg : F ∈ sfR G)
      (hΓ : Γ ≐ joinCtxAtP l F) : FRJr G false Γ F
  /-- `⋈^∨,p`: the promise variant of `⋈^∨`. -/
  | joinOrP {l Γ C₁ C₂ Δ D bp} (ps : Prems G l) (pr : FRJr G bp Δ D)
      (j1 : J1 l) (j2 : J2 l) (j4₁ : C₁ ∈ ups l) (j4₂ : C₂ ∈ ups l)
      (j5 : J5 l Δ) (j6 : J6 l Δ) (j7 : J7 Γ Δ) (hg : Form.or C₁ C₂ ∈ sfR G)
      (hΓ : Γ ≐ joinCtxOrP l) : FRJr G false Γ (.or C₁ C₂)

/-- Refutations of irregular sequents `Σ ; Θ → C`. -/
inductive FRJi (G : Form) : List Form → List Form → Form → Type
  /-- `Ax^→`: `⊢ · ; Ĝ_at \ {F}, Ĝ_imp, Ĝ_◯ → F`, `F ∈ Prime`.

  DIVERGENCE: the paper's `Θ` is `Ĝ_at \ {F}, Ĝ_imp`; the third zone joins
  it, since `Θ` is what the world below may force and `◯`-formulas are now
  among the determining data.  On a `◯`-free goal `Ĝ_◯ = ∅` and this is
  the paper's axiom. -/
  | axI {St Th F} (hF : F.isPrime = true) (hg : F ∈ sfR G)
      (hSt : St ≐ []) (hTh : Th ≐ rm (gAt G) F ++ gImp G ++ gCirc G) :
      FRJi G St Th F
  /-- `∧` irregular, `k = 1`. -/
  | andI₁ {St Th A₁ A₂} (d : FRJi G St Th A₁) (hg : Form.and A₁ A₂ ∈ sfR G) :
      FRJi G St Th (.and A₁ A₂)
  /-- `∧` irregular, `k = 2`. -/
  | andI₂ {St Th A₁ A₂} (d : FRJi G St Th A₂) (hg : Form.and A₁ A₂ ∈ sfR G) :
      FRJi G St Th (.and A₁ A₂)
  /-- `∨`, sides `Σ₁ ⊆ Σ₂ ∪ Θ₂` and `Σ₂ ⊆ Σ₁ ∪ Θ₁`. -/
  | orI {St Th St₁ Th₁ St₂ Th₂ C₁ C₂}
      (d₁ : FRJi G St₁ Th₁ C₁) (d₂ : FRJi G St₂ Th₂ C₂)
      (s₁ : St₁ ⊆ St₂ ++ Th₂) (s₂ : St₂ ⊆ St₁ ++ Th₁)
      (hSt : St ≐ St₁ ++ St₂) (hTh : Th ≐ cap Th₁ Th₂)
      (hg : Form.or C₁ C₂ ∈ sfR G) : FRJi G St Th (.or C₁ C₂)
  /-- `⊃∈` irregular: the premise's `Θ'` is partitioned as `Θ, Λ` and `Λ`
  is shifted to the left of the semicolon; sides `Θ ∩ Λ = ∅` and
  `A ∈ Cl(Σ ∪ Λ)`. -/
  | impInI {St Th St₁ Th' Λ A B} (d : FRJi G St₁ Th' B)
      (hTh' : Th' ≐ Th ++ Λ) (hdisj : ∀ x ∈ Th, x ∉ Λ)
      (hA : Clo (St₁ ++ Λ) A) (hSt : St ≐ St₁ ++ Λ)
      (hg : Form.imp A B ∈ sfR G) : FRJi G St Th (.imp A B)
  /-- `⊃∉`, the only rule turning a regular sequent into an irregular one;
  sides `Θ ⊆ Cl(Γ) ∩ Ĝ` and `A ∈ Cl(Γ) \ Cl(Θ)`. -/
  | impNotIn {b St Th Γ A B} (d : FRJr G b Γ B)
      (hTh : ∀ x ∈ Th, Clo Γ x ∧ x ∈ gHat G)
      (hA : Clo Γ A) (hnA : ¬ Clo Th A) (hSt : St ≐ [])
      (hg : Form.imp A B ∈ sfR G) : FRJi G St Th (.imp A B)

/-- The premises of a join: `n ≥ 1` irregular refutations, the `n ≥ 1`
carried by the shape of the index list. -/
inductive Prems (G : Form) : List Prem → Type
  | one {St Th A} : FRJi G St Th A → Prems G [⟨St, Th, A⟩]
  | cons {St Th A l} : FRJi G St Th A → Prems G l → Prems G (⟨St, Th, A⟩ :: l)

end

theorem Prems.ne_nil {G : Form} : ∀ {l : List Prem}, Prems G l → l ≠ []
  | _, .one _ => by simp
  | _, .cons _ _ => by simp

/-! ## Provability

"`D` is an `FRJ(G)`-refutation of `G` iff there exists a (possibly empty)
set of formulas `Γ` such that `D` is an `FRJ(G)`-refutation of `Γ ⇒ G`";
"`G` is provable in `FRJ(G)`, denoted `⊢_FRJ(G) G`, iff there exists an
`FRJ(G)`-refutation of `G`."

`Refutation` is the `Type`-valued reading — a refutation is data, and the
completeness construction of W4 must return one.  `Provable` is the
`Prop` shadow, for statements where only existence matters. -/

/-- An `FRJ(G)`-refutation of `G`: a context together with a refutation of
`Γ ⇒ G`. -/
def Refutation (G : Form) : Type := (b : Bool) × (Γ : List Form) × FRJr G b Γ G

/-- `⊢_FRJ(G) G`. -/
def Provable (G : Form) : Prop := Nonempty (Refutation G)

theorem Provable.intro {G : Form} (d : Refutation G) : Provable G := ⟨d⟩

/-! ## The no-green-slime check

Every constructor above returns one of

    FRJr G Γ F                FRJr G Γ (.and A₁ A₂)
    FRJr G Γ (.imp A B)       FRJr G Γ (.or C₁ C₂)
    FRJi G St Th F            FRJi G St Th (.and A₁ A₂)
    FRJi G St Th (.or C₁ C₂)  FRJi G St Th (.imp A B)
    Prems G [⟨St, Th, A⟩]     Prems G (⟨St, Th, A⟩ :: l)

— every context index a bare variable, every goal index a variable or a
constructor applied to variables, and the two `Prems` indices constructor
forms.  No `++`, no `rm`, no `cap`, no `filter` appears in any return
type.  All ten computed contexts of Figure 1 enter through `≐`, `⊆` or
`∈` hypotheses instead.

The consequence intended: exchange, weakening and contraction are not
needed as structural rules, and nothing downstream will need `▸`, `cast`
or `HEq`. -/

/-! ## Axiom audit

`Classical.choice` is absent; the judgments and every side-condition
decision procedure sit at `[propext]`.  Pinned with `#guard_msgs` in the
module itself, so a regression is a build failure. -/

/-- info: 'FRJLax.Sequent.lhs' does not depend on any axioms -/
#guard_msgs in
#print axioms Sequent.lhs

/-- info: 'FRJLax.interAll' depends on axioms: [propext] -/
#guard_msgs in
#print axioms interAll

/-- info: 'FRJLax.mem_restrict' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mem_restrict

/-- info: 'FRJLax.joinCtxAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms joinCtxAt

/-- info: 'FRJLax.joinCtxOr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms joinCtxOr

/-- info: 'FRJLax.FRJr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FRJr

/-- info: 'FRJLax.FRJi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms FRJi

/-- info: 'FRJLax.Prems' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Prems

/-- info: 'FRJLax.Prems.ne_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Prems.ne_nil

/-- info: 'FRJLax.Provable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Provable

/-- info: 'FRJLax.decJ1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decJ1

/-- info: 'FRJLax.decJ2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decJ2

/-- info: 'FRJLax.mem_interAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mem_interAll

end FRJLax
