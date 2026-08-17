/-
# FRJ(G) — the calculus

Section 3 of Fiorentini–Ferrari (TOCL 21(3), 2020; arXiv:1804.06689),
Figure "The calculus FRJ(G)", transcribed rule by rule.

The judgment is an indexed inductive family with one constructor per
published rule and every side condition present as a field.  Nothing
here is invented: each constructor's docstring quotes the rule it
encodes.
-/
import FRJ.Basic

namespace FRJ

open Form

/-! ## Set operations used by the join rules

The joins take `n ≥ 1` premises, so unions and intersections range over
a nonempty finite index.  We index premises by `Fin (n+1)`.
-/

/-- `⋃_{1≤j≤n} f j`. -/
def unionAll {n : Nat} (f : Fin (n + 1) → List Form) : List Form :=
  (List.finRange (n + 1)).flatMap f

@[simp] theorem mem_unionAll {n : Nat} {f : Fin (n + 1) → List Form} {x : Form} :
    x ∈ unionAll f ↔ ∃ j, x ∈ f j := by
  simp [unionAll, List.mem_flatMap]

/-- `⋂_{1≤j≤n} f j`.  Defined by filtering the first component, which is
legitimate exactly because the index is nonempty. -/
def interAll {n : Nat} (f : Fin (n + 1) → List Form) : List Form :=
  (f 0).filter (fun x => decide (∀ j, x ∈ f j))

@[simp] theorem mem_interAll {n : Nat} {f : Fin (n + 1) → List Form} {x : Form} :
    x ∈ interAll f ↔ ∀ j, x ∈ f j := by
  simp only [interAll, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h 0, h⟩⟩

/-- Membership test for the restriction operator. -/
def inRestrict (Υ : List Form) : Form → Bool
  | .imp A _ => decide (A ∈ Υ)
  | _ => false

/-- "Given a set of ⊃-formulas `Γ⊃` and a set of formulas `Υ`, let
`Γ⊃/Υ = { Y ⊃ Z ∈ Γ⊃ | Y ∈ Υ }`.  We call `Γ⊃/Υ` the *restriction* of
`Γ⊃` to `Υ`." -/
def restrict (X Υ : List Form) : List Form :=
  X.filter (fun f => inRestrict Υ f)

theorem mem_restrict {X Υ : List Form} {A B : Form} :
    Form.imp A B ∈ restrict X Υ ↔ (Form.imp A B ∈ X ∧ A ∈ Υ) := by
  simp [restrict, inRestrict, List.mem_filter]

theorem restrict_subset {X Υ : List Form} : restrict X Υ ⊆ X :=
  fun _ h => (List.mem_filter.mp h).1

/-- Membership test for the MODAL restriction: keep `◯Y` when SOME promise
context has `Y ∈ Cl(Δᵢ)`.  The modal analogue of `inRestrict`, against the
closures of the promise family — an existential because the `◯`-clause
needs ONE modal successor forcing `Y`, and different kept formulas may be
witnessed by different promise worlds.  The framework is PLL-general: the
family's arity `k+1` is arbitrary (Matthew, 2026-08-17 — PCLL's unary
case is a later specialisation, not the target). -/
def inRestrictC {k : Nat} (Δs : Fin (k + 1) → List Form) : Form → Bool
  | .circ Y => (List.finRange (k + 1)).any (fun i => cloB (Δs i) Y)
  | _ => false

/-- `Θ^◯ / Cl(Δ⃗) = { ◯Y ∈ Θ^◯ | ∃ i, Y ∈ Cl(Δᵢ) }`.  (J5) for the second
zone, as a restriction rather than a side condition — mirroring the
paper's `Θ^⊃/Υ`. -/
def restrictC {k : Nat} (X : List Form) (Δs : Fin (k + 1) → List Form) : List Form :=
  X.filter (fun f => inRestrictC Δs f)

theorem mem_restrictC {k : Nat} {X : List Form} {Δs : Fin (k + 1) → List Form}
    {Y : Form} :
    Form.circ Y ∈ restrictC X Δs ↔ (Form.circ Y ∈ X ∧ ∃ i, Clo (Δs i) Y) := by
  simp [restrictC, inRestrictC, List.mem_filter, List.any_eq_true, cloB_iff]

theorem restrictC_subset {k : Nat} {X : List Form} {Δs : Fin (k + 1) → List Form} :
    restrictC X Δs ⊆ X :=
  fun _ h => (List.mem_filter.mp h).1

theorem isCirc_of_mem_restrictC {k : Nat} {X : List Form}
    {Δs : Fin (k + 1) → List Form} {A : Form}
    (h : A ∈ restrictC X Δs) : A.isCirc = true := by
  have := (List.mem_filter.mp h).2
  cases A <;> simp_all [inRestrictC, Form.isCirc]

/-! ## The conclusion contexts of the join rules

Named so that the `↦` relation of Sec. 3.1 and the calculus cannot drift
apart: both refer to these. -/

/-- `Υ = {A₁, …, Aₙ}`, the right formulas of the join's premises. -/
def upsilon {n : Nat} (rhs : Fin (n + 1) → Form) : List Form :=
  (List.finRange (n + 1)).map rhs

/-- The conclusion context of `⋈^At`:  `Σ^at, Θ^at \ {F}, Σ^imp, Θ^imp`. -/
def joinCtxAt {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form) : List Form :=
  unionAll (fun j => atPart (stab j)) ++
    rm (interAll (fun j => atPart (th j))) F ++
    unionAll (fun j => impPart (stab j)) ++
    restrict (interAll (fun j => impPart (th j))) (upsilon rhs)

/-- The conclusion context of `⋈^∨`:  `Σ^at, Θ^at, Σ^imp, Θ^imp`. -/
def joinCtxOr {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) : List Form :=
  unionAll (fun j => atPart (stab j)) ++
    interAll (fun j => atPart (th j)) ++
    unionAll (fun j => impPart (stab j)) ++
    restrict (interAll (fun j => impPart (th j))) (upsilon rhs)

/-- The modal part a PROMISE join keeps:  `Σ^◯, Θ^◯/Cl(Δ⃗)` — the stable
modal formulas (side condition (J5) makes their bodies land in some
`Cl(Δᵢ)`) plus the second-zone ones whose bodies do. -/
def joinCtxCircP {n k : Nat} (stab th : Fin (n + 1) → List Form)
    (Δs : Fin (k + 1) → List Form) : List Form :=
  unionAll (fun j => circPart (stab j)) ++
    restrictC (interAll (fun j => circPart (th j))) Δs

/-- The modal part a FALLIBLE join keeps: everything — a fallible witness
forces every body, so no restriction is needed. -/
def joinCtxCircF {n : Nat} (stab th : Fin (n + 1) → List Form) : List Form :=
  unionAll (fun j => circPart (stab j)) ++
    interAll (fun j => circPart (th j))

/-- Conclusion context of the promise `⋈^At`. -/
def joinCtxAtP {n k : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form) (Δs : Fin (k + 1) → List Form) : List Form :=
  joinCtxAt stab th rhs F ++ joinCtxCircP stab th Δs

/-- Conclusion context of the fallible `⋈^At`. -/
def joinCtxAtF {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (F : Form) : List Form :=
  joinCtxAt stab th rhs F ++ joinCtxCircF stab th

/-- Conclusion context of the promise `⋈^∨`. -/
def joinCtxOrP {n k : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) (Δs : Fin (k + 1) → List Form) : List Form :=
  joinCtxOr stab th rhs ++ joinCtxCircP stab th Δs

/-- Conclusion context of the fallible `⋈^∨`. -/
def joinCtxOrF {n : Nat} (stab th : Fin (n + 1) → List Form)
    (rhs : Fin (n + 1) → Form) : List Form :=
  joinCtxOr stab th rhs ++ joinCtxCircF stab th

/-! ## The pledge tag

The index that gates the modal introduction rule.  `Mod(D)`'s root world
has a modal cone: itself alone (a BARREN root — axioms and promise-free
joins), or itself plus the chain of promise components.  `◯∈` from
`Γ ⇒ Z` is sound exactly when every world of that cone refutes `Z`
(`tag_cone` in `FRJ/Sound.lean`); the tag is the syntactic record making
that decidable.

This is the single-pledge shadow of the canonical model's `mfal`
component (`LaxLogic/PLLCompleteness.lean`): `chain Z` says `Z` is
pledged false along the root's whole modal cone. -/
inductive Tag where
  /-- the root's modal cone is `{root}` -/
  | barren
  /-- the root's modal cone is a promise chain, every world of which
  refutes `D` -/
  | chain (D : Form)
  /-- no claim (a fallible promise, or an unmatched chain) -/
  | blocked
  deriving DecidableEq, Repr

/-! ## The calculus

Two mutually inductive families, one per sequent form:

* `FRJr G Γ C` — derivations of the regular sequent `Γ ⇒ C`;
* `FRJi G Σ Θ C` — derivations of the irregular sequent `Σ ; Θ → C`.

The blanket side condition of the figure — "in the conclusion `σ` of each
rule, `Rhs(σ) ∈ Sf^R(G)`" — appears as a field `hgoal` on every
constructor.
-/

mutual

/-- Derivations of regular sequents `Γ ⇒ C`, indexed by the pledge tag of
the root world of the extracted model. -/
inductive FRJr (G : Form) : Tag → List Form → Form → Type
  /-- `Ax^R`:  `⊢ Ĝ_at \ {F} ⇒ F`,  `F ∈ Prime`.  Its world is barren. -/
  | axR (F : Form) (hF : F.isPrime) (hgoal : F ∈ sfR G) :
      FRJr G .barren (rm (gAt G) F) F
  /-- `∧` (regular), `k = 1`:  from `Γ ⇒ A₁` infer `Γ ⇒ A₁ ∧ A₂`. -/
  | andR1 {t : Tag} {Γ : List Form} {A₁ A₂ : Form}
      (d : FRJr G t Γ A₁) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJr G t Γ (.and A₁ A₂)
  /-- `∧` (regular), `k = 2`:  from `Γ ⇒ A₂` infer `Γ ⇒ A₁ ∧ A₂`. -/
  | andR2 {t : Tag} {Γ : List Form} {A₁ A₂ : Form}
      (d : FRJr G t Γ A₂) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJr G t Γ (.and A₁ A₂)
  /-- `⊃∈` (regular):  from `Γ ⇒ B` infer `Γ ⇒ A ⊃ B`,  side `A ∈ Cl(Γ)`. -/
  | impIn {t : Tag} {Γ : List Form} {A B : Form}
      (d : FRJr G t Γ B) (hA : Clo Γ A) (hgoal : Form.imp A B ∈ sfR G) :
      FRJr G t Γ (.imp A B)
  /-- `◯∈` (regular):  from `Γ ⇒ Z` infer `Γ ⇒ ◯Z`, provided the root's
      whole modal cone refutes `Z` — i.e. the tag is `barren` (the cone is
      the root itself, which refutes `Z` by the premise) or `chain Z` (a
      promise chain pledged to `Z`).  `tag_cone` is the semantic content;
      the world stays the same, so the tag passes through. -/
  | circIn {t : Tag} {Γ : List Form} {Z : Form}
      (d : FRJr G t Γ Z) (htag : t = .barren ∨ t = .chain Z)
      (hgoal : Form.circ Z ∈ sfR G) :
      FRJr G t Γ (.circ Z)
  /-- `⋈^At`: from `n ≥ 1` irregular premises `σⱼ = Σⱼ ; Θⱼ → Aⱼ` infer
      `Σ^at, Θ^at \ {F}, Σ^imp, Θ^imp ⇒ F`, with side conditions
      (J1) `Σᵢ ⊆ Σⱼ ++ Θⱼ` for `i ≠ j`,
      (J2) `Y ⊃ Z ∈ Σ^imp` implies `Y ∈ Υ`, and
      `F ∈ Prime \ Σ^at`. -/
  | joinAt {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form}
      (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hcirc : unionAll (fun j => circPart (stab j)) = [])
      (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
      (hgoal : F ∈ sfR G) :
      FRJr G .barren (joinCtxAt stab th rhs F) F
  /-- `⋈^At,p` — the PROMISE join.  A FAMILY of `k+1` additional REGULAR
      premises `Δᵢ ⇒ Dᵢ`, whose worlds become the modal successors of the
      new world.  The family arity is arbitrary — full PLL needs unbounded
      arity (`docs/frj-lifting.md` §3), so the framework hard-wires no
      bound; the unary case is `k = 0`.  New side conditions:
      (J5) each stable modal body lands in SOME `Cl(Δᵢ)` (for `Θ^◯` this
      is the restriction built into the context);
      (J7) the whole conclusion context lands in EVERY `Cl(Δᵢ)` — each
      promise world lies modally, hence intuitionistically, above the new
      world.
      The tag: `chain D` when every promise pledges `D` and continues the
      pledge down its own cone, else `blocked`. -/
  | joinAtP {n k : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {t' : Tag}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
      (dps : ∀ i, FRJr G (tps i) (Δs i) (Ds i))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
        ∃ i, Clo (Δs i) Y)
      (hJ7 : ∀ i, ∀ X ∈ joinCtxAtP stab th rhs F Δs, Clo (Δs i) X)
      (htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
        (tps i = .barren ∨ tps i = .chain (Ds 0))))
      (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
      (hgoal : F ∈ sfR G) :
      FRJr G t' (joinCtxAtP stab th rhs F Δs) F
  /-- `⋈^At,⊥` — the FALLIBLE join.  The modal successor of the new world
      is a declared fallible world; it forces everything, so the whole
      modal zone is kept with no condition, and no `◯`-formula can be
      refuted at the new world: the tag is `blocked`. -/
  | joinAtF {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form}
      (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
      (hgoal : F ∈ sfR G) :
      FRJr G .blocked (joinCtxAtF stab th rhs F) F
  /-- `⋈^∨`: as `⋈^At`, but the conclusion's right formula is a
      `∨`-formula `C₁ ∨ C₂` with `{C₁,C₂} ⊆ Υ`, and `Θ^at` is kept whole. -/
  | joinOr {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form}
      (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hcirc : unionAll (fun j => circPart (stab j)) = [])
      (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
      (hgoal : Form.or C₁ C₂ ∈ sfR G) :
      FRJr G .barren (joinCtxOr stab th rhs) (.or C₁ C₂)
  /-- `⋈^∨,p` — the promise `⋈^∨`, with the same promise family. -/
  | joinOrP {n k : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {t' : Tag}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
      (dps : ∀ i, FRJr G (tps i) (Δs i) (Ds i))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
        ∃ i, Clo (Δs i) Y)
      (hJ7 : ∀ i, ∀ X ∈ joinCtxOrP stab th rhs Δs, Clo (Δs i) X)
      (htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
        (tps i = .barren ∨ tps i = .chain (Ds 0))))
      (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
      (hgoal : Form.or C₁ C₂ ∈ sfR G) :
      FRJr G t' (joinCtxOrP stab th rhs Δs) (.or C₁ C₂)
  /-- `⋈^∨,⊥` — the fallible `⋈^∨`. -/
  | joinOrF {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form}
      (prem : ∀ j, FRJi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
      (hgoal : Form.or C₁ C₂ ∈ sfR G) :
      FRJr G .blocked (joinCtxOrF stab th rhs) (.or C₁ C₂)

/-- Derivations of irregular sequents `Σ ; Θ → C`. -/
inductive FRJi (G : Form) : List Form → List Form → Form → Type
  /-- `Ax^I`:  `⊢ [] ; Ĝ_at \ {F}, Ĝ_imp → F`,  `F ∈ Prime`. -/
  | axI (F : Form) (hF : F.isPrime) (hgoal : F ∈ sfR G) :
      FRJi G [] (nf G ((rm (gAt G) F) ++ gImp G ++ gCirc G)) F
  /-- `∧` (irregular), `k = 1`. -/
  | andI1 {St Th : List Form} {A₁ A₂ : Form}
      (d : FRJi G St Th A₁) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJi G St Th (.and A₁ A₂)
  /-- `∧` (irregular), `k = 2`. -/
  | andI2 {St Th : List Form} {A₁ A₂ : Form}
      (d : FRJi G St Th A₂) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJi G St Th (.and A₁ A₂)
  /-- `∨`: from `Σ₁ ; Θ₁ → C₁` and `Σ₂ ; Θ₂ → C₂` infer
      `Σ₁, Σ₂ ; Θ₁ ∩ Θ₂ → C₁ ∨ C₂`, side conditions
      `Σ₁ ⊆ Σ₂ ++ Θ₂` and `Σ₂ ⊆ Σ₁ ++ Θ₁`. -/
  | orI {St₁ Th₁ St₂ Th₂ : List Form} {C₁ C₂ : Form}
      (d₁ : FRJi G St₁ Th₁ C₁) (d₂ : FRJi G St₂ Th₂ C₂)
      (h₁ : St₁ ⊆ St₂ ++ Th₂) (h₂ : St₂ ⊆ St₁ ++ Th₁)
      (hgoal : Form.or C₁ C₂ ∈ sfR G) :
      FRJi G (St₁ ++ St₂) (nf G (cap Th₁ Th₂)) (.or C₁ C₂)
  /-- `⊃∈` (irregular): from `Σ ; Θ, Λ → B` infer `Σ, Λ ; Θ → A ⊃ B`,
      side conditions `Θ ∩ Λ = ∅` and `A ∈ Cl(Σ ++ Λ)`. -/
  | impInI {St Th Lam : List Form} {A B : Form}
      (d : FRJi G St (nf G (Th ++ Lam)) B)
      (hdisj : cap Th Lam = []) (hA : Clo (nf G (St ++ Lam)) A)
      (hgoal : Form.imp A B ∈ sfR G) :
      FRJi G (nf G (St ++ Lam)) (nf G Th) (.imp A B)
  /-- `⊃∉`: from the REGULAR premise `Γ ⇒ B` infer `[] ; Θ → A ⊃ B`,
      side conditions `Θ ⊆ Cl(Γ) ∩ Ĝ` and `A ∈ Cl(Γ) \ Cl(Θ)`. -/
  | impNotIn {t : Tag} {Γ Th : List Form} {A B : Form}
      (d : FRJr G t Γ B)
      (hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G)
      (hA : Clo Γ A) (hAnot : ¬ Clo Th A)
      (hgoal : Form.imp A B ∈ sfR G) :
      FRJi G [] Th (.imp A B)
  /-- `◯∉`: from the REGULAR premise `Γ ⇒ Z`, whose root's whole modal
      cone refutes `Z` (the tag condition, as in `◯∈`), infer
      `[] ; Θ → ◯Z`, side condition `Θ ⊆ Cl(Γ) ∩ Ĝ`.  The premise's
      world realises the conclusion: it forces `Cl(Γ) ⊇ Θ` and refutes
      `◯Z` with itself as the `∃`-witness.  This is `⊃∉` with the tag
      condition in place of the antecedent conditions — W4's repair of
      the W3 completeness gap (`docs/frj-w4.md` §1 (D2)): without it no
      derivable context contains an implication with modal antecedent,
      since `hJ2` demands the antecedent among the irregular premises'
      right formulas and nothing produced `rhs = ◯Z`. -/
  | circNotIn {t : Tag} {Γ Th : List Form} {Z : Form}
      (d : FRJr G t Γ Z) (htag : t = .barren ∨ t = .chain Z)
      (hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G)
      (hgoal : Form.circ Z ∈ sfR G) :
      FRJi G [] Th (.circ Z)

end

/-! ## Provability

"`D` is an `FRJ(G)`-derivation of `G` iff there exists a (possibly
empty) set of formulas `Γ` such that `D` is an `FRJ(G)`-derivation of
`Γ ⇒ G`."
-/

/-- `⊢_{FRJ(G)} G`: the goal formula `G` is provable in `FRJ(G)`. -/
def Provable (G : Form) : Prop := ∃ (t : Tag) (Γ : List Form), Nonempty (FRJr G t Γ G)

end FRJ
