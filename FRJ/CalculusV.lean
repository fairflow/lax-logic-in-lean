/-
# FRJ(G) with the RefAt joins — the repaired calculus `FRJV`

The paper family `FRJr`/`FRJi` (`FRJ/Calculus.lean`) is PROVABLY
incomplete (`wip/frj80_noprov.lean`, `wip/frj81_noprov.lean`); the
repair (`docs/refat-plan.md`) relaxes the three BARREN joins:

* the second-zone retention `Θ^⊃/Υ` becomes an explicit `kept` zone with
  a stratified `KeptChain` certificate (each kept implication's
  antecedent is `RefAt`-refuted over the base context plus the earlier
  links);
* `⋈^∨`'s `hC` and `⋈^◯`'s `hZ` test `RefAt` membership instead of
  membership in Υ.

Everything else — the axioms, the single-premise rules, the irregular
rules, the promise and fallible joins — is the paper family verbatim
(the promise/fallible cones are not the root alone, so the `◯`-clause is
unsound there and the relaxation is deliberately NOT applied; see the
divergence log in the plan).

This is a SEPARATE family, not an extension of `FRJr`/`FRJi`: `Provable`
must keep its meaning — the incompleteness theorems are exhaustive case
analyses over the paper family and must survive verbatim.  The paper
calculus embeds (`toVr`/`toVi` below), so every derivation-existence
result transfers; the incompleteness theorems do not (that is the point).
-/
import FRJ.Calculus
import FRJ.RefAt

namespace FRJ

open Form

/-! ## The V-join contexts

The base is the old join context MINUS the restricted second zone; the
kept zone replaces the restriction.  The candidate pool is the joint
second-zone implications — `impPart` of the intersection, which denotes
the same set as the intersection of the `impPart`s used by the paper
formers. -/

/-- `Σ^at, Θ^at \ {F}, Σ^imp` — the `⋈^At` context without its second
implication zone. -/
def joinCtxAtVBase {n : Nat} (stab th : Fin (n + 1) → List Form)
    (F : Form) : List Form :=
  unionAll (fun j => atPart (stab j)) ++
    rm (interAll (fun j => atPart (th j))) F ++
    unionAll (fun j => impPart (stab j))

/-- `Σ^at, Θ^at, Σ^imp` — the `⋈^∨` context without its second
implication zone. -/
def joinCtxOrVBase {n : Nat} (stab th : Fin (n + 1) → List Form) :
    List Form :=
  unionAll (fun j => atPart (stab j)) ++
    interAll (fun j => atPart (th j)) ++
    unionAll (fun j => impPart (stab j))

/-- The retention pool: `Θ^⊃∩`. -/
def thPool {n : Nat} (th : Fin (n + 1) → List Form) : List Form :=
  impPart (interAll th)

/-- `⋂` commutes with the `impPart` filter (as sets). -/
theorem thPool_eq_interImp {n : Nat} {th : Fin (n + 1) → List Form} :
    thPool th ≐ interAll (fun j => impPart (th j)) := by
  intro x
  constructor
  · intro hx
    have h1 := List.mem_filter.mp hx
    have h2 := mem_interAll.mp h1.1
    exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨h2 j, h1.2⟩)
  · intro hx
    have h := mem_interAll.mp hx
    exact List.mem_filter.mpr
      ⟨mem_interAll.mpr (fun j => (List.mem_filter.mp (h j)).1),
        (List.mem_filter.mp (h 0)).2⟩

/-! ## The calculus -/

mutual

/-- Regular derivations of the repaired calculus.  Identical to `FRJr`
except at `joinAt`, `joinOr`, `joinCirc`. -/
inductive FRJVr (G : Form) : Tag → List Form → Form → Type
  | axR (F : Form) (hF : F.isPrime) (hgoal : F ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ rm (gAt G) F) :
      FRJVr G .barren Γ' F
  | andR1 {t : Tag} {Γ : List Form} {A₁ A₂ : Form}
      (d : FRJVr G t Γ A₁) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJVr G t Γ (.and A₁ A₂)
  | andR2 {t : Tag} {Γ : List Form} {A₁ A₂ : Form}
      (d : FRJVr G t Γ A₂) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJVr G t Γ (.and A₁ A₂)
  | impIn {t : Tag} {Γ : List Form} {A B : Form}
      (d : FRJVr G t Γ B) (hA : Clo Γ A) (hgoal : Form.imp A B ∈ sfR G) :
      FRJVr G t Γ (.imp A B)
  | circIn {t : Tag} {Γ : List Form} {Z : Form}
      (d : FRJVr G t Γ Z)
      (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z)
      (hgoal : Form.circ Z ∈ sfR G) :
      FRJVr G t Γ (.circ Z)
  /-- `⋈^At` with the kept zone: `Σ^at, Θ^at \ {F}, Σ^imp, kept` where
      `kept` is a `KeptChain` over the base context. -/
  | joinAt {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {kept : List Form}
      (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hcirc : unionAll (fun j => circPart (stab j)) = [])
      (hkc : KeptChain (upsilon rhs) (joinCtxAtVBase stab th F)
        (thPool th) kept)
      (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
      (hgoal : F ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtVBase stab th F ++ kept) :
      FRJVr G .barren Γ' F
  | joinAtP {n k : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {t' : Tag}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
      (dps : ∀ i, FRJVr G (tps i) (Δs i) (Ds i))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
        ∃ i, Clo (Δs i) Y)
      (hJ7s : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
      (htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0))))
      (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
      (hgoal : F ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtP stab th rhs F Δs) :
      FRJVr G t' Γ' F
  | joinAtF {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form}
      (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
      (hgoal : F ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtF stab th rhs F) :
      FRJVr G .blocked Γ' F
  /-- `⋈^∨` with the kept zone and `RefAt`-relaxed disjunct conditions. -/
  | joinOr {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {kept : List Form}
      (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hcirc : unionAll (fun j => circPart (stab j)) = [])
      (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase stab th)
        (thPool th) kept)
      (hC : RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) C₁ ∧
        RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) C₂)
      (hgoal : Form.or C₁ C₂ ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrVBase stab th ++ kept) :
      FRJVr G .barren Γ' (.or C₁ C₂)
  | joinOrP {n k : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {t' : Tag}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
      (dps : ∀ i, FRJVr G (tps i) (Δs i) (Ds i))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
        ∃ i, Clo (Δs i) Y)
      (hJ7s : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
      (htag : t' = .blocked ∨ (t' = .chain (Ds 0) ∧ ∀ i, Ds i = Ds 0 ∧
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W (Ds 0))))
      (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
      (hgoal : Form.or C₁ C₂ ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrP stab th rhs Δs) :
      FRJVr G t' Γ' (.or C₁ C₂)
  | joinOrF {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form}
      (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
      (hgoal : Form.or C₁ C₂ ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrF stab th rhs) :
      FRJVr G .blocked Γ' (.or C₁ C₂)
  /-- `⋈^◯` with the kept zone and the `RefAt`-relaxed body condition. -/
  | joinCirc {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {Z : Form} {kept : List Form}
      (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hcirc : unionAll (fun j => circPart (stab j)) = [])
      (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase stab th)
        (thPool th) kept)
      (hZ : RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) Z)
      (hgoal : Form.circ Z ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrVBase stab th ++ kept) :
      FRJVr G .barren Γ' (.circ Z)
  | joinCircP {n k : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {Z : Form}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      (prem : ∀ j, FRJVi G (stab j) (th j) (rhs j))
      (dps : ∀ i, FRJVr G (tps i) (Δs i) (Ds i))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hJ5 : ∀ Y : Form, Form.circ Y ∈ unionAll (fun j => circPart (stab j)) →
        ∃ i, Clo (Δs i) Y)
      (hJ7s : ∀ i j, ∀ X ∈ stab j, Clo (Δs i) X)
      (hDs : ∀ i, Ds i = Z ∧
        (tps i = .barren ∨ ∃ W, tps i = .chain W ∧ Covers (Δs i) W Z))
      (hZ : Z ∈ upsilon rhs)
      (hgoal : Form.circ Z ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrP stab th rhs Δs) :
      FRJVr G (.chain Z) Γ' (.circ Z)

/-- Irregular derivations of the repaired calculus — the paper rules
verbatim. -/
inductive FRJVi (G : Form) : List Form → List Form → Form → Type
  | axI (F : Form) (hF : F.isPrime) (hgoal : F ∈ sfR G)
      {Th' : List Form} (hTh : Th' ≐ (rm (gAt G) F) ++ gImp G ++ gCirc G) :
      FRJVi G [] Th' F
  | andI1 {St Th : List Form} {A₁ A₂ : Form}
      (d : FRJVi G St Th A₁) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJVi G St Th (.and A₁ A₂)
  | andI2 {St Th : List Form} {A₁ A₂ : Form}
      (d : FRJVi G St Th A₂) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJVi G St Th (.and A₁ A₂)
  | orI {St₁ Th₁ St₂ Th₂ : List Form} {C₁ C₂ : Form}
      (d₁ : FRJVi G St₁ Th₁ C₁) (d₂ : FRJVi G St₂ Th₂ C₂)
      (h₁ : St₁ ⊆ St₂ ++ Th₂) (h₂ : St₂ ⊆ St₁ ++ Th₁)
      (hgoal : Form.or C₁ C₂ ∈ sfR G)
      {St' Th' : List Form} (hSt : St' ≐ St₁ ++ St₂) (hTh : Th' ≐ cap Th₁ Th₂) :
      FRJVi G St' Th' (.or C₁ C₂)
  | impInI {St Th Lam ThLam : List Form} {A B : Form}
      (d : FRJVi G St ThLam B) (hpre : ThLam ≐ Th ++ Lam)
      (hdisj : cap Th Lam = []) (hA : Clo (St ++ Lam) A)
      (hgoal : Form.imp A B ∈ sfR G)
      {St' Th' : List Form} (hSt : St' ≐ St ++ Lam) (hTh : Th' ≐ Th) :
      FRJVi G St' Th' (.imp A B)
  | impNotIn {t : Tag} {Γ Th : List Form} {A B : Form}
      (d : FRJVr G t Γ B)
      (hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G)
      (hA : Clo Γ A) (hAnot : ¬ Clo Th A)
      (hgoal : Form.imp A B ∈ sfR G) :
      FRJVi G [] Th (.imp A B)
  | circNotIn {t : Tag} {Γ Th : List Form} {Z : Form}
      (d : FRJVr G t Γ Z)
      (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z)
      (hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G)
      (hgoal : Form.circ Z ∈ sfR G) :
      FRJVi G [] Th (.circ Z)
  | axIC (F : Form) (ats : List Form) (hats : ats ⊆ gAt G)
      (hFf : classForce ats F = false) (hgoal : Form.circ F ∈ sfR G)
      {Th' : List Form} (hTh : Th' ≐ vacZoneA G ats) :
      FRJVi G [] Th' (.circ F)
  -- **(Lift)**, added 2026-09-01.  OURS, not the paper's — divergence, see
  -- `docs/frj-fidelity.md`.
  --
  --     Γ ⇒ C      Θ ⊆ Cl(Γ),  Θ ⊆ Ĝ
  --     ───────────────────────────────  (Lift)
  --              ∅ ; Θ → C
  --
  -- The missing member of the family `⊃∉` and `◯∉` already belong to —
  -- regular premise, empty stable zone — with the formula-changing part
  -- dropped.  Without it `FRJVi` has no rule at all taking a regular
  -- premise to the SAME goal formula, and `◯(◯Z ⊃ Z)` is then FRJV-
  -- underivable in the irregular judgment while being FRJV-derivable in
  -- the regular one (`FRJ.Gbu.evalI_Gcc` is the disproof that fills that
  -- hole; `FRJ.V.WCounter.irregular_circ_imp_self_lifts` is what survives
  -- of the theorem that recorded it).
  --
  -- Soundness is the `liftI` arm of `lemma39I` and needs neither `w`'s
  -- infallibility, nor the zone bound, nor the stable-part hypothesis:
  -- its whole content is that a regular disproof refutes its goal at the
  -- root of the model it extracts.  It contributes nothing to the joins:
  -- with `Σ = ∅` the premise has `impPart [] = circPart [] = []`.
  | liftI {t : Tag} {Γ Th : List Form} {C : Form}
      (d : FRJVr G t Γ C)
      (hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G) :
      FRJVi G [] Th C

end

/-- `⊢_{FRJV(G)} G`. -/
def ProvableV (G : Form) : Prop :=
  ∃ (t : Tag) (Γ : List Form), Nonempty (FRJVr G t Γ G)

/-! ## Transport: contexts are sets, in the V-family too -/

def transportVr {G : Form} : ∀ {t : Tag} {Γ Γ' : List Form} {C : Form},
    FRJVr G t Γ C → Γ ≐ Γ' → FRJVr G t Γ' C
  | _, _, _, _, .axR F hF hg hΓ, h => .axR F hF hg (h.symm.trans hΓ)
  | _, _, _, _, .andR1 d hg, h => .andR1 (transportVr d h) hg
  | _, _, _, _, .andR2 d hg, h => .andR2 (transportVr d h) hg
  | _, _, _, _, .impIn d hA hg, h =>
      .impIn (transportVr d h) (clo_mono h.subset hA) hg
  | _, _, _, _, .circIn d htag hg, h =>
      .circIn (transportVr d h)
        (htag.imp id (fun ⟨W, hW, hc⟩ => ⟨W, hW, covers_mono h.subset hc⟩)) hg
  | _, _, _, _, .joinAt prem hJ1 hJ2 hcirc hkc hF hFnot hg hΓ, h =>
      .joinAt prem hJ1 hJ2 hcirc hkc hF hFnot hg (h.symm.trans hΓ)
  | _, _, _, _, .joinAtP prem dps hJ1 hJ2 hJ5 hJ7s htag hF hFnot hg hΓ, h =>
      .joinAtP prem dps hJ1 hJ2 hJ5 hJ7s htag hF hFnot hg (h.symm.trans hΓ)
  | _, _, _, _, .joinAtF prem hJ1 hJ2 hF hFnot hg hΓ, h =>
      .joinAtF prem hJ1 hJ2 hF hFnot hg (h.symm.trans hΓ)
  | _, _, _, _, .joinOr prem hJ1 hJ2 hcirc hkc hC hg hΓ, h =>
      .joinOr prem hJ1 hJ2 hcirc hkc hC hg (h.symm.trans hΓ)
  | _, _, _, _, .joinOrP prem dps hJ1 hJ2 hJ5 hJ7s htag hC hg hΓ, h =>
      .joinOrP prem dps hJ1 hJ2 hJ5 hJ7s htag hC hg (h.symm.trans hΓ)
  | _, _, _, _, .joinOrF prem hJ1 hJ2 hC hg hΓ, h =>
      .joinOrF prem hJ1 hJ2 hC hg (h.symm.trans hΓ)
  | _, _, _, _, .joinCirc prem hJ1 hJ2 hcirc hkc hZ hg hΓ, h =>
      .joinCirc prem hJ1 hJ2 hcirc hkc hZ hg (h.symm.trans hΓ)
  | _, _, _, _, .joinCircP prem dps hJ1 hJ2 hJ5 hJ7s hDs hZ hg hΓ, h =>
      .joinCircP prem dps hJ1 hJ2 hJ5 hJ7s hDs hZ hg (h.symm.trans hΓ)

/-! ## The paper calculus embeds

The three strict barren joins are instances of the V-joins: the paper's
kept zone `Θ^⊃/Υ` is a chain in any order (`keptChain_of_ups` — every
antecedent is in Υ), and `C ∈ Υ` is the `ups` clause of `RefAt`. -/

/-- Local copy of `Step.lean`'s `interAll_subset` (importing `FRJ.Step`
here would invert the dependency order). -/
theorem interAll_subset' {n : Nat} {f : Fin (n + 1) → List Form}
    (j : Fin (n + 1)) {x : Form} (h : x ∈ interAll f) : x ∈ f j :=
  mem_interAll.mp h j

theorem restrict_keptChain {n : Nat} {th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} (base : List Form) :
    KeptChain (upsilon rhs) base (thPool th)
      (restrict (interAll (fun j => impPart (th j))) (upsilon rhs)) := by
  refine keptChain_of_ups ?_ ?_ ?_
  · intro X hX
    have hX' := restrict_subset hX
    exact (thPool_eq_interImp X).mpr hX'
  · intro A B hAB
    exact (mem_restrict.mp hAB).2
  · intro X hX
    have hX' := restrict_subset hX
    exact (List.mem_filter.mp (interAll_subset' 0 hX')).2

/-- The old `⋈^At` context is the V-base plus the old restriction. -/
theorem joinCtxAt_eq_base {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} {F : Form} :
    joinCtxAt stab th rhs F ≐
      joinCtxAtVBase stab th F ++
        restrict (interAll (fun j => impPart (th j))) (upsilon rhs) := by
  intro x
  simp only [joinCtxAt, joinCtxAtVBase, List.append_assoc, List.mem_append]

theorem joinCtxOr_eq_base {n : Nat} {stab th : Fin (n + 1) → List Form}
    {rhs : Fin (n + 1) → Form} :
    joinCtxOr stab th rhs ≐
      joinCtxOrVBase stab th ++
        restrict (interAll (fun j => impPart (th j))) (upsilon rhs) := by
  intro x
  simp only [joinCtxOr, joinCtxOrVBase, List.append_assoc, List.mem_append]

mutual

/-- Every paper derivation is a V-derivation, at the same indices. -/
def toVr {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form},
    FRJr G t Γ C → FRJVr G t Γ C
  | _, _, _, .axR F hF hg hΓ => .axR F hF hg hΓ
  | _, _, _, .andR1 d hg => .andR1 (toVr d) hg
  | _, _, _, .andR2 d hg => .andR2 (toVr d) hg
  | _, _, _, .impIn d hA hg => .impIn (toVr d) hA hg
  | _, _, _, .circIn d htag hg => .circIn (toVr d) htag hg
  | _, _, _, .joinAt prem hJ1 hJ2 hcirc hF hFnot hg hΓ =>
      .joinAt (fun j => toVi (prem j)) hJ1 hJ2 hcirc
        (restrict_keptChain _) hF hFnot hg
        (hΓ.trans joinCtxAt_eq_base)
  | _, _, _, .joinAtP prem dps hJ1 hJ2 hJ5 hJ7s htag hF hFnot hg hΓ =>
      .joinAtP (fun j => toVi (prem j)) (fun i => toVr (dps i))
        hJ1 hJ2 hJ5 hJ7s htag hF hFnot hg hΓ
  | _, _, _, .joinAtF prem hJ1 hJ2 hF hFnot hg hΓ =>
      .joinAtF (fun j => toVi (prem j)) hJ1 hJ2 hF hFnot hg hΓ
  | _, _, _, .joinOr prem hJ1 hJ2 hcirc hC hg hΓ =>
      .joinOr (fun j => toVi (prem j)) hJ1 hJ2 hcirc
        (restrict_keptChain _)
        ⟨.ups hC.1, .ups hC.2⟩ hg
        (hΓ.trans joinCtxOr_eq_base)
  | _, _, _, .joinOrP prem dps hJ1 hJ2 hJ5 hJ7s htag hC hg hΓ =>
      .joinOrP (fun j => toVi (prem j)) (fun i => toVr (dps i))
        hJ1 hJ2 hJ5 hJ7s htag hC hg hΓ
  | _, _, _, .joinOrF prem hJ1 hJ2 hC hg hΓ =>
      .joinOrF (fun j => toVi (prem j)) hJ1 hJ2 hC hg hΓ
  | _, _, _, .joinCirc prem hJ1 hJ2 hcirc hZ hg hΓ =>
      .joinCirc (fun j => toVi (prem j)) hJ1 hJ2 hcirc
        (restrict_keptChain _) (.ups hZ) hg
        (hΓ.trans joinCtxOr_eq_base)
  | _, _, _, .joinCircP prem dps hJ1 hJ2 hJ5 hJ7s hDs hZ hg hΓ =>
      .joinCircP (fun j => toVi (prem j)) (fun i => toVr (dps i))
        hJ1 hJ2 hJ5 hJ7s hDs hZ hg hΓ

def toVi {G : Form} : ∀ {St Th : List Form} {C : Form},
    FRJi G St Th C → FRJVi G St Th C
  | _, _, _, .axI F hF hg hTh => .axI F hF hg hTh
  | _, _, _, .andI1 d hg => .andI1 (toVi d) hg
  | _, _, _, .andI2 d hg => .andI2 (toVi d) hg
  | _, _, _, .orI d₁ d₂ h₁ h₂ hg hSt hTh =>
      .orI (toVi d₁) (toVi d₂) h₁ h₂ hg hSt hTh
  | _, _, _, .impInI d hpre hdisj hA hg hSt hTh =>
      .impInI (toVi d) hpre hdisj hA hg hSt hTh
  | _, _, _, .impNotIn d hTh hA hAnot hg =>
      .impNotIn (toVr d) hTh hA hAnot hg
  | _, _, _, .circNotIn d htag hTh hg =>
      .circNotIn (toVr d) htag hTh hg
  | _, _, _, .axIC F ats hats hFf hg hTh => .axIC F ats hats hFf hg hTh

end

theorem provableV_of_provable {G : Form} (h : Provable G) : ProvableV G := by
  obtain ⟨t, Γ, ⟨d⟩⟩ := h
  exact ⟨t, Γ, ⟨toVr d⟩⟩

end FRJ
