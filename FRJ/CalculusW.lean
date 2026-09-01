/-
# FRJW — FRJV with `Lift`, without `⊃∉`

FRJW is a NEW calculus (`docs/frjw-plan.md`): `FRJVr`/`FRJVi`
(`FRJ/CalculusV.lean`) with one rule added and one deleted, transcribed
as a separate mutual family `FRJWr`/`FRJWi`.  Nothing in this campaign
modifies the V-family, and no FRJV theorem is inherited by renaming or
aliasing: every result about FRJW — soundness included — is proved
afresh over these constructors.  If the families are ever merged, the
merged system gets a third name (FRJ◯); until then results must not
migrate silently between the names.

An object of `FRJWr`/`FRJWi` is a DISPROOF (regular / irregular).
"Proof" is reserved for the provability calculi — Gbu◯, LaxND, G4c, SC.

**Added — `lift` (working name `(R^bar)`, `wip/rbar.lean`).**  A regular
disproof becomes an irregular one over any retained `Ĝ`-context inside
the closure of its own context:

        Γ ⇒ C          Θ ⊆ Ĝ,   Θ ⊆ Cl(Γ)
    ─────────────────────────────────────────  (Lift)
                   ∅ ; Θ → C

Its soundness clause is `not_force_of_rootAbove` (`wip/rbar.lean`): the
regular component's root sits above the target world and refutes `C`,
and forcing is monotone.

**Deleted — `⊃∉` (`impNotIn`).**  It is `lift` composed with `⊃∈`: from
`d : Γ ⇒ B` and `Cl(Γ) ∋ A`, `⊃∈` gives `Γ ⇒ A ⊃ B` with no side
condition, and `lift` gives `∅ ; Θ → A ⊃ B`.  `⊃∉`'s extra condition
`¬ Cl(Θ) ∋ A` is not needed.  The reconstruction is stage W2's
conservativity map.

**Kept — `◯∉` (`circNotIn`).**  Not redundant: its premise is a regular
disproof of `Z`, not of `◯Z`, so it climbs the modality and `lift` does
not.  Every other FRJV rule is transcribed verbatim.  The shared context
formers (`joinCtxAtVBase`, `joinCtxOrVBase`, `thPool`, and the paper
formers from `FRJ/Calculus.lean`) are DEFINITIONS, imported and reused;
theorems are not.

Fidelity / divergence log: `docs/frjw-plan.md`.
-/
import FRJ.CalculusV
import Meta.Slime

namespace FRJ

open Form

/-! ## The calculus -/

mutual

/-- Regular disproofs of FRJW.  Identical to `FRJVr` except that the
irregular premises are `FRJWi`. -/
inductive FRJWr (G : Form) : Tag → List Form → Form → Type
  | axR (F : Form) (hF : F.isPrime) (hgoal : F ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ rm (gAt G) F) :
      FRJWr G .barren Γ' F
  | andR1 {t : Tag} {Γ : List Form} {A₁ A₂ : Form}
      (d : FRJWr G t Γ A₁) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJWr G t Γ (.and A₁ A₂)
  | andR2 {t : Tag} {Γ : List Form} {A₁ A₂ : Form}
      (d : FRJWr G t Γ A₂) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJWr G t Γ (.and A₁ A₂)
  | impIn {t : Tag} {Γ : List Form} {A B : Form}
      (d : FRJWr G t Γ B) (hA : Clo Γ A) (hgoal : Form.imp A B ∈ sfR G) :
      FRJWr G t Γ (.imp A B)
  | circIn {t : Tag} {Γ : List Form} {Z : Form}
      (d : FRJWr G t Γ Z)
      (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z)
      (hgoal : Form.circ Z ∈ sfR G) :
      FRJWr G t Γ (.circ Z)
  /-- `⋈^At` with the kept zone: `Σ^at, Θ^at \ {F}, Σ^imp, kept` where
      `kept` is a `KeptChain` over the base context. -/
  | joinAt {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {kept : List Form}
      (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hcirc : unionAll (fun j => circPart (stab j)) = [])
      (hkc : KeptChain (upsilon rhs) (joinCtxAtVBase stab th F)
        (thPool th) kept)
      (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
      (hgoal : F ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtVBase stab th F ++ kept) :
      FRJWr G .barren Γ' F
  | joinAtP {n k : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form} {t' : Tag}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
      (dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i))
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
      FRJWr G t' Γ' F
  | joinAtF {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {F : Form}
      (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hF : F.isPrime) (hFnot : F ∉ unionAll (fun j => atPart (stab j)))
      (hgoal : F ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxAtF stab th rhs F) :
      FRJWr G .blocked Γ' F
  /-- `⋈^∨` with the kept zone and `RefAt`-relaxed disjunct conditions. -/
  | joinOr {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {kept : List Form}
      (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
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
      FRJWr G .barren Γ' (.or C₁ C₂)
  | joinOrP {n k : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form} {t' : Tag}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
      (dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i))
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
      FRJWr G t' Γ' (.or C₁ C₂)
  | joinOrF {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {C₁ C₂ : Form}
      (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        A ∈ upsilon rhs)
      (hC : C₁ ∈ upsilon rhs ∧ C₂ ∈ upsilon rhs)
      (hgoal : Form.or C₁ C₂ ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrF stab th rhs) :
      FRJWr G .blocked Γ' (.or C₁ C₂)
  /-- `⋈^◯` with the kept zone, the `RefAt`-relaxed body condition, and
      the `RefAt`-relaxed barren (J2): a stable-zone implication needs
      its antecedent refuted at the root, and `RefAt` over the
      conclusion context certifies exactly that (sound by
      `refAt_refutes_sf`; the strict `A ∈ Υ` is the `.ups` instance).
      Relaxed 2026-09-01 with Matthew's sign-off — the FRJW joins may
      diverge from FRJV here; `⋈^At`/`⋈^∨` keep the strict (J2) until
      a manufacture needs more. -/
  | joinCirc {n : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {Z : Form} {kept : List Form}
      (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
      (hJ1 : ∀ i j, i ≠ j → stab i ⊆ stab j ++ th j)
      (hJ2 : ∀ A B : Form, Form.imp A B ∈ unionAll (fun j => impPart (stab j)) →
        RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) A)
      (hcirc : unionAll (fun j => circPart (stab j)) = [])
      (hkc : KeptChain (upsilon rhs) (joinCtxOrVBase stab th)
        (thPool th) kept)
      (hZ : RefAt true (upsilon rhs) (joinCtxOrVBase stab th ++ kept) Z)
      (hgoal : Form.circ Z ∈ sfR G)
      {Γ' : List Form} (hΓ : Γ' ≐ joinCtxOrVBase stab th ++ kept) :
      FRJWr G .barren Γ' (.circ Z)
  | joinCircP {n k : Nat} {stab th : Fin (n + 1) → List Form}
      {rhs : Fin (n + 1) → Form} {Z : Form}
      {tps : Fin (k + 1) → Tag} {Δs : Fin (k + 1) → List Form}
      {Ds : Fin (k + 1) → Form}
      (prem : ∀ j, FRJWi G (stab j) (th j) (rhs j))
      (dps : ∀ i, FRJWr G (tps i) (Δs i) (Ds i))
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
      FRJWr G (.chain Z) Γ' (.circ Z)

/-- Irregular disproofs of FRJW: the `FRJVi` rules with `⊃∉`
(`impNotIn`) deleted and `lift` added in its place. -/
inductive FRJWi (G : Form) : List Form → List Form → Form → Type
  | axI (F : Form) (hF : F.isPrime) (hgoal : F ∈ sfR G)
      {Th' : List Form} (hTh : Th' ≐ (rm (gAt G) F) ++ gImp G ++ gCirc G) :
      FRJWi G [] Th' F
  | andI1 {St Th : List Form} {A₁ A₂ : Form}
      (d : FRJWi G St Th A₁) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJWi G St Th (.and A₁ A₂)
  | andI2 {St Th : List Form} {A₁ A₂ : Form}
      (d : FRJWi G St Th A₂) (hgoal : Form.and A₁ A₂ ∈ sfR G) :
      FRJWi G St Th (.and A₁ A₂)
  | orI {St₁ Th₁ St₂ Th₂ : List Form} {C₁ C₂ : Form}
      (d₁ : FRJWi G St₁ Th₁ C₁) (d₂ : FRJWi G St₂ Th₂ C₂)
      (h₁ : St₁ ⊆ St₂ ++ Th₂) (h₂ : St₂ ⊆ St₁ ++ Th₁)
      (hgoal : Form.or C₁ C₂ ∈ sfR G)
      {St' Th' : List Form} (hSt : St' ≐ St₁ ++ St₂) (hTh : Th' ≐ cap Th₁ Th₂) :
      FRJWi G St' Th' (.or C₁ C₂)
  | impInI {St Th Lam ThLam : List Form} {A B : Form}
      (d : FRJWi G St ThLam B) (hpre : ThLam ≐ Th ++ Lam)
      (hdisj : cap Th Lam = []) (hA : Clo (St ++ Lam) A)
      (hgoal : Form.imp A B ∈ sfR G)
      {St' Th' : List Form} (hSt : St' ≐ St ++ Lam) (hTh : Th' ≐ Th) :
      FRJWi G St' Th' (.imp A B)
  /-- `Lift`: a regular disproof becomes an irregular one over any
      retained `Ĝ`-context inside the closure of its own context. -/
  | lift {t : Tag} {Γ Th : List Form} {C : Form}
      (d : FRJWr G t Γ C)
      (hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G) :
      FRJWi G [] Th C
  | circNotIn {t : Tag} {Γ Th : List Form} {Z : Form}
      (d : FRJWr G t Γ Z)
      (htag : t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z)
      (hTh : ∀ X ∈ Th, Clo Γ X ∧ X ∈ gHat G)
      (hgoal : Form.circ Z ∈ sfR G) :
      FRJWi G [] Th (.circ Z)
  | axIC (F : Form) (ats : List Form) (hats : ats ⊆ gAt G)
      (hFf : classForce ats F = false) (hgoal : Form.circ F ∈ sfR G)
      {Th' : List Form} (hTh : Th' ≐ vacZoneA G ats) :
      FRJWi G [] Th' (.circ F)

end

/-- `G` has a (regular, root) FRJW disproof.  This is the W-family
analogue of `ProvableV`, renamed so it reads the right way round: an
FRJW object DISPROVES its goal. -/
def DisprovableW (G : Form) : Prop :=
  ∃ (t : Tag) (Γ : List Form), Nonempty (FRJWr G t Γ G)

/-! ## Transport: contexts are sets, in the W-family too -/

def transportWr {G : Form} : ∀ {t : Tag} {Γ Γ' : List Form} {C : Form},
    FRJWr G t Γ C → Γ ≐ Γ' → FRJWr G t Γ' C
  | _, _, _, _, .axR F hF hg hΓ, h => .axR F hF hg (h.symm.trans hΓ)
  | _, _, _, _, .andR1 d hg, h => .andR1 (transportWr d h) hg
  | _, _, _, _, .andR2 d hg, h => .andR2 (transportWr d h) hg
  | _, _, _, _, .impIn d hA hg, h =>
      .impIn (transportWr d h) (clo_mono h.subset hA) hg
  | _, _, _, _, .circIn d htag hg, h =>
      .circIn (transportWr d h)
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

/-! ## Stage W2 — conservativity: FRJV embeds

Every FRJV disproof is an FRJW disproof, at the same indices.  The only
case that is not the identity on the rule name is `impNotIn`,
reconstructed as `lift` composed with `⊃∈`: from `d : Γ ⇒ B` and
`Cl(Γ) ∋ A`, `impIn` gives `Γ ⇒ A ⊃ B`, and `lift` retains the same `Θ`
(`⊃∉`'s `hTh` is verbatim `lift`'s side condition).  `⊃∉`'s extra
condition `¬ Cl(Θ) ∋ A` (`hAnot`) is discarded — it is not needed.

This is what licenses reusing the FRJV corpus over FRJW; it is proved
BEFORE soundness (W3) for exactly that reason. -/

mutual

/-- Every regular FRJV disproof is a regular FRJW disproof. -/
def toWr {G : Form} : ∀ {t : Tag} {Γ : List Form} {C : Form},
    FRJVr G t Γ C → FRJWr G t Γ C
  | _, _, _, .axR F hF hg hΓ => .axR F hF hg hΓ
  | _, _, _, .andR1 d hg => .andR1 (toWr d) hg
  | _, _, _, .andR2 d hg => .andR2 (toWr d) hg
  | _, _, _, .impIn d hA hg => .impIn (toWr d) hA hg
  | _, _, _, .circIn d htag hg => .circIn (toWr d) htag hg
  | _, _, _, .joinAt prem hJ1 hJ2 hcirc hkc hF hFnot hg hΓ =>
      .joinAt (fun j => toWi (prem j)) hJ1 hJ2 hcirc hkc hF hFnot hg hΓ
  | _, _, _, .joinAtP prem dps hJ1 hJ2 hJ5 hJ7s htag hF hFnot hg hΓ =>
      .joinAtP (fun j => toWi (prem j)) (fun i => toWr (dps i))
        hJ1 hJ2 hJ5 hJ7s htag hF hFnot hg hΓ
  | _, _, _, .joinAtF prem hJ1 hJ2 hF hFnot hg hΓ =>
      .joinAtF (fun j => toWi (prem j)) hJ1 hJ2 hF hFnot hg hΓ
  | _, _, _, .joinOr prem hJ1 hJ2 hcirc hkc hC hg hΓ =>
      .joinOr (fun j => toWi (prem j)) hJ1 hJ2 hcirc hkc hC hg hΓ
  | _, _, _, .joinOrP prem dps hJ1 hJ2 hJ5 hJ7s htag hC hg hΓ =>
      .joinOrP (fun j => toWi (prem j)) (fun i => toWr (dps i))
        hJ1 hJ2 hJ5 hJ7s htag hC hg hΓ
  | _, _, _, .joinOrF prem hJ1 hJ2 hC hg hΓ =>
      .joinOrF (fun j => toWi (prem j)) hJ1 hJ2 hC hg hΓ
  | _, _, _, .joinCirc prem hJ1 hJ2 hcirc hkc hZ hg hΓ =>
      .joinCirc (fun j => toWi (prem j)) hJ1
        (fun A B h => .ups (hJ2 A B h)) hcirc hkc hZ hg hΓ
  | _, _, _, .joinCircP prem dps hJ1 hJ2 hJ5 hJ7s hDs hZ hg hΓ =>
      .joinCircP (fun j => toWi (prem j)) (fun i => toWr (dps i))
        hJ1 hJ2 hJ5 hJ7s hDs hZ hg hΓ

/-- Every irregular FRJV disproof is an irregular FRJW disproof.  The
`impNotIn` case is the reconstruction `lift (impIn d hA hgoal) hTh`;
`hAnot` is discarded. -/
def toWi {G : Form} : ∀ {St Th : List Form} {C : Form},
    FRJVi G St Th C → FRJWi G St Th C
  | _, _, _, .axI F hF hg hTh => .axI F hF hg hTh
  | _, _, _, .andI1 d hg => .andI1 (toWi d) hg
  | _, _, _, .andI2 d hg => .andI2 (toWi d) hg
  | _, _, _, .orI d₁ d₂ h₁ h₂ hg hSt hTh =>
      .orI (toWi d₁) (toWi d₂) h₁ h₂ hg hSt hTh
  | _, _, _, .impInI d hpre hdisj hA hg hSt hTh =>
      .impInI (toWi d) hpre hdisj hA hg hSt hTh
  | _, _, _, .impNotIn d hTh hA _hAnot hg =>
      .lift (.impIn (toWr d) hA hg) hTh
  | _, _, _, .circNotIn d htag hTh hg =>
      .circNotIn (toWr d) htag hTh hg
  | _, _, _, .axIC F ats hats hFf hg hTh => .axIC F ats hats hFf hg hTh

end

/-- **Conservativity over FRJV**, at the judgment level: whatever FRJV
disproves, FRJW disproves. -/
theorem disprovableW_of_provableV {G : Form} (h : ProvableV G) :
    DisprovableW G := by
  obtain ⟨t, Γ, ⟨d⟩⟩ := h
  exact ⟨t, Γ, ⟨toWr d⟩⟩

/-- info: 'FRJ.disprovableW_of_provableV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms disprovableW_of_provableV

/-! ## Stage-W1 gate: no computed index in any constructor's return type

`#rules FRJWr` / `#rules FRJWi` print the rule tables for inspection
against `FRJ/CalculusV.lean` and the plan; they are run from a scratch
file, not pinned here. -/

/--
info: FRJ.FRJWr — 3 indices, 13 constructors, 0 carrying green slime

  clean: axR, andR1, andR2, impIn, circIn, joinAt, joinAtP, joinAtF, joinOr, joinOrP, joinOrF, joinCirc, joinCircP
-/
#guard_msgs in
#slime FRJWr

/--
info: FRJ.FRJWi — 3 indices, 8 constructors, 0 carrying green slime

  clean: axI, andI1, andI2, orI, impInI, lift, circNotIn, axIC
-/
#guard_msgs in
#slime FRJWi

end FRJ
