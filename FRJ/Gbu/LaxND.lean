/-
# `Gbu◯(G)` is sound for natural deduction: the syntactic bridge

Every rule of `Gbu◯(G)` is admissible in `LaxND` (`LaxLogic/PLLNDCore.lean`):
the intuitionistic rules are the natural-deduction rules under the
membership-based `iden`, `L◯` at a `◯`-goal is `laxElim`, `R◯` is
`laxIntro`, and `≐`-contexts are handled by `LaxND.rename`.  So a `Gbu◯`
derivation translates, constructor for constructor, into a natural
deduction derivation of the same sequent read through `toPLL`.

Composed with the dichotomy (`gbuw_complete`) and FRJW soundness
(`soundnessW`), this is the syntactic bridge from the crown's SEMANTIC
`PLL` (validity in every `FRJ.Kripke` model, `FRJ/Basic.lean:567`) to
`LaxND`-provability, and back through `FRJ.Bridge.valid_of_derivable`:

    PLL (ofPLL φ) ↔ Nonempty (LaxND [] φ)

Route chosen over the finite-model-property bridge on 2026-09-02: the
FMP's finite models are preorders, `FRJ.Kripke` requires a poset, and
the ≤-quotient does not preserve `◯`-forcing (four-world witness,
kernel-checked).  This route is choice-free and yields the finite POSET
model property as a corollary.
-/
import FRJ.Gbu.Circ
import FRJ.Bridge

namespace FRJ.Gbu

open PLLND

/-! ## Helpers: membership and `≐`-transport through the syntax map -/

private theorem mem_map_toPLL {Γ : List Form} {A : Form} (h : A ∈ Γ) :
    toPLL A ∈ Γ.map toPLL :=
  List.mem_map_of_mem h

/-- Transport a derivation along a set-inclusion of `Form`-contexts. -/
private def renameSub {Δ Γ : List Form} {φ : PLLFormula}
    (H : ∀ X, X ∈ Δ → X ∈ Γ) (p : LaxND (Δ.map toPLL) φ) :
    LaxND (Γ.map toPLL) φ :=
  p.rename (fun ψ h => by
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp h
    exact List.mem_map_of_mem (H A hA))

private theorem sub_of_ctxEq {Γ Ψ : List Form} {X : Form} (hΓ : Γ ≐ X :: Ψ) :
    ∀ Y, Y ∈ Ψ → Y ∈ Γ :=
  fun Y hY => (hΓ Y).mpr (List.mem_cons_of_mem _ hY)

private theorem head_of_ctxEq {Γ Ψ : List Form} {X : Form} (hΓ : Γ ≐ X :: Ψ) :
    X ∈ Γ :=
  (hΓ X).mpr List.mem_cons_self

private theorem cons_sub {Δ Γ : List Form} {X : Form} (H : ∀ Y, Y ∈ Δ → Y ∈ Γ) :
    ∀ Y, Y ∈ X :: Δ → Y ∈ X :: Γ := by
  intro Y hY
  rcases List.mem_cons.mp hY with rfl | hY
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (H Y hY)

/-- Cut: substitute a derivation for a hypothesis (`⊃I` then `⊃E`). -/
private def cut {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (p : LaxND Γ φ) (q : LaxND (φ :: Γ) ψ) : LaxND Γ ψ :=
  .impElim (.impIntro q) p

/-! ## The translation -/

mutual

/-- Regular `Gbu◯` sequents are `LaxND`-derivable. -/
def laxOfR {G : Form} : ∀ {Γ : List Form} {C : Form},
    GbuRC G Γ C → LaxND (Γ.map toPLL) (toPLL C)
  | _, _, .ax A hΓ => .iden (mem_map_toPLL (head_of_ctxEq hΓ))
  | _, _, .lbot C hΓ =>
      .falsoElim _ (.iden (mem_map_toPLL (head_of_ctxEq hΓ)))
  | Γ, _, .landL (A := A) (B := B) d hΓ =>
      let ab : LaxND (Γ.map toPLL) (.and (toPLL A) (toPLL B)) :=
        .iden (mem_map_toPLL (head_of_ctxEq hΓ))
      let d' : LaxND ((A :: B :: Γ).map toPLL) _ :=
        renameSub (cons_sub (cons_sub (sub_of_ctxEq hΓ))) (laxOfR d)
      cut (.andElim2 ab) (cut ((LaxND.andElim1 ab).weaken _) d')
  | _, _, .randR d₁ d₂ => .andIntro (laxOfR d₁) (laxOfR d₂)
  | Γ, _, .lorL (A := A) (B := B) d₁ d₂ hΓ =>
      .orElim (.iden (mem_map_toPLL (head_of_ctxEq hΓ)))
        (renameSub (Γ := A :: Γ) (cons_sub (sub_of_ctxEq hΓ)) (laxOfR d₁))
        (renameSub (Γ := B :: Γ) (cons_sub (sub_of_ctxEq hΓ)) (laxOfR d₂))
  | _, _, .rorR1 d => .orIntro1 (laxOfI d)
  | _, _, .rorR2 d => .orIntro2 (laxOfI d)
  | Γ, _, .limpL (A := A) (B := B) d₁ d₂ hΓ =>
      let imp : LaxND (Γ.map toPLL) (.ifThen (toPLL A) (toPLL B)) :=
        .iden (mem_map_toPLL (head_of_ctxEq hΓ))
      let a : LaxND (Γ.map toPLL) (toPLL A) :=
        renameSub (fun Y hY => (hΓ Y).mpr hY) (laxOfI d₁)
      cut (.impElim imp a)
        (renameSub (Γ := B :: Γ) (cons_sub (sub_of_ctxEq hΓ)) (laxOfR d₂))
  | _, _, .rimpI d _ => .impIntro ((laxOfR d).weaken _)
  | _, _, .rimpNI d _ => .impIntro (laxOfR d)
  | Γ, _, .lcirc (Z := Z) d _ hΓ =>
      .laxElim (.iden (mem_map_toPLL (head_of_ctxEq hΓ)))
        (renameSub (Γ := Z :: Γ) (cons_sub (sub_of_ctxEq hΓ)) (laxOfR d))
  | _, _, .rcirc d _ => .laxIntro (laxOfI d)

/-- Irregular `Gbu◯` sequents are `LaxND`-derivable. -/
def laxOfI {G : Form} : ∀ {Γ : List Form} {C : Form},
    GbuIC G Γ C → LaxND (Γ.map toPLL) (toPLL C)
  | _, _, .ax A hΓ => .iden (mem_map_toPLL (head_of_ctxEq hΓ))
  | _, _, .randI d₁ d₂ => .andIntro (laxOfI d₁) (laxOfI d₂)
  | _, _, .rorI1 d => .orIntro1 (laxOfI d)
  | _, _, .rorI2 d => .orIntro2 (laxOfI d)
  | _, _, .rimpII d _ => .impIntro ((laxOfI d).weaken _)
  | _, _, .rimpNII d _ => .impIntro (laxOfR d)
  | Γ, _, .lcircI (Z := Z) d _ hΓ =>
      .laxElim (.iden (mem_map_toPLL (head_of_ctxEq hΓ)))
        (renameSub (Γ := Z :: Γ) (cons_sub (sub_of_ctxEq hΓ)) (laxOfI d))
  | Γ, _, .limpLI (A := A) (B := B) d₁ d₂ _ _ hΓ =>
      let imp : LaxND (Γ.map toPLL) (.ifThen (toPLL A) (toPLL B)) :=
        .iden (mem_map_toPLL (head_of_ctxEq hΓ))
      let a : LaxND (Γ.map toPLL) (toPLL A) :=
        renameSub (fun Y hY => (hΓ Y).mpr hY) (laxOfI d₁)
      cut (.impElim imp a)
        (renameSub (Γ := B :: Γ) (cons_sub (sub_of_ctxEq hΓ)) (laxOfI d₂))
  | _, _, .lbotI _ hΓ =>
      .falsoElim _ (.iden (mem_map_toPLL (head_of_ctxEq hΓ)))
  | Γ, _, .landLI (A := A) (B := B) d _ hΓ =>
      let ab : LaxND (Γ.map toPLL) (.and (toPLL A) (toPLL B)) :=
        .iden (mem_map_toPLL (head_of_ctxEq hΓ))
      let d' : LaxND ((A :: B :: Γ).map toPLL) _ :=
        renameSub (cons_sub (cons_sub (sub_of_ctxEq hΓ))) (laxOfI d)
      cut (.andElim2 ab) (cut ((LaxND.andElim1 ab).weaken _) d')
  | Γ, _, .lorLI (A := A) (B := B) d₁ d₂ _ hΓ =>
      .orElim (.iden (mem_map_toPLL (head_of_ctxEq hΓ)))
        (renameSub (Γ := A :: Γ) (cons_sub (sub_of_ctxEq hΓ)) (laxOfI d₁))
        (renameSub (Γ := B :: Γ) (cons_sub (sub_of_ctxEq hΓ)) (laxOfI d₂))
  | _, _, .rcircI d _ => .laxIntro (laxOfI d)

end

/-! ## The bridge -/

/-- **Syntactic soundness of `Gbu◯(G)`**: a provable goal is a natural
deduction theorem. -/
theorem laxND_of_provableGbuC {G : Form} (h : ProvableGbuC G) :
    Nonempty (LaxND [] (toPLL G)) :=
  let ⟨d⟩ := h
  ⟨laxOfR d⟩

/-- info: 'FRJ.Gbu.laxND_of_provableGbuC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms laxND_of_provableGbuC

end FRJ.Gbu
