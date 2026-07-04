import LaxLogic.PLLFormula
import LaxLogic.PLLAxiom

open PLLFormula

inductive LaxND : (List PLLFormula)→ PLLFormula → Prop -- Natural deduction for PLL
--  | atom : (Γ Δ : List PLLFormula) → (a : String) → LaxND (Γ ++ [prop a] ++ Δ) (prop a)
-- this first is not sufficiently general
  | iden : (Γ Δ : List PLLFormula) → (φ : PLLFormula) → LaxND (Γ ++ φ :: Δ) φ
  | falsoElim : {Γ : List PLLFormula} → (φ : PLLFormula) → LaxND Γ falsePLL → LaxND Γ φ
  | impIntro : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxND (Γ ++ φ :: Δ) ψ → LaxND (Γ ++ Δ) (ifThen φ ψ)
  | impElim  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ (ifThen φ ψ) →
    LaxND Γ φ → LaxND Γ ψ
  | andIntro : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ φ → LaxND Γ ψ →
    LaxND Γ (and φ ψ)
  | andElim1 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ (and φ ψ) → LaxND Γ φ
  | andElim2 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ (and φ ψ) → LaxND Γ ψ
  | orIntro1 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ φ → LaxND Γ (or φ ψ)
  | orIntro2 : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxND Γ ψ → LaxND Γ (or φ ψ)
  | orElim   : {Γ Δ : List PLLFormula} → {φ ψ χ : PLLFormula} →
      LaxND (Γ ++ φ :: Δ) χ →
      LaxND (Γ ++ ψ :: Δ) χ → LaxND (Γ ++ Δ) χ
  | laxIntro : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxND Γ φ →
      LaxND Γ (somehow φ)
  | laxElim : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxND (Γ ++ Δ) (somehow φ) → LaxND (Γ ++ φ :: Δ) (somehow ψ) →
      LaxND (Γ ++ Δ) (somehow ψ)
--  | laxFlatten : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxND Γ (somehow (somehow φ)) → LaxND Γ (somehow φ)
-- this last is derivable

infix:70 " ⊢- " => LaxND -- turnstile

def LaxValid (φ : PLLFormula) : Prop := ([] : List PLLFormula) ⊢- φ

open LaxND

lemma OI (φ : PLLFormula) : [] ⊢- ifThen φ (somehow φ) := impIntro (laxIntro (iden [] [] φ))
lemma OItrue (φ : PLLFormula) : LaxValid <| ifThen φ (somehow φ) := by apply OI

lemma OSL (φ ψ : PLLFormula) : [] ⊢- ifThen (somehow (and φ ψ)) (and (somehow φ) (somehow ψ)) := by
  apply @impIntro [] [] ;
  apply @andIntro;
  apply @laxElim [(φ.and ψ).somehow] [] (φ.and ψ);
  apply iden [] ; apply laxIntro
  apply andElim1 ; apply iden
  apply @laxElim [(φ.and ψ).somehow] [] (φ.and ψ);
  apply iden [] ; apply laxIntro
  apply andElim2 ; apply iden
lemma OSLtrue (φ ψ : PLLFormula) : LaxValid <| ifThen (somehow (and φ ψ)) (and (somehow φ) (somehow ψ)) := by apply OSL

lemma OSR (φ ψ : PLLFormula) : [] ⊢- ifThen (and (somehow φ) (somehow ψ)) (somehow (and φ ψ)) := by
  apply @impIntro [] [] ; -- simp -- makes progress but not needed
  apply @laxElim [φ.somehow.and ψ.somehow] [] φ ; -- simp
  apply andElim1; apply iden []; -- simp
  apply @laxElim [φ.somehow.and ψ.somehow] [φ] ψ ; -- simp
  apply andElim2; apply iden []; -- simp
  apply laxIntro; apply andIntro
  apply iden [φ.somehow.and ψ.somehow, ψ] [] φ
  apply iden [φ.somehow.and ψ.somehow] [φ] ψ   -- note it looks "out of order" but makes same context as above
lemma OSRtrue (φ ψ : PLLFormula) : LaxValid <| ifThen (and (somehow φ) (somehow ψ)) (somehow (and φ ψ)) := by apply OSR

lemma OMoops {Γ : List PLLFormula} {φ : PLLFormula} : (Γ ++ []) /- awk -/⊢- ifThen (somehow (somehow φ)) (somehow φ) :=
  impIntro (
    laxElim
      (iden Γ [] (somehow (somehow φ)))
      (iden Γ [φ.somehow.somehow] (somehow φ))
  )
-- well I did think that way of permuting contexts might throw up problems! simp helps interactively
lemma OM {φ : PLLFormula} : [] ⊢- ifThen (somehow (somehow φ)) (somehow φ) := by
  apply @impIntro [] ; simp;  apply @laxElim [(somehow (somehow φ))] [] (somehow φ) ; simp;
  apply iden [] ; apply iden
lemma OMtrue (φ : PLLFormula) : LaxValid <| ifThen (somehow (somehow φ)) (somehow φ) := by apply OM

section Conservativity

-- Define what it means for a formula to be in IPL (no somehow modality)
def isIPLFormula : PLLFormula → Prop
  | PLLFormula.prop _  => true
  | falsePLL    => true
  | ifThen φ ψ  => isIPLFormula φ ∧ isIPLFormula ψ
  | PLLFormula.and φ ψ => isIPLFormula φ ∧ isIPLFormula ψ
  | PLLFormula.or φ ψ  => isIPLFormula φ ∧ isIPLFormula ψ
  | somehow _   => false

def isIPLFormulaC : PLLFormula → Bool
  | PLLFormula.prop _  => true
  | falsePLL    => true
  | ifThen φ ψ  => isIPLFormulaC φ ∧ isIPLFormulaC ψ
  | PLLFormula.and φ ψ => isIPLFormulaC φ && isIPLFormulaC ψ
  | PLLFormula.or φ ψ  => isIPLFormulaC φ && isIPLFormulaC ψ
  | somehow _   => false

@[match_pattern] -- is this needed, and if so, why?
inductive LaxNDτ: (List PLLFormula)→ PLLFormula → Type -- ND for PLL, proof term version
  | idenτ : (Γ Δ : List PLLFormula) → (φ : PLLFormula) → LaxNDτ (Γ ++ φ :: Δ) φ
  | falsoElimτ  : {Γ : List PLLFormula} → (φ : PLLFormula) → LaxNDτ Γ falsePLL → LaxNDτ Γ φ
  | impIntroτ  : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxNDτ (Γ ++ φ :: Δ) ψ → LaxNDτ (Γ ++ Δ) (ifThen φ ψ)
  | impElimτ   : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ (ifThen φ ψ) →
    LaxNDτ Γ φ → LaxNDτ Γ ψ
  | andIntroτ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ φ → LaxNDτ Γ ψ →
    LaxNDτ Γ (and φ ψ)
  | andElim1τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ (and φ ψ) → LaxNDτ Γ φ
  | andElim2τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ (and φ ψ) → LaxNDτ Γ ψ
  | orIntro1τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ φ → LaxNDτ Γ (or φ ψ)
  | orIntro2τ  : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxNDτ Γ ψ → LaxNDτ Γ (or φ ψ)
  | orElimτ    : {Γ Δ : List PLLFormula} → {φ ψ χ : PLLFormula} →
      LaxNDτ (Γ ++ φ :: Δ) χ →
      LaxNDτ (Γ ++ ψ :: Δ) χ → LaxNDτ (Γ ++ Δ) χ
  | laxIntroτ  : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxNDτ Γ φ → LaxNDτ Γ (somehow φ)
  | laxElimτ  : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxNDτ (Γ ++ Δ) (somehow φ) → LaxNDτ (Γ ++ φ :: Δ) (somehow ψ) →
      LaxNDτ (Γ ++ Δ) (somehow ψ)

open LaxNDτ

/-! ### A blessed cast API for `LaxNDτ` (the `eqToHom` pattern, §4.4 of the
transport-problem brief).  All equality-transport of proof terms goes through
`castCtx`/`castF` — never raw `▸`/`cast`/`Eq.rec` — so that one small simp set
can cancel and commute every cast. -/

namespace LaxNDτ

/-- Cast a proof term along a context equality. -/
def castCtx {Γ₁ Γ₂ : List PLLFormula} {φ : PLLFormula} (h : Γ₁ = Γ₂)
    (p : LaxNDτ Γ₁ φ) : LaxNDτ Γ₂ φ :=
  cast (congrArg (fun Γ => LaxNDτ Γ φ) h) p

/-- Cast a proof term along a formula equality. -/
def castF {Γ : List PLLFormula} {φ₁ φ₂ : PLLFormula} (h : φ₁ = φ₂)
    (p : LaxNDτ Γ φ₁) : LaxNDτ Γ φ₂ :=
  cast (congrArg (fun φ => LaxNDτ Γ φ) h) p

@[simp] theorem castCtx_rfl {Γ : List PLLFormula} {φ : PLLFormula}
    (p : LaxNDτ Γ φ) : castCtx rfl p = p := rfl

@[simp] theorem castF_rfl {Γ : List PLLFormula} {φ : PLLFormula}
    (p : LaxNDτ Γ φ) : castF rfl p = p := rfl

@[simp] theorem castCtx_castCtx {Γ₁ Γ₂ Γ₃ : List PLLFormula} {φ : PLLFormula}
    (h₁ : Γ₁ = Γ₂) (h₂ : Γ₂ = Γ₃) (p : LaxNDτ Γ₁ φ) :
    castCtx h₂ (castCtx h₁ p) = castCtx (h₁.trans h₂) p := by
  subst h₁; subst h₂; rfl

@[simp] theorem castF_castF {Γ : List PLLFormula} {φ₁ φ₂ φ₃ : PLLFormula}
    (h₁ : φ₁ = φ₂) (h₂ : φ₂ = φ₃) (p : LaxNDτ Γ φ₁) :
    castF h₂ (castF h₁ p) = castF (h₁.trans h₂) p := by
  subst h₁; subst h₂; rfl

/-- Normal form: `castF` innermost, `castCtx` outermost. -/
@[simp] theorem castF_castCtx {Γ₁ Γ₂ : List PLLFormula} {φ₁ φ₂ : PLLFormula}
    (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) (p : LaxNDτ Γ₁ φ₁) :
    castF hφ (castCtx hΓ p) = castCtx hΓ (castF hφ p) := by
  subst hΓ; subst hφ; rfl

end LaxNDτ

-- this next is a kind of Cut rule
def impInContext : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxNDτ (Γ ++ Δ) φ → LaxNDτ (Γ ++ φ :: Δ) ψ → LaxNDτ (Γ ++ Δ) ψ := by
      intros Γ Δ φ ψ prf1 prf2
      apply @impElimτ _ φ ψ
      apply impIntroτ; exact prf2; exact prf1

#print impInContext

-- Define what it means for a PLL proof to be an IPL proof
-- more inference could be requested
def isIPLProof1 : (Γ : List PLLFormula) → (φ : PLLFormula) → (prf : LaxNDτ Γ φ) → Prop
  | _, _,  idenτ Γ Δ φ     => isIPLFormula φ -- only you could have a proof in IPL using lax formulae
  | _, _,  falsoElimτ _ prf  => isIPLProof1 _ falsePLL prf
  | _, _,  @impIntroτ Γ Δ φ ψ prf => isIPLProof1 (Γ ++ φ :: Δ) ψ prf
  | _, _,  @impElimτ Γ _ _ prf1 prf2  => isIPLProof1 Γ _ prf1 ∧ isIPLProof1 _ _ prf2
  | _, _,  @andIntroτ _ _ _ prf1 prf2 => isIPLProof1 _ _ prf1 ∧ isIPLProof1 _ _ prf2
  | _, _,  @andElim1τ _ _ _ prf     => isIPLProof1 _ _ prf
  | _, _,  andElim2τ prf => isIPLProof1 _ _ prf
  | _, _,  orIntro1τ prf => isIPLProof1 _ _ prf
  | _, _,  orIntro2τ prf => isIPLProof1 _ _ prf
  | _, _,  orElimτ prf1 prf2 => isIPLProof1 _ _ prf1 ∧ isIPLProof1 _ _ prf2
  | _, _,  laxIntroτ _  => false
  | _, _,  laxElimτ _ _ => false

-- Define what it means for a PLL proof to be an IPL proof
def isIPLProof : {Γ : List PLLFormula} → {φ : PLLFormula} → (prf : LaxNDτ Γ φ) → Prop
  | _, _,  idenτ Γ Δ φ     => isIPLFormula φ -- only you could have a proof in IPL using lax formulae
  | _, _,  falsoElimτ _ prf  => isIPLProof prf
  | _, _,  @impIntroτ Γ Δ φ ψ prf => isIPLProof prf
  | _, _,  @impElimτ Γ _ _ prf1 prf2  => isIPLProof prf1 ∧ isIPLProof prf2
  | _, _,  @andIntroτ _ _ _ prf1 prf2 => isIPLProof prf1 ∧ isIPLProof prf2
  | _, _,  @andElim1τ _ _ _ prf     => isIPLProof prf
  | _, _,  andElim2τ prf => isIPLProof prf
  | _, _,  orIntro1τ prf => isIPLProof prf
  | _, _,  orIntro2τ prf => isIPLProof prf
  | _, _,  orElimτ prf1 prf2 => isIPLProof prf1 ∧ isIPLProof prf2
  | _, _,  laxIntroτ _  => false
  | _, _,  laxElimτ _ _ => false

/-! `isIPLProof` is invariant under the blessed casts (UIP makes these
`subst`-trivial), and computes through `impInContext`.  These three simp
lemmas are what unblock `PLLconservative` below. -/

@[simp] theorem isIPLProof_castCtx {Γ₁ Γ₂ : List PLLFormula} {φ : PLLFormula}
    (h : Γ₁ = Γ₂) (p : LaxNDτ Γ₁ φ) :
    isIPLProof (LaxNDτ.castCtx h p) = isIPLProof p := by
  subst h; rfl

@[simp] theorem isIPLProof_castF {Γ : List PLLFormula} {φ₁ φ₂ : PLLFormula}
    (h : φ₁ = φ₂) (p : LaxNDτ Γ φ₁) :
    isIPLProof (LaxNDτ.castF h p) = isIPLProof p := by
  subst h; rfl

@[simp] theorem isIPLProof_impInContext {Γ Δ : List PLLFormula}
    {φ ψ : PLLFormula} (p₁ : LaxNDτ (Γ ++ Δ) φ) (p₂ : LaxNDτ (Γ ++ φ :: Δ) ψ) :
    isIPLProof (impInContext p₁ p₂) = (isIPLProof p₂ ∧ isIPLProof p₁) := rfl

@[simp]
def eraseSomehow : PLLFormula → PLLFormula
  | PLLFormula.prop a => prop a
  | falsePLL    => falsePLL
  | ifThen φ ψ  => ifThen (eraseSomehow φ) (eraseSomehow ψ)
  | PLLFormula.and φ ψ     => and (eraseSomehow φ) (eraseSomehow ψ)
  | PLLFormula.or φ ψ      => or (eraseSomehow φ) (eraseSomehow ψ)
  | PLLFormula.somehow φ   => eraseSomehow φ

theorem map_append_distrib {α β : Type} (f : α → β) (xs ys : List α) (z : α):
  List.map f (xs ++ z :: ys) = List.map f xs ++ f z :: List.map f ys := by
  simp [List.map_append]

theorem map_append_distrib_sym {α β : Type} (f : α → β) (xs ys : List α) (z : α):
  List.map f xs ++ f z :: List.map f ys = List.map f (xs ++ z :: ys) := by
  simp [List.map_append]

@[simp] lemma isIPLFormula_eraseSomehow (φ : PLLFormula) :
    isIPLFormula (_root_.eraseSomehow φ) := by
  induction φ <;> simp [isIPLFormula, *]

section recursors

def erasePLLProof {Γ : List PLLFormula} {φ : PLLFormula} (h : LaxNDτ Γ φ) :
  LaxNDτ (List.map _root_.eraseSomehow Γ) (_root_.eraseSomehow φ) :=
  match h with
  | idenτ Γ Δ φ =>
    -- Handle identity rule: Γ ++ φ :: Δ ⊢ φ becomes erase(Γ) ++ erase(φ) :: erase(Δ) ⊢ erase(φ)
    let Γ' := List.map _root_.eraseSomehow Γ
    let Δ' := List.map _root_.eraseSomehow Δ
    let φ' := _root_.eraseSomehow φ
    -- how do we actually use definitions above to simplify statement of h1?
    let h1 : List.map _root_.eraseSomehow (Γ ++ φ :: Δ) = List.map _root_.eraseSomehow Γ ++ _root_.eraseSomehow φ :: List.map _root_.eraseSomehow Δ := by -- sorry -- make general lemma outside
      simp[List.map_append, List.map_cons]
    LaxNDτ.castCtx (Eq.symm h1)
        (idenτ (List.map _root_.eraseSomehow Γ) (List.map _root_.eraseSomehow Δ) (_root_.eraseSomehow φ))

  | @impIntroτ Γ Δ φ ψ prf =>
    -- Implication introduction: Γ ++ Δ ⊢ φ → ψ becomes erase(Γ) ++ erase(Δ) ⊢ erase(φ) → erase(ψ)
    let prf' := erasePLLProof prf
    let h1 : List.map _root_.eraseSomehow (Γ ++ φ :: Δ) = List.map _root_.eraseSomehow Γ ++ _root_.eraseSomehow φ :: List.map _root_.eraseSomehow Δ := by
      simp [List.map_append]
    let prf_fix := LaxNDτ.castCtx h1 prf'

    -- now need to fix up proof term to match expected return type; at least 2 more casts needed
    let ans := impIntroτ prf_fix
    let h2 : List.map _root_.eraseSomehow (Γ ++ Δ) =
      List.map _root_.eraseSomehow Γ ++ List.map _root_.eraseSomehow Δ := by
      simp [List.map_append]
    let ans_ctx_fix := LaxNDτ.castCtx (Eq.symm h2) ans
    -- not required -- have h_formula : _root_.eraseSomehow (φ.ifThen ψ) = (_root_.eraseSomehow φ).ifThen (_root_.eraseSomehow ψ) := by simp
    ans_ctx_fix

  | falsoElimτ φ prf =>
    -- False elimination: Γ ⊢ ⊥ → Γ ⊢ φ becomes erase(Γ) ⊢ ⊥ → erase(Γ) ⊢ erase(φ)
    falsoElimτ (_root_.eraseSomehow φ) (erasePLLProof prf)

  | impElimτ prf1 prf2 =>
    -- Implication elimination: Combine erased proofs
    impElimτ (erasePLLProof prf1) (erasePLLProof prf2)

  | andIntroτ prf1 prf2 =>
    -- Conjunction introduction: Combine erased proofs
    andIntroτ (erasePLLProof prf1) (erasePLLProof prf2)

  | andElim1τ prf =>
    -- Conjunction elimination (left)
    andElim1τ (erasePLLProof prf)

  | andElim2τ prf =>
    -- Conjunction elimination (right)
    andElim2τ (erasePLLProof prf)

  | orIntro1τ prf =>
    -- Disjunction introduction (left)
    orIntro1τ (erasePLLProof prf)

  | orIntro2τ prf =>
    -- Disjunction introduction (right)
    orIntro2τ (erasePLLProof prf)

  | @orElimτ Γ Δ φ ψ χ prf1 prf2 =>
    -- Disjunction elimination: Combine erased proofs
    let prf1' := erasePLLProof prf1
    let prf2' := erasePLLProof prf2
    let h1 : List.map _root_.eraseSomehow (Γ ++ φ :: Δ) =
      List.map _root_.eraseSomehow Γ ++ _root_.eraseSomehow φ ::List.map _root_.eraseSomehow Δ := by
      simp [_root_.eraseSomehow, List.map_append]
    let prf1_cxt_fix := LaxNDτ.castCtx h1 prf1'
    let h2 {Δ : List PLLFormula} : List.map _root_.eraseSomehow (Γ ++ Δ) =
      List.map _root_.eraseSomehow Γ ++ List.map _root_.eraseSomehow Δ := by
      simp [List.map_append]
    let prf2_cxt_fix := LaxNDτ.castCtx h2 prf2'

    -- explicit arguments make no difference
    -- @orElimτ (List.map _root_.eraseSomehow Γ) (List.map _root_.eraseSomehow Δ) (_root_.eraseSomehow φ) (_root_.eraseSomehow ψ) (_root_.eraseSomehow χ)
    let ans := orElimτ prf1_cxt_fix prf2_cxt_fix
    let ans_cxt_fix := LaxNDτ.castCtx (Eq.symm h2) ans
    ans_cxt_fix

  | @laxIntroτ Γ φ prf =>
    -- Lax introduction: Erase the inner somehow
    @erasePLLProof Γ φ prf

  | @laxElimτ Γ Δ φ ψ prf1 prf2 =>
  -- For laxElimτ, we need multiple casts
  let prf1' := erasePLLProof prf1
  let prf2' := erasePLLProof prf2

  -- First, handle the context equality
  let h_context1 : List.map _root_.eraseSomehow (Γ ++ Δ) = List.map _root_.eraseSomehow Γ ++ List.map _root_.eraseSomehow Δ := by
    simp [List.map_append]

  -- Then, handle the formula equality for the first premise
  let h_formula1 : _root_.eraseSomehow (somehow φ) = _root_.eraseSomehow φ := by
    simp [_root_.eraseSomehow]
  let prf1_ctx_fix := LaxNDτ.castCtx h_context1 prf1'
  -- Cast the first premise to match the expected type
  let prf1_fix := LaxNDτ.castF h_formula1 prf1_ctx_fix

  -- For prf2', we need to handle the context transformation
  -- The context in prf2' is (Γ ++ φ :: Δ), which needs to be transformed to
  -- (List.map _root_.eraseSomehow Γ ++ _root_.eraseSomehow φ :: List.map _root_.eraseSomehow Δ)
  let h_context2 : List.map _root_.eraseSomehow (Γ ++ φ :: Δ) =
                    List.map _root_.eraseSomehow Γ ++ _root_.eraseSomehow φ :: List.map _root_.eraseSomehow Δ := by
    simp [List.map_append]
  let h_formula2 : _root_.eraseSomehow (somehow ψ) = _root_.eraseSomehow ψ := by
    simp [_root_.eraseSomehow]

  -- Cast prf2' to fix its context
  let prf2_cxt_fix := LaxNDτ.castCtx h_context2 prf2'
  let prf2_fix := LaxNDτ.castF h_formula2 prf2_cxt_fix

   -- Now we can use impInContext with the properly cast arguments
  let ans := impInContext prf1_fix prf2_fix -- notice no laxElimτ
  -- imvert h1_contezt and h_formula2 and put them together
  let ans_cxt_fix := LaxNDτ.castCtx (Eq.symm h_context1) ans
  let ans_fix := LaxNDτ.castF (Eq.symm h_formula2) ans_cxt_fix

  ans_fix

-- The erasePLLProof function is not a recursor, but it is a proof term
-- that can be used to show that the LaxNDτ proof is a valid IPL proof.
end recursors

/-- **Conservativity on proof terms.**  The blessed-cast simp set
(`isIPLProof_castCtx`/`isIPLProof_castF`/`isIPLProof_impInContext`) lets
`isIPLProof` compute straight through every cast in `erasePLLProof`, so each
case reduces to its induction hypotheses. -/
theorem PLLconservativeDirect {Γ : List PLLFormula} {φ : PLLFormula}
    (prf : LaxNDτ Γ φ) : isIPLProof (erasePLLProof prf) := by
  induction prf with
  | idenτ Γ Δ φ => simp [erasePLLProof, isIPLProof]
  | falsoElimτ φ prf ih => exact ih
  | impIntroτ prf ih => simpa [erasePLLProof, isIPLProof] using ih
  | impElimτ prf1 prf2 ih1 ih2 => exact ⟨ih1, ih2⟩
  | andIntroτ prf1 prf2 ih1 ih2 => exact ⟨ih1, ih2⟩
  | andElim1τ prf ih => exact ih
  | andElim2τ prf ih => exact ih
  | orIntro1τ prf ih => exact ih
  | orIntro2τ prf ih => exact ih
  | orElimτ prf1 prf2 ih1 ih2 =>
      simpa [erasePLLProof, isIPLProof] using ⟨ih1, ih2⟩
  | laxIntroτ prf ih => exact ih
  | laxElimτ prf1 prf2 ih1 ih2 =>
      simpa [erasePLLProof, isIPLProof] using ⟨ih2, ih1⟩

theorem erasePLLProof2 {Γ : List PLLFormula} {φ : PLLFormula}
  (h : LaxNDτ Γ φ) : Nonempty (LaxNDτ (List.map _root_.eraseSomehow Γ) (_root_.eraseSomehow φ)) := by
  induction h with
  | idenτ G D f =>
    simp [map_append_distrib] -- Use simp to handle the type mismatch
    exact ⟨ idenτ (List.map _root_.eraseSomehow G) (List.map _root_.eraseSomehow D) (_root_.eraseSomehow f) ⟩
  | @impIntroτ Γ Δ ψ χ prf ih => -- why is this syntax not supported for induction tactic?
    simp [map_append_distrib] at ih; simp
    exact ⟨ impIntroτ ih.some ⟩
  | @falsoElimτ Γ φ prf ih =>
    let ih' := falsoElimτ (_root_.eraseSomehow φ) ih.some
    exact ⟨ ih' ⟩
  | @impElimτ Γ φ ψ prf1 prf2 ih1 ih2 =>
    constructor
    apply impElimτ; exact ih1.some; exact ih2.some
  | @andIntroτ Γ φ ψ prf1 prf2 ih1 ih2 =>
    constructor;
    apply andIntroτ; exact ih1.some; exact ih2.some
  | @andElim1τ Γ φ ψ prf ih =>
    constructor
    apply andElim1τ; exact ih.some
  | @andElim2τ Γ φ ψ prf ih =>
    constructor
    apply andElim2τ; exact ih.some
  | @orIntro1τ Γ φ ψ prf ih =>
    constructor
    apply orIntro1τ; exact ih.some
  | @orIntro2τ Γ φ ψ prf ih =>
    constructor
    apply orIntro2τ; exact ih.some
  | @orElimτ Γ Δ φ ψ χ prf1 prf2 ih1 ih2 =>
    simp; constructor -- we need the simp to handle the type mismatch
    apply orElimτ
    simp[map_append_distrib] at ih1
    exact ih1.some
    simp[map_append_distrib] at ih2
    -- constructor -- a simpler approach but harder to read
    exact ih2.some
  | @laxIntroτ Γ φ prf ih =>
    simp; exact ih  -- the somehow has somehow gone :-)
  | @laxElimτ Γ Δ φ ψ prf1 prf2 ih1 ih2 =>
    simp[map_append_distrib] at ih1
    simp[map_append_distrib] at ih2
    simp; constructor
    apply impInContext
    exact ih1.some; exact ih2.some

theorem PLLconservativeUnprovable
  {Γ : List PLLFormula} {φ : PLLFormula}
  (prf : LaxNDτ Γ φ) :
  isIPLProof (erasePLLProof2 prf).some := sorry -- thought to be unprovable

lemma eraseSomehow_id_on_IPL : ∀ φ, isIPLFormula φ → _root_.eraseSomehow φ = φ
| PLLFormula.prop _, _ => rfl
| falsePLL, _ => rfl
| ifThen φ ψ, ⟨hφ, hψ⟩ =>
    by simp [_root_.eraseSomehow, eraseSomehow_id_on_IPL φ hφ, eraseSomehow_id_on_IPL ψ hψ]
| PLLFormula.and φ ψ, ⟨hφ, hψ⟩ =>
    by simp [_root_.eraseSomehow, eraseSomehow_id_on_IPL φ hφ, eraseSomehow_id_on_IPL ψ hψ]
| PLLFormula.or φ ψ, ⟨hφ, hψ⟩ =>
    by simp [_root_.eraseSomehow, eraseSomehow_id_on_IPL φ hφ, eraseSomehow_id_on_IPL ψ hψ]


theorem PLLconservative_sigma -- now immediate from PLLconservativeDirect
  {Γ : List PLLFormula} {φ : PLLFormula}
  (h : LaxNDτ Γ φ) :
  Nonempty (Σ t : LaxNDτ (List.map _root_.eraseSomehow Γ) (_root_.eraseSomehow φ), PLift (isIPLProof t)) :=
  ⟨⟨erasePLLProof h, ⟨PLLconservativeDirect h⟩⟩⟩

theorem PLLconservative {Γ : List PLLFormula} {φ : PLLFormula}
  (h : LaxNDτ Γ φ) :
  Nonempty (Exists λ t : (LaxNDτ (List.map _root_.eraseSomehow Γ) (_root_.eraseSomehow φ)) => isIPLProof t)
   := ⟨⟨erasePLLProof h, PLLconservativeDirect h⟩⟩

end Conservativity
