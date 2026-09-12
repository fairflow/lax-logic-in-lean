/-
# `LaxLogic.QLL.CLPMachine` — SLD and SLD◯ in one format

Table 2 (`Step`, `CLPOper`) rewrites a flat goal list and forgets the
derivation; Fig. 3 (`ATyped`, `CLPAbstract`) is a proof-tree calculus and
does no rewriting.  This module gives both passes the same operational form:
a state is a *partial proof tree* — a proof tree with open leaves — and a
step expands one open leaf by one rule.  The goal list of Table 2 is the
projection `opens` of the tree, and the proof tree of Theorem 9.4 is the tree
itself once no leaf is open.

**The rules, one format for both machines.**  An open leaf `S` is replaced
by a node whose open leaves are the new goals:

    rule     open leaf S            new node                      store (SLD only)
    top      ⊤                      ⊤                             —
    cstr     B(t̃), isC B            B(t̃)  leaf                    c ∧ B(t̃), if ok
    and      A ∧ B                  ∧I [A] [B]                    —
    orL/orR  A ∨ B                  ∨I₁ [A]  /  ∨I₂ [B]           —
    ex       ∃x.A                   ∃I t [A[t]],  t closed        —
    clause   P(t̃)                   clause w t̃ [S_w[t̃]]           —

`SLD` (`Expand`) runs on a concrete program and threads a store; `SLD◯`
(`ExpandA`) runs on the abstract program `Θ♯`, whose clause heads are all
modal and whose bodies have `⊤` where the constraints were, so `cstr` has
become `top` and there is no store: the constraint is extracted from the
finished tree (`AProof.ext`).  Every judgement of SLD◯ is lax, so the `◯`
appears in no rule; it appears in the QLL derivation that justifies each:

    top      ◯I ⊤I
    and      ◯E, ◯E, ◯I (∧I)
    orL/orR  ◯E, ◯I (∨I₁ / ∨I₂)
    ex       ◯E, ◯I (∃I t)
    clause   ∀E on ∀x̃. S♯ ⊃ ◯P(x̃),  ◯E on the body's ◯S♯,  ⊃E

(these are the cases of `ATyped.prv`).

**Proved here.**

    SLD step  ⟹  Table 2 step on the projections                    (`SLDStep.goal_step`)
    typing is preserved; a closed tree is a `CProof` of the goal      (`Expand.typed`, `PTree.close_typed`)
    c₀ □ [S] ⇝* c □ [p],  p closed to q   ⟹   c ⊣⊢ c₀ ∧ total q     (`SLDSteps.store`, Theorem 9.4 as an invariant)
                                          and  Θ ⊢ total q ⊃ S      (`SLDSteps.prv`)
    SLD step on Θ  ⟹  SLD◯ step on Θ♯ under toA                     (`Expand.toA`, heads not constraints)
    SLD◯ typing preserved; closed ⟹ `AProof`; run ⟹ Θ♯ ⊢ ◯S       (`ExpandA.typed`, `ATree.close_typed`, `SLDCSteps.prv`)

**Not yet built** (statements fixed, in this order): Table 2 step ⟹ SLD
step at the corresponding leaf (the lifting direction of the projection);
SLD◯ step ⟹ SLD step under `toA` when `ok` accepts every store (with
pruning it fails at `cstr`, which is the exact content of pruning); every
`CTyped`/`ATyped` tree is the log of some run (completeness of the machines);
and, as corollaries through `world2_free` and `thm_7_5_canon1/2`,
soundness and completeness with respect to the Herbrand models.
-/
import LaxLogic.QLL.CLPAbstract

namespace LaxLogic.QLL.SLD

/-! ## Partial proof trees -/

/-- A `CProof` with open leaves. -/
inductive PTree where
  | hole (S : Form)
  | top
  | cstr (B : String) (ts : List Tm)
  | andI (p q : PTree)
  | orL (p : PTree)
  | orR (p : PTree)
  | exI (t : Tm) (p : PTree)
  | clause (w : Nat) (ts : List Tm) (p : PTree)
  deriving Repr, Inhabited

/-- The open leaves, left to right: Table 2's goal list. -/
def PTree.opens : PTree → List Form
  | .hole S => [S]
  | .top | .cstr _ _ => []
  | .andI p q => p.opens ++ q.opens
  | .orL p | .orR p | .exI _ p | .clause _ _ p => p.opens

/-- The constraint leaves reached so far; an open leaf contributes `⊤`. -/
def PTree.store : PTree → Form
  | .hole _ | .top => .top
  | .cstr B ts => .pred B ts
  | .andI p q => .and p.store q.store
  | .orL p | .orR p | .exI _ p | .clause _ _ p => p.store

/-- A tree with no open leaf, as a `CProof`. -/
def PTree.close : PTree → Option CProof
  | .hole _ => none
  | .top => some .top
  | .cstr B ts => some (.cstr B ts)
  | .andI p q =>
      match p.close, q.close with
      | some p', some q' => some (.andI p' q')
      | _, _ => none
  | .orL p => match p.close with | some p' => some (.orL p') | none => none
  | .orR p => match p.close with | some p' => some (.orR p') | none => none
  | .exI t p => match p.close with | some p' => some (.exI t p') | none => none
  | .clause w ts p => match p.close with | some p' => some (.clause w ts p') | none => none

/-- On a closed tree, the store is the total constraint. -/
theorem PTree.store_close : ∀ (p : PTree) (q : CProof), p.close = some q → p.store = q.total
  | .hole _, _, h => nomatch h
  | .top, _, h => by cases h; rfl
  | .cstr _ _, _, h => by cases h; rfl
  | .andI p q, r, h => by
      cases hp : p.close with
      | none => simp [PTree.close, hp] at h
      | some p' =>
        cases hq : q.close with
        | none => simp [PTree.close, hp, hq] at h
        | some q' =>
          simp only [PTree.close, hp, hq, Option.some.injEq] at h
          subst h
          show Form.and p.store q.store = Form.and p'.total q'.total
          rw [PTree.store_close p p' hp, PTree.store_close q q' hq]
  | .orL p, r, h => by
      cases hp : p.close with
      | none => simp [PTree.close, hp] at h
      | some p' =>
        simp only [PTree.close, hp, Option.some.injEq] at h
        subst h; exact PTree.store_close p p' hp
  | .orR p, r, h => by
      cases hp : p.close with
      | none => simp [PTree.close, hp] at h
      | some p' =>
        simp only [PTree.close, hp, Option.some.injEq] at h
        subst h; exact PTree.store_close p p' hp
  | .exI t p, r, h => by
      cases hp : p.close with
      | none => simp [PTree.close, hp] at h
      | some p' =>
        simp only [PTree.close, hp, Option.some.injEq] at h
        subst h; exact PTree.store_close p p' hp
  | .clause w ts p, r, h => by
      cases hp : p.close with
      | none => simp [PTree.close, hp] at h
      | some p' =>
        simp only [PTree.close, hp, Option.some.injEq] at h
        subst h; exact PTree.store_close p p' hp

/-! ## SLD: one step expands one open leaf -/

/-- `Expand c p p' c'`: one rule applied at one open leaf of `p`, store `c` to `c'`. -/
inductive Expand (isC : String → Bool) (Θ : Program) (ok : Form → Prop) :
    Form → PTree → PTree → Form → Prop
  | top {c : Form} : Expand isC Θ ok c (.hole .top) .top c
  | cstr {c : Form} {B : String} {ts : List Tm} :
      isC B = true → ok (.and c (.pred B ts)) →
      Expand isC Θ ok c (.hole (.pred B ts)) (.cstr B ts) (.and c (.pred B ts))
  | and {c : Form} {A B : Form} :
      Expand isC Θ ok c (.hole (.and A B)) (.andI (.hole A) (.hole B)) c
  | orL {c : Form} {A B : Form} : Expand isC Θ ok c (.hole (.or A B)) (.orL (.hole A)) c
  | orR {c : Form} {A B : Form} : Expand isC Θ ok c (.hole (.or A B)) (.orR (.hole B)) c
  | ex {c : Form} {A : Form} (t : Tm) : Tm.lcAt 0 t →
      Expand isC Θ ok c (.hole (.exists_ A)) (.exI t (.hole (A.openAt 0 t))) c
  | clause {c : Form} {cl : Clause} (w : Nat) (ts : List Tm) :
      Θ[w]? = some cl → cl.modal = false → ts.length = cl.arity → (∀ t ∈ ts, Tm.lcAt 0 t) →
      Expand isC Θ ok c (.hole (.pred cl.head (Tm.instAllList ts (headVars cl.arity))))
        (.clause w ts (.hole (Form.instAll ts cl.body))) c
  | andL {c c' : Form} {p p' q : PTree} :
      Expand isC Θ ok c p p' c' → Expand isC Θ ok c (.andI p q) (.andI p' q) c'
  | andR {c c' : Form} {p q q' : PTree} :
      Expand isC Θ ok c q q' c' → Expand isC Θ ok c (.andI p q) (.andI p q') c'
  | inOrL {c c' : Form} {p p' : PTree} :
      Expand isC Θ ok c p p' c' → Expand isC Θ ok c (.orL p) (.orL p') c'
  | inOrR {c c' : Form} {p p' : PTree} :
      Expand isC Θ ok c p p' c' → Expand isC Θ ok c (.orR p) (.orR p') c'
  | inEx {c c' : Form} {t : Tm} {p p' : PTree} :
      Expand isC Θ ok c p p' c' → Expand isC Θ ok c (.exI t p) (.exI t p') c'
  | inClause {c c' : Form} {w : Nat} {ts : List Tm} {p p' : PTree} :
      Expand isC Θ ok c p p' c' → Expand isC Θ ok c (.clause w ts p) (.clause w ts p') c'

/-- A machine state: the store and a forest, one tree per initial goal. -/
structure MState where
  c : Form
  forest : List PTree

/-- One SLD step: expand one leaf of one tree. -/
inductive SLDStep (isC : String → Bool) (Θ : Program) (ok : Form → Prop) : MState → MState → Prop
  | mk {c c' : Form} {p p' : PTree} (l r : List PTree) :
      Expand isC Θ ok c p p' c' → SLDStep isC Θ ok ⟨c, l ++ p :: r⟩ ⟨c', l ++ p' :: r⟩

/-- Runs. -/
inductive SLDSteps (isC : String → Bool) (Θ : Program) (ok : Form → Prop) : MState → MState → Prop
  | refl (s : MState) : SLDSteps isC Θ ok s s
  | step {s s' s'' : MState} :
      SLDStep isC Θ ok s s' → SLDSteps isC Θ ok s' s'' → SLDSteps isC Θ ok s s''

/-- The projection to Table 2's goals. -/
def MState.goal (s : MState) : Goal := ⟨s.c, s.forest.flatMap PTree.opens⟩

section
variable {isC : String → Bool} {Θ : Program} {ok : Form → Prop}

/-! ### The projection to Table 2 -/

/-- An expansion rewrites exactly one open leaf, and that is a Table 2 step. -/
theorem Expand.opens {c c' : Form} {p p' : PTree} (h : Expand isC Θ ok c p p' c') :
    ∀ l r : List Form, Step isC Θ ok ⟨c, l ++ (p.opens ++ r)⟩ ⟨c', l ++ (p'.opens ++ r)⟩ := by
  induction h with
  | top => intro l r; exact Step.top
  | cstr hB hok => intro l r; exact Step.cstr hB hok
  | and => intro l r; exact Step.and
  | orL => intro l r; exact Step.orL
  | orR => intro l r; exact Step.orR
  | ex t ht => intro l r; exact Step.ex t ht
  | clause w ts hc hm hlen hts => intro l r; exact Step.clause w ts hc hm hlen hts
  | @andL c₁' p₁ p₁' q₁ _ ih =>
      intro l r
      show Step isC Θ ok ⟨c, l ++ ((p₁.opens ++ q₁.opens) ++ r)⟩
        ⟨c₁', l ++ ((p₁'.opens ++ q₁.opens) ++ r)⟩
      simp only [List.append_assoc]
      exact ih l (q₁.opens ++ r)
  | @andR c₁' p₁ q₁ q₁' _ ih =>
      intro l r
      show Step isC Θ ok ⟨c, l ++ ((p₁.opens ++ q₁.opens) ++ r)⟩
        ⟨c₁', l ++ ((p₁.opens ++ q₁'.opens) ++ r)⟩
      have := ih (l ++ p₁.opens) r
      simp only [List.append_assoc] at this ⊢
      exact this
  | inOrL _ ih => intro l r; exact ih l r
  | inOrR _ ih => intro l r; exact ih l r
  | inEx _ ih => intro l r; exact ih l r
  | inClause _ ih => intro l r; exact ih l r

/-- Every SLD step is a Table 2 step on the projections. -/
theorem SLDStep.goal_step {s s' : MState} (h : SLDStep isC Θ ok s s') :
    Step isC Θ ok s.goal s'.goal := by
  cases h with
  | mk l r he =>
      show Step isC Θ ok ⟨_, (l ++ _ :: r).flatMap PTree.opens⟩ ⟨_, (l ++ _ :: r).flatMap PTree.opens⟩
      simp only [List.flatMap_append, List.flatMap_cons]
      exact he.opens _ _

/-! ### Typing is preserved -/

/-- `p` is a partial proof of `S`: open leaves are typed by their formula. -/
inductive PTyped (isC : String → Bool) (Θ : Program) : Form → PTree → Prop
  | hole (S : Form) : PTyped isC Θ S (.hole S)
  | top : PTyped isC Θ .top .top
  | cstr {B : String} {ts : List Tm} : isC B = true → PTyped isC Θ (.pred B ts) (.cstr B ts)
  | andI {A B : Form} {p q : PTree} :
      PTyped isC Θ A p → PTyped isC Θ B q → PTyped isC Θ (.and A B) (.andI p q)
  | orL {A B : Form} {p : PTree} : PTyped isC Θ A p → PTyped isC Θ (.or A B) (.orL p)
  | orR {A B : Form} {p : PTree} : PTyped isC Θ B p → PTyped isC Θ (.or A B) (.orR p)
  | exI {A : Form} {p : PTree} (t : Tm) : Tm.lcAt 0 t →
      PTyped isC Θ (A.openAt 0 t) p → PTyped isC Θ (.exists_ A) (.exI t p)
  | clause {c : Clause} {p : PTree} (w : Nat) (ts : List Tm) : Θ[w]? = some c →
      c.modal = false → ts.length = c.arity → (∀ t ∈ ts, Tm.lcAt 0 t) →
      PTyped isC Θ (Form.instAll ts c.body) p →
      PTyped isC Θ (.pred c.head (Tm.instAllList ts (headVars c.arity))) (.clause w ts p)

theorem Expand.typed {c c' : Form} {p p' : PTree} (h : Expand isC Θ ok c p p' c') :
    ∀ {S : Form}, PTyped isC Θ S p → PTyped isC Θ S p' := by
  induction h with
  | top => intro S hp; cases hp; exact .top
  | cstr hB _ => intro S hp; cases hp; exact .cstr hB
  | and => intro S hp; cases hp; exact .andI (.hole _) (.hole _)
  | orL => intro S hp; cases hp; exact .orL (.hole _)
  | orR => intro S hp; cases hp; exact .orR (.hole _)
  | ex t ht => intro S hp; cases hp; exact .exI t ht (.hole _)
  | clause w ts hc hm hlen hts => intro S hp; cases hp; exact .clause w ts hc hm hlen hts (.hole _)
  | andL _ ih => intro S hp; cases hp with | andI h₁ h₂ => exact .andI (ih h₁) h₂
  | andR _ ih => intro S hp; cases hp with | andI h₁ h₂ => exact .andI h₁ (ih h₂)
  | inOrL _ ih => intro S hp; cases hp with | orL h₁ => exact .orL (ih h₁)
  | inOrR _ ih => intro S hp; cases hp with | orR h₁ => exact .orR (ih h₁)
  | inEx _ ih => intro S hp; cases hp with | exI _ ht h₁ => exact .exI _ ht (ih h₁)
  | inClause _ ih =>
      intro S hp
      cases hp with | clause _ _ hc hm hlen hts h₁ => exact .clause _ _ hc hm hlen hts (ih h₁)

/-- A closed, typed tree is a `CProof` of its goal. -/
theorem PTree.close_typed {S : Form} {p : PTree} (hp : PTyped isC Θ S p) :
    ∀ {q : CProof}, p.close = some q → CTyped isC Θ S q := by
  induction hp with
  | hole S => intro q h; exact nomatch h
  | top => intro q h; cases h; exact .top
  | cstr hB => intro q h; cases h; exact .cstr hB
  | @andI _ _ p₁ p₂ _ _ ih₁ ih₂ =>
      intro q h
      cases hp₁ : p₁.close with
      | none => simp [PTree.close, hp₁] at h
      | some q₁ =>
        cases hp₂ : p₂.close with
        | none => simp [PTree.close, hp₁, hp₂] at h
        | some q₂ =>
          simp only [PTree.close, hp₁, hp₂, Option.some.injEq] at h
          subst h; exact .andI (ih₁ hp₁) (ih₂ hp₂)
  | @orL _ _ p₁ _ ih =>
      intro q h
      cases hp₁ : p₁.close with
      | none => simp [PTree.close, hp₁] at h
      | some q₁ =>
        simp only [PTree.close, hp₁, Option.some.injEq] at h
        subst h; exact .orL (ih hp₁)
  | @orR _ _ p₁ _ ih =>
      intro q h
      cases hp₁ : p₁.close with
      | none => simp [PTree.close, hp₁] at h
      | some q₁ =>
        simp only [PTree.close, hp₁, Option.some.injEq] at h
        subst h; exact .orR (ih hp₁)
  | @exI _ p₁ t ht _ ih =>
      intro q h
      cases hp₁ : p₁.close with
      | none => simp [PTree.close, hp₁] at h
      | some q₁ =>
        simp only [PTree.close, hp₁, Option.some.injEq] at h
        subst h; exact .exI t ht (ih hp₁)
  | @clause _ p₁ w ts hc hm hlen hts _ ih =>
      intro q h
      cases hp₁ : p₁.close with
      | none => simp [PTree.close, hp₁] at h
      | some q₁ =>
        simp only [PTree.close, hp₁, Option.some.injEq] at h
        subst h; exact .clause w ts hc hm hlen hts (ih hp₁)

/-! ### Theorem 9.4 as a step invariant: the store is `c₀ ∧ store` -/

theorem Expand.store {c c' : Form} {p p' : PTree} (h : Expand isC Θ ok c p p' c') :
    ∀ c₀ : Form, PEq c (.and c₀ p.store) → PEq c' (.and c₀ p'.store) := by
  induction h with
  | top => intro c₀ hc; exact hc
  | cstr _ _ =>
      intro c₀ hc
      exact (PEq.and hc (PEq.refl _)).trans (PEq.and (PEq.and_top _) (PEq.refl _))
  | and =>
      intro c₀ hc
      exact hc.trans (PEq.and (PEq.refl _) (PEq.and_top _).symm)
  | orL => intro c₀ hc; exact hc
  | orR => intro c₀ hc; exact hc
  | ex _ _ => intro c₀ hc; exact hc
  | clause _ _ _ _ _ _ => intro c₀ hc; exact hc
  | @andL _ p p' q _ ih =>
      intro c₀ hc
      have h₁ : PEq c (.and (.and c₀ q.store) p.store) :=
        hc.trans ((PEq.and (PEq.refl c₀) (PEq.and_comm p.store q.store)).trans
          (PEq.and_assoc c₀ q.store p.store).symm)
      exact (ih _ h₁).trans ((PEq.and_assoc c₀ q.store p'.store).trans
        (PEq.and (PEq.refl c₀) (PEq.and_comm q.store p'.store)))
  | @andR _ p q q' _ ih =>
      intro c₀ hc
      have h₁ : PEq c (.and (.and c₀ p.store) q.store) :=
        hc.trans (PEq.and_assoc c₀ p.store q.store).symm
      exact (ih _ h₁).trans (PEq.and_assoc c₀ p.store q'.store)
  | inOrL _ ih => intro c₀ hc; exact ih c₀ hc
  | inOrR _ ih => intro c₀ hc; exact ih c₀ hc
  | inEx _ ih => intro c₀ hc; exact ih c₀ hc
  | inClause _ ih => intro c₀ hc; exact ih c₀ hc

/-- Unpacking a step. -/
theorem SLDStep.inv {s s' : MState} (h : SLDStep isC Θ ok s s') :
    ∃ l r p p' c c', s = ⟨c, l ++ p :: r⟩ ∧ s' = ⟨c', l ++ p' :: r⟩ ∧ Expand isC Θ ok c p p' c' := by
  cases h with
  | mk l r he => exact ⟨l, r, _, _, _, _, rfl, rfl, he⟩

/-- A step from a singleton forest stays a singleton forest. -/
theorem SLDStep.single {c : Form} {p : PTree} {s' : MState} (h : SLDStep isC Θ ok ⟨c, [p]⟩ s') :
    ∃ c' p', s' = ⟨c', [p']⟩ ∧ Expand isC Θ ok c p p' c' := by
  obtain ⟨l, r, p₀, p₀', c₁, c₁', hs, hs', he⟩ := h.inv
  obtain ⟨hc, hf⟩ := MState.mk.inj hs
  subst hc
  have hl := congrArg List.length hf
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  cases l with
  | cons _ _ => simp only [List.length_cons] at hl; omega
  | nil =>
    cases r with
    | cons _ _ => simp only [List.length_cons] at hl; omega
    | nil =>
      have hp₀ : p = p₀ := by simpa using hf
      subst hp₀
      exact ⟨c₁', p₀', hs', he⟩

/-- Along a run from `c₀ □ [S]`, the tree stays typed by `S` and the store is `c₀ ∧ store`. -/
theorem SLDSteps.inv {c₀ : Form} {S : Form} {s s' : MState} (h : SLDSteps isC Θ ok s s') :
    ∀ {c₁ : Form} {p₁ : PTree}, s = ⟨c₁, [p₁]⟩ → PTyped isC Θ S p₁ → PEq c₁ (.and c₀ p₁.store) →
      ∀ {c : Form} {p : PTree}, s' = ⟨c, [p]⟩ → PTyped isC Θ S p ∧ PEq c (.and c₀ p.store) := by
  induction h with
  | refl s =>
      intro c₁ p₁ hs ht hc c p hs'
      subst hs
      obtain ⟨hc', hf⟩ := MState.mk.inj hs'
      subst hc'
      obtain ⟨hp', -⟩ := List.cons.inj hf
      subst hp'
      exact ⟨ht, hc⟩
  | step h₁ _ ih =>
      intro c₁ p₁ hs ht hc c p hs'
      subst hs
      obtain ⟨c₂, p₂, rfl, he⟩ := h₁.single
      exact ih rfl (he.typed ht) (he.store c₀ hc) hs'

/-- **Theorem 9.4, machine form.**  A run from `c₀ □ [S]` that closes its tree to `q` has
`c ⊣⊢ c₀ ∧ total q`, with `q` a proof tree of `S`. -/
theorem SLDSteps.store {c₀ c : Form} {S : Form} {p : PTree} {q : CProof}
    (h : SLDSteps isC Θ ok ⟨c₀, [.hole S]⟩ ⟨c, [p]⟩) (hq : p.close = some q) :
    CTyped isC Θ S q ∧ PEq c (.and c₀ q.total) := by
  obtain ⟨ht, hc⟩ := h.inv (c₀ := c₀) (S := S) rfl (.hole S) (PEq.and_top _).symm rfl
  exact ⟨PTree.close_typed ht hq, by rw [← PTree.store_close p q hq]; exact hc⟩

/-- **Soundness with respect to QLL.**  The finished tree proves `total q ⊃ S`. -/
theorem SLDSteps.prv {c₀ c : Form} {S : Form} {p : PTree} {q : CProof}
    (h : SLDSteps isC Θ ok ⟨c₀, [.hole S]⟩ ⟨c, [p]⟩) (hq : p.close = some q) :
    Prv Θ.forms (.imp q.total S) :=
  (h.store hq).1.prv_total

end

/-! ## SLD◯: the same machine on the abstract program -/

/-- An `AProof` with open leaves. -/
inductive ATree where
  | hole (S : Form)
  | val
  | andC (p q : ATree)
  | orL (p : ATree)
  | orR (p : ATree)
  | exC (t : Tm) (p : ATree)
  | impC (w : Nat) (ts : List Tm) (p : ATree)
  deriving Repr, Inhabited

/-- The open leaves. -/
def ATree.opens : ATree → List Form
  | .hole S => [S]
  | .val => []
  | .andC p q => p.opens ++ q.opens
  | .orL p | .orR p | .exC _ p | .impC _ _ p => p.opens

/-- A tree with no open leaf, as an `AProof`. -/
def ATree.close : ATree → Option AProof
  | .hole _ => none
  | .val => some .val
  | .andC p q =>
      match p.close, q.close with
      | some p', some q' => some (.andC p' q')
      | _, _ => none
  | .orL p => match p.close with | some p' => some (.orL p') | none => none
  | .orR p => match p.close with | some p' => some (.orR p') | none => none
  | .exC t p => match p.close with | some p' => some (.exC t p') | none => none
  | .impC w ts p => match p.close with | some p' => some (.impC w ts p') | none => none

/-- `toA` on partial trees: constraint leaves become `val`, open leaves are abstracted. -/
def PTree.toA (isC : String → Bool) : PTree → ATree
  | .hole S => .hole (S.strip isC)
  | .top | .cstr _ _ => .val
  | .andI p q => .andC (p.toA isC) (q.toA isC)
  | .orL p => .orL (p.toA isC)
  | .orR p => .orR (p.toA isC)
  | .exI t p => .exC t (p.toA isC)
  | .clause w ts p => .impC w ts (p.toA isC)

/-- One rule at one open leaf, on the abstract program: the same format, no store,
`cstr` gone (its leaf is now `⊤`). -/
inductive ExpandA (Θ : Program) (q : Q) : ATree → ATree → Prop
  | top : ExpandA Θ q (.hole .top) .val
  | and {A B : Form} : ExpandA Θ q (.hole (.and A B)) (.andC (.hole A) (.hole B))
  | orL {A B : Form} : ExpandA Θ q (.hole (.or A B)) (.orL (.hole A))
  | orR {A B : Form} : ExpandA Θ q (.hole (.or A B)) (.orR (.hole B))
  | ex {A : Form} (t : Tm) : Tm.lcAt 0 t →
      ExpandA Θ q (.hole (.exists_ A)) (.exC t (.hole (A.openAt 0 t)))
  | clause {cl : Clause} (w : Nat) (ts : List Tm) :
      Θ[w]? = some cl → cl.modal = true → cl.q = q → ts.length = cl.arity →
      (∀ t ∈ ts, Tm.lcAt 0 t) →
      ExpandA Θ q (.hole (.pred cl.head (Tm.instAllList ts (headVars cl.arity))))
        (.impC w ts (.hole (Form.instAll ts cl.body)))
  | andL {p p' r : ATree} : ExpandA Θ q p p' → ExpandA Θ q (.andC p r) (.andC p' r)
  | andR {p r r' : ATree} : ExpandA Θ q r r' → ExpandA Θ q (.andC p r) (.andC p r')
  | inOrL {p p' : ATree} : ExpandA Θ q p p' → ExpandA Θ q (.orL p) (.orL p')
  | inOrR {p p' : ATree} : ExpandA Θ q p p' → ExpandA Θ q (.orR p) (.orR p')
  | inEx {t : Tm} {p p' : ATree} : ExpandA Θ q p p' → ExpandA Θ q (.exC t p) (.exC t p')
  | inImp {w : Nat} {ts : List Tm} {p p' : ATree} :
      ExpandA Θ q p p' → ExpandA Θ q (.impC w ts p) (.impC w ts p')

/-- One SLD◯ step on a forest. -/
inductive SLDCStep (Θ : Program) (q : Q) : List ATree → List ATree → Prop
  | mk {p p' : ATree} (l r : List ATree) : ExpandA Θ q p p' → SLDCStep Θ q (l ++ p :: r) (l ++ p' :: r)

/-- Runs. -/
inductive SLDCSteps (Θ : Program) (q : Q) : List ATree → List ATree → Prop
  | refl (F : List ATree) : SLDCSteps Θ q F F
  | step {F F' F'' : List ATree} : SLDCStep Θ q F F' → SLDCSteps Θ q F' F'' → SLDCSteps Θ q F F''

/-- `a` is a partial abstract proof of `◯S`. -/
inductive PTypedA (Θ : Program) (q : Q) : Form → ATree → Prop
  | hole (S : Form) : PTypedA Θ q S (.hole S)
  | val : PTypedA Θ q .top .val
  | andC {A B : Form} {p r : ATree} :
      PTypedA Θ q A p → PTypedA Θ q B r → PTypedA Θ q (.and A B) (.andC p r)
  | orL {A B : Form} {p : ATree} : PTypedA Θ q A p → PTypedA Θ q (.or A B) (.orL p)
  | orR {A B : Form} {p : ATree} : PTypedA Θ q B p → PTypedA Θ q (.or A B) (.orR p)
  | exC {A : Form} {p : ATree} (t : Tm) : Tm.lcAt 0 t →
      PTypedA Θ q (A.openAt 0 t) p → PTypedA Θ q (.exists_ A) (.exC t p)
  | impC {c : Clause} {p : ATree} (w : Nat) (ts : List Tm) :
      Θ[w]? = some c → c.modal = true → c.q = q → ts.length = c.arity →
      (∀ t ∈ ts, Tm.lcAt 0 t) → PTypedA Θ q (Form.instAll ts c.body) p →
      PTypedA Θ q (.pred c.head (Tm.instAllList ts (headVars c.arity))) (.impC w ts p)

section
variable {Θ : Program} {q : Q}

theorem ExpandA.typed {p p' : ATree} (h : ExpandA Θ q p p') :
    ∀ {S : Form}, PTypedA Θ q S p → PTypedA Θ q S p' := by
  induction h with
  | top => intro S hp; cases hp; exact .val
  | and => intro S hp; cases hp; exact .andC (.hole _) (.hole _)
  | orL => intro S hp; cases hp; exact .orL (.hole _)
  | orR => intro S hp; cases hp; exact .orR (.hole _)
  | ex t ht => intro S hp; cases hp; exact .exC t ht (.hole _)
  | clause w ts hc hm hq hlen hts => intro S hp; cases hp; exact .impC w ts hc hm hq hlen hts (.hole _)
  | andL _ ih => intro S hp; cases hp with | andC h₁ h₂ => exact .andC (ih h₁) h₂
  | andR _ ih => intro S hp; cases hp with | andC h₁ h₂ => exact .andC h₁ (ih h₂)
  | inOrL _ ih => intro S hp; cases hp with | orL h₁ => exact .orL (ih h₁)
  | inOrR _ ih => intro S hp; cases hp with | orR h₁ => exact .orR (ih h₁)
  | inEx _ ih => intro S hp; cases hp with | exC _ ht h₁ => exact .exC _ ht (ih h₁)
  | inImp _ ih =>
      intro S hp
      cases hp with | impC _ _ hc hm hq hlen hts h₁ => exact .impC _ _ hc hm hq hlen hts (ih h₁)

/-- A closed, typed abstract tree is an `AProof` of its goal. -/
theorem ATree.close_typed {S : Form} {a : ATree} (ha : PTypedA Θ q S a) :
    ∀ {b : AProof}, a.close = some b → ATyped Θ q S b := by
  induction ha with
  | hole S => intro b h; exact nomatch h
  | val => intro b h; cases h; exact .val
  | @andC _ _ p₁ p₂ _ _ ih₁ ih₂ =>
      intro b h
      cases hp₁ : p₁.close with
      | none => simp [ATree.close, hp₁] at h
      | some b₁ =>
        cases hp₂ : p₂.close with
        | none => simp [ATree.close, hp₁, hp₂] at h
        | some b₂ =>
          simp only [ATree.close, hp₁, hp₂, Option.some.injEq] at h
          subst h; exact .andC (ih₁ hp₁) (ih₂ hp₂)
  | @orL _ _ p₁ _ ih =>
      intro b h
      cases hp₁ : p₁.close with
      | none => simp [ATree.close, hp₁] at h
      | some b₁ =>
        simp only [ATree.close, hp₁, Option.some.injEq] at h
        subst h; exact .orL (ih hp₁)
  | @orR _ _ p₁ _ ih =>
      intro b h
      cases hp₁ : p₁.close with
      | none => simp [ATree.close, hp₁] at h
      | some b₁ =>
        simp only [ATree.close, hp₁, Option.some.injEq] at h
        subst h; exact .orR (ih hp₁)
  | @exC _ p₁ t ht _ ih =>
      intro b h
      cases hp₁ : p₁.close with
      | none => simp [ATree.close, hp₁] at h
      | some b₁ =>
        simp only [ATree.close, hp₁, Option.some.injEq] at h
        subst h; exact .exC t ht (ih hp₁)
  | @impC _ p₁ w ts hc hm hq hlen hts _ ih =>
      intro b h
      cases hp₁ : p₁.close with
      | none => simp [ATree.close, hp₁] at h
      | some b₁ =>
        simp only [ATree.close, hp₁, Option.some.injEq] at h
        subst h; exact .impC w ts hc hm hq hlen hts (ih hp₁)

/-- Unpacking a step. -/
theorem SLDCStep.inv {F F' : List ATree} (h : SLDCStep Θ q F F') :
    ∃ l r p p', F = l ++ p :: r ∧ F' = l ++ p' :: r ∧ ExpandA Θ q p p' := by
  cases h with
  | mk l r he => exact ⟨l, r, _, _, rfl, rfl, he⟩

/-- A step from a singleton forest stays a singleton forest. -/
theorem SLDCStep.single {a : ATree} {F' : List ATree} (h : SLDCStep Θ q [a] F') :
    ∃ a', F' = [a'] ∧ ExpandA Θ q a a' := by
  obtain ⟨l, r, a₀, a₀', hf, hf', he⟩ := h.inv
  have hl := congrArg List.length hf
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  cases l with
  | cons _ _ => simp only [List.length_cons] at hl; omega
  | nil =>
    cases r with
    | cons _ _ => simp only [List.length_cons] at hl; omega
    | nil =>
      have ha₀ : a = a₀ := by simpa using hf
      subst ha₀
      exact ⟨a₀', hf', he⟩

theorem SLDCSteps.inv {S : Form} {F F' : List ATree} (h : SLDCSteps Θ q F F') :
    ∀ {a₁ : ATree}, F = [a₁] → PTypedA Θ q S a₁ → ∀ {a : ATree}, F' = [a] → PTypedA Θ q S a := by
  induction h with
  | refl F =>
      intro a₁ hF ht a hF'
      subst hF
      obtain ⟨hp', -⟩ := List.cons.inj hF'
      subst hp'
      exact ht
  | step h₁ _ ih =>
      intro a₁ hF ht a hF'
      subst hF
      obtain ⟨a₂, rfl, he⟩ := h₁.single
      exact ih rfl (he.typed ht) hF'

/-- **Soundness of SLD◯ with respect to QLL.**  A run from `[S]` that closes its tree to `b`
gives an abstract proof, hence `Θ ⊢ ◯S`. -/
theorem SLDCSteps.prv {S : Form} {a : ATree} {b : AProof}
    (h : SLDCSteps Θ q [.hole S] [a]) (hb : a.close = some b) :
    ATyped Θ q S b ∧ Prv Θ.forms (.circ q S) :=
  have ht := ATree.close_typed (h.inv (S := S) rfl (.hole S) rfl) hb
  ⟨ht, ht.prv⟩

end

/-! ## SLD simulates into SLD◯ under `toA` -/

section
variable {isC : String → Bool} {Θ : Program} {ok : Form → Prop}

/-- Every SLD step on `Θ` is an SLD◯ step on `Θ♯` at the image leaf: `cstr` becomes `top`,
every other rule is itself. -/
theorem Expand.toA (q : Q) (hH : Θ.HeadsOK isC) {c c' : Form} {p p' : PTree}
    (h : Expand isC Θ ok c p p' c') :
    ExpandA (Θ.abs isC q) q (p.toA isC) (p'.toA isC) := by
  induction h with
  | top => exact .top
  | cstr hB _ =>
      show ExpandA _ _ (.hole ((Form.pred _ _).strip isC)) .val
      rw [Form.strip_pred_C _ hB]; exact .top
  | and => exact .and
  | orL => exact .orL
  | orR => exact .orR
  | ex t ht =>
      show ExpandA _ _ (.hole (.exists_ (Form.strip isC _))) (.exC t (.hole ((Form.openAt 0 t _).strip isC)))
      rw [Form.strip_openAt]; exact .ex t ht
  | @clause cl w ts hc hm hlen hts =>
      show ExpandA _ _ (.hole ((Form.pred cl.head _).strip isC))
        (.impC w ts (.hole ((Form.instAll ts cl.body).strip isC)))
      rw [Form.strip_pred_of _ (hH cl (List.mem_of_getElem? hc)), Form.strip_instAll]
      exact .clause (cl := cl.abs isC q) w ts (Program.abs_getElem? hc) rfl rfl hlen hts
  | andL _ ih => exact .andL ih
  | andR _ ih => exact .andR ih
  | inOrL _ ih => exact .inOrL ih
  | inOrR _ ih => exact .inOrR ih
  | inEx _ ih => exact .inEx ih
  | inClause _ ih => exact .inImp ih

/-- The simulation on states. -/
theorem SLDStep.toA (q : Q) (hH : Θ.HeadsOK isC) {s s' : MState} (h : SLDStep isC Θ ok s s') :
    SLDCStep (Θ.abs isC q) q (s.forest.map (PTree.toA isC)) (s'.forest.map (PTree.toA isC)) := by
  cases h with
  | mk l r he =>
      show SLDCStep _ _ ((l ++ _ :: r).map _) ((l ++ _ :: r).map _)
      simp only [List.map_append, List.map_cons]
      exact .mk _ _ (he.toA q hH)

theorem SLDSteps.toA (q : Q) (hH : Θ.HeadsOK isC) {s s' : MState} (h : SLDSteps isC Θ ok s s') :
    SLDCSteps (Θ.abs isC q) q (s.forest.map (PTree.toA isC)) (s'.forest.map (PTree.toA isC)) := by
  induction h with
  | refl s => exact .refl _
  | step h₁ _ ih => exact .step (h₁.toA q hH) ih

end

/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.SLD.SLDStep.goal_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms SLDStep.goal_step

/-- info: 'LaxLogic.QLL.SLD.SLDSteps.store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SLDSteps.store

/-- info: 'LaxLogic.QLL.SLD.SLDSteps.prv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SLDSteps.prv

/-- info: 'LaxLogic.QLL.SLD.SLDCSteps.prv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SLDCSteps.prv

/-- info: 'LaxLogic.QLL.SLD.SLDSteps.toA' depends on axioms: [propext] -/
#guard_msgs in #print axioms SLDSteps.toA

end LaxLogic.QLL.SLD
