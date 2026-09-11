/-
# `LaxLogic.QLL.CLPAbstract` — abstraction, extraction and refinement (the `◯` pass)

The second pass over §§4, 6, 8 and 9 of the CLP draft.  Constraints are
formulas, `⊗ = ∧` and `ε = true`, so every equation of the draft holds here up
to provable equivalence `⊣⊢` (`PEq`).

**Abstraction (Definition 6.2, Theorem 6.3).**  `S♯` replaces each constraint
atom by `true`; a clause `∀x̃. S ⊃ P` becomes `∀x̃. S♯ ⊃ ◯P`.  An abstract proof
tree (`AProof`) uses the rules of Fig. 3 against the abstract program, and a
concrete proof tree maps to one (`CProof.toA`):

    CTyped Θ S p  →  ATyped Θ♯ (S♯) (toA p)  →  Θ♯ ⊢ ◯S♯                 (Theorem 6.3)

**Extraction (§4, Lemmas 8.3 and 8.4, Theorem 9.7).**  The writer monad
`C × −` gives every abstract proof a constraint and a witness, `a.ext T`, where
`T` is a constraint table (Def 6.2's `θ♯₁`).  For the table of the concrete
program itself:

    ctable S (wit p) = active p                                          (Lemma 8.3)
    (ext (toA p)).2 = wit p,   (ext (toA p)).1 ⊣⊢ latent p               (Lemma 8.4)
    true □ φ ⇝* c □ ε,  φ pure  →  c ⊣⊢ (ext (toA p)).1 for a proof p of φ  (Theorem 9.7)

**Refinement (Definition 6.5, Theorem 6.8, Proposition 6.6).**  Definition 6.5
turns a table into refined clauses `∀x̃. (⋁_g ∃ỹ. ⋀Dᵢ ∧ π₁(p x̃ g)) ⊃ P`.  Here
the refined clauses are used through their instances: `RefinedBy Δ Θ♯ T` says
that `Π` proves `T w t̃ z ∧ S[t̃]@z ⊃ P(t̃)` for every clause `w`, instance `t̃`
and witness `z`, where `S@z` is the disjunct of `S` that `z` selects, with its
existential witnesses substituted (Table 1, with terms for the variables).
Then, for every abstract proof `a` of `◯S`, and any table:

    RefinedBy Δ Θ♯ T  →  Π ⊢ π₁(ext a) ⊃ S                              (Theorem 6.8)
    RefinedBy Θ Θ♯ (ctable Θ)   for a non-modal program Θ              (Proposition 6.6, first half)

so a concrete program proves the extracted constraint of any abstract proof
against its abstraction, `Θ ⊢ π₁(ext a) ⊃ S` (Corollary 9.8 by the draft's
route).  The second half of Proposition 6.6, `(p : θ)♭ ⊢ θ` for a modal clause,
is REFUTED as stated (`HerbrandCLP.p66_refuted`, a one-world countermodel); it
holds once the table's constraints are assumed lax-true (`p66_with_lax`).

**The monad (Lemma 4.3 and Theorem 4.4, read equationally).**  The unit and
associativity laws of `C × −`, and commutativity, hold up to `⊣⊢`
(`WM.bind_val_left`, `WM.bind_val_right`, `WM.bind_assoc`, `WM.bind_comm`).
Commutativity is what makes the answer constraint independent of the order in
which subgoals are selected; with a non-commutative monoid of constraints it
would not be.
-/
import LaxLogic.QLL.CLPOper

namespace LaxLogic.QLL

/-! ## Abstraction `♯` -/

/-- `A♯`: every constraint atom replaced by `true`. -/
def Form.strip (isC : String → Bool) : Form → Form
  | .top => .top
  | .bot => .bot
  | .pred B ts => if isC B then .top else .pred B ts
  | .and A B => .and (A.strip isC) (B.strip isC)
  | .or A B => .or (A.strip isC) (B.strip isC)
  | .imp A B => .imp (A.strip isC) (B.strip isC)
  | .circ q A => .circ q (A.strip isC)
  | .forall_ A => .forall_ (A.strip isC)
  | .exists_ A => .exists_ (A.strip isC)

theorem Form.strip_pred_C {isC : String → Bool} {B : String} (ts : List Tm) (h : isC B = true) :
    (Form.pred B ts).strip isC = .top := if_pos h

theorem Form.strip_pred_of {isC : String → Bool} {B : String} (ts : List Tm) (h : isC B = false) :
    (Form.pred B ts).strip isC = .pred B ts := if_neg (by rw [h]; decide)

theorem Form.strip_openAt (isC : String → Bool) (t : Tm) :
    ∀ (A : Form) (k : Nat), (A.openAt k t).strip isC = (A.strip isC).openAt k t
  | .top, _ => rfl
  | .bot, _ => rfl
  | .pred B ts, k => by
      show (if isC B = true then Form.top else .pred B (Tm.openAtList k t ts))
        = Form.openAt k t (if isC B = true then Form.top else .pred B ts)
      by_cases h : isC B = true
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h]; rfl
  | .and A B, k => congrArg₂ Form.and (Form.strip_openAt isC t A k) (Form.strip_openAt isC t B k)
  | .or A B, k => congrArg₂ Form.or (Form.strip_openAt isC t A k) (Form.strip_openAt isC t B k)
  | .imp A B, k => congrArg₂ Form.imp (Form.strip_openAt isC t A k) (Form.strip_openAt isC t B k)
  | .circ q A, k => congrArg (Form.circ q) (Form.strip_openAt isC t A k)
  | .forall_ A, k => congrArg Form.forall_ (Form.strip_openAt isC t A (k + 1))
  | .exists_ A, k => congrArg Form.exists_ (Form.strip_openAt isC t A (k + 1))

theorem Form.strip_instAll (isC : String → Bool) :
    ∀ (ts : List Tm) (A : Form), (Form.instAll ts A).strip isC = Form.instAll ts (A.strip isC)
  | [], _ => rfl
  | t :: ts, A => by
      show (Form.instAll ts (A.openAt ts.length t)).strip isC
        = Form.instAll ts ((A.strip isC).openAt ts.length t)
      rw [Form.strip_instAll isC ts, Form.strip_openAt]

theorem IsSigma.strip (isC : String → Bool) {S : Form} (h : IsSigma S) : IsSigma (S.strip isC) := by
  induction h with
  | top => exact .top
  | pred B ts =>
      show IsSigma (if isC B = true then Form.top else .pred B ts)
      split
      · exact .top
      · exact .pred B ts
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | or _ _ ih₁ ih₂ => exact .or ih₁ ih₂
  | ex _ ih => exact .ex ih

theorem IsSigma.openAt' {A : Form} (h : IsSigma A) : ∀ (k : Nat) (t : Tm), IsSigma (A.openAt k t) := by
  induction h with
  | top => intro _ _; exact .top
  | pred P ts => intro _ _; exact .pred P _
  | and _ _ ih₁ ih₂ => intro k t; exact .and (ih₁ k t) (ih₂ k t)
  | or _ _ ih₁ ih₂ => intro k t; exact .or (ih₁ k t) (ih₂ k t)
  | ex _ ih => intro k t; exact .ex (ih (k + 1) t)

/-- `θ♯₂ = ∀x̃. S♯ ⊃ ◯P(x̃)`. -/
def Clause.abs (isC : String → Bool) (q : Q) (c : Clause) : Clause :=
  ⟨c.arity, c.body.strip isC, c.body_sigma.strip isC, c.head, true, q⟩

/-- `Θ♯₂`, clause by clause. -/
def Program.abs (isC : String → Bool) (q : Q) (Θ : Program) : Program := Θ.map (Clause.abs isC q)

/-- Definition 5.1's requirement that no head is a constraint. -/
def Program.HeadsOK (isC : String → Bool) (Θ : Program) : Prop := ∀ c ∈ Θ, isC c.head = false

theorem Program.abs_getElem? {isC : String → Bool} {q : Q} {Θ : Program} {w : Nat} {c : Clause}
    (h : Θ[w]? = some c) : (Θ.abs isC q)[w]? = some (c.abs isC q) := by
  rw [Program.abs, List.getElem?_map, h]; rfl

/-! ## Abstract proof trees: Fig. 3 against the abstract program -/

/-- Abstract proof terms of the LLP fragment: `val(⋆)`, `∧◯`, `∨◯`, `∃◯`, `⊃◯`. -/
inductive AProof where
  | val
  | andC (p r : AProof)
  | orL (p : AProof)
  | orR (p : AProof)
  | exC (t : Tm) (p : AProof)
  | impC (w : Nat) (ts : List Tm) (p : AProof)
  deriving Repr, Inhabited

/-- `Θ ⊢ a : ◯_q S`. -/
inductive ATyped (Θ : Program) (q : Q) : Form → AProof → Prop
  | val : ATyped Θ q .top .val
  | andC {A B : Form} {p r : AProof} : ATyped Θ q A p → ATyped Θ q B r →
      ATyped Θ q (.and A B) (.andC p r)
  | orL {A B : Form} {p : AProof} : ATyped Θ q A p → ATyped Θ q (.or A B) (.orL p)
  | orR {A B : Form} {p : AProof} : ATyped Θ q B p → ATyped Θ q (.or A B) (.orR p)
  | exC {A : Form} {p : AProof} (t : Tm) : Tm.lcAt 0 t → ATyped Θ q (A.openAt 0 t) p →
      ATyped Θ q (.exists_ A) (.exC t p)
  | impC {c : Clause} {p : AProof} (w : Nat) (ts : List Tm) :
      Θ[w]? = some c → c.modal = true → c.q = q → ts.length = c.arity →
      (∀ t ∈ ts, Tm.lcAt 0 t) → ATyped Θ q (Form.instAll ts c.body) p →
      ATyped Θ q (.pred c.head (Tm.instAllList ts (headVars c.arity))) (.impC w ts p)

/-- Abstract proofs are proofs. -/
theorem ATyped.prv {Θ : Program} {q : Q} {S : Form} {a : AProof} (h : ATyped Θ q S a) :
    Prv Θ.forms (.circ q S) := by
  induction h with
  | val => exact .circI .topI
  | andC _ _ ih₁ ih₂ =>
      exact .circE ih₁ (.circE ih₂.weaken_cons
        (.circI (.andI (.var (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))) .hd)))
  | orL _ ih => exact .circE ih (.circI (.orI₁ .hd))
  | orR _ ih => exact .circE ih (.circI (.orI₂ .hd))
  | exC t ht _ ih => exact .circE ih (.circI (.exI t ht .hd))
  | @impC c p w ts hc hm hq hlen hts _ ih =>
      have hmem : c ∈ Θ := List.mem_of_getElem? hc
      have hlen' : ts.length = c.arity := hlen
      have hf : Prv Θ.forms (Form.foralls ts.length (.imp c.body c.headForm)) := by
        rw [hlen']; exact .var (List.mem_map.2 ⟨c, hmem, rfl⟩)
      have hi := Prv.allEs ts hts hf
      rw [Form.instAll_imp] at hi
      have e : Form.instAll ts c.headForm
          = .circ q (.pred c.head (Tm.instAllList ts (headVars c.arity))) := by
        unfold Clause.headForm; rw [hm]
        show Form.instAll ts (.circ c.q _) = _
        rw [Form.instAll_circ, Form.instAll_pred, hq]
      rw [e] at hi
      exact .circE ih (.impE hi.weaken_cons .hd)

/-- The abstract image of a concrete proof tree (Definition 8.2): constraint
leaves become `val(⋆) : ◯true`, every other node its modal counterpart. -/
def CProof.toA : CProof → AProof
  | .top | .cstr _ _ => .val
  | .andI p q => .andC p.toA q.toA
  | .orL p => .orL p.toA
  | .orR p => .orR p.toA
  | .exI t p => .exC t p.toA
  | .clause w ts p => .impC w ts p.toA

section
variable {isC : String → Bool} {Θ : Program}

/-- **Theorem 6.3** (soundness of abstraction), at the level of proof terms. -/
theorem CTyped.toA (q : Q) (hH : Θ.HeadsOK isC) {S : Form} {p : CProof} (h : CTyped isC Θ S p) :
    ATyped (Θ.abs isC q) q (S.strip isC) p.toA := by
  induction h with
  | top => exact .val
  | cstr hB => rw [Form.strip_pred_C _ hB]; exact .val
  | andI _ _ ih₁ ih₂ => exact .andC ih₁ ih₂
  | orL _ ih => exact .orL ih
  | orR _ ih => exact .orR ih
  | exI t ht _ ih => exact .exC t ht (by rw [← Form.strip_openAt]; exact ih)
  | @clause c p w ts hc hm hlen hts _ ih =>
      rw [Form.strip_pred_of _ (hH c (List.mem_of_getElem? hc))]
      exact .impC (c := c.abs isC q) w ts (Program.abs_getElem? hc) rfl rfl hlen hts
        (by show ATyped _ q (Form.instAll ts (c.body.strip isC)) p.toA
            rw [← Form.strip_instAll]; exact ih)

/-- **Theorem 6.3**: `Θ ⊢ S` gives `Θ♯₂ ⊢ ◯S♯`. -/
theorem CTyped.prv_abs (q : Q) (hH : Θ.HeadsOK isC) {S : Form} {p : CProof}
    (h : CTyped isC Θ S p) : Prv (Θ.abs isC q).forms (.circ q (S.strip isC)) :=
  (h.toA q hH).prv

end

/-! ## The writer monad `C × −` and extraction -/

/-- Values of the types `|S|` of Σ-formulas: `1`, products, sums, `U × −`. -/
inductive Wit where
  | unit
  | pair (a b : Wit)
  | inl (a : Wit)
  | inr (a : Wit)
  | pack (t : Tm) (a : Wit)
  deriving Repr, Inhabited

/-- `C × α`, with constraints as formulas. -/
abbrev WM (α : Type) := Form × α

def WM.val {α : Type} (a : α) : WM α := (.top, a)

def WM.bind {α β : Type} (m : WM α) (f : α → WM β) : WM β := (.and m.1 (f m.2).1, (f m.2).2)

/-- Equality up to `⊣⊢` on the constraint. -/
def WEq {α : Type} (m m' : WM α) : Prop := PEq m.1 m'.1 ∧ m.2 = m'.2

theorem WM.bind_val_left {α β : Type} (a : α) (f : α → WM β) : WEq (WM.bind (WM.val a) f) (f a) :=
  ⟨PEq.top_and _, rfl⟩

theorem WM.bind_val_right {α : Type} (m : WM α) : WEq (WM.bind m WM.val) m :=
  ⟨PEq.and_top _, rfl⟩

theorem WM.bind_assoc {α β γ : Type} (m : WM α) (f : α → WM β) (g : β → WM γ) :
    WEq (WM.bind (WM.bind m f) g) (WM.bind m fun a => WM.bind (f a) g) :=
  ⟨PEq.and_assoc _ _ _, rfl⟩

/-- The monad is commutative: the order of two independent computations does
not matter, up to `⊣⊢`. -/
theorem WM.bind_comm {α β γ : Type} (m : WM α) (n : WM β) (f : α → β → WM γ) :
    WEq (WM.bind m fun a => WM.bind n fun b => f a b) (WM.bind n fun b => WM.bind m fun a => f a b) :=
  ⟨(PEq.and_assoc _ _ _).symm.trans
      ((PEq.and (PEq.and_comm _ _) (PEq.refl _)).trans (PEq.and_assoc _ _ _)), rfl⟩

/-- The extracted constraint and witness of an abstract proof, `|a|`, given a
constraint table `T w t̃ z` (the first component of `θ♯₁ t̃ z` for clause `w`). -/
def AProof.ext (T : Nat → List Tm → Wit → Form) : AProof → WM Wit
  | .val => WM.val .unit
  | .andC p r => WM.bind (p.ext T) fun y => WM.bind (r.ext T) fun z => WM.val (.pair y z)
  | .orL p => WM.bind (p.ext T) fun z => WM.val (.inl z)
  | .orR p => WM.bind (p.ext T) fun z => WM.val (.inr z)
  | .exC t p => WM.bind (p.ext T) fun z => WM.val (.pack t z)
  | .impC w ts p => WM.bind (p.ext T) fun z => (T w ts z, .unit)

/-- Selection-order independence at the level of one node: extracting the two
premises of `∧◯` in either order gives the same result, up to `⊣⊢`. -/
theorem AProof.ext_andC_swap (T : Nat → List Tm → Wit → Form) (p r : AProof) :
    WEq ((AProof.andC p r).ext T)
      (WM.bind (r.ext T) fun z => WM.bind (p.ext T) fun y => WM.val (.pair y z)) :=
  WM.bind_comm (p.ext T) (r.ext T) (fun y z => WM.val (Wit.pair y z))

/-- Definition 6.2's constraint table for a body, as a function of the witness:
the constraint atoms of the disjunct `z` selects, with its existential witnesses. -/
def ctable (isC : String → Bool) : Form → Wit → Form
  | .pred B ts, _ => if isC B then .pred B ts else .top
  | .and A B, .pair a b => .and (ctable isC A a) (ctable isC B b)
  | .or A _, .inl a => ctable isC A a
  | .or _ B, .inr a => ctable isC B a
  | .exists_ A, .pack t a => ctable isC (A.openAt 0 t) a
  | _, _ => .top

/-- The table of a concrete program, clause by clause. -/
def Program.table (isC : String → Bool) (Θ : Program) : Nat → List Tm → Wit → Form :=
  fun w ts z => match Θ[w]? with
    | some c => ctable isC (Form.instAll ts c.body) z
    | none => .top

/-- The witness a concrete proof tree carries. -/
def CProof.wit : CProof → Wit
  | .top | .cstr _ _ | .clause _ _ _ => .unit
  | .andI p q => .pair p.wit q.wit
  | .orL p => .inl p.wit
  | .orR p => .inr p.wit
  | .exI t p => .pack t p.wit

section
variable {isC : String → Bool} {Θ : Program}

/-- **Lemma 8.3**: the table, at the witness of a proof, is its active constraint. -/
theorem CTyped.ctable_wit (hH : Θ.HeadsOK isC) {S : Form} {p : CProof} (h : CTyped isC Θ S p) :
    ctable isC S p.wit = p.active := by
  induction h with
  | top => rfl
  | cstr hB => show (if isC _ = true then _ else _) = _; rw [if_pos hB]; rfl
  | andI _ _ ih₁ ih₂ => show Form.and _ _ = Form.and _ _; rw [ih₁, ih₂]
  | orL _ ih => exact ih
  | orR _ ih => exact ih
  | exI t _ _ ih => exact ih
  | @clause c p w ts hc _ _ _ _ _ =>
      show (if isC c.head = true then _ else _) = Form.top
      rw [if_neg (by rw [hH c (List.mem_of_getElem? hc)]; decide)]

/-- **Lemma 8.4**: extraction from the abstract image returns the proof's
witness, and its latent constraint. -/
theorem CTyped.ext_toA (hH : Θ.HeadsOK isC) {S : Form} {p : CProof} (h : CTyped isC Θ S p) :
    (p.toA.ext (Θ.table isC)).2 = p.wit ∧ PEq (p.toA.ext (Θ.table isC)).1 p.latent := by
  induction h with
  | top => exact ⟨rfl, PEq.refl _⟩
  | cstr _ => exact ⟨rfl, PEq.refl _⟩
  | andI _ _ ih₁ ih₂ =>
      refine ⟨by show Wit.pair _ _ = Wit.pair _ _; rw [ih₁.1, ih₂.1], ?_⟩
      show PEq (.and _ (.and _ .top)) (.and _ _)
      exact PEq.and ih₁.2 ((PEq.and_top _).trans ih₂.2)
  | orL _ ih =>
      exact ⟨by show Wit.inl _ = Wit.inl _; rw [ih.1], (PEq.and_top _).trans ih.2⟩
  | orR _ ih =>
      exact ⟨by show Wit.inr _ = Wit.inr _; rw [ih.1], (PEq.and_top _).trans ih.2⟩
  | exI t _ _ ih =>
      exact ⟨by show Wit.pack t _ = Wit.pack t _; rw [ih.1], (PEq.and_top _).trans ih.2⟩
  | @clause c p w ts hc _ _ _ hp ih =>
      refine ⟨rfl, ?_⟩
      have e : Θ.table isC w ts (p.toA.ext (Θ.table isC)).2 = p.active := by
        rw [ih.1]; unfold Program.table; rw [hc]; exact hp.ctable_wit hH
      show PEq (.and _ (Θ.table isC w ts (p.toA.ext (Θ.table isC)).2)) (.and p.latent p.active)
      rw [e]; exact PEq.and ih.2 (PEq.refl _)

/-- Extracted constraint and active constraint together are the total one. -/
theorem CTyped.ext_total (hH : Θ.HeadsOK isC) {S : Form} {p : CProof} (h : CTyped isC Θ S p) :
    PEq (.and (p.toA.ext (Θ.table isC)).1 p.active) p.total :=
  (PEq.and (h.ext_toA hH).2 (PEq.refl _)).trans ⟨p.total_equiv.2, p.total_equiv.1⟩

end

/-- A query without constraint atoms ("pure", Theorem 9.7). -/
def Form.pureB (isC : String → Bool) : Form → Bool
  | .pred B _ => !isC B
  | .and A B | .or A B => A.pureB isC && B.pureB isC
  | .exists_ A => A.pureB isC
  | _ => true

theorem Form.pureB_openAt (isC : String → Bool) (t : Tm) :
    ∀ (A : Form) (k : Nat), (A.openAt k t).pureB isC = A.pureB isC
  | .top, _ | .bot, _ | .pred _ _, _ | .imp _ _, _ | .circ _ _, _ | .forall_ _, _ => rfl
  | .and A B, k => by
      show ((A.openAt k t).pureB isC && (B.openAt k t).pureB isC) = (A.pureB isC && B.pureB isC)
      rw [Form.pureB_openAt isC t A k, Form.pureB_openAt isC t B k]
  | .or A B, k => by
      show ((A.openAt k t).pureB isC && (B.openAt k t).pureB isC) = (A.pureB isC && B.pureB isC)
      rw [Form.pureB_openAt isC t A k, Form.pureB_openAt isC t B k]
  | .exists_ A, k => Form.pureB_openAt isC t A (k + 1)

theorem Form.strip_pure (isC : String → Bool) {S : Form} (hS : IsSigma S) (hp : S.pureB isC = true) :
    S.strip isC = S := by
  induction hS with
  | top => rfl
  | pred B ts =>
      have : isC B = false := by simpa only [Form.pureB, Bool.not_eq_true'] using hp
      exact Form.strip_pred_of ts this
  | and _ _ ih₁ ih₂ =>
      simp only [Form.pureB, Bool.and_eq_true] at hp
      exact congrArg₂ Form.and (ih₁ hp.1) (ih₂ hp.2)
  | or _ _ ih₁ ih₂ =>
      simp only [Form.pureB, Bool.and_eq_true] at hp
      exact congrArg₂ Form.or (ih₁ hp.1) (ih₂ hp.2)
  | ex _ ih => exact congrArg Form.exists_ (ih hp)

theorem CTyped.active_pure {isC : String → Bool} {Θ : Program} {S : Form} {p : CProof}
    (h : CTyped isC Θ S p) (hp : S.pureB isC = true) : PEq p.active .top := by
  induction h with
  | top => exact PEq.refl _
  | cstr hB => rw [Form.pureB, hB] at hp; exact absurd hp (by decide)
  | andI _ _ ih₁ ih₂ =>
      simp only [Form.pureB, Bool.and_eq_true] at hp
      exact (PEq.and (ih₁ hp.1) (ih₂ hp.2)).trans (PEq.top_and _)
  | orL _ ih =>
      simp only [Form.pureB, Bool.and_eq_true] at hp
      exact ih hp.1
  | orR _ ih =>
      simp only [Form.pureB, Bool.and_eq_true] at hp
      exact ih hp.2
  | exI t _ _ ih => exact ih (by rw [Form.pureB_openAt]; exact hp)
  | clause _ _ _ _ _ _ _ => exact PEq.refl _

/-- **Theorem 9.7**: for a pure query, the answer constraint of a successful
derivation is, up to `⊣⊢`, the constraint extracted from an abstract proof of
`◯φ` against `Θ♯₂`. -/
theorem thm_9_7 {isC : String → Bool} {Θ : Program} (q : Q) (hH : Θ.HeadsOK isC)
    {ok : Form → Prop} {φ c : Form}
    (hD : Steps isC Θ ok ⟨.top, [φ]⟩ ⟨c, []⟩) (hφ : IsSigma φ) (hpure : φ.pureB isC = true) :
    ∃ p : CProof, CTyped isC Θ φ p ∧ ATyped (Θ.abs isC q) q φ p.toA ∧
      PEq c (p.toA.ext (Θ.table isC)).1 := by
  obtain ⟨ps, hF, hE⟩ := steps_forest hD rfl
  cases hF with
  | cons hp hF' =>
    cases hF'
    rename_i p
    refine ⟨p, hp, ?_, ?_⟩
    · have := hp.toA q hH
      rwa [Form.strip_pure isC hφ hpure] at this
    · have e1 : PEq (.and .top (totals [p])) p.total := (PEq.top_and _).trans (PEq.and_top _)
      have e2 : PEq p.total (p.toA.ext (Θ.table isC)).1 :=
        (hp.ext_total hH).symm.trans ((PEq.and (PEq.refl _) (hp.active_pure hpure)).trans
          (PEq.and_top _))
      exact (hE.trans e1).trans e2

/-! ## Refinement and Theorem 6.8 -/

/-- The disjunct of a Σ-formula that a witness selects, with the existential
witnesses substituted: Table 1, with terms in place of the variables `ỹ`. -/
def atW : Form → Wit → Form
  | .top, _ => .top
  | .pred B ts, _ => .pred B ts
  | .and A B, .pair a b => .and (atW A a) (atW B b)
  | .or A _, .inl a => atW A a
  | .or _ B, .inr a => atW B a
  | .exists_ A, .pack t a => atW (A.openAt 0 t) a
  | _, _ => .bot

/-- The witness terms are locally closed. -/
def Wit.lc : Wit → Prop
  | .unit => True
  | .pair a b => a.lc ∧ b.lc
  | .inl a | .inr a => a.lc
  | .pack t a => Tm.lcAt 0 t ∧ a.lc

/-- Definition 6.5, through its instances: `Π` proves every instance of the
refined clauses of `Θ♯` with table `T`. -/
def RefinedBy (Δ : List Form) (Θa : Program) (T : Nat → List Tm → Wit → Form) : Prop :=
  ∀ (w : Nat) (c : Clause) (ts : List Tm) (z : Wit), Θa[w]? = some c → c.modal = true →
    ts.length = c.arity → (∀ t ∈ ts, Tm.lcAt 0 t) → z.lc →
    Prv Δ (.imp (.and (T w ts z) (atW (Form.instAll ts c.body) z))
      (.pred c.head (Tm.instAllList ts (headVars c.arity))))

theorem ATyped.refine {Δ : List Form} {Θa : Program} {T : Nat → List Tm → Wit → Form} {q : Q}
    (hR : RefinedBy Δ Θa T) {S : Form} {a : AProof} (h : ATyped Θa q S a) :
    (a.ext T).2.lc ∧ Prv Δ (.imp (a.ext T).1 (atW S (a.ext T).2)) ∧
      Prv Δ (.imp (atW S (a.ext T).2) S) := by
  induction h with
  | val => exact ⟨trivial, .impI .topI, .impI .topI⟩
  | andC _ _ ih₁ ih₂ =>
      refine ⟨⟨ih₁.1, ih₂.1⟩, ?_, ?_⟩
      · exact .impI (.andI (.impE ih₁.2.1.weaken_cons (.andE₁ .hd))
          (.impE ih₂.2.1.weaken_cons (.andE₁ (.andE₂ .hd))))
      · exact .impI (.andI (.impE ih₁.2.2.weaken_cons (.andE₁ .hd))
          (.impE ih₂.2.2.weaken_cons (.andE₂ .hd)))
  | orL _ ih =>
      exact ⟨ih.1, .impI (.impE ih.2.1.weaken_cons (.andE₁ .hd)),
        .impI (.orI₁ (.impE ih.2.2.weaken_cons .hd))⟩
  | orR _ ih =>
      exact ⟨ih.1, .impI (.impE ih.2.1.weaken_cons (.andE₁ .hd)),
        .impI (.orI₂ (.impE ih.2.2.weaken_cons .hd))⟩
  | exC t ht _ ih =>
      exact ⟨⟨ht, ih.1⟩, .impI (.impE ih.2.1.weaken_cons (.andE₁ .hd)),
        .impI (.exI t ht (.impE ih.2.2.weaken_cons .hd))⟩
  | @impC c p w ts hc hm _ hlen hts _ ih =>
      refine ⟨trivial, ?_, .impI .hd⟩
      have hr := hR w c ts _ hc hm hlen hts ih.1
      exact .impI (.impE hr.weaken_cons (.andI (.andE₂ .hd) (.impE ih.2.1.weaken_cons (.andE₁ .hd))))

/-- **Theorem 6.8**: a program that refines `Θ♯` with table `T` proves the
constraint extracted from any abstract proof of `◯S`, implying `S`. -/
theorem thm_6_8 {Δ : List Form} {Θa : Program} {T : Nat → List Tm → Wit → Form} {q : Q}
    (hR : RefinedBy Δ Θa T) {S : Form} {a : AProof} (h : ATyped Θa q S a) :
    Prv Δ (.imp (a.ext T).1 S) :=
  let r := h.refine hR
  .impI (.impE r.2.2.weaken_cons (.impE r.2.1.weaken_cons .hd))

theorem ctable_atW (isC : String → Bool) {Γ : List Form} :
    ∀ (z : Wit) {S : Form}, IsSigma S → z.lc →
      Prv Γ (ctable isC S z) → Prv Γ (atW (S.strip isC) z) → Prv Γ S := by
  intro z
  induction z with
  | unit =>
      intro S hS _ h₁ h₂
      cases hS with
      | top => exact .topI
      | pred B ts =>
          by_cases hB : isC B = true
          · exact (show Prv Γ (if isC B = true then .pred B ts else .top) from h₁) |> fun h => by
              rw [if_pos hB] at h; exact h
          · have h₂' : Prv Γ (atW (if isC B = true then .top else .pred B ts) .unit) := h₂
            rw [if_neg hB] at h₂'; exact h₂'
      | and _ _ => exact .botE h₂
      | or _ _ => exact .botE h₂
      | ex _ => exact .botE h₂
  | pair a b iha ihb =>
      intro S hS hz h₁ h₂
      cases hS with
      | top => exact .topI
      | pred B ts =>
          by_cases hB : isC B = true
          · have h := (show Prv Γ (if isC B = true then .pred B ts else .top) from h₁)
            rw [if_pos hB] at h; exact h
          · have h₂' : Prv Γ (atW (if isC B = true then .top else .pred B ts) (.pair a b)) := h₂
            rw [if_neg hB] at h₂'; exact h₂'
      | and hA hB => exact .andI (iha hA hz.1 (.andE₁ h₁) (.andE₁ h₂)) (ihb hB hz.2 (.andE₂ h₁) (.andE₂ h₂))
      | or _ _ => exact .botE h₂
      | ex _ => exact .botE h₂
  | inl a ih =>
      intro S hS hz h₁ h₂
      cases hS with
      | top => exact .topI
      | pred B ts =>
          by_cases hB : isC B = true
          · have h := (show Prv Γ (if isC B = true then .pred B ts else .top) from h₁)
            rw [if_pos hB] at h; exact h
          · have h₂' : Prv Γ (atW (if isC B = true then .top else .pred B ts) (.inl a)) := h₂
            rw [if_neg hB] at h₂'; exact h₂'
      | and _ _ => exact .botE h₂
      | or hA _ => exact .orI₁ (ih hA hz h₁ h₂)
      | ex _ => exact .botE h₂
  | inr a ih =>
      intro S hS hz h₁ h₂
      cases hS with
      | top => exact .topI
      | pred B ts =>
          by_cases hB : isC B = true
          · have h := (show Prv Γ (if isC B = true then .pred B ts else .top) from h₁)
            rw [if_pos hB] at h; exact h
          · have h₂' : Prv Γ (atW (if isC B = true then .top else .pred B ts) (.inr a)) := h₂
            rw [if_neg hB] at h₂'; exact h₂'
      | and _ _ => exact .botE h₂
      | or _ hB => exact .orI₂ (ih hB hz h₁ h₂)
      | ex _ => exact .botE h₂
  | pack t a ih =>
      intro S hS hz h₁ h₂
      cases hS with
      | top => exact .topI
      | pred B ts =>
          by_cases hB : isC B = true
          · have h := (show Prv Γ (if isC B = true then .pred B ts else .top) from h₁)
            rw [if_pos hB] at h; exact h
          · have h₂' : Prv Γ (atW (if isC B = true then .top else .pred B ts) (.pack t a)) := h₂
            rw [if_neg hB] at h₂'; exact h₂'
      | and _ _ => exact .botE h₂
      | or _ _ => exact .botE h₂
      | @ex A hA =>
          have h₂' : Prv Γ (atW ((A.strip isC).openAt 0 t) a) := h₂
          rw [← Form.strip_openAt] at h₂'
          exact .exI t hz.1 (ih (hA.openAt' 0 t) hz.2 h₁ h₂')

/-- **Proposition 6.6**, first half: a non-modal program refines its own
abstraction with its own constraint table. -/
theorem refinedBy_abs {isC : String → Bool} {Θ : Program} (q : Q)
    (hm : ∀ c ∈ Θ, c.modal = false) : RefinedBy Θ.forms (Θ.abs isC q) (Θ.table isC) := by
  intro w c' ts z hc' _ hlen hts hz
  rw [Program.abs, List.getElem?_map] at hc'
  cases hc : Θ[w]? with
  | none => rw [hc] at hc'; cases hc'
  | some c =>
    rw [hc] at hc'
    have e0 : some (c.abs isC q) = some c' := hc'
    cases e0
    have hmem : c ∈ Θ := List.mem_of_getElem? hc
    have hlen' : ts.length = c.arity := hlen
    have hf : Prv Θ.forms (Form.foralls ts.length (.imp c.body c.headForm)) := by
      rw [hlen']; exact .var (List.mem_map.2 ⟨c, hmem, rfl⟩)
    have hi := Prv.allEs ts hts hf
    rw [Form.instAll_imp] at hi
    have e : Form.instAll ts c.headForm = .pred c.head (Tm.instAllList ts (headVars c.arity)) := by
      unfold Clause.headForm; rw [hm c hmem]; exact Form.instAll_pred ts _ _
    rw [e] at hi
    have ht : Θ.table isC w ts z = ctable isC (Form.instAll ts c.body) z := by
      unfold Program.table; rw [hc]
    refine .impI (.impE hi.weaken_cons (ctable_atW isC z (c.body_sigma.instAll ts) hz ?_ ?_))
    · rw [← ht]; exact .andE₁ .hd
    · exact (congrArg (fun X => Prv (Form.and (Θ.table isC w ts z)
          (atW (Form.instAll ts (c.abs isC q).body) z) :: Θ.forms) (atW X z))
          (Form.strip_instAll isC ts c.body)).mpr (Prv.andE₂ Prv.hd)

/-- **Corollary 9.8**, by the draft's route (Theorem 6.8 and Proposition 6.6):
a non-modal program proves the constraint extracted from any abstract proof of
`◯S` against its abstraction, implying `S`. -/
theorem cor_9_8_abs {isC : String → Bool} {Θ : Program} {q : Q}
    (hm : ∀ c ∈ Θ, c.modal = false) {S : Form} {a : AProof} (h : ATyped (Θ.abs isC q) q S a) :
    Prv Θ.forms (.imp (a.ext (Θ.table isC)).1 S) :=
  thm_6_8 (refinedBy_abs q hm) h


/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.Form.strip_openAt' does not depend on any axioms -/
#guard_msgs in #print axioms Form.strip_openAt

/-- info: 'LaxLogic.QLL.Form.strip_pure' depends on axioms: [propext] -/
#guard_msgs in #print axioms Form.strip_pure

/-- info: 'LaxLogic.QLL.ATyped.prv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ATyped.prv

/-- info: 'LaxLogic.QLL.CTyped.toA' depends on axioms: [propext] -/
#guard_msgs in #print axioms CTyped.toA

/-- info: 'LaxLogic.QLL.CTyped.prv_abs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CTyped.prv_abs

/-- info: 'LaxLogic.QLL.WM.bind_val_left' depends on axioms: [propext] -/
#guard_msgs in #print axioms WM.bind_val_left

/-- info: 'LaxLogic.QLL.WM.bind_val_right' depends on axioms: [propext] -/
#guard_msgs in #print axioms WM.bind_val_right

/-- info: 'LaxLogic.QLL.WM.bind_assoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms WM.bind_assoc

/-- info: 'LaxLogic.QLL.WM.bind_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms WM.bind_comm

/-- info: 'LaxLogic.QLL.AProof.ext_andC_swap' depends on axioms: [propext] -/
#guard_msgs in #print axioms AProof.ext_andC_swap

/-- info: 'LaxLogic.QLL.CTyped.ctable_wit' depends on axioms: [propext] -/
#guard_msgs in #print axioms CTyped.ctable_wit

/-- info: 'LaxLogic.QLL.CTyped.ext_toA' depends on axioms: [propext] -/
#guard_msgs in #print axioms CTyped.ext_toA

/-- info: 'LaxLogic.QLL.CTyped.ext_total' depends on axioms: [propext] -/
#guard_msgs in #print axioms CTyped.ext_total

/-- info: 'LaxLogic.QLL.thm_9_7' depends on axioms: [propext] -/
#guard_msgs in #print axioms thm_9_7

/-- info: 'LaxLogic.QLL.ATyped.refine' depends on axioms: [propext] -/
#guard_msgs in #print axioms ATyped.refine

/-- info: 'LaxLogic.QLL.thm_6_8' depends on axioms: [propext] -/
#guard_msgs in #print axioms thm_6_8

/-- info: 'LaxLogic.QLL.ctable_atW' depends on axioms: [propext] -/
#guard_msgs in #print axioms ctable_atW

/-- info: 'LaxLogic.QLL.refinedBy_abs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms refinedBy_abs

/-- info: 'LaxLogic.QLL.cor_9_8_abs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cor_9_8_abs

end LaxLogic.QLL
