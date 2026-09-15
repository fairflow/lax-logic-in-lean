/-
# `LaxLogic.QLL.CLPOper` — goal reduction (Table 2) and Theorem 9.4, `◯`-free

Stage 6, first pass (`docs/qll-clp-review.md` §4).  A goal is `c □ φ₁,…,φₙ`: a
constraint and a list of Σ-formulas.  A derivation step (Definition 9.2, Table
2) rewrites one `φᵢ`, at any position, so the selection rule is arbitrary:

    1  B(t̃)       ⟶  removed, c ↦ c ∧ B(t̃)      (B a constraint; ok c′ required)
    0  true        ⟶  removed                       (not in Table 2; Σ contains true)
    2  φ₁ ∨ φ₂     ⟶  φ₁   or   φ₂
    3  φ₁ ∧ φ₂     ⟶  φ₁, φ₂
    4  ∃x. φ       ⟶  φ[t/x]                        (t locally closed; a fresh name in the engine)
    5  P(t̃)        ⟶  ψ[t̃/ỹ]                        (w : ∀ỹ. ψ ⊃ P(ỹ) in Θ)

`ok` is the solvability test on the new constraint (the draft requires `c′`
solvable); it plays no part in soundness.

**Theorem 9.4** (`steps_forest`): a successful derivation from `d □ φ̄` to
`d₀ □ ε` yields proof trees `pᵢ` of the `φᵢ` with

    d₀  ⊣⊢  d ∧ total(p₁) ∧ … ∧ total(pₙ)

and so (**Corollary 9.8**, `steps_sound`) `Θ ⊢ d₀ ⊃ φᵢ` for every `i`.
-/
import LaxLogic.QLL.CLPCore

namespace LaxLogic.QLL

/-- `c □ φ₁,…,φₙ`. -/
structure Goal where
  c : Form
  gs : List Form

/-- One step of Table 2, at any position. -/
inductive Step (isC : String → Bool) (Θ : Program) (ok : Form → Prop) : Goal → Goal → Prop
  | cstr {c : Form} {l r : List Form} {B : String} {ts : List Tm} :
      isC B = true → ok (.and c (.pred B ts)) →
      Step isC Θ ok ⟨c, l ++ .pred B ts :: r⟩ ⟨.and c (.pred B ts), l ++ r⟩
  | top {c : Form} {l r : List Form} : Step isC Θ ok ⟨c, l ++ .top :: r⟩ ⟨c, l ++ r⟩
  | orL {c : Form} {l r : List Form} {A B : Form} :
      Step isC Θ ok ⟨c, l ++ .or A B :: r⟩ ⟨c, l ++ A :: r⟩
  | orR {c : Form} {l r : List Form} {A B : Form} :
      Step isC Θ ok ⟨c, l ++ .or A B :: r⟩ ⟨c, l ++ B :: r⟩
  | and {c : Form} {l r : List Form} {A B : Form} :
      Step isC Θ ok ⟨c, l ++ .and A B :: r⟩ ⟨c, l ++ A :: B :: r⟩
  | ex {c : Form} {l r : List Form} {A : Form} (t : Tm) : Tm.lcAt 0 t →
      Step isC Θ ok ⟨c, l ++ .exists_ A :: r⟩ ⟨c, l ++ A.openAt 0 t :: r⟩
  | clause {c : Form} {l r : List Form} {cl : Clause} (w : Nat) (ts : List Tm) :
      Θ[w]? = some cl → cl.modal = false → ts.length = cl.arity → (∀ t ∈ ts, Tm.lcAt 0 t) →
      Step isC Θ ok ⟨c, l ++ .pred cl.head (Tm.instAllList ts (headVars cl.arity)) :: r⟩
        ⟨c, l ++ Form.instAll ts cl.body :: r⟩

/-- Derivations (Definition 9.3): finite sequences of steps. -/
inductive Steps (isC : String → Bool) (Θ : Program) (ok : Form → Prop) : Goal → Goal → Prop
  | refl (g : Goal) : Steps isC Θ ok g g
  | step {g g' g'' : Goal} : Step isC Θ ok g g' → Steps isC Θ ok g' g'' → Steps isC Θ ok g g''

/-! ## Provable equivalence, and conjunctions of lists -/

/-- `A ⊣⊢ B`. -/
def PEq (A B : Form) : Prop := Prv [A] B ∧ Prv [B] A

/-- Cut for single-assumption contexts. -/
theorem Prv.cut1 {A B C : Form} (h₁ : Prv [A] B) (h₂ : Prv [B] C) : Prv [A] C :=
  .impE ((Prv.impI h₂).weaken fun _ h => nomatch h) h₁

/-- `⊣⊢` is reflexive. -/
theorem PEq.refl (A : Form) : PEq A A := ⟨.hd, .hd⟩
/-- `⊣⊢` is symmetric. -/
theorem PEq.symm {A B : Form} (h : PEq A B) : PEq B A := ⟨h.2, h.1⟩
/-- `⊣⊢` is transitive. -/
theorem PEq.trans {A B C : Form} (h₁ : PEq A B) (h₂ : PEq B C) : PEq A C :=
  ⟨h₁.1.cut1 h₂.1, h₂.2.cut1 h₁.2⟩

/-- `⊣⊢` is a congruence for `∧`. -/
theorem PEq.and {A A' B B' : Form} (hA : PEq A A') (hB : PEq B B') :
    PEq (.and A B) (.and A' B') :=
  ⟨.andI (Prv.cut1 (.andE₁ .hd) hA.1) (Prv.cut1 (.andE₂ .hd) hB.1),
   .andI (Prv.cut1 (.andE₁ .hd) hA.2) (Prv.cut1 (.andE₂ .hd) hB.2)⟩

/-- `∧` is associative up to `⊣⊢`. -/
theorem PEq.and_assoc (A B C : Form) : PEq (.and (.and A B) C) (.and A (.and B C)) :=
  ⟨.andI (.andE₁ (.andE₁ .hd)) (.andI (.andE₂ (.andE₁ .hd)) (.andE₂ .hd)),
   .andI (.andI (.andE₁ .hd) (.andE₁ (.andE₂ .hd))) (.andE₂ (.andE₂ .hd))⟩

/-- `∧` is commutative up to `⊣⊢`. -/
theorem PEq.and_comm (A B : Form) : PEq (.and A B) (.and B A) :=
  ⟨.andI (.andE₂ .hd) (.andE₁ .hd), .andI (.andE₂ .hd) (.andE₁ .hd)⟩

/-- `⊤` is a left unit for `∧` up to `⊣⊢`. -/
theorem PEq.top_and (A : Form) : PEq (.and .top A) A := ⟨.andE₂ .hd, .andI .topI .hd⟩

/-- `⊤` is a right unit for `∧` up to `⊣⊢`. -/
theorem PEq.and_top (A : Form) : PEq (.and A .top) A := ⟨.andE₁ .hd, .andI .hd .topI⟩

/-- `φ₁ ∧ (φ₂ ∧ ( … ∧ true))`. -/
def conjs : List Form → Form
  | [] => .top
  | A :: As => .and A (conjs As)

/-- Pulling an element out of the middle. -/
theorem conjs_mid : ∀ (l r : List Form) (x : Form),
    PEq (conjs (l ++ x :: r)) (.and x (conjs (l ++ r)))
  | [], _, x => PEq.refl _
  | a :: l, r, x => by
      show PEq (.and a (conjs (l ++ x :: r))) (.and x (.and a (conjs (l ++ r))))
      refine (PEq.and (PEq.refl a) (conjs_mid l r x)).trans ?_
      refine (PEq.and_assoc a x _).symm.trans ?_
      refine (PEq.and (PEq.and_comm a x) (PEq.refl _)).trans ?_
      exact PEq.and_assoc x a _

/-! ## Forests of proof trees -/

/-- `ps` proves the list of goals `gs`, pointwise. -/
inductive Forest (isC : String → Bool) (Θ : Program) : List Form → List CProof → Prop
  | nil : Forest isC Θ [] []
  | cons {A : Form} {p : CProof} {gs : List Form} {ps : List CProof} :
      CTyped isC Θ A p → Forest isC Θ gs ps → Forest isC Θ (A :: gs) (p :: ps)

/-- A forest for `l ++ x :: r` splits into forests for `l`, `r` and a tree for `x`. -/
theorem Forest.split {isC : String → Bool} {Θ : Program} :
    ∀ (l : List Form) {x : Form} {r : List Form} {ps : List CProof},
      Forest isC Θ (l ++ x :: r) ps →
      ∃ psl p psr, ps = psl ++ p :: psr ∧ Forest isC Θ l psl ∧ CTyped isC Θ x p ∧ Forest isC Θ r psr
  | [], _, _, _, .cons hx hr => ⟨[], _, _, rfl, .nil, hx, hr⟩
  | _ :: l, _, _, _, .cons ha h => by
      obtain ⟨psl, p, psr, rfl, hl, hx, hr⟩ := Forest.split l h
      exact ⟨_ :: psl, p, psr, rfl, .cons ha hl, hx, hr⟩

/-- A forest for `l ++ r` splits into forests for `l` and `r`. -/
theorem Forest.split_app {isC : String → Bool} {Θ : Program} :
    ∀ (l : List Form) {r : List Form} {ps : List CProof}, Forest isC Θ (l ++ r) ps →
      ∃ psl psr, ps = psl ++ psr ∧ Forest isC Θ l psl ∧ Forest isC Θ r psr
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | _ :: l, _, _, .cons ha h => by
      obtain ⟨psl, psr, rfl, hl, hr⟩ := Forest.split_app l h
      exact ⟨_ :: psl, psr, rfl, .cons ha hl, hr⟩

/-- Forests for `l` and `r` join into one for `l ++ r`. -/
theorem Forest.append {isC : String → Bool} {Θ : Program} :
    ∀ {l r : List Form} {psl psr : List CProof},
      Forest isC Θ l psl → Forest isC Θ r psr → Forest isC Θ (l ++ r) (psl ++ psr)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ha hl, h => .cons ha (Forest.append hl h)

/-! ## Theorem 9.4 -/

/-- The totals of a forest, conjoined. -/
def totals (ps : List CProof) : Form := conjs (ps.map CProof.total)

/-- A tree's total can be moved to the front, up to `⊣⊢`. -/
theorem totals_mid (psl psr : List CProof) (p : CProof) :
    PEq (totals (psl ++ p :: psr)) (.and p.total (totals (psl ++ psr))) := by
  unfold totals
  rw [List.map_append, List.map_cons, List.map_append]
  exact conjs_mid _ _ _

/-- Totals depend only on the trees' totals. -/
theorem totals_congr (psl psr : List CProof) {x y : CProof} (h : x.total = y.total) :
    totals (psl ++ x :: psr) = totals (psl ++ y :: psr) := by
  unfold totals; rw [List.map_append, List.map_cons, List.map_append, List.map_cons, h]

/-- **Theorem 9.4**, `◯`-free: a successful derivation yields a forest of proofs
of the goals whose totals, conjoined with the initial constraint, are
equivalent to the answer constraint. -/
theorem steps_forest {isC : String → Bool} {Θ : Program} {ok : Form → Prop} :
    ∀ {g g' : Goal}, Steps isC Θ ok g g' → g'.gs = [] →
      ∃ ps, Forest isC Θ g.gs ps ∧ PEq g'.c (.and g.c (totals ps))
  | _, _, .refl ⟨c, gs⟩, hnil => by
      simp only at hnil; subst hnil
      exact ⟨[], .nil, (PEq.and_top c).symm⟩
  | _, _, .step hs rest, hnil => by
      obtain ⟨ps', hF, hE⟩ := steps_forest rest hnil
      cases hs with
      | @cstr c l r B ts hB _ =>
          obtain ⟨psl, psr, rfl, hl, hr⟩ := Forest.split_app l hF
          refine ⟨psl ++ .cstr B ts :: psr, Forest.append hl (.cons (.cstr hB) hr), ?_⟩
          refine hE.trans ((PEq.and_assoc _ _ _).trans (PEq.and (PEq.refl c) ?_))
          exact (totals_mid psl psr (.cstr B ts)).symm
      | @top c l r =>
          obtain ⟨psl, psr, rfl, hl, hr⟩ := Forest.split_app l hF
          refine ⟨psl ++ .top :: psr, Forest.append hl (.cons .top hr), ?_⟩
          refine hE.trans (PEq.and (PEq.refl c) ?_)
          exact ((totals_mid psl psr .top).trans (PEq.top_and _)).symm
      | @orL c l r A B =>
          obtain ⟨psl, p, psr, rfl, hl, hx, hr⟩ := Forest.split l hF
          refine ⟨psl ++ .orL p :: psr, Forest.append hl (.cons (.orL hx) hr), ?_⟩
          rw [totals_congr psl psr (x := .orL p) (y := p) rfl]
          exact hE
      | @orR c l r A B =>
          obtain ⟨psl, p, psr, rfl, hl, hx, hr⟩ := Forest.split l hF
          refine ⟨psl ++ .orR p :: psr, Forest.append hl (.cons (.orR hx) hr), ?_⟩
          rw [totals_congr psl psr (x := .orR p) (y := p) rfl]
          exact hE
      | @and c l r A B =>
          obtain ⟨psl, p, psr, rfl, hl, hx, hr⟩ := Forest.split l hF
          cases hr with
          | @cons _ q _ psr' hy hr' =>
              refine ⟨psl ++ .andI p q :: psr', Forest.append hl (.cons (.andI hx hy) hr'), ?_⟩
              refine hE.trans (PEq.and (PEq.refl c) ?_)
              refine (totals_mid psl (q :: psr') p).trans ?_
              refine (PEq.and (PEq.refl _) (totals_mid psl psr' q)).trans ?_
              refine (PEq.and_assoc _ _ _).symm.trans ?_
              exact (totals_mid psl psr' (.andI p q)).symm
      | @ex c l r A t ht =>
          obtain ⟨psl, p, psr, rfl, hl, hx, hr⟩ := Forest.split l hF
          refine ⟨psl ++ .exI t p :: psr, Forest.append hl (.cons (.exI t ht hx) hr), ?_⟩
          rw [totals_congr psl psr (x := .exI t p) (y := p) rfl]
          exact hE
      | @clause c l r cl w ts hc hm hlen hts =>
          obtain ⟨psl, p, psr, rfl, hl, hx, hr⟩ := Forest.split l hF
          refine ⟨psl ++ .clause w ts p :: psr,
            Forest.append hl (.cons (.clause w ts hc hm hlen hts hx) hr), ?_⟩
          rw [totals_congr psl psr (x := .clause w ts p) (y := p) rfl]
          exact hE

/-- The answer constraint entails every goal of a forest. -/
theorem Forest.prv {isC : String → Bool} {Θ : Program} :
    ∀ {gs : List Form} {ps : List CProof}, Forest isC Θ gs ps →
      Prv Θ.forms (.imp (totals ps) (conjs gs))
  | _, _, .nil => .impI .topI
  | _, _, .cons hA h => by
      have h₁ := hA.prv_total
      have h₂ := Forest.prv h
      exact .impI (.andI (.impE h₁.weaken_cons (.andE₁ .hd)) (.impE h₂.weaken_cons (.andE₂ .hd)))

/-- **Corollary 9.8**, `◯`-free: the answer constraint of a successful derivation
entails the initial constraint and the goals. -/
theorem steps_sound {isC : String → Bool} {Θ : Program} {ok : Form → Prop} {g g' : Goal}
    (h : Steps isC Θ ok g g') (hnil : g'.gs = []) :
    Prv Θ.forms (.imp g'.c (.and g.c (conjs g.gs))) := by
  obtain ⟨ps, hF, hE⟩ := steps_forest h hnil
  have hf := hF.prv
  have e' : Prv (g'.c :: Θ.forms) (.and g.c (totals ps)) :=
    hE.1.weaken fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact nomatch hx
  exact .impI (.andI (.andE₁ e') (.impE hf.weaken_cons (.andE₂ e')))


/-! ## Axioms -/

/-- info: 'LaxLogic.QLL.steps_forest' depends on axioms: [propext] -/
#guard_msgs in #print axioms steps_forest

/-- info: 'LaxLogic.QLL.steps_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms steps_sound

/-- info: 'LaxLogic.QLL.Forest.prv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Forest.prv

end LaxLogic.QLL
