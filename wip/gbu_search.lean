/-
# `Gbu(G)`: Theorem 8, the correctness of `BSearch`

Stage 3 of the adoption, continued.  Source: Fiorentini–Ferrari,
arXiv:1804.06689, §5, lines 3287–4314.

`BSearch(τ, DB(G))` is a *backtracking-free* proof-search procedure: at
each of the two non-invertible rules (`R∨ₖ`, `L⊃`) it consults the
saturated database instead of guessing.  Its correctness statement
(source 4215) is

    Let `DB(G)` be saturated and let `τ` satisfy
      (BSr1)  `DB(G) ⋫ τ`
      (BSr2)  if `τ = Ω →g C` then `Ω ⊆ Ĝ`.
    Then `BSearch(τ, DB(G))` computes a `Gbu(G)`-derivation of `τ`.

Since a `Gbu(G)`-derivation is a `Type`-valued family here, "computes a
derivation" is mechanised as `Nonempty (GbuR …)` / `Nonempty (GbuI …)`
with every case decided — the two `Decidable` arguments below are the
database queries the paper's `Search` performs, so the proof is a
procedure and not an appeal to excluded middle.

## Divergences (continuing D1–D6 of `docs/gbu-adoption-plan.md`)

* **D7 — the well-formedness invariant is explicit.**  The paper leaves
  `Ψ ⊆ Sf^L(G)` and `C ∈ Sf^R(G)` implicit in "a `Gbu(G)`-sequent".  We
  carry them as hypotheses of `SearchOk`; they are exactly what makes
  `unclosed_lt` (Property 2, the `R⊃ₙᵢ` measure drop) apply and what the
  FRJ side conditions of Lemmas 9–12 need.

* **D8 — ◯-freeness is a hypothesis, not an assumption of the syntax.**
  Our `Form` has a `◯` constructor because the same datatype carries the
  modal development.  §5 is a result about IPC, so `search` below takes
  `hcircL`/`hcircR`: no left or right subformula of `G` is a `◯`-formula.
  These two hypotheses are consumed at EXACTLY three points, marked
  `-- ◯-SEAM` in the proof:

    1. a `◯`-formula in the regular left zone (no `L◯` rule exists);
    2. a `◯` goal in a regular sequent (no regular `R◯` rule);
    3. a `◯` goal in an irregular sequent (no focused `R◯` rule).

  Those three points are the complete obligation list for `Gbu◯(G)`:
  any extension of `Gbu` to the modal language must supply a rule (or a
  discharge) at each, and nowhere else.  This is the deliverable of the
  present stage — the rules are read off the gaps rather than guessed.
-/
import wip.gbu_db
import FRJ.SoundV

namespace FRJ.Gbu

open FRJ Form

/-! ## Decidable case split, without `Classical` -/

private theorem byDec {p : Prop} (d : Decidable p) {q : Prop}
    (h1 : p → q) (h2 : ¬ p → q) : q := by
  cases d with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

private def decClo (Ψ : List Form) (A : Form) : Decidable (Clo Ψ A) :=
  match h : cloB Ψ A with
  | true => isTrue (cloB_iff.mp h)
  | false => isFalse (by intro hc; rw [cloB_iff.mpr hc] at h; exact Bool.noConfusion h)

/-- Scan a list for a failure of a decidable predicate. -/
private theorem findNot {α : Type} {P : α → Prop} (dec : ∀ a, Decidable (P a)) :
    ∀ l : List α, (∀ a ∈ l, P a) ∨ ∃ a, a ∈ l ∧ ¬ P a
  | [] => Or.inl (fun _ ha => absurd ha List.not_mem_nil)
  | a :: t =>
      byDec (dec a)
        (fun h =>
          match findNot dec t with
          | Or.inl hall => Or.inl (by
              intro b hb
              rcases List.mem_cons.mp hb with rfl | hb'
              · exact h
              · exact hall b hb')
          | Or.inr ⟨b, hb, hnb⟩ => Or.inr ⟨b, List.mem_cons_of_mem _ hb, hnb⟩)
        (fun h => Or.inr ⟨a, List.mem_cons_self, h⟩)

/-! ## Context bookkeeping -/

private theorem ctxEq_cons_self {Γ : List Form} {A : Form} (h : A ∈ Γ) :
    Γ ≐ A :: Γ := by
  intro x
  constructor
  · exact fun hx => List.mem_cons_of_mem _ hx
  · intro hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h
    · exact hx'

private theorem ctxEq_split {l r : List Form} {X : Form} :
    (l ++ X :: r) ≐ X :: (l ++ r) := by
  intro x
  constructor
  · intro h
    rcases List.mem_append.mp h with h' | h'
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ h')
    · rcases List.mem_cons.mp h' with rfl | h''
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ h'')
  · intro h
    rcases List.mem_cons.mp h with rfl | h'
    · exact List.mem_append_right _ List.mem_cons_self
    · rcases List.mem_append.mp h' with h'' | h''
      · exact List.mem_append_left _ h''
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h'')

private theorem ctxEq_symm {l m : List Form} (h : l ≐ m) : m ≐ l :=
  fun x => (h x).symm

/-- `Ψ` is either all atoms-and-implications, or it splits around a
member that is neither. -/
private theorem orTrue {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

private def isAtImp (X : Form) : Bool := X.isPV || X.isImp

private theorem splitCtx : ∀ Ψ : List Form,
    (∀ X ∈ Ψ, isAtImp X = true) ∨
    (∃ l r X, Ψ = l ++ X :: r ∧ isAtImp X = false)
  | [] => Or.inl (fun _ hX => absurd hX List.not_mem_nil)
  | X :: t =>
      match h : isAtImp X with
      | true =>
          match splitCtx t with
          | Or.inl hall => Or.inl (by
              intro Y hY
              rcases List.mem_cons.mp hY with rfl | hY'
              · exact h
              · exact hall Y hY')
          | Or.inr ⟨l, r, Y, hY, hY'⟩ =>
              Or.inr ⟨X :: l, r, Y, by rw [hY]; rfl, hY'⟩
      | false => Or.inr ⟨[], t, X, rfl, h⟩

/-! ## Transport of the evaluation relation along `≐` -/

private theorem evalR_ctxEq {D : FSeq → Prop} {Ψ Ψ' : List Form} {C : Form}
    (h : Ψ ≐ Ψ') (he : EvalR D Ψ C) : EvalR D Ψ' C := by
  obtain ⟨Γ, hm, hcl⟩ := he
  exact ⟨Γ, hm, fun X hX => hcl X ((h X).mpr hX)⟩

private theorem evalI_ctxEq {D : FSeq → Prop} {Ω Ω' : List Form} {C : Form}
    (h : Ω ≐ Ω') (he : EvalI D Ω C) : EvalI D Ω' C := by
  obtain ⟨St, Th, hm, h1, h2⟩ := he
  exact ⟨St, Th, hm, fun {x} hx => (h x).mp (h1 hx), fun {x} hx => h2 ((h x).mpr hx)⟩

/-! ## Size arithmetic -/

private theorem seqSize_cons {Ψ : List Form} {X C : Form} :
    seqSize (X :: Ψ) C = X.size + seqSize Ψ C := by
  show ((X :: Ψ).map Form.size).sum + C.size
      = X.size + (((Ψ.map Form.size).sum) + C.size)
  rw [List.map_cons, List.sum_cons, Nat.add_assoc]

private theorem seqSize_split {l r : List Form} {X C : Form} :
    seqSize (l ++ X :: r) C = seqSize (l ++ r) C + X.size := by
  show ((l ++ X :: r).map Form.size).sum + C.size
      = (((l ++ r).map Form.size).sum + C.size) + X.size
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons]
  omega

private theorem seqSize_goal {Ψ : List Form} {C C' : Form} (h : C'.size < C.size) :
    seqSize Ψ C' < seqSize Ψ C := Nat.add_lt_add_left h _

/-! ## The measure steps -/

private theorem wgKeep {G : Form} {r : Bool} {Ψ Ψ' : List Form} {C C' : Form}
    (hcl : ∀ X ∈ Ψ, Clo Ψ' X) (hs : seqSize Ψ' C' < seqSize Ψ C) :
    WgLt (wg G r Ψ' C') (wg G r Ψ C) := by
  have hmono : unclosed G Ψ' ≤ unclosed G Ψ :=
    unclosed_mono (fun _ hX => clo_trans hcl hX)
  rcases Nat.lt_or_ge (unclosed G Ψ') (unclosed G Ψ) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨Nat.le_antisymm hmono h, Or.inr ⟨rfl, hs⟩⟩

private theorem wgFocus {G : Form} {Ψ Ψ' : List Form} {C C' : Form}
    (hcl : ∀ X ∈ Ψ, Clo Ψ' X) :
    WgLt (wg G false Ψ' C') (wg G true Ψ C) := by
  have hmono : unclosed G Ψ' ≤ unclosed G Ψ :=
    unclosed_mono (fun _ hX => clo_trans hcl hX)
  rcases Nat.lt_or_ge (unclosed G Ψ') (unclosed G Ψ) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨Nat.le_antisymm hmono h, Or.inl Nat.zero_lt_one⟩

private theorem wgDrop {G : Form} {r r' : Bool} {Ψ Ψ' : List Form} {C C' : Form}
    (h : unclosed G Ψ' < unclosed G Ψ) : WgLt (wg G r' Ψ' C') (wg G r Ψ C) := Or.inl h

/-! ## The irregular atomic axiom of `FRJ`, as a database fact

If `Ω ⊆ Ĝ` and the prime goal `F` is not in `Ω`, then `Ax^I` derives
`∅ ; Ĝ∖{F} → F`, which covers `Ω`; by (DB2) the database has a
subsuming row.  This is why the irregular judgment needs no left rules:
a prime goal is either in `Ω` (`Ax`) or already refuted. -/

theorem evalI_axI {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {F : Form} (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hFp : F.isPrime = true) (hF : F ∈ sfR G) (hFn : F ∉ Ω) : EvalI D Ω F := by
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F)
      ⟨.axI F hFp hF (CtxEq.refl _)⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSt, hTh⟩ =>
      refine ⟨St', Th', hs'mem, fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil, ?_⟩
      intro x hx
      refine List.mem_append_right _ (hTh ?_)
      rcases List.mem_append.mp (hΩ x hx) with h | h
      · refine List.mem_append_left _ (List.mem_append_left _ (mem_rm.mpr ⟨?_, h⟩))
        intro he
        exact hFn (he ▸ hx)
      · exact List.mem_append_left _ (List.mem_append_right _ h)

/-! ## The specification of `BSearch` -/

/-- `SearchOk G D (reg, Ψ, C)`: the specification of `BSearch` at the
sequent `Ψ ⇒g C` (`reg = true`) or `Ψ →g C` (`reg = false`).  The first
two hypotheses are the well-formedness invariant (D7); the last is
(BSr1), and for the irregular clause the first is (BSr2). -/
def SearchOk (G : Form) (D : FSeq → Prop) : Bool × List Form × Form → Prop
  | (true, Ψ, C) =>
      (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G → ¬ EvalR D Ψ C → Nonempty (GbuR G Ψ C)
  | (false, Ω, C) =>
      (∀ X ∈ Ω, X ∈ gAt G ++ gImp G) → C ∈ sfR G → ¬ EvalI D Ω C → Nonempty (GbuI G Ω C)

/-- **Theorem 8** (source 4215), correctness of `BSearch`. -/
theorem search {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    (decI : ∀ Ω C, Decidable (EvalI D Ω C))
    (hcircL : ∀ X ∈ sfL G, X.isCirc = false)
    (hcircR : ∀ X ∈ sfR G, X.isCirc = false) :
    ∀ p : Bool × List Form × Form, SearchOk G D p := by
  have main : ∀ x : Nat × Nat × Nat, ∀ p : Bool × List Form × Form,
      wg G p.1 p.2.1 p.2.2 = x → SearchOk G D p := by
    intro x
    induction x using wgLt_wf.induction with
    | _ x ih =>
      rintro ⟨reg, Ψ, C⟩ hx
      have IH : ∀ q : Bool × List Form × Form,
          WgLt (wg G q.1 q.2.1 q.2.2) (wg G reg Ψ C) → SearchOk G D q :=
        fun q hq => ih _ (hx ▸ hq) q rfl
      cases reg
      · -- ==================== IRREGULAR: `Ψ →g C` ====================
        show (∀ X ∈ Ψ, X ∈ gAt G ++ gImp G) → C ∈ sfR G → ¬ EvalI D Ψ C →
          Nonempty (GbuI G Ψ C)
        intro hΩ hC hne
        have hΨL : ∀ X ∈ Ψ, X ∈ sfL G := by
          intro X hX
          rcases List.mem_append.mp (hΩ X hX) with h | h
          · exact (List.mem_filter.mp h).1
          · exact (List.mem_filter.mp h).1
        refine byDec (inferInstance : Decidable (C ∈ Ψ))
          (fun hax => ⟨.ax C (ctxEq_cons_self hax)⟩) (fun hax => ?_)
        cases C with
        | atom a => exact absurd (evalI_axI hsat hΩ rfl hC hax) hne
        | bot => exact absurd (evalI_axI hsat hΩ rfl hC hax) hne
        | circ Z =>
            -- ◯-SEAM 3: no focused `R◯` rule exists.
            exact Bool.noConfusion (hcircR _ hC)
        | and C₁ C₂ =>
            obtain ⟨h₁, h₂⟩ := sfR_and hC
            obtain ⟨d₁⟩ := IH (false, Ψ, C₁)
              (wgKeep (fun _ h => .base h) (seqSize_goal
                (show C₁.size < (Form.and C₁ C₂).size from
                  Nat.lt_succ_of_le (Nat.le_add_right _ _))))
              hΩ h₁ (fun h => hne (gbuInv7 hsat hC (Or.inl h)))
            obtain ⟨d₂⟩ := IH (false, Ψ, C₂)
              (wgKeep (fun _ h => .base h) (seqSize_goal
                (show C₂.size < (Form.and C₁ C₂).size from
                  Nat.lt_succ_of_le (Nat.le_add_left _ _))))
              hΩ h₂ (fun h => hne (gbuInv7 hsat hC (Or.inr h)))
            exact ⟨.randI d₁ d₂⟩
        | or C₁ C₂ =>
            obtain ⟨h₁, h₂⟩ := sfR_or hC
            refine byDec (decI Ψ C₁) (fun he₁ => ?_) (fun he₁ => ?_)
            · refine byDec (decI Ψ C₂) (fun he₂ => ?_) (fun he₂ => ?_)
              · exact absurd (gbuInv10 hsat hC he₁ he₂) hne
              · obtain ⟨d⟩ := IH (false, Ψ, C₂)
                  (wgKeep (fun _ h => .base h) (seqSize_goal
                    (show C₂.size < (Form.or C₁ C₂).size from
                      Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                  hΩ h₂ he₂
                exact ⟨.rorI2 d⟩
            · obtain ⟨d⟩ := IH (false, Ψ, C₁)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (show C₁.size < (Form.or C₁ C₂).size from
                    Nat.lt_succ_of_le (Nat.le_add_right _ _))))
                hΩ h₁ he₁
              exact ⟨.rorI1 d⟩
        | imp A B =>
            obtain ⟨hA, hB⟩ := sfR_imp hC
            refine byDec (decClo Ψ A) (fun hcl => ?_) (fun hcl => ?_)
            · obtain ⟨d⟩ := IH (false, Ψ, B)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (show B.size < (Form.imp A B).size from
                    Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                hΩ hB (fun h => hne (gbuInv8 hsat hC hcl h))
              exact ⟨.rimpII d hcl⟩
            · obtain ⟨d⟩ := IH (true, A :: Ψ, B) (wgDrop (unclosed_lt hA hcl))
                (by
                  intro Y hY
                  rcases List.mem_cons.mp hY with rfl | hY'
                  · exact hA
                  · exact hΨL Y hY')
                hB (fun h => hne (gbuInv9 hsat hC
                  (fun X hX => List.mem_append_left _ (hΩ X hX)) hcl h))
              exact ⟨.rimpNII d hcl⟩
      · -- ==================== REGULAR: `Ψ ⇒g C` ====================
        show (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G → ¬ EvalR D Ψ C →
          Nonempty (GbuR G Ψ C)
        intro hΨ hC hne
        refine byDec (inferInstance : Decidable (C ∈ Ψ))
          (fun hax => ⟨.ax C (ctxEq_cons_self hax)⟩) (fun hax => ?_)
        rcases splitCtx Ψ with hall | ⟨l, r, X, hsplit, hX⟩
        · -- (B4)/(B5): the context is critical
          have hΩ : ∀ Y ∈ Ψ, Y ∈ gAt G ++ gImp G := by
            intro Y hY
            rcases orTrue (hall Y hY) with hp | hi
            · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hΨ Y hY, hp⟩)
            · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hΨ Y hY, hi⟩)
          -- the shared `L⊃` step, given a failing antecedent
          have limpStep : ∀ A B : Form, Form.imp A B ∈ Ψ → ¬ EvalI D Ψ A →
              Nonempty (GbuR G Ψ C) := by
            intro A B hYΨ hnA
            obtain ⟨lY, rY, hYsplit⟩ := List.append_of_mem hYΨ
            obtain ⟨hAsf, hBsf⟩ := sfL_imp (hΨ _ hYΨ)
            have hΓ : Ψ ≐ .imp A B :: (lY ++ rY) := by
              rw [hYsplit]; exact ctxEq_split
            have hmemsub : ∀ W ∈ lY ++ rY, W ∈ Ψ :=
              fun W hW => (hΓ W).mpr (List.mem_cons_of_mem _ hW)
            obtain ⟨d₁⟩ := IH (false, .imp A B :: (lY ++ rY), A)
              (wgFocus (fun W hW => .base ((hΓ W).mp hW)))
              (fun W hW => hΩ W ((hΓ W).mpr hW)) hAsf
              (fun h => hnA (evalI_ctxEq (ctxEq_symm hΓ) h))
            obtain ⟨d₂⟩ := IH (true, B :: (lY ++ rY), C)
              (by
                refine wgKeep (fun W hW => ?_) ?_
                · rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                  · exact .imp (.base List.mem_cons_self)
                  · exact .base (List.mem_cons_of_mem _ hW')
                · show seqSize (B :: (lY ++ rY)) C < seqSize Ψ C
                  rw [hYsplit, seqSize_split, seqSize_cons]
                  have hb : B.size < (Form.imp A B).size :=
                    Nat.lt_succ_of_le (Nat.le_add_left _ _)
                  omega)
              (by
                intro W hW
                rcases List.mem_cons.mp hW with rfl | hW'
                · exact hBsf
                · exact hΨ W (hmemsub W hW'))
              hC (fun h => hne (evalR_ctxEq (ctxEq_symm hΓ) (gbuInv4 h)))
            exact ⟨.limpL d₁ d₂ hΓ⟩
          -- turn a failing member of `Υ` into the `L⊃` step
          have fromUps : ∀ Z : Form, Z ∈ (impPart Ψ).map ante → ¬ EvalI D Ψ Z →
              Nonempty (GbuR G Ψ C) := by
            intro Z hZ hnZ
            obtain ⟨Y, hYmem, hYante⟩ := List.mem_map.mp hZ
            obtain ⟨hYΨ, hYi⟩ := List.mem_filter.mp hYmem
            match Y, hYi, hYante, hYΨ with
            | .imp A B, _, hYante, hYΨ =>
                have hAZ : A = Z := hYante
                exact limpStep A B hYΨ (by rw [hAZ]; exact hnZ)
          have upsToImp : (∀ Z ∈ (impPart Ψ).map ante, EvalI D Ψ Z) →
              ∀ A B : Form, Form.imp A B ∈ Ψ → EvalI D Ψ A := by
            intro hallI A B hAB
            exact hallI A (List.mem_map.mpr ⟨.imp A B,
              List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩)
          cases C with
          | circ Z =>
              -- ◯-SEAM 2: no regular `R◯` rule exists.
              exact Bool.noConfusion (hcircR _ hC)
          | atom a =>
              rcases findNot (fun Z => decI Ψ Z) ((impPart Ψ).map ante) with
                hallI | ⟨Z, hZ, hnZ⟩
              · exact absurd (gbuSuccAt hsat hΩ rfl hC hax (upsToImp hallI)) hne
              · exact fromUps Z hZ hnZ
          | bot =>
              rcases findNot (fun Z => decI Ψ Z) ((impPart Ψ).map ante) with
                hallI | ⟨Z, hZ, hnZ⟩
              · exact absurd (gbuSuccAt hsat hΩ rfl hC hax (upsToImp hallI)) hne
              · exact fromUps Z hZ hnZ
          | and C₁ C₂ =>
              obtain ⟨h₁, h₂⟩ := sfR_and hC
              obtain ⟨d₁⟩ := IH (true, Ψ, C₁)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (show C₁.size < (Form.and C₁ C₂).size from
                    Nat.lt_succ_of_le (Nat.le_add_right _ _))))
                hΨ h₁ (fun h => hne (gbuInv2 hsat hC (Or.inl h)))
              obtain ⟨d₂⟩ := IH (true, Ψ, C₂)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (show C₂.size < (Form.and C₁ C₂).size from
                    Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                hΨ h₂ (fun h => hne (gbuInv2 hsat hC (Or.inr h)))
              exact ⟨.randR d₁ d₂⟩
          | imp A B =>
              obtain ⟨hA, hB⟩ := sfR_imp hC
              refine byDec (decClo Ψ A) (fun hcl => ?_) (fun hcl => ?_)
              · obtain ⟨d⟩ := IH (true, Ψ, B)
                  (wgKeep (fun _ h => .base h) (seqSize_goal
                    (show B.size < (Form.imp A B).size from
                      Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                  hΨ hB (fun h => hne (gbuInv5 hsat hC hcl h))
                exact ⟨.rimpI d hcl⟩
              · obtain ⟨d⟩ := IH (true, A :: Ψ, B) (wgDrop (unclosed_lt hA hcl))
                  (by
                    intro Y hY
                    rcases List.mem_cons.mp hY with rfl | hY'
                    · exact hA
                    · exact hΨ Y hY')
                  hB (fun h => hne (gbuInv6 hsat hC h))
                exact ⟨.rimpNI d hcl⟩
          | or C₁ C₂ =>
              obtain ⟨h₁, h₂⟩ := sfR_or hC
              refine byDec (decI Ψ C₁) (fun he₁ => ?_) (fun he₁ => ?_)
              · refine byDec (decI Ψ C₂) (fun he₂ => ?_) (fun he₂ => ?_)
                · rcases findNot (fun Z => decI Ψ Z) ((impPart Ψ).map ante) with
                    hallI | ⟨Z, hZ, hnZ⟩
                  · exact absurd (gbuSuccOr hsat hΩ hC (upsToImp hallI) he₁ he₂) hne
                  · exact fromUps Z hZ hnZ
                · obtain ⟨d⟩ := IH (false, Ψ, C₂)
                    (wgFocus (fun _ h => .base h)) hΩ h₂ he₂
                  exact ⟨.rorR2 d⟩
              · obtain ⟨d⟩ := IH (false, Ψ, C₁)
                  (wgFocus (fun _ h => .base h)) hΩ h₁ he₁
                exact ⟨.rorR1 d⟩
        · -- (B2): the context is non-critical; apply an invertible left rule
          subst hsplit
          have hXmem : X ∈ l ++ X :: r := List.mem_append_right _ List.mem_cons_self
          have hΓ : (l ++ X :: r) ≐ X :: (l ++ r) := ctxEq_split
          have hmemsub : ∀ W ∈ l ++ r, W ∈ l ++ X :: r :=
            fun W hW => (hΓ W).mpr (List.mem_cons_of_mem _ hW)
          cases X with
          | atom a => exact Bool.noConfusion hX
          | imp A B => exact Bool.noConfusion hX
          | circ Z =>
              -- ◯-SEAM 1: no `L◯` rule exists.
              exact Bool.noConfusion (hcircL _ (hΨ _ hXmem))
          | bot => exact ⟨.lbot C (ctxEq_cons_self hXmem)⟩
          | and A B =>
              obtain ⟨hA, hB⟩ := sfL_and (hΨ _ hXmem)
              obtain ⟨d⟩ := IH (true, A :: B :: (l ++ r), C)
                (by
                  refine wgKeep (fun W hW => ?_) ?_
                  · rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                    · exact .and (.base List.mem_cons_self)
                        (.base (List.mem_cons_of_mem _ List.mem_cons_self))
                    · exact .base (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hW'))
                  · rw [seqSize_split, seqSize_cons, seqSize_cons]
                    show A.size + (B.size + seqSize (l ++ r) C)
                      < seqSize (l ++ r) C + (A.size + B.size + 1)
                    omega)
                (by
                  intro W hW
                  rcases List.mem_cons.mp hW with rfl | hW'
                  · exact hA
                  · rcases List.mem_cons.mp hW' with rfl | hW''
                    · exact hB
                    · exact hΨ W (hmemsub W hW''))
                hC (fun h => hne (evalR_ctxEq (ctxEq_symm hΓ) (gbuInv1 h)))
              exact ⟨.landL d hΓ⟩
          | or A B =>
              obtain ⟨hA, hB⟩ := sfL_or (hΨ _ hXmem)
              have hsz : ∀ Y : Form, Y.size < (Form.or A B).size →
                  seqSize (Y :: (l ++ r)) C < seqSize (l ++ Form.or A B :: r) C := by
                intro Y hY
                rw [seqSize_split, seqSize_cons]
                omega
              obtain ⟨d₁⟩ := IH (true, A :: (l ++ r), C)
                (by
                  refine wgKeep (fun W hW => ?_)
                    (hsz A (Nat.lt_succ_of_le (Nat.le_add_right _ _)))
                  rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                  · exact .orL (.base List.mem_cons_self)
                  · exact .base (List.mem_cons_of_mem _ hW'))
                (by
                  intro W hW
                  rcases List.mem_cons.mp hW with rfl | hW'
                  · exact hA
                  · exact hΨ W (hmemsub W hW'))
                hC (fun h => hne (evalR_ctxEq (ctxEq_symm hΓ) (gbuInv3L h)))
              obtain ⟨d₂⟩ := IH (true, B :: (l ++ r), C)
                (by
                  refine wgKeep (fun W hW => ?_)
                    (hsz B (Nat.lt_succ_of_le (Nat.le_add_left _ _)))
                  rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                  · exact .orR (.base List.mem_cons_self)
                  · exact .base (List.mem_cons_of_mem _ hW'))
                (by
                  intro W hW
                  rcases List.mem_cons.mp hW with rfl | hW'
                  · exact hB
                  · exact hΨ W (hmemsub W hW'))
                hC (fun h => hne (evalR_ctxEq (ctxEq_symm hΓ) (gbuInv3R h)))
              exact ⟨.lorL d₁ d₂ hΓ⟩
  exact fun p => main _ p rfl

/-! ## The maximal database

`Subsumes` is reflexive, so the set of ALL `FRJV(G)`-derivable sequents
is a saturated database.  It is not the database `BSearch` runs on — for
that one needs the FINITE forward closure of §4, together with a
decision procedure for `▷`, which is the remaining engineering of stage
4 — but it shows that saturation itself is not the obstruction. -/

theorem saturated_fderivable (G : Form) : Saturated G (FDerivable G) := by
  refine ⟨fun _ h => h, fun s h => ⟨s, h, ?_⟩⟩
  cases s with
  | reg Γ C => exact ⟨rfl, fun {_} h => h⟩
  | regC Γ C => exact ⟨rfl, fun {_} h => h⟩
  | irr St Th C => exact ⟨rfl, fun _ => Iff.rfl, fun {_} h => h⟩

/-! ## Theorem 9 (`theo:GBU-FRJ`, source 4320) — the duality

    ⊢_Gbu(G) G   iff   ⊬_FRJ(G) G

One direction is the two soundness theorems; the other is `BSearch`
started at `⇒g G`, which is legitimate precisely because a database row
`Γ ⇒ G` would BE an `FRJ(G)`-proof of `G`. -/

/-- **Theorem 9**, forward: soundness on both sides. -/
theorem not_provableV_of_provableGbu {G : Form} (h : ProvableGbu G) :
    ¬ ProvableV G := fun hv => soundnessV hv (pll_of_provableGbu h)

/-- **Theorem 9**, backward: `BSearch` at the root sequent. -/
theorem provableGbu_of_not_provableV {G : Form} {D : FSeq → Prop}
    (hsat : Saturated G D) (decI : ∀ Ω C, Decidable (EvalI D Ω C))
    (hcircL : ∀ X ∈ sfL G, X.isCirc = false)
    (hcircR : ∀ X ∈ sfR G, X.isCirc = false)
    (h : ¬ ProvableV G) : ProvableGbu G := by
  refine search hsat decI hcircL hcircR (true, [], G)
    (fun _ hX => absurd hX List.not_mem_nil) (sfR_self G) ?_
  rintro ⟨Γ, hmem, -⟩
  obtain ⟨t, hd⟩ := hsat.1 _ hmem
  exact h ⟨t, Γ, hd⟩

/-- **Theorem 9** (source 4320). -/
theorem gbu_frj_duality {G : Form} {D : FSeq → Prop}
    (hsat : Saturated G D) (decI : ∀ Ω C, Decidable (EvalI D Ω C))
    (hcircL : ∀ X ∈ sfL G, X.isCirc = false)
    (hcircR : ∀ X ∈ sfR G, X.isCirc = false) :
    ProvableGbu G ↔ ¬ ProvableV G :=
  ⟨not_provableV_of_provableGbu,
   provableGbu_of_not_provableV hsat decI hcircL hcircR⟩

/-! ## Theorem 10 (source 4353) — completeness of both calculi

Corollaries of Theorem 9 and the two soundness theorems. -/

/-- **Theorem 10(i)**: `G ∉ IPL` implies `⊢_FRJV(G) G` — the completeness
of the REPAIRED refutation calculus, on the `◯`-free fragment. -/
theorem provableV_of_not_pll {G : Form} {D : FSeq → Prop}
    (hsat : Saturated G D) (decRoot : Decidable (EvalR D [] G))
    (decI : ∀ Ω C, Decidable (EvalI D Ω C))
    (hcircL : ∀ X ∈ sfL G, X.isCirc = false)
    (hcircR : ∀ X ∈ sfR G, X.isCirc = false)
    (h : ¬ PLL G) : ProvableV G := by
  refine byDec decRoot (fun he => ?_) (fun hne => ?_)
  · obtain ⟨Γ, hmem, -⟩ := he
    obtain ⟨t, hd⟩ := hsat.1 _ hmem
    exact ⟨t, Γ, hd⟩
  · exact absurd (pll_of_provableGbu (search hsat decI hcircL hcircR (true, [], G)
      (fun _ hX => absurd hX List.not_mem_nil) (sfR_self G) hne)) h

/-- **Theorem 10(ii)**: `G ∈ IPL` implies `⊢_Gbu(G) G`. -/
theorem provableGbu_of_pll {G : Form} {D : FSeq → Prop}
    (hsat : Saturated G D) (decI : ∀ Ω C, Decidable (EvalI D Ω C))
    (hcircL : ∀ X ∈ sfL G, X.isCirc = false)
    (hcircR : ∀ X ∈ sfR G, X.isCirc = false)
    (h : PLL G) : ProvableGbu G :=
  provableGbu_of_not_provableV hsat decI hcircL hcircR (fun hv => soundnessV hv h)

/-! ## Axiom pins -/

/-- info: 'FRJ.Gbu.evalI_axI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evalI_axI

/-- info: 'FRJ.Gbu.search' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms search

/-- info: 'FRJ.Gbu.saturated_fderivable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms saturated_fderivable

/-- info: 'FRJ.Gbu.gbu_frj_duality' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbu_frj_duality

/-- info: 'FRJ.Gbu.provableV_of_not_pll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_of_not_pll

/-- info: 'FRJ.Gbu.provableGbu_of_pll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableGbu_of_pll

end FRJ.Gbu
