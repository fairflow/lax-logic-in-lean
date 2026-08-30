/-
# `Gbu◯(G)`: Theorem 8◯, the correctness of `BSearch` in the modal calculus

Stage 3 of the adoption, modal layer.  The IPC original is
`wip/gbu_search.lean`; this file follows it clause by clause, adding the
`◯` cases and nothing else, per the extension discipline.

## Modes

`Gbu(G)` has two judgments; the search over `Gbu◯(G)` needs THREE
specifications, because the modal rules query the database differently:

| mode | sequent | (BSr1) query | why |
|---|---|---|---|
| `reg` | `Ψ ⇒g C` | `¬ D ▷ (Ψ ⇒g C)` | as in the paper |
| `irr` | `Ω →g C` | `UnrefutedBelow` | the paper's, plus a `Ĝ` ancestor |
| `cirr` | `Ω →g C` | `¬ D ▷ᶜ (Ω ⇒g C)` | `◯∉` reads the CLEAN stratum |

The third is forced: `R◯ᵢ`'s licence is `gbuSuccCircI`, whose hypothesis
is `RefutedCleanly G Ω Z` — the clean lookup — not `D ▷ (Ω →g Z)`.  So
the premise of `R◯ᵢ` is searched under the clean query, and the two
irregular modes are incomparable (`EvalI` and `EvalRC` neither implies
the other).  `cirr` also carries the `Υ` queries, which the clean
success lemmas need and `EvalI`'s do not.

The `irr` query is `UnrefutedBelow`, not the bare `D ⋫ (Ω →g C)`: on a
`Ĝ` context the two coincide, but `L⊃ᵢ`'s second premise puts an
arbitrary `B ∈ Sf^L(G)` into the context, where the bare query is
satisfied vacuously (no `FRJVi` zone reaches outside `Ĝ`) and licenses
nothing.  Carrying the last `Ĝ` ancestor — unrefuted, and `Clo`-below
the current context — restores the licence at every left rule.
-/
import wip.gbu_circ
import wip.gbu_weakening

namespace FRJ.Gbu

open FRJ Form

/-! ## The three modes -/

inductive Mode where
  | reg
  | irr
  /-- irregular, under the CLEAN query -/
  | cirr
  deriving DecidableEq, Repr

def Mode.isReg : Mode → Bool
  | .reg => true
  | _ => false

/-! ## Context bookkeeping, `Ĝ`-flavoured

The IPC search splits a regular context into "all atoms-and-implications"
(critical) or "contains a `⊥`/`∧`/`∨`".  With `◯` the critical zone is
`Ĝ` — atoms, implications AND modal formulas — which is exactly
`sfL_dec`. -/

private theorem byDec {p : Prop} (d : Decidable p) {q : Prop}
    (h1 : p → q) (h2 : ¬ p → q) : q := by
  cases d with
  | isTrue h => exact h1 h
  | isFalse h => exact h2 h

private def decClo (Ψ : List Form) (A : Form) : Decidable (Clo Ψ A) :=
  match h : cloB Ψ A with
  | true => isTrue (cloB_iff.mp h)
  | false => isFalse (by intro hc; rw [cloB_iff.mpr hc] at h; exact Bool.noConfusion h)

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

private theorem ctxEq_cons_self {Γ : List Form} {A : Form} (h : A ∈ Γ) :
    Γ ≐ A :: Γ := by
  intro x
  refine ⟨fun hx => List.mem_cons_of_mem _ hx, fun hx => ?_⟩
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

private theorem orTrue {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

/-- Membership of the critical zone `Ĝ`, as a Boolean on the shape. -/
private def isHat (X : Form) : Bool := X.isPV || X.isImp || X.isCirc

/-- `Ψ` is all-`Ĝ`-shaped, or it splits around a `⊥`/`∧`/`∨`. -/
private theorem splitHat : ∀ Ψ : List Form,
    (∀ X ∈ Ψ, isHat X = true) ∨
    (∃ l r X, Ψ = l ++ X :: r ∧ isHat X = false)
  | [] => Or.inl (fun _ hX => absurd hX List.not_mem_nil)
  | X :: t =>
      match h : isHat X with
      | true =>
          match splitHat t with
          | Or.inl hall => Or.inl (by
              intro Y hY
              rcases List.mem_cons.mp hY with rfl | hY'
              · exact h
              · exact hall Y hY')
          | Or.inr ⟨l, r, Y, hY, hY'⟩ =>
              Or.inr ⟨X :: l, r, Y, by rw [hY]; rfl, hY'⟩
      | false => Or.inr ⟨[], t, X, rfl, h⟩

/-- A `Ĝ`-shaped left subformula is in `Ĝ`. -/
private theorem mem_gHat_of_isHat {G X : Form} (hsf : X ∈ sfL G)
    (h : isHat X = true) : X ∈ gHat G := by
  rcases orTrue h with h' | hc
  · rcases orTrue h' with hp | hi
    · exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_filter.mpr ⟨hsf, hp⟩))
    · exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_filter.mpr ⟨hsf, hi⟩))
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hsf, hc⟩)

/-! ## Transport and size arithmetic (verbatim from the IPC search) -/

private theorem evalR_ctxEq {D : FSeq → Prop} {Ψ Ψ' : List Form} {C : Form}
    (h : Ψ ≐ Ψ') (he : EvalR D Ψ C) : EvalR D Ψ' C := by
  obtain ⟨Γ, hm, hcl⟩ := he
  exact ⟨Γ, hm, fun X hX => hcl X ((h X).mpr hX)⟩

private theorem evalRC_ctxEq {D : FSeq → Prop} {Ψ Ψ' : List Form} {C : Form}
    (h : Ψ ≐ Ψ') (he : EvalRC D Ψ C) : EvalRC D Ψ' C := by
  obtain ⟨Γ, hm, hcl⟩ := he
  exact ⟨Γ, hm, fun X hX => hcl X ((h X).mpr hX)⟩

private theorem evalI_ctxEq {D : FSeq → Prop} {Ω Ω' : List Form} {C : Form}
    (h : Ω ≐ Ω') (he : EvalI D Ω C) : EvalI D Ω' C := by
  obtain ⟨St, Th, hm, h1, h2⟩ := he
  exact ⟨St, Th, hm, fun {x} hx => (h x).mp (h1 hx), fun {x} hx => h2 ((h x).mpr hx)⟩

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

/-- The `tp` obligation is discharged by an auto-param: `Nat.le_refl` for
a regular step or a context rule, `hasCirc`-monotonicity for a goal
decomposition, and `tpC_le_circ` where the conclusion's goal is modal. -/
private theorem wgKeep {G : Form} {r : Bool} {Ψ Ψ' : List Form} {C C' : Form}
    (hcl : ∀ X ∈ Ψ, Clo Ψ' X) (hs : seqSize Ψ' C' < seqSize Ψ C)
    (htp : tpC r C' ≤ tpC r C := by
      first
        | exact Nat.le_refl _
        | exact tpC_false_mono orL'
        | exact tpC_false_mono orR'
        | exact tpC_le_circ _ _) :
    WgLt (wgC G r Ψ' C') (wgC G r Ψ C) :=
  wgCCtx (fun _ hX => clo_trans hcl hX) htp hs

private theorem wgFocus {G : Form} {Ψ Ψ' : List Form} {C C' : Form}
    (hcl : ∀ X ∈ Ψ, Clo Ψ' X) :
    WgLt (wgC G false Ψ' C') (wgC G true Ψ C) :=
  wgCFocus (fun _ hX => clo_trans hcl hX) (tpC_false_lt_true C C')

private theorem wgTpLt {G : Form} {r : Bool} {Ψ Ψ' : List Form} {C C' : Form}
    (hcl : ∀ X ∈ Ψ, Clo Ψ' X) (htp : tpC r C' < tpC r C) :
    WgLt (wgC G r Ψ' C') (wgC G r Ψ C) :=
  wgCFocus (fun _ hX => clo_trans hcl hX) htp

private theorem tpC_free_lt_circ {A Z : Form} (h : A.hasCirc = false) :
    tpC false A < tpC false (Form.circ Z) := by
  show (if A.hasCirc = true then 1 else 0) < 1
  rw [h]
  exact Nat.zero_lt_one

private theorem wgDrop {G : Form} {r r' : Bool} {Ψ Ψ' : List Form} {C C' : Form}
    (h : unclosed G Ψ' < unclosed G Ψ) : WgLt (wgC G r' Ψ' C') (wgC G r Ψ C) :=
  Or.inl h

/-! ## The weight

Both irregular modes sit at the paper's `tp = 0`: a goal decomposition
can turn a non-modal goal into a modal one (`R∧ᵢ` at `C₁ ∧ ◯C₂`), so the
mode cannot be graded by the goal's shape, and `Wg` is unchanged.  What
pays for `L⊃ᵢ`, whose premises are both irregular, is the rule's own
`hsz` field. -/

/-! ## The specification -/

/-- `SearchOkO G D (m, Ψ, C)`.  The `reg` and `irr` clauses are the
paper's, with the `Ĝ` invariant relaxed at a `◯` goal (where the
irregular judgment has the regular left rules).  The `cirr` clause is
the modal addition: its query is the CLEAN lookup, and it carries the
`Υ` queries that the clean success lemmas consume. -/
def SearchOkO (G : Form) (D : FSeq → Prop) : Mode × List Form × Form → Prop
  | (.reg, Ψ, C) =>
      (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G → ¬ EvalR D Ψ C → Nonempty (GbuRC G Ψ C)
  | (.irr, Ω, C) =>
      (∀ X ∈ Ω, X ∈ sfL G) → (C.isCirc = false → ∀ X ∈ Ω, X ∈ gHat G) →
        C ∈ sfR G → UnrefutedBelow G D Ω C → Nonempty (GbuIC G Ω C)
      -- `UnrefutedBelow` is (BSr1) plus the `Ĝ` ancestor; on a `Ĝ`
      -- context (`unrefutedBelow_of_gHat`) the two are the same thing.
  | (.cirr, Ω, C) =>
      (∀ X ∈ Ω, X ∈ gAt G ++ gImp G) → C ∈ sfR G →
        (∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A) →
        ¬ EvalRC D Ω C → Nonempty (GbuIC G Ω C)

/-! ## The two residues, named

Everything the modal search cannot close from `Gbu◯(G)`'s current rule
set is isolated here as an explicit hypothesis, with its displayed
statement.  Neither is a `sorry`: each is a `Prop` consumed at exactly
one branch, so the theorem below states precisely what it does and does
not establish.  (S3) is now known to be FALSE — see `not_cleanReg`.

(S2), the unlicensed `L⊥ᵢ`/`L∧ᵢ`/`L∨ᵢ`, is CLEARED — see
`UnrefutedBelow` in `wip/gbu_circ.lean`.  The numbering is kept.) -/

/-- **(S1)** `L⊃ᵢ` admits any `◯`-FREE antecedent, and otherwise needs
`|A| < |◯C|`.  What is left out is modus ponens on an implication whose
antecedent BOTH carries a `◯` and is too large — and the `Υ` query that
the clean mode needs cannot then be discharged.

    Ω ⊆ Ĝ_at ∪ Ĝ_imp,  A ⊃ B ∈ Ω,  ◯Z ∈ Sf^R(G),
    D ⋫ (Ω →g A),  |A| ≥ |◯Z|
    ⟹  Ω →g ◯Z -/
def BigAnte (G : Form) (D : FSeq → Prop) : Prop :=
  ∀ (Ω : List Form) (A B Z : Form),
    (∀ X ∈ Ω, X ∈ gAt G ++ gImp G) → Form.imp A B ∈ Ω →
    Form.circ Z ∈ sfR G → ¬ EvalI D Ω A →
    ¬ (A.hasCirc = false ∨ A.size < (Form.circ Z).size) →
    Nonempty (GbuIC G Ω (.circ Z))

/-- **(S3)** the CLEAN-regular search, which `R⊃ₙᵢ` in the clean
irregular mode releases into.  **REFUTED** — see `not_cleanReg` at the
end of this file.  It is kept as a hypothesis so that the shape of the
obligation stays on the record, but it is FALSE for any `G` with a modal
subformula, and `searchO` is therefore vacuous there.

    Ψ ⊆ Sf^L(G),  C ∈ Sf^R(G),  D ⋫ᶜ (Ψ ⇒g C)  ⟹  Ψ ⇒g C -/
def CleanReg (G : Form) (D : FSeq → Prop) : Prop :=
  ∀ (Ψ : List Form) (C : Form), (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G →
    ¬ EvalRC D Ψ C → Nonempty (GbuRC G Ψ C)

/-! ## Theorem 8◯ -/

theorem searchO {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    (decI : ∀ Ω C, Decidable (EvalI D Ω C))
    (decRC : ∀ Ψ C, Decidable (EvalRC D Ψ C))
    (bigAnte : BigAnte G D) (cleanReg : CleanReg G D) :
    ∀ p : Mode × List Form × Form, SearchOkO G D p := by
  have main : ∀ x : Nat × Nat × Nat, ∀ p : Mode × List Form × Form,
      wgC G p.1.isReg p.2.1 p.2.2 = x → SearchOkO G D p := by
    intro x
    induction x using wgLt_wf.induction with
    | _ x ih =>
      rintro ⟨mode, Ψ, C⟩ hx
      have IH : ∀ q : Mode × List Form × Form,
          WgLt (wgC G q.1.isReg q.2.1 q.2.2) (wgC G mode.isReg Ψ C) → SearchOkO G D q :=
        fun q hq => ih _ (hx ▸ hq) q rfl
      cases mode with
      | reg =>
          -- ==================== REGULAR: `Ψ ⇒g C` ====================
          show (∀ X ∈ Ψ, X ∈ sfL G) → C ∈ sfR G → ¬ EvalR D Ψ C →
            Nonempty (GbuRC G Ψ C)
          intro hΨ hC hne
          refine byDec (inferInstance : Decidable (C ∈ Ψ))
            (fun hax => ⟨.ax C (ctxEq_cons_self hax)⟩) (fun hax => ?_)
          rcases splitHat Ψ with hall | ⟨l, r, X, hsplit, hX⟩
          · -- critical: `Ψ ⊆ Ĝ`
            have hΩ : ∀ Y ∈ Ψ, Y ∈ gHat G :=
              fun Y hY => mem_gHat_of_isHat (hΨ Y hY) (hall Y hY)
            have limpStep : ∀ A B : Form, Form.imp A B ∈ Ψ → ¬ EvalI D Ψ A →
                Nonempty (GbuRC G Ψ C) := by
              intro A B hYΨ hnA
              obtain ⟨lY, rY, hYsplit⟩ := List.append_of_mem hYΨ
              obtain ⟨hAsf, hBsf⟩ := sfL_imp (hΨ _ hYΨ)
              have hΓ : Ψ ≐ .imp A B :: (lY ++ rY) := by
                rw [hYsplit]; exact ctxEq_split
              have hmemsub : ∀ W ∈ lY ++ rY, W ∈ Ψ :=
                fun W hW => (hΓ W).mpr (List.mem_cons_of_mem _ hW)
              obtain ⟨d₁⟩ := IH (.irr, .imp A B :: (lY ++ rY), A)
                (wgFocus (fun W hW => .base ((hΓ W).mp hW)))
                (by
                  intro W hW
                  rcases List.mem_cons.mp hW with rfl | hW'
                  · exact hΨ _ hYΨ
                  · exact hΨ W (hmemsub W hW'))
                (by
                  intro _ W hW
                  rcases List.mem_cons.mp hW with rfl | hW'
                  · exact hΩ _ hYΨ
                  · exact hΩ W (hmemsub W hW'))
                hAsf (unrefutedBelow_of_gHat
                  (by
                    intro W hW
                    rcases List.mem_cons.mp hW with rfl | hW'
                    · exact hΩ _ hYΨ
                    · exact hΩ W (hmemsub W hW'))
                  (fun h => hnA (evalI_ctxEq (ctxEq_symm hΓ) h)))
              obtain ⟨d₂⟩ := IH (.reg, B :: (lY ++ rY), C)
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
            have fromUps : ∀ Z : Form, Z ∈ (impPart Ψ).map ante → ¬ EvalI D Ψ Z →
                Nonempty (GbuRC G Ψ C) := by
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
            | atom a =>
                rcases findNot (fun Z => decI Ψ Z) ((impPart Ψ).map ante) with
                  hallI | ⟨Z, hZ, hnZ⟩
                · exact absurd (gbuSuccAtF hsat hΩ rfl hC hax (upsToImp hallI)) hne
                · exact fromUps Z hZ hnZ
            | bot =>
                rcases findNot (fun Z => decI Ψ Z) ((impPart Ψ).map ante) with
                  hallI | ⟨Z, hZ, hnZ⟩
                · exact absurd (gbuSuccAtF hsat hΩ rfl hC hax (upsToImp hallI)) hne
                · exact fromUps Z hZ hnZ
            | and C₁ C₂ =>
                obtain ⟨h₁, h₂⟩ := sfR_and hC
                obtain ⟨d₁⟩ := IH (.reg, Ψ, C₁)
                  (wgKeep (fun _ h => .base h) (seqSize_goal
                    (show C₁.size < (Form.and C₁ C₂).size from
                      Nat.lt_succ_of_le (Nat.le_add_right _ _))))
                  hΨ h₁ (fun h => hne (gbuInv2 hsat hC (Or.inl h)))
                obtain ⟨d₂⟩ := IH (.reg, Ψ, C₂)
                  (wgKeep (fun _ h => .base h) (seqSize_goal
                    (show C₂.size < (Form.and C₁ C₂).size from
                      Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                  hΨ h₂ (fun h => hne (gbuInv2 hsat hC (Or.inr h)))
                exact ⟨.randR d₁ d₂⟩
            | imp A B =>
                obtain ⟨hA, hB⟩ := sfR_imp hC
                refine byDec (decClo Ψ A) (fun hcl => ?_) (fun hcl => ?_)
                · obtain ⟨d⟩ := IH (.reg, Ψ, B)
                    (wgKeep (fun _ h => .base h) (seqSize_goal
                      (show B.size < (Form.imp A B).size from
                        Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                    hΨ hB (fun h => hne (gbuInv5 hsat hC hcl h))
                  exact ⟨.rimpI d hcl⟩
                · obtain ⟨d⟩ := IH (.reg, A :: Ψ, B) (wgDrop (unclosed_lt hA hcl))
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
                    · exact absurd (gbuSuccOrF hsat hΩ hC (upsToImp hallI) he₁ he₂) hne
                    · exact fromUps Z hZ hnZ
                  · obtain ⟨d⟩ := IH (.irr, Ψ, C₂)
                      (wgFocus (fun _ h => .base h))
                      hΨ (fun _ => hΩ) h₂ (unrefutedBelow_of_gHat hΩ he₂)
                    exact ⟨.rorR2 d⟩
                · obtain ⟨d⟩ := IH (.irr, Ψ, C₁)
                    (wgFocus (fun _ h => .base h))
                    hΨ (fun _ => hΩ) h₁ (unrefutedBelow_of_gHat hΩ he₁)
                  exact ⟨.rorR1 d⟩
            | circ Z =>
                -- `L◯` is invertible (`gbuInv11`), so exhaust it first.
                rcases findNot (fun X => (inferInstance : Decidable (X.isCirc = false))) Ψ with
                  hnoc | ⟨Y, hYΨ, hYc⟩
                · -- no modal formula left: `Ψ ⊆ Ĝ_at ∪ Ĝ_imp`, so `⋈^◯` applies
                  have hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G := by
                    intro W hW
                    rcases gHat_cases (hΩ W hW) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hc⟩
                    · exact List.mem_append_left _ h
                    · exact List.mem_append_right _ h
                    · exact absurd hc (by simpa using hnoc W hW)
                  refine byDec (decI Ψ Z) (fun heZ => ?_) (fun heZ => ?_)
                  · rcases findNot (fun W => decI Ψ W) ((impPart Ψ).map ante) with
                      hallI | ⟨W, hW, hnW⟩
                    · exact absurd (gbuSuccCirc hsat hΩai hC (upsToImp hallI) heZ) hne
                    · exact fromUps W hW hnW
                  · obtain ⟨d⟩ := IH (.irr, Ψ, Z)
                      (wgFocus (fun _ h => .base h))
                      hΨ (fun _ => hΩ) (sfR_circ hC)
                      (unrefutedBelow_of_gHat hΩ heZ)
                    exact ⟨.rcirc d hC⟩
                · -- a `◯Y'` in the context: apply `L◯`
                  have hYc' : Y.isCirc = true := by
                    cases hb : Y.isCirc with
                    | true => rfl
                    | false => exact absurd hb hYc
                  match Y, hYc' with
                  | .circ Y', _ =>
                      obtain ⟨lY, rY, hYsplit⟩ := List.append_of_mem hYΨ
                      have hΓ : Ψ ≐ .circ Y' :: (lY ++ rY) := by
                        rw [hYsplit]; exact ctxEq_split
                      have hmemsub : ∀ W ∈ lY ++ rY, W ∈ Ψ :=
                        fun W hW => (hΓ W).mpr (List.mem_cons_of_mem _ hW)
                      have hY'sf : Y' ∈ sfL G := sfL_circ (hΨ _ hYΨ)
                      obtain ⟨d⟩ := IH (.reg, Y' :: (lY ++ rY), Form.circ Z)
                        (by
                          refine wgKeep (fun W hW => ?_) ?_
                          · rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                            · exact .circ (.base List.mem_cons_self)
                            · exact .base (List.mem_cons_of_mem _ hW')
                          · show seqSize (Y' :: (lY ++ rY)) (Form.circ Z) < seqSize Ψ _
                            rw [hYsplit, seqSize_split, seqSize_cons]
                            have : Y'.size < (Form.circ Y').size := Nat.lt_succ_self _
                            omega)
                        (by
                          intro W hW
                          rcases List.mem_cons.mp hW with rfl | hW'
                          · exact hY'sf
                          · exact hΨ W (hmemsub W hW'))
                        hC (fun h => hne (evalR_ctxEq (ctxEq_symm hΓ) (gbuInv11 h)))
                      exact ⟨.lcirc d (hΨ _ hYΨ) hΓ⟩
          · -- non-critical: an invertible LEFT rule
            subst hsplit
            have hXmem : X ∈ l ++ X :: r := List.mem_append_right _ List.mem_cons_self
            have hΓ : (l ++ X :: r) ≐ X :: (l ++ r) := ctxEq_split
            have hmemsub : ∀ W ∈ l ++ r, W ∈ l ++ X :: r :=
              fun W hW => (hΓ W).mpr (List.mem_cons_of_mem _ hW)
            cases X with
            | atom a => exact Bool.noConfusion hX
            | imp A B => exact Bool.noConfusion hX
            | circ Z => exact Bool.noConfusion hX
            | bot => exact ⟨.lbot C (ctxEq_cons_self hXmem)⟩
            | and A B =>
                obtain ⟨hA, hB⟩ := sfL_and (hΨ _ hXmem)
                obtain ⟨d⟩ := IH (.reg, A :: B :: (l ++ r), C)
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
                obtain ⟨d₁⟩ := IH (.reg, A :: (l ++ r), C)
                  (wgKeep (fun W hW => by
                      rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                      · exact .orL (.base List.mem_cons_self)
                      · exact .base (List.mem_cons_of_mem _ hW'))
                    (hsz A (Nat.lt_succ_of_le (Nat.le_add_right _ _))))
                  (by
                    intro W hW
                    rcases List.mem_cons.mp hW with rfl | hW'
                    · exact hA
                    · exact hΨ W (hmemsub W hW'))
                  hC (fun h => hne (evalR_ctxEq (ctxEq_symm hΓ) (gbuInv3L h)))
                obtain ⟨d₂⟩ := IH (.reg, B :: (l ++ r), C)
                  (wgKeep (fun W hW => by
                      rcases List.mem_cons.mp ((hΓ W).mp hW) with rfl | hW'
                      · exact .orR (.base List.mem_cons_self)
                      · exact .base (List.mem_cons_of_mem _ hW'))
                    (hsz B (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                  (by
                    intro W hW
                    rcases List.mem_cons.mp hW with rfl | hW'
                    · exact hB
                    · exact hΨ W (hmemsub W hW'))
                  hC (fun h => hne (evalR_ctxEq (ctxEq_symm hΓ) (gbuInv3R h)))
                exact ⟨.lorL d₁ d₂ hΓ⟩
      | irr =>
          -- ==================== IRREGULAR: `Ψ →g C` ====================
          show (∀ X ∈ Ψ, X ∈ sfL G) → (C.isCirc = false → ∀ X ∈ Ψ, X ∈ gHat G) →
            C ∈ sfR G → UnrefutedBelow G D Ψ C → Nonempty (GbuIC G Ψ C)
          intro hΨ hΩc hC hnb
          have hne : ¬ EvalI D Ψ C := hnb.1
          refine byDec (inferInstance : Decidable (C ∈ Ψ))
            (fun hax => ⟨.ax C (ctxEq_cons_self hax)⟩) (fun hax => ?_)
          cases C with
          | atom a => exact absurd (evalI_axI_gHat hsat (hΩc rfl) rfl hC hax) hne
          | bot => exact absurd (evalI_axI_gHat hsat (hΩc rfl) rfl hC hax) hne
          | and C₁ C₂ =>
              obtain ⟨h₁, h₂⟩ := sfR_and hC
              have hg := hΩc rfl
              obtain ⟨d₁⟩ := IH (.irr, Ψ, C₁)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (Nat.lt_succ_of_le (Nat.le_add_right _ _))))
                hΨ (fun _ => hg) h₁ (unrefutedBelow_of_gHat hg
                  (fun h => hne (gbuInv7 hsat hC (Or.inl h))))
              obtain ⟨d₂⟩ := IH (.irr, Ψ, C₂)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                hΨ (fun _ => hg) h₂ (unrefutedBelow_of_gHat hg
                  (fun h => hne (gbuInv7 hsat hC (Or.inr h))))
              exact ⟨.randI d₁ d₂⟩
          | or C₁ C₂ =>
              obtain ⟨h₁, h₂⟩ := sfR_or hC
              have hg := hΩc rfl
              refine byDec (decI Ψ C₁) (fun he₁ => ?_) (fun he₁ => ?_)
              · refine byDec (decI Ψ C₂) (fun he₂ => ?_) (fun he₂ => ?_)
                · exact absurd (gbuInv10 hsat hC he₁ he₂) hne
                · obtain ⟨d⟩ := IH (.irr, Ψ, C₂)
                    (wgKeep (fun _ h => .base h) (seqSize_goal
                      (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                    hΨ (fun _ => hg) h₂ (unrefutedBelow_of_gHat hg he₂)
                  exact ⟨.rorI2 d⟩
              · obtain ⟨d⟩ := IH (.irr, Ψ, C₁)
                  (wgKeep (fun _ h => .base h) (seqSize_goal
                    (Nat.lt_succ_of_le (Nat.le_add_right _ _))))
                  hΨ (fun _ => hg) h₁ (unrefutedBelow_of_gHat hg he₁)
                exact ⟨.rorI1 d⟩
          | imp A B =>
              obtain ⟨hA, hB⟩ := sfR_imp hC
              have hg := hΩc rfl
              refine byDec (decClo Ψ A) (fun hcl => ?_) (fun hcl => ?_)
              · obtain ⟨d⟩ := IH (.irr, Ψ, B)
                  (wgKeep (fun _ h => .base h) (seqSize_goal
                    (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                  hΨ (fun _ => hg) hB (unrefutedBelow_of_gHat hg
                    (fun h => hne (gbuInv8 hsat hC hcl h)))
                exact ⟨.rimpII d hcl⟩
              · obtain ⟨d⟩ := IH (.reg, A :: Ψ, B) (wgDrop (unclosed_lt hA hcl))
                  (by
                    intro Y hY
                    rcases List.mem_cons.mp hY with rfl | hY'
                    · exact hA
                    · exact hΨ Y hY')
                  hB (fun h => hne (gbuInv9 hsat hC hg hcl h))
                exact ⟨.rimpNII d hcl⟩
          | circ Z =>
              have hZsf : Z ∈ sfR G := sfR_circ hC
              rcases findNot (fun X => (inferInstance : Decidable (X ∈ gHat G))) Ψ with
                hg | ⟨X, hXΨ, hXn⟩
              · rcases findNot
                  (fun X => (inferInstance : Decidable (X.isCirc = false))) Ψ with
                  hnoc | ⟨Y, hYΨ, hYc⟩
                · -- `Ψ ⊆ Ĝ_at ∪ Ĝ_imp`: the critical modal cell
                  have hΩai : ∀ W ∈ Ψ, W ∈ gAt G ++ gImp G := by
                    intro W hW
                    rcases gHat_cases (hg W hW) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hc⟩
                    · exact List.mem_append_left _ h
                    · exact List.mem_append_right _ h
                    · exact absurd hc (by simpa using hnoc W hW)
                  refine byDec (decRC Ψ Z) (fun hrc => ?_) (fun hrc => ?_)
                  · exact absurd (gbuSuccCircIC hsat hg hC hrc) hne
                  · rcases findNot (fun W => decI Ψ W) ((impPart Ψ).map ante) with
                      hallI | ⟨W, hW, hnW⟩
                    · obtain ⟨d⟩ := IH (.cirr, Ψ, Z)
                        (wgKeep (fun _ h => .base h)
                          (seqSize_goal (Nat.lt_succ_self _)))
                        hΩai hZsf
                        (fun A B hAB => hallI A (List.mem_map.mpr
                          ⟨.imp A B, List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩))
                        hrc
                      exact ⟨.rcircI d hC⟩
                    · obtain ⟨Y', hYmem, hYante⟩ := List.mem_map.mp hW
                      obtain ⟨hYΨ', hYi⟩ := List.mem_filter.mp hYmem
                      match Y', hYi, hYante, hYΨ' with
                      | .imp A B, _, hYante, hYΨ' =>
                          have hAW : A = W := hYante
                          have hnA : ¬ EvalI D Ψ A := by rw [hAW]; exact hnW
                          obtain ⟨lY, rY, hYsplit⟩ := List.append_of_mem hYΨ'
                          obtain ⟨hAsf, hBsf⟩ := sfL_imp (hΨ _ hYΨ')
                          have hΓ : Ψ ≐ .imp A B :: (lY ++ rY) := by
                            rw [hYsplit]; exact ctxEq_split
                          have hmemsub : ∀ V ∈ lY ++ rY, V ∈ Ψ :=
                            fun V hV => (hΓ V).mpr (List.mem_cons_of_mem _ hV)
                          have hclA : ∀ V ∈ Ψ, Clo (Form.imp A B :: (lY ++ rY)) V :=
                            fun V hV => .base ((hΓ V).mp hV)
                          have go : ∀ _hsz : A.hasCirc = false ∨
                              A.size < (Form.circ Z).size,
                              Nonempty (GbuIC G Ψ (Form.circ Z)) := by
                            intro hsz
                            obtain ⟨d₁⟩ := IH (.irr, .imp A B :: (lY ++ rY), A)
                              (by
                                rcases hsz with hfree | hlt
                                · exact wgTpLt hclA (tpC_free_lt_circ hfree)
                                · refine wgKeep hclA ?_ (tpC_le_circ _ _)
                                  have hgoal' := seqSize_goal (Ψ := lY ++ rY) hlt
                                  show seqSize (Form.imp A B :: (lY ++ rY)) A
                                    < seqSize Ψ (Form.circ Z)
                                  rw [hYsplit, seqSize_split, seqSize_cons]
                                  omega)
                              (by
                                intro V hV
                                rcases List.mem_cons.mp hV with rfl | hV'
                                · exact hΨ _ hYΨ'
                                · exact hΨ V (hmemsub V hV'))
                              (by
                                intro _ V hV
                                rcases List.mem_cons.mp hV with rfl | hV'
                                · exact hg _ hYΨ'
                                · exact hg V (hmemsub V hV'))
                              hAsf (unrefutedBelow_of_gHat
                              (by
                                intro V hV
                                rcases List.mem_cons.mp hV with rfl | hV'
                                · exact hg _ hYΨ'
                                · exact hg V (hmemsub V hV'))
                              (fun h => hnA (evalI_ctxEq (ctxEq_symm hΓ) h)))
                            obtain ⟨d₂⟩ := IH (.irr, B :: (lY ++ rY), Form.circ Z)
                              (by
                                refine wgKeep (fun V hV => ?_) ?_
                                · rcases List.mem_cons.mp ((hΓ V).mp hV) with rfl | hV'
                                  · exact .imp (.base List.mem_cons_self)
                                  · exact .base (List.mem_cons_of_mem _ hV')
                                · show seqSize (B :: (lY ++ rY)) (Form.circ Z)
                                    < seqSize Ψ (Form.circ Z)
                                  rw [hYsplit, seqSize_split, seqSize_cons]
                                  have hb : B.size < (Form.imp A B).size :=
                                    Nat.lt_succ_of_le (Nat.le_add_left _ _)
                                  omega)
                              (by
                                intro V hV
                                rcases List.mem_cons.mp hV with rfl | hV'
                                · exact hBsf
                                · exact hΨ V (hmemsub V hV'))
                              (fun h => Bool.noConfusion h) hC
                              (unrefutedBelow_step hsat (fun V hV => by
                                rcases List.mem_cons.mp ((hΓ V).mp hV) with rfl | hV'
                                · exact .imp (.base List.mem_cons_self)
                                · exact .base (List.mem_cons_of_mem _ hV')) hnb)
                            exact ⟨.limpLI d₁ d₂ hsz hC hΓ⟩
                          refine byDec
                            (inferInstance : Decidable (A.hasCirc = false))
                            (fun hfree => go (Or.inl hfree)) (fun hnfree => ?_)
                          refine byDec
                            (inferInstance : Decidable (A.size < (Form.circ Z).size))
                            (fun hlt => go (Or.inr hlt))
                            (fun hnlt => bigAnte Ψ A B Z hΩai hYΨ' hC hnA
                              (fun hc => hc.elim hnfree hnlt))
                · -- a modal formula in the context: `L◯ᵢ`
                  have hYc' : Y.isCirc = true := by
                    cases hb : Y.isCirc with
                    | true => rfl
                    | false => exact absurd hb hYc
                  match Y, hYc' with
                  | .circ Y', _ =>
                      obtain ⟨lY, rY, hYsplit⟩ := List.append_of_mem hYΨ
                      have hΓ : Ψ ≐ .circ Y' :: (lY ++ rY) := by
                        rw [hYsplit]; exact ctxEq_split
                      have hmemsub : ∀ V ∈ lY ++ rY, V ∈ Ψ :=
                        fun V hV => (hΓ V).mpr (List.mem_cons_of_mem _ hV)
                      have hY'sf : Y' ∈ sfL G := sfL_circ (hΨ _ hYΨ)
                      have hcov : ∀ V ∈ Ψ, Clo (Y' :: (lY ++ rY)) V := by
                        intro V hV
                        rcases List.mem_cons.mp ((hΓ V).mp hV) with rfl | hV'
                        · exact .circ (.base List.mem_cons_self)
                        · exact .base (List.mem_cons_of_mem _ hV')
                      obtain ⟨d⟩ := IH (.irr, Y' :: (lY ++ rY), Form.circ Z)
                        (by
                          refine wgKeep hcov ?_
                          show seqSize (Y' :: (lY ++ rY)) (Form.circ Z)
                            < seqSize Ψ (Form.circ Z)
                          rw [hYsplit, seqSize_split, seqSize_cons]
                          have : Y'.size < (Form.circ Y').size := Nat.lt_succ_self _
                          omega)
                        (by
                          intro V hV
                          rcases List.mem_cons.mp hV with rfl | hV'
                          · exact hY'sf
                          · exact hΨ V (hmemsub V hV'))
                        (fun h => Bool.noConfusion h) hC
                        (unrefutedBelow_step hsat hcov hnb)
                      exact ⟨.lcircI d (hΨ _ hYΨ) hΓ⟩
              · -- a NON-`Ĝ` member: `⊥`, `∧` or `∨`, and the rules obstruction 2
                -- added apply.  Their premises are licensed by the `Ĝ`
                -- ancestor the invariant carries, not by the parent.
                obtain ⟨lX, rX, hXsplit⟩ := List.append_of_mem hXΨ
                have hΓ : Ψ ≐ X :: (lX ++ rX) := by
                  rw [hXsplit]; exact ctxEq_split
                have hmemsub : ∀ V ∈ lX ++ rX, V ∈ Ψ :=
                  fun V hV => (hΓ V).mpr (List.mem_cons_of_mem _ hV)
                rcases sfL_dec (hΨ X hXΨ) with hgh | hbot | ⟨A, B, hand⟩ | ⟨A, B, hor⟩
                · exact absurd hgh hXn
                · exact ⟨.lbotI hC (hbot ▸ hΓ)⟩
                · subst hand
                  obtain ⟨hA, hB⟩ := sfL_and (hΨ _ hXΨ)
                  have hcov : ∀ V ∈ Ψ, Clo (A :: B :: (lX ++ rX)) V := by
                    intro V hV
                    rcases List.mem_cons.mp ((hΓ V).mp hV) with rfl | hV'
                    · exact .and (.base List.mem_cons_self)
                        (.base (List.mem_cons_of_mem _ List.mem_cons_self))
                    · exact .base (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hV'))
                  obtain ⟨d⟩ := IH (.irr, A :: B :: (lX ++ rX), Form.circ Z)
                    (by
                      refine wgKeep hcov ?_
                      show seqSize (A :: B :: (lX ++ rX)) (Form.circ Z)
                        < seqSize Ψ (Form.circ Z)
                      rw [hXsplit, seqSize_split, seqSize_cons, seqSize_cons]
                      show A.size + (B.size + seqSize (lX ++ rX) (Form.circ Z))
                        < seqSize (lX ++ rX) (Form.circ Z) + (A.size + B.size + 1)
                      omega)
                    (by
                      intro V hV
                      rcases List.mem_cons.mp hV with rfl | hV'
                      · exact hA
                      · rcases List.mem_cons.mp hV' with rfl | hV''
                        · exact hB
                        · exact hΨ V (hmemsub V hV''))
                    (fun h => Bool.noConfusion h) hC
                    (unrefutedBelow_step hsat hcov hnb)
                  exact ⟨.landLI d hC hΓ⟩
                · subst hor
                  obtain ⟨hA, hB⟩ := sfL_or (hΨ _ hXΨ)
                  have hsz : ∀ Y : Form, Y.size < (Form.or A B).size →
                      seqSize (Y :: (lX ++ rX)) (Form.circ Z)
                        < seqSize Ψ (Form.circ Z) := by
                    intro Y hY
                    rw [hXsplit, seqSize_split, seqSize_cons]
                    omega
                  have hcovL : ∀ V ∈ Ψ, Clo (A :: (lX ++ rX)) V := by
                    intro V hV
                    rcases List.mem_cons.mp ((hΓ V).mp hV) with rfl | hV'
                    · exact .orL (.base List.mem_cons_self)
                    · exact .base (List.mem_cons_of_mem _ hV')
                  have hcovR : ∀ V ∈ Ψ, Clo (B :: (lX ++ rX)) V := by
                    intro V hV
                    rcases List.mem_cons.mp ((hΓ V).mp hV) with rfl | hV'
                    · exact .orR (.base List.mem_cons_self)
                    · exact .base (List.mem_cons_of_mem _ hV')
                  obtain ⟨d₁⟩ := IH (.irr, A :: (lX ++ rX), Form.circ Z)
                    (wgKeep hcovL (hsz A (Nat.lt_succ_of_le (Nat.le_add_right _ _))))
                    (by
                      intro V hV
                      rcases List.mem_cons.mp hV with rfl | hV'
                      · exact hA
                      · exact hΨ V (hmemsub V hV'))
                    (fun h => Bool.noConfusion h) hC
                    (unrefutedBelow_step hsat hcovL hnb)
                  obtain ⟨d₂⟩ := IH (.irr, B :: (lX ++ rX), Form.circ Z)
                    (wgKeep hcovR (hsz B (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                    (by
                      intro V hV
                      rcases List.mem_cons.mp hV with rfl | hV'
                      · exact hB
                      · exact hΨ V (hmemsub V hV'))
                    (fun h => Bool.noConfusion h) hC
                    (unrefutedBelow_step hsat hcovR hnb)
                  exact ⟨.lorLI d₁ d₂ hC hΓ⟩
      | cirr =>
          -- ============ IRREGULAR, CLEAN QUERY: `Ψ →g C` ============
          show (∀ X ∈ Ψ, X ∈ gAt G ++ gImp G) → C ∈ sfR G →
            (∀ A B, Form.imp A B ∈ Ψ → EvalI D Ψ A) → ¬ EvalRC D Ψ C →
            Nonempty (GbuIC G Ψ C)
          intro hΩai hC hups hne
          have hg : ∀ X ∈ Ψ, X ∈ gHat G :=
            fun X hX => List.mem_append_left _ (hΩai X hX)
          have hΨ : ∀ X ∈ Ψ, X ∈ sfL G := by
            intro X hX
            rcases List.mem_append.mp (hΩai X hX) with h | h
            · exact (List.mem_filter.mp h).1
            · exact (List.mem_filter.mp h).1
          have toRC : ∀ {Ω : List Form} {F : Form}, RefutedCleanly G Ω F → EvalRC D Ω F :=
            fun h => evalRC_of_refutedCleanly hsat h
          have fromRC : ∀ {Ω : List Form} {F : Form}, EvalRC D Ω F → RefutedCleanly G Ω F :=
            fun h => (evalRC_iff_refutedCleanly hsat).mp h
          refine byDec (inferInstance : Decidable (C ∈ Ψ))
            (fun hax => ⟨.ax C (ctxEq_cons_self hax)⟩) (fun hax => ?_)
          cases C with
          | atom a =>
              exact absurd (toRC (refutedCleanly_at hsat hΩai rfl hC hax hups)) hne
          | bot =>
              exact absurd (toRC (refutedCleanly_at hsat hΩai rfl hC hax hups)) hne
          | and C₁ C₂ =>
              obtain ⟨h₁, h₂⟩ := sfR_and hC
              obtain ⟨d₁⟩ := IH (.cirr, Ψ, C₁)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (Nat.lt_succ_of_le (Nat.le_add_right _ _))))
                hΩai h₁ hups (fun h => hne (toRC (refutedCleanly_and1 hC (fromRC h))))
              obtain ⟨d₂⟩ := IH (.cirr, Ψ, C₂)
                (wgKeep (fun _ h => .base h) (seqSize_goal
                  (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                hΩai h₂ hups (fun h => hne (toRC (refutedCleanly_and2 hC (fromRC h))))
              exact ⟨.randI d₁ d₂⟩
          | or C₁ C₂ =>
              obtain ⟨h₁, h₂⟩ := sfR_or hC
              refine byDec (decI Ψ C₁) (fun he₁ => ?_) (fun he₁ => ?_)
              · refine byDec (decI Ψ C₂) (fun he₂ => ?_) (fun he₂ => ?_)
                · exact absurd
                    (toRC (refutedCleanly_or hsat hΩai hC hups he₁ he₂)) hne
                · obtain ⟨d⟩ := IH (.irr, Ψ, C₂)
                    (wgKeep (fun _ h => .base h) (seqSize_goal
                      (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                    hΨ (fun _ => hg) h₂ (unrefutedBelow_of_gHat hg he₂)
                  exact ⟨.rorI2 d⟩
              · obtain ⟨d⟩ := IH (.irr, Ψ, C₁)
                  (wgKeep (fun _ h => .base h) (seqSize_goal
                    (Nat.lt_succ_of_le (Nat.le_add_right _ _))))
                  hΨ (fun _ => hg) h₁ (unrefutedBelow_of_gHat hg he₁)
                exact ⟨.rorI1 d⟩
          | imp A B =>
              obtain ⟨hA, hB⟩ := sfR_imp hC
              refine byDec (decClo Ψ A) (fun hcl => ?_) (fun hcl => ?_)
              · obtain ⟨d⟩ := IH (.cirr, Ψ, B)
                  (wgKeep (fun _ h => .base h) (seqSize_goal
                    (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
                  hΩai hB hups
                  (fun h => hne (toRC (refutedCleanly_imp hC
                    (refutedCleanly_clo (fun X hX => by
                      rcases List.mem_cons.mp hX with rfl | hX'
                      · exact hcl
                      · exact .base hX') (fromRC h)))))
                exact ⟨.rimpII d hcl⟩
              · obtain ⟨d⟩ := cleanReg (A :: Ψ) B
                  (by
                    intro Y hY
                    rcases List.mem_cons.mp hY with rfl | hY'
                    · exact hA
                    · exact hΨ Y hY')
                  hB (fun h => hne (toRC (refutedCleanly_imp hC (fromRC h))))
                exact ⟨.rimpNII d hcl⟩
          | circ Z =>
              obtain ⟨d⟩ := IH (.cirr, Ψ, Z)
                (wgKeep (fun _ h => .base h) (seqSize_goal (Nat.lt_succ_self _)))
                hΩai (sfR_circ hC) hups
                (fun h => hne (toRC (refutedCleanly_circIn hC (fromRC h))))
              exact ⟨.rcircI d hC⟩
  exact fun p => main _ p rfl

/-! ## The root sequent

`BSearch` at `⇒g G` is legitimate for the same reason as in the paper: a
database row `Γ ⇒ G` would BE an `FRJV(G)`-refutation of `G`. -/

theorem provableGbuC_of_not_provableV {G : Form} {D : FSeq → Prop}
    (hsat : Saturated G D)
    (decI : ∀ Ω C, Decidable (EvalI D Ω C))
    (decRC : ∀ Ψ C, Decidable (EvalRC D Ψ C))
    (bigAnte : BigAnte G D) (cleanReg : CleanReg G D)
    (hroot : ¬ EvalR D [] G) : ProvableGbuC G :=
  searchO hsat decI decRC bigAnte cleanReg (.reg, [], G)
    (fun _ h => absurd h List.not_mem_nil) (sfR_self G) hroot

/-- On the canonical database the root hypothesis IS `⊬_{FRJV(G)} G`. -/
theorem not_evalR_root {G : Form} (h : ¬ ProvableV G) :
    ¬ EvalR (FDerivable G) [] G := by
  rintro ⟨Γ, ⟨t, hd⟩, -⟩
  exact h ⟨t, Γ, hd⟩

/-- info: 'FRJ.Gbu.searchO' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms searchO

/-- info: 'FRJ.Gbu.provableGbuC_of_not_provableV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableGbuC_of_not_provableV

/-- info: 'FRJ.Gbu.not_evalR_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_evalR_root

/-! ## (S3) is FALSE, and so is the `cirr` clause it serves

`CleanReg` cannot be discharged: it is refuted, and by the sharpest cell
in the development.

    G = ◯p ⊃ p,    Ψ = { ◯p },    C = p

* `D ⋫ᶜ (Ψ ⇒g p)` — any clean derivation of `Γ ⇒ p` with `◯p ∈ Cl(Γ)`
  contradicts `not_clean_of_clo_circ`: the root would force `◯p`, hence
  some `Rm`-successor forces `p`, hence (by `tag_cone`) the root does,
  contradicting `lemma39R`.  This is `tag_weakening_refuted`'s fact
  again, now as a database statement.
* But `Ψ ⇒g p` is NOT derivable in `Gbu◯(G)`: by `soundRC` it would give
  `◯p ⊨ p`, and `Kmc` refutes that.

So (S3) is not a gap to be filled but a FALSE hypothesis, and `searchO`
is vacuous wherever it is assumed — which is any `G` with a modal
subformula.  The fault is upstream, in the `cirr` clause itself. -/

private def pcr : Form := .atom "p"
private def Gcr : Form := .imp (.circ pcr) pcr

/-- No CLEAN row refutes `◯p ⇒ p`. -/
theorem not_evalRC_circ_self :
    ¬ EvalRC (FDerivable Gcr) [Form.circ pcr] pcr := by
  intro h
  obtain ⟨Γ, t, ⟨d⟩, htag, hcov⟩ :=
    (evalRC_iff_refutedCleanly (saturated_fderivable Gcr)).mp h
  exact FRJ.V.not_clean_of_clo_circ d (hcov _ List.mem_cons_self) htag

/-- …and `◯p ⇒g p` is not derivable, since `◯p ⊭ p`. -/
theorem not_gbuRC_circ_self : ¬ Nonempty (GbuRC Gcr [Form.circ pcr] pcr) := by
  rintro ⟨d⟩
  refine Kmc_not_force_p (soundRC (K := Kmc) d W2.wa ?_)
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact Kmc_force_circ_p
  · exact absurd hX' List.not_mem_nil

/-- **(S3) is REFUTED.** -/
theorem not_cleanReg : ¬ CleanReg Gcr (FDerivable Gcr) := by
  intro h
  exact not_gbuRC_circ_self
    (h [Form.circ pcr] pcr
      (fun X hX => by
        rcases List.mem_cons.mp hX with rfl | hX'
        · exact (by decide : Form.circ pcr ∈ sfL Gcr)
        · exact absurd hX' List.not_mem_nil)
      (by decide) not_evalRC_circ_self)

/-- info: 'FRJ.Gbu.not_cleanReg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_cleanReg

/-! ## `◯(◯p ⊃ p)` is NOT valid — the OPEN question of §2026-08-30k, closed

Matthew, 2026-08-30: if `◯(◯p ⊃ p)` were a theorem then so would be its
substitution instance at `p := ⊥`,

    ◯(◯⊥ ⊃ ⊥)  =  ◯¬◯⊥  =  q5  =  ρ7

and ρ7 is provably distinct from `⊤` in the ρ-order.  The verdict was
already in the repository — `PLLND.RNC.rnc_ref_1_5` in `wip/rncCert.lean`
kernel-checks `¬ ConfluentU.DerivU [q1] q5` on the three-world model

    ⟨3, ≤ = [(1,0),(2,0),(2,1)], Rm = [(1,0)], Fal = {0}, V = ∅⟩,  w = 2

— and the standing rule is to look the cell up BEFORE searching.  I did
not; I asserted a semantic hunch, and the hunch was wrong.

What follows is the same fact obtained the way it should be: by driving
`FRJV(G)` to the refutation and letting `modR` extract the model. -/

private def pv : Form := .atom "p"
/-- `G = ◯(◯p ⊃ p)`. -/
def Gcc : Form := .circ (.imp (.circ pv) pv)

-- `Ĝ_at = {p}`, `Ĝ_imp = ∅`, `Ĝ_◯ = {◯p}`, and `Ĝ_at ∖ {p} = ∅`.
example : (gAt Gcc, gImp Gcc, gCirc Gcc, rm (gAt Gcc) pv)
    = ([pv], [], [Form.circ pv], []) := rfl

private theorem not_clo_nil_circ_atom : ¬ Clo [] (Form.circ pv) := by
  intro h
  cases h with
  | base hm => exact absurd hm List.not_mem_nil
  | circ h' => cases h' with
    | base hm => exact absurd hm List.not_mem_nil

/-- **`FRJV(G)` finds the countermodel.**  Three steps, each forced:

1. `Ax^I◯`… no — `Ax^I` on the prime goal `p`, then the FALLIBLE atomic
   join `⋈^At_F`, which keeps the whole modal zone.  Its conclusion is
   `◯p ⇒ p` at tag `blocked`: the extracted world reaches `p` only
   through a fallible successor, which is exactly why `◯p ⊃ p` fails.
2. `⊃∉` turns that into the irregular `∅ ; ∅ → ◯p ⊃ p`.  Its side
   condition `¬ Cl(Θ) ∋ ◯p` is met by taking the moveable zone EMPTY —
   the antecedent is closed by the premise's context, not by `Θ`.
3. `⋈^◯` lifts it under the modality.  The join's `RefAt` obligation is
   discharged by its base clause `Υ`-membership, and the conclusion
   context is empty, so this IS `⊢_{FRJV(Gcc)} Gcc`.

The tag of step 1 is `blocked`, which is why step 3 must be the JOIN and
not `◯∈` — `not_clean_of_clo_circ` forbids the latter.  The dirty tag is
the whole content of the cell. -/
def GccWitness : (Γ : List Form) × FRJVr Gcc .barren Γ Gcc :=
  let hax : FRJVi Gcc [] (rm (gAt Gcc) pv ++ gImp Gcc ++ gCirc Gcc) pv :=
    .axI pv rfl (by decide) (CtxEq.refl _)
  let hjoin := FRJVr.joinAtF (G := Gcc) (n := 0)
    (stab := fun _ => []) (rhs := fun _ => pv) (F := pv)
    (fun _ => hax)
    (by intro i j h;
        exact absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) h)
    (by intro A B h; simp [unionAll, impPart] at h)
    rfl (by simp [unionAll, atPart]) (by decide) (CtxEq.refl _)
  let hirr : FRJVi Gcc [] [] (Form.imp (.circ pv) pv) :=
    .impNotIn hjoin (fun X hX => absurd hX List.not_mem_nil)
      (.base (by decide)) not_clo_nil_circ_atom (by decide)
  ⟨_, FRJVr.joinCirc (G := Gcc) (n := 0)
    (stab := fun _ => []) (th := fun _ => [])
    (rhs := fun _ => Form.imp (.circ pv) pv)
    (fun _ => hirr)
    (by intro i j h;
        exact absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) h)
    (by intro A B h; simp [unionAll, impPart] at h)
    (by simp [unionAll, circPart])
    (keptChainRestrict _ _)
    (.ups (by simp [upsilon]))
    (by decide) (CtxEq.refl _)⟩

theorem provableV_Gcc : ProvableV Gcc :=
  ⟨.barren, GccWitness.1, ⟨GccWitness.2⟩⟩

/-- **`◯(◯p ⊃ p)` is NOT PLL-valid** — the open question of §2026-08-30k,
closed by the calculus itself rather than by a hand-built model. -/
theorem not_pll_Gcc : ¬ PLL Gcc := soundnessV provableV_Gcc


/-- The countermodel itself, extracted from the derivation by `modR`. -/
theorem countermodel_Gcc : ∃ K : Kripke, Countermodel K Gcc := by
  exact ⟨FRJ.V.modR GccWitness.2, FRJ.V.modR_countermodel GccWitness.2⟩

/-- info: 'FRJ.Gbu.provableV_Gcc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_Gcc

/-- info: 'FRJ.Gbu.not_pll_Gcc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_pll_Gcc

/-- info: 'FRJ.Gbu.countermodel_Gcc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms countermodel_Gcc

/-! ### The extracted model, burned in

`preR`/`modR` build the countermodel FROM the derivation.  Dumping it is
a closed computation, so the model below is checked by the build, not
asserted in prose. -/

private def ppF : Form → String
  | .atom p => p
  | .bot => "⊥"
  | .and a b => s!"({ppF a} ∧ {ppF b})"
  | .or a b => s!"({ppF a} ∨ {ppF b})"
  | .imp a .bot => s!"¬{ppF a}"
  | .imp a b => s!"({ppF a} ⊃ {ppF b})"
  | .circ a => s!"◯{ppF a}"

private def ppL (l : List Form) : String :=
  if l.isEmpty then "·" else String.intercalate ", " (l.map ppF)

/-- Dump the model a derivation extracts: worlds, labels, `≤`, `Rm`,
fallibility. -/
def dumpModel {G : Form} {t : Tag} {Γ : List Form} {C : Form}
    (d : FRJVr G t Γ C) : String :=
  let P := FRJ.V.preR d
  let ws := P.elems
  let ix : P.W → Nat := fun w => ws.findIdx (fun x => decide (x = w))
  let leOf : P.W → List Nat := fun w =>
    (ws.filter (fun v => @decide (P.le w v) (P.decLe w v))).map ix
  let rmOf : P.W → List Nat := fun w =>
    (ws.filter (fun v => @decide (P.rm w v) (P.decRm w v))).map ix
  let falOf : P.W → Bool := fun w => @decide (P.fal w) (P.decFal w)
  let lines := ws.map (fun w =>
    let tag := if falOf w then "FALLIBLE" else "        "
    s!"  w{ix w} {tag}  lbl = [{ppL (P.lbl w)}]  le -> {leOf w}  rm -> {rmOf w}")
  s!"root = w{ix P.root}, worlds = {ws.length}\n" ++ String.intercalate "\n" lines

/-!  The countermodel for `◯(◯p ⊃ p)`, as the derivation builds it.

`w0` is the barren root of the `⋈^◯` conclusion — its modal cone is
`{w0}`, which IS the `barren` tag.  `w1` is the `⋈^At_F` world: its cone
is `{w1, w2}` and contains the fallible `w2`, which is the `blocked` tag.
So `w1 ⊩ ◯p` (through the fallible successor) while `w1 ⊮ p`, hence
`w1 ⊮ ◯p ⊃ p`; and `w0`'s only modal successor is `w0` itself, which
refutes `◯p ⊃ p` for the same reason — so `w0 ⊮ ◯(◯p ⊃ p)`.

This is `rnc_ref_1_5`'s three-world model, up to reversal of the
indexing.

`#guard_msgs` below pins the dump, so the model is checked by the build. -/

/--
info: root = w0, worlds = 3
  w0           lbl = [·]  le -> [0, 1, 2]  rm -> [0]
  w1           lbl = [◯p]  le -> [1, 2]  rm -> [1, 2]
  w2 FALLIBLE  lbl = [◯p]  le -> [2]  rm -> [2]
-/
#guard_msgs in
#eval IO.println (dumpModel GccWitness.2)

/-! ### Why FRJV reaches for FALLIBILITY here, and not `Fal = ∅`

The economical model — same frame, no fallible world, `p` simply true at
the top — refutes `◯(◯p ⊃ p)` just as well:

    w0 ≤ w1 ≤ w2,   Rm: w0→{w0}, w1→{w1,w2}, w2→{w2},   V(p) = {w2}

`w1 ⊩ ◯p` through the infallible `w2`, `w1 ⊮ p`, so `w1 ⊮ ◯p ⊃ p`; and
`w0`'s only modal successor is itself.  So FRJV's fallible world is not
forced by the FORMULA.  It is forced by the CALCULUS, and precisely:

**no `FRJV(Gcc)` axiom can make `p` true at any world.**

* `Ax^R` / `Ax^I` at the only prime right subformula `p` leave the atomic
  zone `Ĝ_at ∖ {p} = ∅` — the axiom's whole job is to exclude its goal.
* There is no OTHER prime right subformula to run an axiom at: `Sf^R(Gcc)`
  is `{◯(◯p⊃p), ◯p⊃p, p}` and contains no `⊥`.  (This is why the
  promise join `⋈^At_P` cannot help either: its components are themselves
  `FRJV(Gcc)` derivations, so their worlds inherit the same zones.)
* `Ax^I◯` chooses a valuation `ats ⊆ Ĝ_at = {p}` and needs
  `classForce ats (◯p ⊃ p) = false`.  Both admissible choices give `true`.

Every world FRJV builds is labelled by one of those zones, so the only
device left that can force `p` is `fal_V`.  FRJV is not being lazy here;
its model space does not contain Matthew's model.

Bearing on FRJV COMPLETENESS: soundness is unaffected — a fallible
countermodel is a countermodel.  But FRJV's countermodels are canonical
(`Ĝ`-labelled), not minimal, and an economical model can lie outside the
space FRJV searches.  That is exactly the kind of restriction a
completeness proof has to confront. -/

/-- The three facts above, decided. -/
theorem no_axiom_forces_p :
    rm (gAt Gcc) pv = [] ∧
    Form.bot ∉ sfR Gcc ∧
    classForce [] (Form.imp (.circ pv) pv) = true ∧
    classForce [pv] (Form.imp (.circ pv) pv) = true := by decide

/-- info: 'FRJ.Gbu.no_axiom_forces_p' depends on axioms: [propext] -/
#guard_msgs in
#print axioms no_axiom_forces_p

end FRJ.Gbu
