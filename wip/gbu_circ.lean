/-
# `Gbu◯(G)`: the modal extension, in the paper's own order

Fiorentini–Ferrari, arXiv:1804.06689 §5, extended to PLL.  Each numbered
result of the paper is taken in its ORIGINAL order and its `◯`-extension
proved (or its obligation named) at that point, so the ledger below is
also the reading order of this file.

| # | source | result | `◯`-status |
|---|---|---|---|
| Lemma 7 | 3122 | soundness of the rules | **EXTENDED** — `sound_lcirc`, `sound_rcirc` |
| Thm 6 | 3107 | `⊢_Gbu(G) G → G ∈ IPL` | composes; nothing new |
| Lemma 8 | 3200 | the weight `Wg` | **REPLACED** — `wip/gbu_measure.lean` |
| Thm 7 | 3222 | termination | **REPLACED** — `stepU_wf`; the naive one is REFUTED (`no_measure_stepC`) |
| Lemma 9 | 3300 | invertibility, 10 clauses | **EXTENDED** — `gbuInv11` free; `gbuInv12`, `gbuInv13` from the kit |
| Lemma 10 | 4130 | `∨`-closure | ports unchanged (`gbuInv10` has no `◯` side condition) |
| Lemma 11 | 4160 | the `At` success lemma | **EXTENDED** — `gbuSuccAtF` |
| Lemma 12 | 4193 | the `∨` success lemma | **EXTENDED** — `gbuSuccOrF` |
| Thm 8 | 4215 | correctness of `BSearch` | OPEN — needs the store-carrying recursion of `wip/gbu_measure.lean` |
| Thm 9 | 4320 | the duality | OPEN — follows Thm 8 |
| Thm 10 | 4353 | completeness of both | OPEN — follows Thm 9 |

## The two re-run points

The campaign changes `FRJ◯` and `Gbu◯` independently, so the file is
organised so that a change to either edits ONE declaration and leaves
the proofs alone.

* **`TagClean`** (§0) is everything the modal layer takes from `FRJ◯`.
  `◯∈` and `◯∉` both carry the side condition

      t = barren  ∨  (t = chain W ∧ Covers Γ W Z)

  so a database row for `Z` can be lifted to `◯Z` only when its tag is
  clean at `Z`.  `TagClean G D Z` says every row for `Z` is.  Lemma 9's
  two modal clauses are then THEOREMS (`gbuInv12`, `gbuInv13`), not
  assumptions.  Change `FRJ◯`'s tag discipline — relax `◯∈` the way
  `RefAt` relaxed the barren joins — and only `TagClean` moves.
  ⚠ `Tag.blocked` is NOT clean: `gbuSuccAtF`/`gbuSuccOrF` produce
  `blocked` rows, so the fallible route and the `◯`-introduction route
  currently have incompatible tags.  That is the live obligation.

* **`FRJCircKit`** (§0) bundles the modal layer's whole interface to
  `FRJ◯` as one record.  Downstream results take a `FRJCircKit`, so a
  change to `Gbu◯`'s rule set changes which fields are asked for, and a
  change to `FRJ◯`'s rules changes how they are supplied — never both.

* **The rules themselves** (§1) are given semantically, one lemma per
  rule, INDEPENDENT of any inductive family.  Writing the extended
  `GbuRC`/`GbuIC` later is then a one-line dispatch per constructor, and
  editing a rule edits its lemma.

The three rules, as derived in `docs/gbu-circ-seams.md` from the `FRJ◯`
rules with matching conclusions:

    Ψ, Z ⇒g ◯C            Ψ ⇒g Z             Ω ⇒g Z
    ───────────── L◯      ──────── R◯        ────────── R◯ₙᵢ
    Ψ, ◯Z ⇒g ◯C           Ψ ⇒g ◯Z            Ω →g ◯Z

`L◯`'s goal MUST be `◯`-shaped: unrestricted the rule is unsound.
-/
import wip.gbu_search
import wip.gbu_measure
import FRJ.Erase

namespace FRJ.Gbu

open FRJ Form

/-! ## §0  The re-run points -/

/-- Every database row for `Z` carries a tag `◯∈` / `◯∉` can lift.  This
is the whole of what the modal layer needs from `FRJ◯`, and it is the
`Covers`/`KeptChain` retention obligation — the same object the LJF◯
campaign met as `CimpAnt`. -/
def TagClean (G : Form) (D : FSeq → Prop) (Z : Form) : Prop :=
  ∀ Γ : List Form, D (.reg Γ Z) → ∃ t : Tag, Nonempty (FRJVr G t Γ Z) ∧
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Γ W Z)

/-- The modal layer's interface to `FRJ◯`, as one record. -/
structure FRJCircKit (G : Form) (D : FSeq → Prop) : Prop where
  /-- Lemma 9, clause 11 (seam 2): the invertibility of `R◯`. -/
  invCircR : ∀ {Ψ : List Form} {Z : Form}, Form.circ Z ∈ sfR G →
    EvalR D Ψ Z → EvalR D Ψ (.circ Z)
  /-- Lemma 9, clause 12 (seam 3): the invertibility of `R◯ₙᵢ`. -/
  invCircNI : ∀ {Ω : List Form} {Z : Form}, Form.circ Z ∈ sfR G →
    (∀ X ∈ Ω, X ∈ gHat G) → EvalR D Ω Z → EvalI D Ω (.circ Z)

/-! ## §1  Lemma 7 (source 3122) — soundness of the three new rules

Stated semantically and per rule, so that they are independent of the
shape of the extended inductive family. -/

/-- `L◯` is sound — this is `◯`-elimination, and it is where the
`◯`-shaped goal is load-bearing.  With an arbitrary goal the rule would
assert `◯Z ⊢ Z`. -/
theorem sound_lcirc {K : Kripke} {Ψ : List Form} {Z C : Form}
    (h : ∀ w : K.W, K.forces w (Z :: Ψ) → K.force w (.circ C)) :
    ∀ w : K.W, K.forces w (.circ Z :: Ψ) → K.force w (.circ C) := by
  intro w hw b hwb
  obtain ⟨c, hbc, hcZ⟩ := hw (.circ Z) List.mem_cons_self b hwb
  have hwc : K.le w c := K.le_trans hwb (K.sub_mi hbc)
  have hcΨ : K.forces c (Z :: Ψ) := by
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX'
    · exact hcZ
    · exact K.forces_mono hwc (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) X hX'
  obtain ⟨e, hce, heC⟩ := h c hcΨ c (K.le_refl c)
  exact ⟨e, K.rm_trans hbc hce, heC⟩

/-- `R◯` and `R◯ₙᵢ` are sound — both are the unit `Z ⊃ ◯Z`.  The two
rules differ only in which judgment they conclude in, so one semantic
lemma covers both. -/
theorem sound_rcirc {K : Kripke} {Ψ : List Form} {Z : Form}
    (h : ∀ w : K.W, K.forces w Ψ → K.force w Z) :
    ∀ w : K.W, K.forces w Ψ → K.force w (.circ Z) := by
  intro w hw b hwb
  exact ⟨b, K.rm_refl b, h b (K.forces_mono hwb hw)⟩

/-- **`L⊃` is sound in EITHER judgment, and for ANY goal.**  It is plain
modus ponens: the left premise gives `A` from `A⊃B, Ψ`; the implication
is in the context, so `B` follows; the right premise then gives `C` from
`B, Ψ`.  Nothing about the judgment or the shape of `C` enters.

This is the answer to "`L⊃ᵢ` doesn't look valid": it is valid, and MORE
generally than the rule states.  The `◯`-shaped goal on `GbuIC.limpLI`
is not a soundness condition at all — it is there ONLY so the rule
cannot fire on a `◯`-free goal, i.e. purely to keep `deCircI` total.
What the irregular `L⊃` does change is the READING of `→g`: the paper's
irregular judgment is "provable with the context frozen", and this rule
unfreezes it.  That is the design cost we accepted, and it is a cost in
proof-search discipline, not in soundness. -/
theorem sound_limp {K : Kripke} {Ψ : List Form} {A B C : Form}
    (h₁ : ∀ w : K.W, K.forces w (.imp A B :: Ψ) → K.force w A)
    (h₂ : ∀ w : K.W, K.forces w (B :: Ψ) → K.force w C) :
    ∀ w : K.W, K.forces w (.imp A B :: Ψ) → K.force w C := by
  intro w h
  have himp := h _ List.mem_cons_self
  have hB := himp w (K.le_refl w) (h₁ w h)
  refine h₂ w (fun X hX => ?_)
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact hB
  · exact h X (List.mem_cons_of_mem _ hX')

/-! ### The `◯`-shaped goal of `L◯` is not a convenience

`sound_lcirc` asserts the restriction; this refutes the unrestricted
rule, so the restriction is a fact and not a stylistic choice.  The
countermodel is two worlds `a ≤ b`, `Rm = ≤`, `p` true only at `b`: the
root forces `◯p` and refutes `p`.  (Built on a bare inductive with
hand-supplied decidability — `Fin`'s order instances drag in
`Classical.choice`.) -/

inductive W2 where
  | wa : W2
  | wb : W2
  deriving DecidableEq

private def le2 : W2 → W2 → Prop
  | .wa, _ => True
  | .wb, .wb => True
  | .wb, .wa => False

private theorem le2_refl : ∀ a : W2, le2 a a
  | .wa => trivial
  | .wb => trivial

private theorem le2_trans : ∀ {a b c : W2}, le2 a b → le2 b c → le2 a c
  | .wa, _, _, _, _ => trivial
  | .wb, .wb, .wb, _, _ => trivial
  | .wb, .wa, _, h, _ => h.elim
  | .wb, .wb, .wa, _, h => h.elim

private theorem le2_antisymm : ∀ {a b : W2}, le2 a b → le2 b a → a = b
  | .wa, .wa, _, _ => rfl
  | .wa, .wb, _, h => h.elim
  | .wb, .wa, h, _ => h.elim
  | .wb, .wb, _, _ => rfl

private def decLe2 : ∀ a b : W2, Decidable (le2 a b)
  | .wa, _ => isTrue trivial
  | .wb, .wb => isTrue trivial
  | .wb, .wa => isFalse (fun h => h)

private theorem v2_mono : ∀ {a b : W2}, le2 a b → a = W2.wb → b = W2.wb
  | .wa, .wa, _, h => h
  | .wa, .wb, _, _ => rfl
  | .wb, .wa, h, _ => h.elim
  | .wb, .wb, _, _ => rfl

private theorem le2_wb : ∀ b : W2, le2 b W2.wb
  | .wa => trivial
  | .wb => trivial

/-- `a ≤ b`, `Rm = ≤`, `p` true exactly at `b`, no fallible world. -/
def Kmc : Kripke where
  W := W2
  elems := [.wa, .wb]
  complete := fun w => by
    cases w
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  decEq := inferInstance
  le := le2
  le_refl := le2_refl
  le_trans := le2_trans
  le_antisymm := le2_antisymm
  root := .wa
  root_le := fun _ => trivial
  V := fun w _ => w = .wb
  V_mono := fun h _ hv => v2_mono h hv
  Rm := le2
  rm_refl := le2_refl
  rm_trans := le2_trans
  sub_mi := fun h => h
  Fal := fun _ => False
  fal_mono := fun _ h => h.elim
  fal_V := fun h => h.elim
  decLe := decLe2
  decV := fun a _ => inferInstanceAs (Decidable (a = W2.wb))
  decRm := decLe2
  decFal := fun _ => isFalse (fun h => h)

theorem Kmc_force_circ_p : Kmc.force W2.wa (.circ (.atom "p")) := by
  intro b _
  refine ⟨W2.wb, ?_, ?_⟩
  · show le2 b W2.wb
    exact le2_wb b
  · show W2.wb = W2.wb
    rfl

theorem Kmc_not_force_p : ¬ Kmc.force W2.wa (.atom "p") := by
  intro h
  have h' : W2.wa = W2.wb := h
  exact W2.noConfusion h'

/-- **`L◯` with an unrestricted goal is UNSOUND.** -/
theorem lcirc_goal_must_be_circ :
    ¬ (∀ (K : Kripke) (Ψ : List Form) (Z C : Form),
        (∀ w : K.W, K.forces w (Z :: Ψ) → K.force w C) →
        ∀ w : K.W, K.forces w (.circ Z :: Ψ) → K.force w C) := by
  intro h
  refine Kmc_not_force_p (h Kmc [] (.atom "p") (.atom "p")
    (fun w hw => hw (.atom "p") List.mem_cons_self) W2.wa ?_)
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact Kmc_force_circ_p
  · exact absurd hX' List.not_mem_nil

/-! ## §2  Theorem 6 (source 3107)

Nothing new: `Gbu◯(G)`-provability implies `PLL`-validity as soon as
every rule is sound, and §1 supplies the three missing cases. -/

/-! ## §3–4  Lemma 8 and Theorem 7 (source 3200, 3222)

The weight and termination are settled in `wip/gbu_measure.lean`, and
the answer is not the paper's.  `R◯ₙᵢ` releases focus, so the paper's
`Wg = ⟨unclosed, tp, size⟩` increases along it; worse, the extended step
relation has a two-cycle, both of whose nodes satisfy (BSr1)
(`not_wf_stepC`, `cyc_notRefuted`), so NO measure on sequents into any
well-founded order can work (`no_measure_stepC`).  The measure that does
is store-carrying:

    Wg◯(τ, U) = ⟨ |Sf^L(G) ∖ Cl(Ψ)| , Σ_{X∈Ψ} |X| , |Ψ^⊃ ∖ U| , |C| ⟩

with `wgo_step` and `stepU_wf`.  `tp` disappears; `ctxSize` replaces it. -/

/-! ## §5  Lemma 9 (source 3300) — the invertibility clauses

Clauses 1–10 are in `wip/gbu_db.lean` and port unchanged.  Three modal
clauses are added here, in the order the rules were derived. -/

/-- **Lemma 9, clause 11** — `L◯`.  FREE, exactly as clauses 1, 3 and 4:
no `FRJ` rule is applied, only the `Clo` closure's modal clause
`Clo Γ X → Clo Γ (◯X)`, which is sound by the unit. -/
theorem gbuInv11 {D : FSeq → Prop} {Ψ : List Form} {Z C : Form}
    (h : EvalR D (Z :: Ψ) C) : EvalR D (.circ Z :: Ψ) C := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  refine ⟨Γ, hmem, fun X hX => ?_⟩
  rcases List.mem_cons.mp hX with rfl | hX'
  · exact .circ (hcl Z List.mem_cons_self)
  · exact hcl X (List.mem_cons_of_mem _ hX')

/-- **Lemma 9, clause 12** — `R◯`, from `◯∈` and (DB2).  A theorem given
`TagClean`; this is the first re-run point. -/
theorem gbuInv12 {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ψ : List Form} {Z : Form} (hclean : TagClean G D Z)
    (hgoal : Form.circ Z ∈ sfR G) (h : EvalR D Ψ Z) :
    EvalR D Ψ (.circ Z) := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  obtain ⟨t, ⟨d⟩, htag⟩ := hclean Γ hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg Γ (.circ Z)) ⟨t, ⟨.circIn d htag hgoal⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      exact ⟨Γ', hs'mem, fun X hX => clo_mono hΓ (hcl X hX)⟩

/-- **Lemma 9, clause 13** — `R◯ₙᵢ`, from `◯∉` and (DB2).  The exact
modal twin of clause 9 (`gbuInv9`, the `R⊃ₙᵢ` clause): the premise is
REGULAR and the conclusion irregular, and the second zone is `Ω`
itself. -/
theorem gbuInv13 {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {Z : Form} (hclean : TagClean G D Z)
    (hgoal : Form.circ Z ∈ sfR G) (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (h : EvalR D Ω Z) : EvalI D Ω (.circ Z) := by
  obtain ⟨Γ, hmem, hcl⟩ := h
  obtain ⟨t, ⟨d⟩, htag⟩ := hclean Γ hmem
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr [] Ω (.circ Z))
      ⟨.circNotIn d htag (fun X hX => ⟨hcl X hX, hΩ X hX⟩) hgoal⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSt, hTh⟩ =>
      exact ⟨St', Th', hs'mem,
        fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil,
        fun {x} hx => List.mem_append_right _ (hTh hx)⟩

/-- The kit, supplied from `TagClean` at every `◯`-body of `G`.  THIS is
the declaration to edit when `FRJ◯`'s tag discipline changes. -/
theorem frjCircKit_of_tagClean {G : Form} {D : FSeq → Prop}
    (hsat : Saturated G D) (hclean : ∀ Z : Form, TagClean G D Z) :
    FRJCircKit G D :=
  { invCircR := fun hgoal h => gbuInv12 hsat (hclean _) hgoal h
    invCircNI := fun hgoal hΩ h => gbuInv13 hsat (hclean _) hgoal hΩ h }

/-! ## §6  Lemma 10 (source 4130)

`gbuInv10` (the `∨`-closure, via `∨ᴵ`) carries no `◯` side condition
and ports unchanged. -/

/-! ## §7  Lemma 11 (source 4160) — the `At` success lemma, modal case

`gbuSuccAt` assumed `Ω ⊆ Ĝ_at ∪ Ĝ_imp`, and used it in exactly ONE
place: to discharge `⋈^At`'s premise `⋃ⱼ (Σⱼ)^◯ = []`.  The FALLIBLE
join `⋈^At_F` has no such premise and keeps the WHOLE modal zone
(`joinCtxCircF`), so the assumption weakens to `Ω ⊆ Ĝ` in its full
three-zone form and the proof goes through with the join swapped.

This is what closes seam 1: at a prime goal the database always refutes,
so (BSr1) fails and backward search never arrives there.  Seam 1 needs
no rule.  The price is the tag — the row is `blocked`. -/

private theorem gHat_cases {G X : Form} (h : X ∈ gHat G) :
    (X ∈ gAt G ∧ X.isPV = true) ∨ (X ∈ gImp G ∧ X.isImp = true) ∨
      (X ∈ gCirc G ∧ X.isCirc = true) := by
  rcases List.mem_append.mp h with h' | h'
  · rcases List.mem_append.mp h' with h'' | h''
    · exact Or.inl ⟨h'', (List.mem_filter.mp h'').2⟩
    · exact Or.inr (Or.inl ⟨h'', (List.mem_filter.mp h'').2⟩)
  · exact Or.inr (Or.inr ⟨h', (List.mem_filter.mp h').2⟩)

/-- `evalI_axI` with the modal zone admitted. -/
theorem evalI_axI_gHat {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {F : Form} (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (hFp : F.isPrime = true) (hF : F ∈ sfR G) (hFn : F ∉ Ω) : EvalI D Ω F := by
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.irr [] (rm (gAt G) F ++ gImp G ++ gCirc G) F)
      ⟨.axI F hFp hF (CtxEq.refl _)⟩
  match s', hsub with
  | .irr St' Th' _, ⟨rfl, hSt, hTh⟩ =>
      refine ⟨St', Th', hs'mem,
        fun {x} hx => absurd ((hSt x).mpr hx) List.not_mem_nil, ?_⟩
      intro x hx
      refine List.mem_append_right _ (hTh ?_)
      rcases gHat_cases (hΩ x hx) with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact List.mem_append_left _ (List.mem_append_left _
          (mem_rm.mpr ⟨fun he => hFn (he ▸ hx), h⟩))
      · exact List.mem_append_left _ (List.mem_append_right _ h)
      · exact List.mem_append_right _ h

/-- **Lemma 11, modal case.** -/
theorem gbuSuccAtF {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {F : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (hFp : F.isPrime = true) (hFgoal : F ∈ sfR G) (hFmem : F ∉ Ω)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A) :
    EvalR D Ω F := by
  let U := F :: (impPart Ω).map ante
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : EvalI D Ω (f j) := by
      by_cases e₀ : f j = F
      · exact e₀ ▸ evalI_axI_gHat hsat hΩ hFp hFgoal hFmem
      have hm : f j ∈ (impPart Ω).map ante := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h e₀
        · exact h
      obtain ⟨X, hXmem, hante⟩ := List.mem_map.mp hm
      obtain ⟨hXΩ, hXi⟩ := List.mem_filter.mp hXmem
      match X, hXi with
      | .imp A B, _ =>
          have hA : A = f j := hante
          exact hA ▸ himp A B hXΩ
    obtain ⟨St, Th, k₁, k₂, k₃⟩ := hev
    exact ⟨(St, Th), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set St : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Th : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStTh : ∀ j, D (.irr (St j) (Th j) (f j)) := fun j => (hg j).1
  have hStΩ : ∀ j, St j ⊆ Ω := fun j => (hg j).2.1
  have hΩSt : ∀ j, Ω ⊆ St j ++ Th j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hStTh j))
  have hJ1 : ∀ i j, i ≠ j → St i ⊆ St j ++ Th j :=
    fun i j _ => fun {_} hX => hΩSt j (hStΩ i hX)
  have hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (St j)) → A ∈ upsilon f := by
    intro A B hmem
    obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
    exact (E.spec A).mpr (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨.imp A B, List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩))
  have hFn : F ∉ unionAll (fun j => atPart (St j)) := by
    intro hX
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    exact hFmem (hStΩ j (List.mem_filter.mp hj).1)
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg (joinCtxAtF St Th f F) F)
      ⟨.blocked, ⟨.joinAtF (fun j => d j) hJ1 hJ2 hFp hFn hFgoal (CtxEq.refl _)⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      refine ⟨Γ', hs'mem, fun X hX => .base (hΓ ?_)⟩
      rcases gHat_cases (hΩ X hX) with ⟨_, hpv⟩ | ⟨_, hi⟩ | ⟨_, hc⟩
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _
              (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hpv⟩⟩))))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_right _
              (mem_rm.mpr ⟨fun he => hFmem (he ▸ hX), ?_⟩))))
          exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hpv⟩)
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _
              (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hi⟩⟩)))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_left _ (List.mem_append_right _ ?_)
          match X, hi with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨?_, ?_⟩
              · exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, rfl⟩)
              · exact (E.spec A).mpr (List.mem_cons_of_mem _
                  (List.mem_map.mpr ⟨.imp A B,
                    List.mem_filter.mpr ⟨hX, rfl⟩, rfl⟩))
      · -- the `◯` case: `⋈^At_F` keeps the whole modal zone
        by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_right _ (List.mem_append_left _
            (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hc⟩⟩))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hc⟩)

/-! ## §8  Lemma 12 (source 4193) — the `∨` success lemma, modal case

The same swap, `⋈^∨ → ⋈^∨_F`.  The fallible `∨`-join also DROPS the
`RefAt` disjunct condition to plain membership in `Υ`, so the proof is
shorter than the `◯`-free one, not longer. -/

/-- **Lemma 12, modal case.** -/
theorem gbuSuccOrF {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {C₁ C₂ : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (hgoal : Form.or C₁ C₂ ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (h₁ : EvalI D Ω C₁) (h₂ : EvalI D Ω C₂) :
    EvalR D Ω (.or C₁ C₂) := by
  let U := C₁ :: C₂ :: (impPart Ω).map ante
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : EvalI D Ω (f j) := by
      by_cases e₁ : f j = C₁
      · exact e₁ ▸ h₁
      by_cases e₂ : f j = C₂
      · exact e₂ ▸ h₂
      have hm : f j ∈ (impPart Ω).map ante := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h e₁
        · rcases List.mem_cons.mp h with h' | h'
          · exact absurd h' e₂
          · exact h'
      obtain ⟨X, hXmem, hante⟩ := List.mem_map.mp hm
      obtain ⟨hXΩ, hXi⟩ := List.mem_filter.mp hXmem
      match X, hXi with
      | .imp A B, _ =>
          have hA : A = f j := hante
          exact hA ▸ himp A B hXΩ
    obtain ⟨St, Th, k₁, k₂, k₃⟩ := hev
    exact ⟨(St, Th), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set St : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Th : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStTh : ∀ j, D (.irr (St j) (Th j) (f j)) := fun j => (hg j).1
  have hStΩ : ∀ j, St j ⊆ Ω := fun j => (hg j).2.1
  have hΩSt : ∀ j, Ω ⊆ St j ++ Th j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hStTh j))
  have hJ1 : ∀ i j, i ≠ j → St i ⊆ St j ++ Th j :=
    fun i j _ => fun {_} hX => hΩSt j (hStΩ i hX)
  have hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (St j)) → A ∈ upsilon f := by
    intro A B hmem
    obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
    exact (E.spec A).mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨.imp A B, List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩)))
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg (joinCtxOrF St Th f) (.or C₁ C₂))
      ⟨.blocked, ⟨.joinOrF (fun j => d j) hJ1 hJ2
        ⟨(E.spec C₁).mpr List.mem_cons_self,
         (E.spec C₂).mpr (List.mem_cons_of_mem _ List.mem_cons_self)⟩
        hgoal (CtxEq.refl _)⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      refine ⟨Γ', hs'mem, fun X hX => .base (hΓ ?_)⟩
      rcases gHat_cases (hΩ X hX) with ⟨_, hpv⟩ | ⟨_, hi⟩ | ⟨_, hc⟩
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _
              (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hpv⟩⟩))))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_right _ ?_)))
          exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hpv⟩)
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _
              (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hi⟩⟩)))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_left _ (List.mem_append_right _ ?_)
          match X, hi with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨?_, ?_⟩
              · exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, rfl⟩)
              · exact (E.spec A).mpr (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨.imp A B,
                    List.mem_filter.mpr ⟨hX, rfl⟩, rfl⟩)))
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_right _ (List.mem_append_left _
            (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hc⟩⟩))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hc⟩)

/-! ## §9  Certificate: the counit, derived in FRJ◯

Seam 1's sharpest instance (`Y = F`), and the cell the closed ρ-corpus
cannot express — that corpus has no propositional variables, so its only
prime formula is `⊥`, where `Ω ⇒ ⊥` asks merely for an infallible root.
Built by hand rather than claimed by the search engine. -/

private def pv : Form := .atom "p"

/-- `◯p ⊃ p`, the counit: PLL-INVALID (two worlds `a ≤ b`, `Rm a b`,
`V(b) = {p}`), so a complete refutation calculus must derive it. -/
def counit : Form := .imp (.circ pv) pv

/-- `Ax^I` at the goal `p`: `∅ ; Ĝ∖{p} → p`; here `Ĝ∖{p} = {◯p}`. -/
def counitPrem : FRJVi counit []
    (rm (gAt counit) pv ++ gImp counit ++ gCirc counit) pv :=
  .axI pv rfl (by decide) (CtxEq.refl _)

/-- The FALLIBLE `⋈^At` over that single premise: it keeps the whole
modal zone, so `◯p` lands in the conclusion context — which is exactly
what seam 1 needs and what `⋈^At` and `⋈^At_P` cannot supply. -/
def counitJoin :
    FRJVr counit .blocked
      (joinCtxAtF (n := 0) (fun _ => [])
        (fun _ => rm (gAt counit) pv ++ gImp counit ++ gCirc counit)
        (fun _ => pv) pv) pv :=
  .joinAtF (fun _ => counitPrem)
    (fun _ _ _ => fun {_} h => absurd h List.not_mem_nil)
    (by
      intro A B h
      obtain ⟨j, hj⟩ := mem_unionAll.mp h
      exact absurd hj List.not_mem_nil)
    rfl
    (by
      intro h
      obtain ⟨j, hj⟩ := mem_unionAll.mp h
      exact absurd hj List.not_mem_nil)
    (by decide) (CtxEq.refl _)

theorem counit_clo :
    Clo (joinCtxAtF (n := 0) (fun _ => [])
      (fun _ => rm (gAt counit) pv ++ gImp counit ++ gCirc counit)
      (fun _ => pv) pv) (Form.circ pv) := .base (by decide)

/-- **The counit is derivable in FRJ◯.** -/
theorem provableV_counit : ProvableV counit :=
  ⟨.blocked, _, ⟨.impIn counitJoin counit_clo (by decide)⟩⟩

/-- The counit is PLL-invalid, so the derivation is not vacuous. -/
theorem not_pll_counit : ¬ PLL counit := soundnessV provableV_counit

/-! ## §10  The tag conflict, SETTLED

`gbuInv12`/`gbuInv13` were proved under `TagClean`.  The question is
whether `TagClean` can be arranged — by relaxing `◯∈`, say, the way
`RefAt` relaxed the barren joins.  It cannot, and the reason is
semantic, not bookkeeping.

`◯∈` and `◯∉` need the root's WHOLE MODAL CONE to refute `Z` (that is
what the tag pledges — `tag_cone`, `FRJ/SoundV.lean:1457`), because
`◯Z` fails at the root only if no `Rm`-successor of any world above it
forces `Z`.  A `blocked` row's extracted model has a FALLIBLE world in
that cone, and a fallible world forces everything; so its root forces
`◯W` for every `W` and cannot refute `◯Z`.  Excluding `blocked` is
therefore forced by soundness, and no relaxation of `◯∈` is available.

What the conflict shows instead is that the seam-2/3 rules were
mis-derived.  The two clauses below are refuted outright — no `TagClean`
hypothesis, no appeal to tags — by the counit's own join.  Take
`Ψ = {◯p}`, `Z = p`:

* `{◯p} ⇒ p` IS refutable — that is `counitJoin`;
* `{◯p} ⇒ ◯p` is NOT, and neither is `{◯p} → ◯p`, because `◯p ⊢ ◯p`
  and a valid sequent is refuted by no database.

So refuting `◯Z` at a root is STRICTLY STRONGER than refuting `Z`, and
`R◯`/`R◯ₙᵢ` with a REGULAR premise cannot be invertible. -/

/-- Refuting `◯Z` is refuted by validity of `◯Z` — the sharp form.  The
lemma in `wip/gbu_measure.lean` asks for validity of the BODY, which is
strictly stronger and unusable here (`◯p ⊨ p` is false).  Only two
`FRJVi` rules conclude `◯Z`: `Ax^I◯`, excluded by `classForce`; and
`◯∉`, whose regular premise can be lifted by `◯∈` — the tag condition
is available, since `◯∉` carries it — giving a row for `◯Z` whose model
root forces `Ω` and refutes `◯Z`. -/
theorem not_evalI_circ_of_valid' {G : Form} {D : FSeq → Prop}
    (hD : IsDatabase G D) {Ω : List Form} {Z : Form}
    (hgoal : Form.circ Z ∈ sfR G)
    (hval : ∀ (K : Kripke) (a : K.W), K.forces a Ω → K.force a (.circ Z))
    (hax : ∀ ats : List Form, classForce ats Z = false →
      ¬ (∀ X ∈ Ω, X ∈ vacZoneA G ats)) :
    ¬ EvalI D Ω (.circ Z) := by
  rintro ⟨St, Th, hmem, hSt, hΩ⟩
  obtain ⟨d⟩ := hD _ hmem
  cases d with
  | axI F hF _ _ => exact Bool.noConfusion hF
  | axIC F ats hats hFf hgoal' hTh =>
      refine hax ats hFf (fun X hX => ?_)
      have h := hΩ hX
      rw [List.nil_append] at h
      exact (hTh X).mp h
  | circNotIn d' htag hTh hgoal' =>
      obtain ⟨K, a, hf, hnf⟩ := frjv_countermodel (.circIn d' htag hgoal')
      refine hnf (hval K a (fun X hX => ?_))
      have h := hΩ hX
      rw [List.nil_append] at h
      exact clo_forces hf (hTh X h).1

/-! ### The cell

`Gtc = (◯p ⊃ p) ⊃ (◯p ⊃ p)` puts `◯p` in BOTH `Sf^L` and `Sf^R`, so the
context `Ω = {◯p}` is critical AND the two clauses' own side condition
`◯Z ∈ Sf^R(G)` is met.  Nothing else about `Gtc` matters. -/

def Gtc : Form := .imp (.imp (.circ pv) pv) (.imp (.circ pv) pv)

/-- `{◯p} ⇒ p` is refutable — straight from Lemma 11's modal case, with
an empty implication family. -/
theorem evalR_tc : EvalR (FDerivable Gtc) [Form.circ pv] pv :=
  gbuSuccAtF (saturated_fderivable Gtc) (by decide) rfl (by decide) (by decide)
    (by
      intro A B hAB
      rcases List.mem_cons.mp hAB with h | h
      · exact absurd h (fun he => Form.noConfusion he)
      · exact absurd h List.not_mem_nil)

/-- `{◯p} ⇒ ◯p` is NOT refutable: `◯p ⊢ ◯p`. -/
theorem not_evalR_tc : ¬ EvalR (FDerivable Gtc) [Form.circ pv] (.circ pv) :=
  not_evalR_of_valid (G := Gtc) (saturated_fderivable Gtc).1
    (fun _ _ hf => hf (Form.circ pv) List.mem_cons_self)

/-- `{◯p} → ◯p` is NOT refutable either. -/
theorem not_evalI_tc : ¬ EvalI (FDerivable Gtc) [Form.circ pv] (.circ pv) := by
  refine not_evalI_circ_of_valid' (G := Gtc) (saturated_fderivable Gtc).1
    (by decide) (fun _ _ hf => hf (Form.circ pv) List.mem_cons_self) ?_
  intro ats hz hsub
  have hmem := List.mem_filter.mp (hsub (Form.circ pv) List.mem_cons_self)
  have hcf : classForce ats pv = true := hmem.2
  rw [hz] at hcf
  exact Bool.noConfusion hcf

/-- **`R◯` with a REGULAR premise is NOT invertible.**  So Lemma 9's
clause 12 cannot hold unconditionally, and `TagClean` is not a
bookkeeping hypothesis that could be discharged by relaxing `◯∈`. -/
theorem rcirc_not_invertible :
    ¬ (∀ (G : Form) (D : FSeq → Prop), Saturated G D →
        ∀ (Ψ : List Form) (Z : Form), Form.circ Z ∈ sfR G →
          EvalR D Ψ Z → EvalR D Ψ (.circ Z)) := fun h =>
  not_evalR_tc (h Gtc (FDerivable Gtc) (saturated_fderivable Gtc)
    [Form.circ pv] pv (by decide) evalR_tc)

/-- **`R◯ₙᵢ` with a REGULAR premise is NOT invertible either**, by the
same cell. -/
theorem rcircNI_not_invertible :
    ¬ (∀ (G : Form) (D : FSeq → Prop), Saturated G D →
        ∀ (Ω : List Form) (Z : Form), Form.circ Z ∈ sfR G →
          (∀ X ∈ Ω, X ∈ gHat G) → EvalR D Ω Z → EvalI D Ω (.circ Z)) := fun h =>
  not_evalI_tc (h Gtc (FDerivable Gtc) (saturated_fderivable Gtc)
    [Form.circ pv] pv (by decide) (by decide) evalR_tc)

/-! ## §10a  Lemma 13 (P2) — the `◯` success lemma

`⋈^◯` carries `hZ : RefAt … Z` where `⋈^∨` carries `hC : … C₁ ∧ … C₂`.
So the `◯` goal is a one-disjunct disjunction: Lemma 12 with the family
`Z :: antecedents` instead of `C₁ :: C₂ :: antecedents`, and `⋈^◯` in
place of `⋈^∨`.

This is P2's licence.  At a critical `Ω ⇒g ◯Z`, if every member of
`Υ ∪ {Z}` is refuted then so is the sequent; so when `Ω →g Z` is NOT
refuted, `R◯` fires with THAT irregular premise.

Note the hypothesis `Ω ⊆ Ĝ_at ∪ Ĝ_imp`: unlike `⋈^At` and `⋈^∨`, the
`◯`-join has NO fallible variant, so the modal-zone case of this lemma
is not a free swap.  It needs `⋈^◯_P` and its `hJ5`, and is left open. -/

theorem gbuSuccCirc {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.circ Z ∈ sfR G)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (hz : EvalI D Ω Z) :
    EvalR D Ω (.circ Z) := by
  let U := Z :: (impPart Ω).map ante
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : EvalI D Ω (f j) := by
      by_cases e₀ : f j = Z
      · exact e₀ ▸ hz
      have hm : f j ∈ (impPart Ω).map ante := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h e₀
        · exact h
      obtain ⟨X, hXmem, hante⟩ := List.mem_map.mp hm
      obtain ⟨hXΩ, hXi⟩ := List.mem_filter.mp hXmem
      match X, hXi with
      | .imp A B, _ =>
          have hA : A = f j := hante
          exact hA ▸ himp A B hXΩ
    obtain ⟨St, Th, k₁, k₂, k₃⟩ := hev
    exact ⟨(St, Th), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set St : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Th : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStTh : ∀ j, D (.irr (St j) (Th j) (f j)) := fun j => (hg j).1
  have hStΩ : ∀ j, St j ⊆ Ω := fun j => (hg j).2.1
  have hΩSt : ∀ j, Ω ⊆ St j ++ Th j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hStTh j))
  have hJ1 : ∀ i j, i ≠ j → St i ⊆ St j ++ Th j :=
    fun i j _ => fun {_} hX => hΩSt j (hStΩ i hX)
  have hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (St j)) → A ∈ upsilon f := by
    intro A B hmem
    obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
    exact (E.spec A).mpr (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨.imp A B, List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩))
  have hcirc : unionAll (fun j => circPart (St j)) = [] := by
    refine eq_nil_of_forall_not_mem (fun X hX => ?_)
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    obtain ⟨hmem, hc⟩ := List.mem_filter.mp hj
    exact absurd hc (by
      rw [not_isCirc_of_gHatAtImp (hΩ X (hStΩ j hmem))]
      exact fun h => Bool.noConfusion h)
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg (joinCtxOrVBase St Th ++ restrict (thPool Th) (upsilon f))
      (.circ Z))
      ⟨.barren, ⟨.joinCirc (fun j => d j) hJ1 hJ2 hcirc (keptChainRestrict _ Th)
        (.ups ((E.spec Z).mpr List.mem_cons_self)) hgoal (CtxEq.refl _)⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      refine ⟨Γ', hs'mem, fun X hX => .base (hΓ ?_)⟩
      by_cases hin : ∃ j, X ∈ St j
      · obtain ⟨j, hj⟩ := hin
        refine List.mem_append_left _ ?_
        by_cases hi : X.isImp
        · exact List.mem_append_right _
            (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hi⟩⟩)
        · refine List.mem_append_left _ (List.mem_append_left _
            (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, ?_⟩⟩))
          have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
          exact (List.mem_filter.mp this).2
      · have hall : ∀ j, X ∈ Th j := by
          intro j
          rcases List.mem_append.mp (hΩSt j hX) with h' | h'
          · exact absurd ⟨j, h'⟩ hin
          · exact h'
        by_cases hi : X.isImp
        · refine List.mem_append_right _ ?_
          match X, hi with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨?_, ?_⟩
              · exact List.mem_filter.mpr ⟨mem_interAll.mpr hall, rfl⟩
              · exact (E.spec A).mpr (List.mem_cons_of_mem _
                  (List.mem_map.mpr ⟨.imp A B,
                    List.mem_filter.mpr ⟨hX, rfl⟩, rfl⟩))
        · refine List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ ?_))
          refine mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, ?_⟩)
          have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
          exact (List.mem_filter.mp this).2

/-! ## §10b  Lemma 13, the MODAL-zone case

`gbuSuccCirc` assumed `Ω ⊆ Ĝ_at ∪ Ĝ_imp`, because `⋈^◯` carries
`hcirc : ⋃ⱼ (Σⱼ)^◯ = []` and — unlike `⋈^At` and `⋈^∨` — has NO
FALLIBLE variant to fall back on.  There is a reason: a `⋈^◯` must make
its root REFUTE `◯Z`, i.e. its whole modal cone must refute `Z`, and a
fallible world in that cone forces `Z`.  So the modal zone has to go
through the PROMISE join `⋈^◯_P`, and its `hJ5` has to be discharged.

`hJ5` is the canonical model's accessibility clause from PLL's
completeness theorem,

    Rm Γ Δ   iff   { Y : ◯Y ∈ Γ } ⊆ Δ,

turned into a proof obligation: for each `◯Y` the context carries, some
premise world must REALISE `Y`.  So the extra hypothesis below is not
bookkeeping — it is exactly "the model has an `Rm`-successor". -/

/-- `Ω` has a promise world at `Z`: a derivation refuting `Z` from a
context `Δ` that covers `Ω` and realises every body of `Ω`'s modal zone,
with a tag `◯∈` can lift.  The last clause is `Rm Ω Δ`. -/
def PromiseWorld (G : Form) (Ω : List Form) (Z : Form) : Prop :=
  ∃ (Δ : List Form) (t : Tag), Nonempty (FRJVr G t Δ Z) ∧
    (t = .barren ∨ ∃ W, t = .chain W ∧ Covers Δ W Z) ∧
    (∀ X ∈ Ω, Clo Δ X) ∧ (∀ Y : Form, Form.circ Y ∈ Ω → Clo Δ Y)

/-- **Lemma 13, modal case.**  Same query set as `gbuSuccCirc` — the
antecedents of `Ω`'s implications, and `Z` — plus a promise world. -/
theorem gbuSuccCircP {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    {Ω : List Form} {Z : Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gHat G)
    (hgoal : Form.circ Z ∈ sfR G)
    (hpw : PromiseWorld G Ω Z)
    (himp : ∀ A B, Form.imp A B ∈ Ω → EvalI D Ω A)
    (hz : EvalI D Ω Z) :
    EvalR D Ω (.circ Z) := by
  obtain ⟨Δ, t, ⟨dΔ⟩, htag, hcov, hreal⟩ := hpw
  let U := Z :: (impPart Ω).map ante
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : EvalI D Ω (f j) := by
      by_cases e₀ : f j = Z
      · exact e₀ ▸ hz
      have hm : f j ∈ (impPart Ω).map ante := by
        rcases List.mem_cons.mp (hfmem j) with h | h
        · exact absurd h e₀
        · exact h
      obtain ⟨X, hXmem, hante⟩ := List.mem_map.mp hm
      obtain ⟨hXΩ, hXi⟩ := List.mem_filter.mp hXmem
      match X, hXi with
      | .imp A B, _ =>
          have hA : A = f j := hante
          exact hA ▸ himp A B hXΩ
    obtain ⟨St, Th, k₁, k₂, k₃⟩ := hev
    exact ⟨(St, Th), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set St : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Th : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStΩ : ∀ j, St j ⊆ Ω := fun j => (hg j).2.1
  have hΩSt : ∀ j, Ω ⊆ St j ++ Th j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hg j).1)
  have hJ1 : ∀ i j, i ≠ j → St i ⊆ St j ++ Th j :=
    fun i j _ => fun {_} hX => hΩSt j (hStΩ i hX)
  have hJ2 : ∀ A B : Form,
      Form.imp A B ∈ unionAll (fun j => impPart (St j)) → A ∈ upsilon f := by
    intro A B hmem
    obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
    exact (E.spec A).mpr (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨.imp A B, List.mem_filter.mpr ⟨hAB, rfl⟩, rfl⟩))
  have hJ5 : ∀ Y : Form,
      Form.circ Y ∈ unionAll (fun j => circPart (St j)) →
      ∃ _i : Fin 1, Clo Δ Y := by
    intro Y hY
    obtain ⟨j, hj⟩ := mem_unionAll.mp hY
    exact ⟨0, hreal Y (hStΩ j (List.mem_filter.mp hj).1)⟩
  have hJ7s : ∀ _i : Fin 1, ∀ j, ∀ X ∈ St j, Clo Δ X :=
    fun _ j X hX => hcov X (hStΩ j hX)
  obtain ⟨s', hs'mem, hsub⟩ :=
    hsat.2 (.reg (joinCtxOrP St Th f (fun _ : Fin 1 => Δ)) (.circ Z))
      ⟨.chain Z, ⟨.joinCircP (fun j => d j) (fun _ => dΔ) hJ1 hJ2 hJ5 hJ7s
        (fun _ => ⟨rfl, htag⟩) ((E.spec Z).mpr List.mem_cons_self) hgoal
        (CtxEq.refl _)⟩⟩
  match s', hsub with
  | .reg Γ' _, ⟨rfl, hΓ⟩ =>
      refine ⟨Γ', hs'mem, fun X hX => .base (hΓ ?_)⟩
      refine mem_restrictP.mpr ⟨?_, fun _ => hcov X hX⟩
      rcases gHat_cases (hΩ X hX) with ⟨_, hpv⟩ | ⟨_, hi⟩ | ⟨_, hc⟩
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_left _
              (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hpv⟩⟩))))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_append_right _ ?_)))
          exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hpv⟩)
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _
              (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hi⟩⟩)))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_left _ (List.mem_append_right _ ?_)
          match X, hi with
          | .imp A B, _ =>
              refine mem_restrict.mpr ⟨?_, ?_⟩
              · exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, rfl⟩)
              · exact (E.spec A).mpr (List.mem_cons_of_mem _
                  (List.mem_map.mpr ⟨.imp A B,
                    List.mem_filter.mpr ⟨hX, rfl⟩, rfl⟩))
      · by_cases hin : ∃ j, X ∈ St j
        · obtain ⟨j, hj⟩ := hin
          exact List.mem_append_right _ (List.mem_append_left _
            (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hj, hc⟩⟩))
        · have hall : ∀ j, X ∈ Th j := by
            intro j
            rcases List.mem_append.mp (hΩSt j hX) with h' | h'
            · exact absurd ⟨j, h'⟩ hin
            · exact h'
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          match X, hc with
          | .circ Y, _ =>
              refine mem_restrictC.mpr ⟨?_, ⟨0, hreal Y hX⟩⟩
              exact mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, rfl⟩)

/-! ## §11  The open question of `docs/gbu-tag-proposal.md` §5, ANSWERED

The question was whether `Ω →g ◯Z` — the IRREGULAR `◯` goal — is always
discharged when reached, in which case seam 3 evaporates and `R◯ₙᵢ` is
unnecessary.  **It is not.**  Worse, `R◯ₙᵢ` alone is INCOMPLETE there.

Take

    Ω = { p ,  p ⊃ ◯q },    Z = q,
    G = p ⊃ ((p ⊃ ◯q) ⊃ (r ∨ ◯q))

so `Ω ⊆ Ĝ` and `◯q ∈ Sf^R(G)` and `◯q ∉ Ω`.  Then

* `Ω ⊨ ◯q` — by the unit and modus ponens — so `Ω →g ◯q` is refutable by
  NO database (`not_evalI_omegaNI`): it satisfies (BSr1), it is not an
  axiom, and `Ω` has no top-level `◯`, so `L◯` cannot apply either.
  Backward search therefore DOES arrive at it, by `R∨₂` from the
  critical `Ω ⇒g r ∨ ◯q`.
* But `Ω ⊭ q`: two worlds `a ≤ b`, `Rm = ≤`, `p` everywhere and `q` only
  at `b`.  So `Ω ⇒g q` — the ONLY premise `R◯ₙᵢ` offers — is not
  derivable in `Gbu◯` at all, by soundness (`not_gbuR_omegaNI`).

Both horns of the question are therefore closed: `R◯ₙᵢ` is needed, and
it does not suffice.  What `Ω ⊢ ◯q` actually uses is modus ponens on
`p ⊃ ◯q`, i.e. `L⊃` — a LEFT rule, which the irregular judgment
forbids.  So the irregular `◯` goal is a genuine third critical case in
its own right, and its rule set has to include a left rule.  That is a
design question for review, not something to settle here. -/

private def qv : Form := .atom "q"
private def rv : Form := .atom "r"

/-- `Ω = {p, p ⊃ ◯q}`. -/
def omegaNI : List Form := [pv, .imp pv (.circ qv)]

/-- `G = p ⊃ ((p ⊃ ◯q) ⊃ (r ∨ ◯q))` — valid, and it makes `Ω` a
legitimate critical context with `◯q ∈ Sf^R(G)`. -/
def Gni : Form := .imp pv (.imp (.imp pv (.circ qv)) (.or rv (.circ qv)))

theorem omegaNI_critical : ∀ X ∈ omegaNI, X ∈ gHat Gni := by decide

theorem circq_goal : Form.circ qv ∈ sfR Gni := by decide

theorem circq_not_mem : Form.circ qv ∉ omegaNI := by decide

/-- `Ω ⊨ ◯q`: modus ponens, then the unit. -/
theorem omegaNI_valid {K : Kripke} {a : K.W} (h : K.forces a omegaNI) :
    K.force a (.circ qv) :=
  h (.imp pv (.circ qv)) (List.mem_cons_of_mem _ List.mem_cons_self)
    a (K.le_refl a) (h pv List.mem_cons_self)

/-- Hence `Ω →g ◯q` is refuted by NO database: (BSr1) holds at it. -/
theorem not_evalI_omegaNI :
    ¬ EvalI (FDerivable Gni) omegaNI (.circ qv) := by
  refine not_evalI_circ_of_valid' (G := Gni) (saturated_fderivable Gni).1
    circq_goal (fun _ _ h => omegaNI_valid h) ?_
  intro ats hz hsub
  have hmem := List.mem_filter.mp
    (hsub (.imp pv (.circ qv)) (List.mem_cons_of_mem _ List.mem_cons_self))
  have hp := List.mem_filter.mp (hsub pv List.mem_cons_self)
  have hcf : (!classForce ats pv || classForce ats qv) = true := hmem.2
  rw [show classForce ats pv = true from hp.2, hz] at hcf
  exact Bool.noConfusion hcf

/-! ### `Ω ⊭ q`: the countermodel

The same two worlds as `Kmc`, with `p` true everywhere and `q` true only
above. -/

private def V2 : W2 → String → Prop := fun w s => s = "p" ∨ w = W2.wb

private theorem v2_mono' : ∀ {a b : W2}, le2 a b → ∀ s, V2 a s → V2 b s
  | .wa, .wa, _, _, h => h
  | .wa, .wb, _, _, _ => Or.inr rfl
  | .wb, .wa, h, _, _ => h.elim
  | .wb, .wb, _, _, h => h

def Kni : Kripke where
  W := W2
  elems := [.wa, .wb]
  complete := fun w => by
    cases w
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  decEq := inferInstance
  le := le2
  le_refl := le2_refl
  le_trans := le2_trans
  le_antisymm := le2_antisymm
  root := .wa
  root_le := fun _ => trivial
  V := V2
  V_mono := v2_mono'
  Rm := le2
  rm_refl := le2_refl
  rm_trans := le2_trans
  sub_mi := fun h => h
  Fal := fun _ => False
  fal_mono := fun _ h => h.elim
  fal_V := fun h _ => h.elim
  decLe := decLe2
  decV := fun a s =>
    inferInstanceAs (Decidable (s = "p" ∨ a = W2.wb))
  decRm := decLe2
  decFal := fun _ => isFalse (fun h => h)

theorem Kni_force_circ_q (w : W2) : Kni.force w (.circ qv) := by
  intro b _
  refine ⟨W2.wb, le2_wb b, ?_⟩
  show V2 W2.wb "q"
  exact Or.inr rfl

theorem Kni_forces_omegaNI : Kni.forces W2.wa omegaNI := by
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX'
  · show V2 W2.wa "p"
    exact Or.inl rfl
  · rcases List.mem_cons.mp hX' with rfl | hX''
    · exact fun c _ _ => Kni_force_circ_q c
    · exact absurd hX'' List.not_mem_nil

theorem Kni_not_force_q : ¬ Kni.force W2.wa qv := by
  intro h
  rcases (h : V2 W2.wa "q") with h' | h'
  · exact absurd h' (by decide)
  · exact W2.noConfusion h'

/-- **`R◯ₙᵢ`'s only premise is not derivable**, while its conclusion must
be.  So the rule is incomplete at the irregular `◯` goal. -/
theorem not_gbuR_omegaNI (G : Form) : ¬ Nonempty (GbuR G omegaNI qv) := by
  rintro ⟨d⟩
  exact Kni_not_force_q (soundR (K := Kni) d W2.wa Kni_forces_omegaNI)

/-! ## §11a  Conservativity: the `◯` rules cannot touch the IPC calculus

A fair worry about admitting `L◯` — and, at the irregular `◯` goal,
`L⊃` — is that it alters the `◯`-FREE calculus, i.e. the paper's own.
It does not, and the reason is the blanket condition on the sequent
language rather than anything about the rules: every sequent of
`Gbu(G)` satisfies `Lhs(τ) ⊆ Sf^L(G)` and `Rhs(τ) ∈ Sf^R(G)`, and if
`G` is `◯`-free then NO signed subformula of `G` is a `◯`-formula
(`mem_sf_noCirc`, `FRJ/Erase.lean`).  Hence for `◯`-free `G`:

* no sequent has a `◯`-shaped goal, so `R◯`, `R◯ₙᵢ` and the proposed
  `◯`-goal-restricted `L⊃` are all INAPPLICABLE;
* no sequent has a `◯` in the left zone, so `L◯` is inapplicable.

So `Gbu◯(G)` and `Gbu(G)` coincide as RULE SETS, not merely in what they
prove, and the results of §§1–12 of `wip/gbu_search.lean` are untouched.
The two `◯`-freeness hypotheses of Theorem 8 become automatic. -/

theorem noCirc_sfR {G : Form} (hG : noCirc G = true) :
    ∀ X ∈ sfR G, X.isCirc = false :=
  fun X hX => mem_sf_noCirc G hG X (Or.inl hX)

theorem noCirc_sfL {G : Form} (hG : noCirc G = true) :
    ∀ X ∈ sfL G, X.isCirc = false :=
  fun X hX => mem_sf_noCirc G hG X (Or.inr (Or.inl hX))

/-- **Theorem 8 for a `◯`-free goal, with no modal hypotheses at all.**
This is the paper's own statement recovered: nothing about `◯` is
assumed, because for such a `G` there is nothing about `◯` to assume. -/
theorem search_of_noCirc {G : Form} {D : FSeq → Prop} (hsat : Saturated G D)
    (decI : ∀ Ω C, Decidable (EvalI D Ω C)) (hG : noCirc G = true) :
    ∀ p : Bool × List Form × Form, SearchOk G D p :=
  search hsat decI (noCirc_sfL hG) (noCirc_sfR hG)

/-- info: 'FRJ.Gbu.search_of_noCirc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms search_of_noCirc

/-! ## §11b  The calculus `Gbu◯(G)`

Matthew's decision (2026-08-30): admit the left rule in the irregular
judgment, conservativity being proved — and RE-CHECK conservativity
whenever the rules change.  The re-check is `deCircR`/`deCircI` below: a
total translation of `Gbu◯(G)` into `Gbu(G)` for `◯`-free `G`.  Add a
rule that can fire on `◯`-free input and that translation stops
compiling.  It is the gate, not a remark.

Six new constructors, all carrying the blanket sequent-language
condition on their `◯`-formula (**divergence D9**: `Gbu(G)`'s own
constructors do not carry it — see D2 — but the new ones must, since
that condition is exactly what makes them inapplicable on a `◯`-free
goal, and so what makes the gate mechanical).

    Ψ, Z ⇒g ◯C            Ψ, Z →g ◯C           Ω →g A     Ω_B →g ◯C
    ───────────── L◯      ───────────── L◯ᵢ    ───────────────────── L⊃ᵢ
    Ψ, ◯Z ⇒g ◯C           Ψ, ◯Z →g ◯C                Ω →g ◯C

    Ω →g Z                Ω →g Z
    ──────── R◯           ────────── R◯ᵢ
    Ω ⇒g ◯Z               Ω →g ◯Z

`L⊃ᵢ` carries `|A| < |◯C|`, and `R◯ᵢ`'s premise is IRREGULAR: those two
choices are what make the PAPER's weight `⟨unclosed, tp, |τ|⟩` decrease
on every step (`wg_stepO`), with no store.  The store-carrying `Wg◯` of
`wip/gbu_measure.lean` — and `no_measure_stepC`, which forced it —
remain as the record of why `R◯ₙᵢ` was abandoned.

`L◯`'s goal must be `◯`-shaped (`lcirc_goal_must_be_circ`); `L⊃ᵢ` is
admitted only at a `◯`-shaped goal, which is what confines it to the
modal fragment. -/

mutual

/-- Regular sequents `Ψ ⇒g A` of `Gbu◯(G)`. -/
inductive GbuRC (G : Form) : List Form → Form → Type
  | ax {Γ Ψ : List Form} (A : Form) (hΓ : Γ ≐ A :: Ψ) : GbuRC G Γ A
  | lbot {Γ Ψ : List Form} (C : Form) (hΓ : Γ ≐ .bot :: Ψ) : GbuRC G Γ C
  | landL {Γ Ψ : List Form} {A B C : Form}
      (d : GbuRC G (A :: B :: Ψ) C) (hΓ : Γ ≐ .and A B :: Ψ) : GbuRC G Γ C
  | randR {Γ : List Form} {A B : Form}
      (d₁ : GbuRC G Γ A) (d₂ : GbuRC G Γ B) : GbuRC G Γ (.and A B)
  | lorL {Γ Ψ : List Form} {A B C : Form}
      (d₁ : GbuRC G (A :: Ψ) C) (d₂ : GbuRC G (B :: Ψ) C)
      (hΓ : Γ ≐ .or A B :: Ψ) : GbuRC G Γ C
  | rorR1 {Γ : List Form} {C₁ C₂ : Form}
      (d : GbuIC G Γ C₁) : GbuRC G Γ (.or C₁ C₂)
  | rorR2 {Γ : List Form} {C₁ C₂ : Form}
      (d : GbuIC G Γ C₂) : GbuRC G Γ (.or C₁ C₂)
  | limpL {Γ Ψ : List Form} {A B C : Form}
      (d₁ : GbuIC G (.imp A B :: Ψ) A) (d₂ : GbuRC G (B :: Ψ) C)
      (hΓ : Γ ≐ .imp A B :: Ψ) : GbuRC G Γ C
  | rimpI {Γ : List Form} {A B : Form}
      (d : GbuRC G Γ B) (hA : Clo Γ A) : GbuRC G Γ (.imp A B)
  | rimpNI {Γ : List Form} {A B : Form}
      (d : GbuRC G (A :: Γ) B) (hA : ¬ Clo Γ A) : GbuRC G Γ (.imp A B)
  /-- `L◯`, seam 1.  The goal must be `◯`-shaped. -/
  | lcirc {Γ Ψ : List Form} {Z C : Form}
      (d : GbuRC G (Z :: Ψ) (.circ C)) (hprin : Form.circ Z ∈ sfL G)
      (hΓ : Γ ≐ .circ Z :: Ψ) : GbuRC G Γ (.circ C)
  /-- `R◯`, seam 2, with the IRREGULAR premise that `⋈^◯`'s `hZ`
  dictates (P2). -/
  | rcirc {Γ : List Form} {Z : Form}
      (d : GbuIC G Γ Z) (hgoal : Form.circ Z ∈ sfR G) : GbuRC G Γ (.circ Z)

/-- Irregular sequents `Ψ →g A` of `Gbu◯(G)`. -/
inductive GbuIC (G : Form) : List Form → Form → Type
  | ax {Γ Ψ : List Form} (A : Form) (hΓ : Γ ≐ A :: Ψ) : GbuIC G Γ A
  | randI {Γ : List Form} {A B : Form}
      (d₁ : GbuIC G Γ A) (d₂ : GbuIC G Γ B) : GbuIC G Γ (.and A B)
  | rorI1 {Γ : List Form} {C₁ C₂ : Form}
      (d : GbuIC G Γ C₁) : GbuIC G Γ (.or C₁ C₂)
  | rorI2 {Γ : List Form} {C₁ C₂ : Form}
      (d : GbuIC G Γ C₂) : GbuIC G Γ (.or C₁ C₂)
  | rimpII {Γ : List Form} {A B : Form}
      (d : GbuIC G Γ B) (hA : Clo Γ A) : GbuIC G Γ (.imp A B)
  | rimpNII {Γ : List Form} {A B : Form}
      (d : GbuRC G (A :: Γ) B) (hA : ¬ Clo Γ A) : GbuIC G Γ (.imp A B)
  /-- `L◯` in the irregular judgment. -/
  | lcircI {Γ Ψ : List Form} {Z C : Form}
      (d : GbuIC G (Z :: Ψ) (.circ C)) (hprin : Form.circ Z ∈ sfL G)
      (hΓ : Γ ≐ .circ Z :: Ψ) : GbuIC G Γ (.circ C)
  /-- `L⊃` in the irregular judgment, at a `◯`-shaped goal ONLY.  This is
  the departure from the paper's frozen-context discipline, forced by
  `not_gbuR_omegaNI`: `Ω ⊢ ◯q` can use modus ponens on an implication of
  `Ω`, and no `◯` rule can substitute for it. -/
  | limpLI {Γ Ψ : List Form} {A B C : Form}
      (d₁ : GbuIC G (.imp A B :: Ψ) A) (d₂ : GbuIC G (B :: Ψ) (.circ C))
      (hsz : A.size < (Form.circ C).size)
      (hgoal : Form.circ C ∈ sfR G) (hΓ : Γ ≐ .imp A B :: Ψ) :
      GbuIC G Γ (.circ C)
  /-- `R◯ᵢ`, seam 3.  The premise is IRREGULAR — focus is NOT released.
  `◯∉`'s premise is regular, which is what made `R◯ₙᵢ` the first
  candidate; but `rcircNI_not_invertible` refutes its licence and
  `not_gbuR_omegaNI` its completeness, and with `L⊃ᵢ` admitted the work
  `R◯ₙᵢ` was doing is done by modus ponens instead.  Keeping the premise
  irregular is what restores the PAPER's weight (`wg_stepO`). -/
  | rcircI {Γ : List Form} {Z : Form}
      (d : GbuIC G Γ Z) (hgoal : Form.circ Z ∈ sfR G) : GbuIC G Γ (.circ Z)

end

/-- `⊢_Gbu◯(G) G`. -/
def ProvableGbuC (G : Form) : Prop := Nonempty (GbuRC G [] G)

/-! ### Lemma 7 for `Gbu◯(G)` -/

mutual

theorem soundRC {G : Form} {K : Kripke} :
    ∀ {Ψ : List Form} {C : Form}, GbuRC G Ψ C →
      ∀ w : K.W, K.forces w Ψ → K.force w C
  | _, _, .ax A hΓ, _, h => (forces_ctxEq hΓ h) A List.mem_cons_self
  | _, _, .lbot C hΓ, _, h =>
      K.fal_force C ((forces_ctxEq hΓ h) .bot List.mem_cons_self)
  | _, _, .landL d hΓ, w, h => by
      have h' := forces_ctxEq hΓ h
      have hab := h' _ List.mem_cons_self
      refine soundRC d w (fun X hX => ?_)
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact hab.1
      rcases List.mem_cons.mp hX' with rfl | hX''
      · exact hab.2
      · exact h' X (List.mem_cons_of_mem _ hX'')
  | _, _, .randR d₁ d₂, w, h => ⟨soundRC d₁ w h, soundRC d₂ w h⟩
  | _, _, .lorL d₁ d₂ hΓ, w, h => by
      have h' := forces_ctxEq hΓ h
      have hor := h' _ List.mem_cons_self
      have tail : ∀ X ∈ _, K.force w X := fun X hX =>
        h' X (List.mem_cons_of_mem _ hX)
      rcases hor with hA | hB
      · exact soundRC d₁ w (fun X hX => by
          rcases List.mem_cons.mp hX with rfl | hX'
          · exact hA
          · exact tail X hX')
      · exact soundRC d₂ w (fun X hX => by
          rcases List.mem_cons.mp hX with rfl | hX'
          · exact hB
          · exact tail X hX')
  | _, _, .rorR1 d, w, h => Or.inl (soundIC d w h)
  | _, _, .rorR2 d, w, h => Or.inr (soundIC d w h)
  | _, _, .limpL d₁ d₂ hΓ, w, h => by
      have h' := forces_ctxEq hΓ h
      have himp := h' _ List.mem_cons_self
      have hA := soundIC d₁ w h'
      have hB := himp w (K.le_refl w) hA
      refine soundRC d₂ w (fun X hX => ?_)
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact hB
      · exact h' X (List.mem_cons_of_mem _ hX')
  | _, _, .rimpI d _, w, h => fun v hwv _ =>
      soundRC d v (K.forces_mono hwv h)
  | _, _, .rimpNI d _, w, h => fun v hwv hA =>
      soundRC d v (fun X hX => by
        rcases List.mem_cons.mp hX with rfl | hX'
        · exact hA
        · exact K.force_mono hwv (h X hX'))
  | _, _, .lcirc d _ hΓ, w, h =>
      sound_lcirc (fun v hv => soundRC d v hv) w (forces_ctxEq hΓ h)
  | _, _, .rcirc d _, w, h =>
      sound_rcirc (fun v hv => soundIC d v hv) w h

theorem soundIC {G : Form} {K : Kripke} :
    ∀ {Ψ : List Form} {C : Form}, GbuIC G Ψ C →
      ∀ w : K.W, K.forces w Ψ → K.force w C
  | _, _, .ax A hΓ, _, h => (forces_ctxEq hΓ h) A List.mem_cons_self
  | _, _, .randI d₁ d₂, w, h => ⟨soundIC d₁ w h, soundIC d₂ w h⟩
  | _, _, .rorI1 d, w, h => Or.inl (soundIC d w h)
  | _, _, .rorI2 d, w, h => Or.inr (soundIC d w h)
  | _, _, .rimpII d _, w, h => fun v hwv _ =>
      soundIC d v (K.forces_mono hwv h)
  | _, _, .rimpNII d _, w, h => fun v hwv hA =>
      soundRC d v (fun X hX => by
        rcases List.mem_cons.mp hX with rfl | hX'
        · exact hA
        · exact K.force_mono hwv (h X hX'))
  | _, _, .lcircI d _ hΓ, w, h =>
      sound_lcirc (fun v hv => soundIC d v hv) w (forces_ctxEq hΓ h)
  | _, _, .limpLI d₁ d₂ _ _ hΓ, w, h => by
      have h' := forces_ctxEq hΓ h
      have himp := h' _ List.mem_cons_self
      have hA := soundIC d₁ w h'
      have hB := himp w (K.le_refl w) hA
      refine soundIC d₂ w (fun X hX => ?_)
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact hB
      · exact h' X (List.mem_cons_of_mem _ hX')
  | _, _, .rcircI d _, w, h =>
      sound_rcirc (fun v hv => soundIC d v hv) w h

end

/-- **Theorem 6 for `Gbu◯(G)`.** -/
theorem pll_of_provableGbuC {G : Form} (h : ProvableGbuC G) : PLL G := by
  obtain ⟨d⟩ := h
  intro K
  exact soundRC d K.root (fun _ hX => absurd hX List.not_mem_nil)

/-! ### THE CONSERVATIVITY GATE

A total translation `Gbu◯(G) → Gbu(G)` for `◯`-free `G`.  Every new
constructor is discharged by its own sequent-language side condition,
which `noCirc_sfL`/`noCirc_sfR` make contradictory.  **If a rule is ever
added that can fire on a `◯`-free goal, this stops compiling.** -/

mutual

def deCircR {G : Form} (hG : noCirc G = true) :
    ∀ {Γ : List Form} {C : Form}, GbuRC G Γ C → GbuR G Γ C
  | _, _, .ax A hΓ => .ax A hΓ
  | _, _, .lbot C hΓ => .lbot C hΓ
  | _, _, .landL d hΓ => .landL (deCircR hG d) hΓ
  | _, _, .randR d₁ d₂ => .randR (deCircR hG d₁) (deCircR hG d₂)
  | _, _, .lorL d₁ d₂ hΓ => .lorL (deCircR hG d₁) (deCircR hG d₂) hΓ
  | _, _, .rorR1 d => .rorR1 (deCircI hG d)
  | _, _, .rorR2 d => .rorR2 (deCircI hG d)
  | _, _, .limpL d₁ d₂ hΓ => .limpL (deCircI hG d₁) (deCircR hG d₂) hΓ
  | _, _, .rimpI d hA => .rimpI (deCircR hG d) hA
  | _, _, .rimpNI d hA => .rimpNI (deCircR hG d) hA
  | _, _, .lcirc _ hprin _ => absurd (noCirc_sfL hG _ hprin) (by simp [Form.isCirc])
  | _, _, .rcirc _ hgoal => absurd (noCirc_sfR hG _ hgoal) (by simp [Form.isCirc])

def deCircI {G : Form} (hG : noCirc G = true) :
    ∀ {Γ : List Form} {C : Form}, GbuIC G Γ C → GbuI G Γ C
  | _, _, .ax A hΓ => .ax A hΓ
  | _, _, .randI d₁ d₂ => .randI (deCircI hG d₁) (deCircI hG d₂)
  | _, _, .rorI1 d => .rorI1 (deCircI hG d)
  | _, _, .rorI2 d => .rorI2 (deCircI hG d)
  | _, _, .rimpII d hA => .rimpII (deCircI hG d) hA
  | _, _, .rimpNII d hA => .rimpNII (deCircR hG d) hA
  | _, _, .lcircI _ hprin _ => absurd (noCirc_sfL hG _ hprin) (by simp [Form.isCirc])
  | _, _, .limpLI _ _ _ hgoal _ => absurd (noCirc_sfR hG _ hgoal) (by simp [Form.isCirc])
  | _, _, .rcircI _ hgoal => absurd (noCirc_sfR hG _ hgoal) (by simp [Form.isCirc])

end

mutual

/-- The other direction: `Gbu(G)` embeds in `Gbu◯(G)`, always. -/
def ofGbuR {G : Form} : ∀ {Γ : List Form} {C : Form}, GbuR G Γ C → GbuRC G Γ C
  | _, _, .ax A hΓ => .ax A hΓ
  | _, _, .lbot C hΓ => .lbot C hΓ
  | _, _, .landL d hΓ => .landL (ofGbuR d) hΓ
  | _, _, .randR d₁ d₂ => .randR (ofGbuR d₁) (ofGbuR d₂)
  | _, _, .lorL d₁ d₂ hΓ => .lorL (ofGbuR d₁) (ofGbuR d₂) hΓ
  | _, _, .rorR1 d => .rorR1 (ofGbuI d)
  | _, _, .rorR2 d => .rorR2 (ofGbuI d)
  | _, _, .limpL d₁ d₂ hΓ => .limpL (ofGbuI d₁) (ofGbuR d₂) hΓ
  | _, _, .rimpI d hA => .rimpI (ofGbuR d) hA
  | _, _, .rimpNI d hA => .rimpNI (ofGbuR d) hA

def ofGbuI {G : Form} : ∀ {Γ : List Form} {C : Form}, GbuI G Γ C → GbuIC G Γ C
  | _, _, .ax A hΓ => .ax A hΓ
  | _, _, .randI d₁ d₂ => .randI (ofGbuI d₁) (ofGbuI d₂)
  | _, _, .rorI1 d => .rorI1 (ofGbuI d)
  | _, _, .rorI2 d => .rorI2 (ofGbuI d)
  | _, _, .rimpII d hA => .rimpII (ofGbuI d) hA
  | _, _, .rimpNII d hA => .rimpNII (ofGbuR d) hA

end

/-- **Conservativity, both directions.**  On a `◯`-free goal the two
calculi prove exactly the same sequents. -/
theorem provableGbuC_iff_provableGbu {G : Form} (hG : noCirc G = true) :
    ProvableGbuC G ↔ ProvableGbu G :=
  ⟨fun ⟨d⟩ => ⟨deCircR hG d⟩, fun ⟨d⟩ => ⟨ofGbuR d⟩⟩

/-! ### Stage-2 gate: no computed index in any constructor's return type -/

#slime FRJ.Gbu.GbuRC FRJ.Gbu.GbuIC

/-- info: 'FRJ.Gbu.provableGbuC_iff_provableGbu' depends on axioms: [propext] -/
#guard_msgs in
#print axioms provableGbuC_iff_provableGbu

/-- info: 'FRJ.Gbu.pll_of_provableGbuC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pll_of_provableGbuC

/-! ## §11c  Termination for `Gbu◯(G)` — and what it costs

Theorem 8◯ is a well-founded recursion, so the measure decides whether
it can be written at all.  Two facts, and they point in opposite
directions.

**With `R◯ₙᵢ` (regular premise) the paper's weight is unusable** — that
is `no_measure_stepC` and `cyc_notRefuted` in `wip/gbu_measure.lean`:
the step relation has a two-cycle both of whose nodes satisfy (BSr1), so
no measure on sequents works, and the store-carrying `Wg◯` is forced.

**But the store cannot carry the recursion.**  The spec would have to
say what a banked implication buys, and the only useful reading is
`∀ A⊃B ∈ U, Nonempty (GbuIC G Ψ A)` — the left premise is already
built.  At the `L⊃` step with `A⊃B ∉ U` the recursion banks it and
recurses for exactly that left premise, so discharging the store
hypothesis of the recursive call requires the derivation being built.
Circular.  Banking after the fact does not drop `|Ψ^⊃ ∖ U|`, so the
measure fails instead.

**The way out is a rule change, and it restores the PAPER's own
measure.**  Replace `R◯ₙᵢ` (regular premise) by

    Ω →g Z
    ────────  R◯ᵢ
    Ω →g ◯Z

— sound by `sound_rcirc`, which is already judgment-generic — and
restrict `L⊃ᵢ` to implications whose antecedent is smaller than the
goal.  Then `Wg = ⟨ |Sf^L(G) ∖ Cl(Ψ)| , tp(τ) , |τ| ⟩` decreases on
every step, with no store: `wg_stepO` and `stepO_wf` below.

The restriction is exactly what kills the cycle.  On
`Γ = ◯z ⊃ ⊥, p, p ⊃ z` the looping step was `L⊃` on `◯z ⊃ ⊥` at goal
`◯z`, and `|◯z| < |◯z|` fails, so it is blocked; `L⊃ᵢ` on `p ⊃ z` is
still available (`|p| = 1 < 2 = |◯z|`) and the cell goes through.  The
two motivating cells survive too: `{p, p⊃◯q} →g ◯q` by `L⊃ᵢ` on
`p ⊃ ◯q` (`|p| < |◯q|`), and `{p} →g ◯p` by `R◯ᵢ`.

This is a change to two rules, so it is PROPOSED, not adopted.  What
follows is the evidence for it. -/

/-- The redesigned step relation: `Step` plus the `◯` steps, with
`R◯ᵢ` in place of `R◯ₙᵢ` and `L⊃ᵢ` size-restricted. -/
inductive StepO (G : Form) : (Bool × List Form × Form) →
    (Bool × List Form × Form) → Prop
  | old {p q} (h : Step G p q) : StepO G p q
  | lcirc {Ψ Z C} :
      StepO G (true, Z :: Ψ, .circ C) (true, .circ Z :: Ψ, .circ C)
  | lcircI {Ψ Z C} :
      StepO G (false, Z :: Ψ, .circ C) (false, .circ Z :: Ψ, .circ C)
  | limpLI1 {Ψ A B C} (hsz : A.size < (Form.circ C).size) :
      StepO G (false, .imp A B :: Ψ, A) (false, .imp A B :: Ψ, .circ C)
  | limpLI2 {Ψ A B C} :
      StepO G (false, B :: Ψ, .circ C) (false, .imp A B :: Ψ, .circ C)
  | rcirc {Ψ Z} : StepO G (false, Ψ, Z) (true, Ψ, .circ Z)
  | rcircI {Ψ Z} : StepO G (false, Ψ, Z) (false, Ψ, .circ Z)

private theorem sqCons {Ψ : List Form} {X C : Form} :
    seqSize (X :: Ψ) C = X.size + seqSize Ψ C := by
  show ((X :: Ψ).map Form.size).sum + C.size
      = X.size + (((Ψ.map Form.size).sum) + C.size)
  rw [List.map_cons, List.sum_cons, Nat.add_assoc]

private theorem sqGoal {Ψ : List Form} {C C' : Form} (h : C'.size < C.size) :
    seqSize Ψ C' < seqSize Ψ C := Nat.add_lt_add_left h _

private theorem wgOCtx {G : Form} {r : Bool} {Ψ Ψ' : List Form} {C C' : Form}
    (hcl : ∀ X ∈ Ψ, Clo Ψ' X) (hs : seqSize Ψ' C' < seqSize Ψ C) :
    WgLt (wg G r Ψ' C') (wg G r Ψ C) := by
  have hmono : unclosed G Ψ' ≤ unclosed G Ψ :=
    unclosed_mono (fun _ hX => clo_trans hcl hX)
  rcases Nat.lt_or_ge (unclosed G Ψ') (unclosed G Ψ) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨Nat.le_antisymm hmono h, Or.inr ⟨rfl, hs⟩⟩

private theorem wgOFocus {G : Form} {Ψ : List Form} {C C' : Form} :
    WgLt (wg G false Ψ C') (wg G true Ψ C) :=
  Or.inr ⟨rfl, Or.inl Nat.zero_lt_one⟩

/-- **Lemma 8 for the redesigned `Gbu◯(G)`**: the PAPER's weight, with no
store, decreases on every step. -/
theorem wg_stepO {G : Form} {p q : Bool × List Form × Form} (h : StepO G p q) :
    WgLt (wg G p.1 p.2.1 p.2.2) (wg G q.1 q.2.1 q.2.2) := by
  cases h with
  | old h => exact wg_step h
  | @lcirc Ψ Z C =>
      refine wgOCtx (fun X hX => ?_) ?_
      · rcases List.mem_cons.mp hX with rfl | hX'
        · exact .circ (.base List.mem_cons_self)
        · exact .base (List.mem_cons_of_mem _ hX')
      · show seqSize (Z :: Ψ) (.circ C) < seqSize (Form.circ Z :: Ψ) (.circ C)
        rw [sqCons, sqCons]
        show Z.size + seqSize Ψ (.circ C) < (Z.size + 1) + seqSize Ψ (.circ C)
        omega
  | @lcircI Ψ Z C =>
      refine wgOCtx (fun X hX => ?_) ?_
      · rcases List.mem_cons.mp hX with rfl | hX'
        · exact .circ (.base List.mem_cons_self)
        · exact .base (List.mem_cons_of_mem _ hX')
      · show seqSize (Z :: Ψ) (.circ C) < seqSize (Form.circ Z :: Ψ) (.circ C)
        rw [sqCons, sqCons]
        show Z.size + seqSize Ψ (.circ C) < (Z.size + 1) + seqSize Ψ (.circ C)
        omega
  | limpLI1 hsz => exact wgOCtx (fun _ h => .base h) (sqGoal hsz)
  | @limpLI2 Ψ A B C =>
      refine wgOCtx (fun X hX => ?_) ?_
      · rcases List.mem_cons.mp hX with rfl | hX'
        · exact .imp (.base List.mem_cons_self)
        · exact .base (List.mem_cons_of_mem _ hX')
      · show seqSize (B :: Ψ) (.circ C) < seqSize (Form.imp A B :: Ψ) (.circ C)
        rw [sqCons, sqCons]
        show B.size + seqSize Ψ (.circ C)
          < (A.size + B.size + 1) + seqSize Ψ (.circ C)
        omega
  | rcirc => exact wgOFocus
  | @rcircI Ψ Z =>
      exact wgOCtx (fun _ h => .base h)
        (sqGoal (show Z.size < (Form.circ Z).size from Nat.lt_succ_self _))

/-- **Termination of backward search in the redesigned `Gbu◯(G)`** —
the paper's own weight suffices. -/
theorem stepO_wf (G : Form) :
    WellFounded (fun p q : Bool × List Form × Form => StepO G p q) :=
  Subrelation.wf (fun {_ _} h => wg_stepO h)
    (InvImage.wf (fun p : Bool × List Form × Form => wg G p.1 p.2.1 p.2.2)
      wgLt_wf)

/-- info: 'FRJ.Gbu.wg_stepO' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wg_stepO

/-- info: 'FRJ.Gbu.stepO_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepO_wf

/-! ## §11d  Theorem 8◯: the case analysis, and the two obstructions left

With the two-rule change the measure is the paper's own, so the
recursion can be written.  Walking every case of `search` against the
new rule set leaves exactly three findings.

**GOOD — the regular `◯` goal needs no promise world.**  `L◯` is
invertible for free (`gbuInv11`, the `Clo.circ` clause) and applies
whenever the goal is `◯`-shaped, so backward search strips the modal
zone EAGERLY: by the time a `◯`-goal sequent is critical, its context
has no top-level `◯` left (each `L◯` replaces `◯Y` by `Y`, and if `Y` is
a `∧` or `∨` the regular `L∧`/`L∨` finish the job).  So `gbuSuccCirc`
suffices there and `gbuSuccCircP`'s `PromiseWorld` hypothesis is NOT
needed by the search.  The modal-zone lemma remains available for the
irregular side.

**OBSTRUCTION 1 — the irregular `◯` goal has no success lemma.**  At an
unrefuted `Ω →g ◯Z` the available rules are `Ax`, `L◯ᵢ`, `L⊃ᵢ`, `R◯ᵢ`,
and NONE of them is invertible: `EvalI` is membership-based, not
`Clo`-based, so even `L◯ᵢ` does not come free the way `gbuInv11` does.
A licence is needed — the analogue of Lemmas 11–13 for this case — and
the only `FRJVi` rules concluding `◯Z` are `Ax^I◯` and `◯∉`, whose
premise is REGULAR.  This is the same mismatch `rcircNI_not_invertible`
exposed, now confined to one case.

**OBSTRUCTION 2 — `L◯ᵢ` breaks the irregular invariant.**  Irregular
sequents carry `Ω ⊆ Ĝ`, and `L◯ᵢ` replaces `◯Y` by `Y`, which need not
be an atom, an implication or a `◯`-formula.  The regular judgment
recovers by `L∧`/`L∨`; the irregular one has neither.  `circ_body_escapes_gHat`
below is a concrete instance.  The fixes are to admit `L∧ᵢ`/`L∨ᵢ` too —
a further departure — or to restrict `L◯ᵢ` to bodies in `Ĝ`, whose
completeness would then have to be checked. -/

private def qw : Form := .atom "q"

/-- `G = ◯(p ∧ q) ⊃ p`.  Here `◯(p∧q) ∈ Ĝ` but its body `p∧q` is not,
so `L◯ᵢ`'s premise leaves the irregular sequent language. -/
def Gesc : Form := .imp (.circ (.and pv qw)) pv

theorem circ_body_escapes_gHat :
    Form.circ (.and pv qw) ∈ gHat Gesc ∧ (Form.and pv qw) ∉ gHat Gesc := by
  constructor <;> decide

/-- info: 'FRJ.Gbu.circ_body_escapes_gHat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms circ_body_escapes_gHat

/-! ## §12  Theorems 8–10

OPEN.  What remains is to rebuild `SearchOk` over the store-carrying
state `SeqU` of `wip/gbu_measure.lean`, with the three new rules
dispatched to §1's soundness lemmas and §5's invertibility clauses, and
`gbuSuccAtF`/`gbuSuccOrF` in place of the `◯`-free success lemmas.  The
one obligation left standing is `TagClean`, and the sharp form of it is:
`gbuSuccAtF`/`gbuSuccOrF` deliver `blocked` rows, which `◯∈`/`◯∉`
cannot lift. -/

/-! ## Axiom pins -/

/-- info: 'FRJ.Gbu.sound_lcirc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sound_lcirc

/-- info: 'FRJ.Gbu.sound_rcirc' does not depend on any axioms -/
#guard_msgs in
#print axioms sound_rcirc

/-- info: 'FRJ.Gbu.lcirc_goal_must_be_circ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lcirc_goal_must_be_circ

/-- info: 'FRJ.Gbu.gbuInv11' depends on axioms: [propext] -/
#guard_msgs in
#print axioms gbuInv11

/-- info: 'FRJ.Gbu.gbuInv12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv12

/-- info: 'FRJ.Gbu.gbuInv13' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuInv13

/-- info: 'FRJ.Gbu.frjCircKit_of_tagClean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frjCircKit_of_tagClean

/-- info: 'FRJ.Gbu.gbuSuccAtF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuSuccAtF

/-- info: 'FRJ.Gbu.gbuSuccOrF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuSuccOrF

/-- info: 'FRJ.Gbu.provableV_counit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms provableV_counit

/-- info: 'FRJ.Gbu.not_pll_counit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_pll_counit

/-- info: 'FRJ.Gbu.rcirc_not_invertible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rcirc_not_invertible

/-- info: 'FRJ.Gbu.rcircNI_not_invertible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rcircNI_not_invertible

/-- info: 'FRJ.Gbu.sound_limp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sound_limp

/-- info: 'FRJ.Gbu.gbuSuccCircP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuSuccCircP

/-- info: 'FRJ.Gbu.gbuSuccCirc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gbuSuccCirc

/-- info: 'FRJ.Gbu.not_evalI_omegaNI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_evalI_omegaNI

/-- info: 'FRJ.Gbu.not_gbuR_omegaNI' depends on axioms: [propext] -/
#guard_msgs in
#print axioms not_gbuR_omegaNI

end FRJ.Gbu
