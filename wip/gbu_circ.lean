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

/-- info: 'FRJ.Gbu.not_evalI_omegaNI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_evalI_omegaNI

/-- info: 'FRJ.Gbu.not_gbuR_omegaNI' depends on axioms: [propext] -/
#guard_msgs in
#print axioms not_gbuR_omegaNI

end FRJ.Gbu
