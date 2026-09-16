/-
# The corner manufactures — the PROVED closure layer of the `searchW`
corner (hoisted 2026-09-01 so the record holds them independently of
the still-open induction)

On the RefAt-relaxed barren (J2) of `⋈^◯` (2026-09-01): the kept-chain
manufacture over the non-stuck part, the prime-body `axI`-family
manufacture with the engine's greedy `keptOf` as a decidable cover,
and the Ξ-emptiness of prime-rhs irregular rows.
-/
import FRJ.Gbu.W.CircDB

namespace FRJ.Gbu.W

open FRJ Form FRJ.Gbu FRJ.Search

/-- Ξ-emptiness at prime rhs: of the `FRJWi` constructors only `axI`
and `lift` produce a prime right-hand side, and both have an empty
stable zone.  Consequence: at a `◯`-critical corner with PRIME `Z`,
the single-row `⋈^◯` family drawn from `WEvalI D Ψ Z` is Ξ-empty, so
the join's side conditions `hJ1`/`hJ2`/`hcirc` are vacuous. -/
theorem st_nil_of_prime {G : Form} {Ξ Θ : List Form} {F : Form}
    (d : FRJWi G Ξ Θ F) (hF : F.isPrime = true) : Ξ = [] := by
  cases d with
  | axI _ _ _ _ => rfl
  | lift _ _ => rfl
  | andI1 _ _ => exact absurd hF (by simp [Form.isPrime])
  | andI2 _ _ => exact absurd hF (by simp [Form.isPrime])
  | orI _ _ _ _ _ _ _ => exact absurd hF (by simp [Form.isPrime])
  | impInI _ _ _ _ _ _ _ => exact absurd hF (by simp [Form.isPrime])
  | circNotIn _ _ _ _ => exact absurd hF (by simp [Form.isPrime])
  | axIC _ _ _ _ _ _ => exact absurd hF (by simp [Form.isPrime])

/-! ## The kept-chain manufacture (the corner closure, on the
RefAt-relaxed barren (J2) of 2026-09-01)

With the relaxed (J2), the `⋈^◯` manufacture no longer needs a row for
EVERY antecedent of `Ω`: an implication is retained by a row for its
antecedent (`.ups` through the family), or by a `RefAt` certificate
over the NON-STUCK part `Ω₀` of the context — the atoms and the
refuted implications — which the join context `Clo`-derives before any
stuck link is added, so the chain extension is order-free. -/

/-- `RefAt` certificates rebase to any context that `Clo`-derives the
old one (only the `imp` clause consults the context, through `Clo`). -/
theorem refAt_clo_mono {cone : Bool} {Υ ctx ctx' : List Form}
    (hcl : ∀ w ∈ ctx, Clo ctx' w) :
    ∀ {X : Form}, RefAt cone Υ ctx X → RefAt cone Υ ctx' X := by
  intro X h
  induction h with
  | ups h => exact .ups h
  | bot => exact .bot
  | imp hA _ ih => exact .imp (clo_trans hcl hA) ih
  | circ hc _ ih => exact .circ hc ih
  | or _ _ ih₁ ih₂ => exact .or ih₁ ih₂
  | andL _ ih => exact .andL ih
  | andR _ ih => exact .andR ih

/-- A `KeptChain` extends by any links certified over the base plus the
chain so far; the extension is order-free because each new link's
certificate is context-monotone. -/
theorem keptChain_extend {Υ base pool : List Form} :
    ∀ (links : List Form) {kept : List Form},
      KeptChain Υ base pool kept →
      (∀ X ∈ links, X ∈ pool) →
      (∀ X ∈ links, X.isImp = true) →
      (∀ {Y B : Form}, Form.imp Y B ∈ links →
        RefAt true Υ (base ++ kept) Y) →
      KeptChain Υ base pool (links ++ kept)
  | [], _, h, _, _, _ => h
  | X :: rest, kept, h, hpool, himp, hcert => by
      match X, himp X List.mem_cons_self with
      | .imp Y B, _ =>
          refine .cons
            (keptChain_extend rest h
              (fun x hx => hpool x (List.mem_cons_of_mem _ hx))
              (fun x hx => himp x (List.mem_cons_of_mem _ hx))
              (fun hx => hcert (List.mem_cons_of_mem _ hx)))
            (hpool _ List.mem_cons_self) ?_
          refine refAt_mono (fun _ h => h) ?_ (hcert List.mem_cons_self)
          intro x hx
          rcases List.mem_append.mp hx with h' | h'
          · exact List.mem_append_left _ h'
          · exact List.mem_append_right _ (List.mem_append_right _ h')

/-- **The corner manufacture.**  `⋈^◯` over the family `Z :: R` (the
goal body and the refuted forms), where an implication of `Ω` is
retained by `.ups` when its antecedent is in `R`, and by a rebased
`RefAt` certificate over `Ω₀ = atoms ++ refuted implications`
otherwise.  The certificate context `Ω₀` is `Clo`-derived by the join
context before any stuck link enters the chain. -/
theorem refutedCleanly_circ_kept {G : Form} {D : WSeq → Prop}
    (hsat : WSaturated G D) {Ω : List Form} {Z : Form} {R : List Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.circ Z ∈ sfR G)
    (hz : WEvalI D Ω Z)
    (hR : ∀ A ∈ R, WEvalI D Ω A)
    (himp : ∀ A B : Form, Form.imp A B ∈ Ω → A ∈ R ∨
      RefAt true (Z :: R)
        (atPart Ω ++ (impPart Ω).filter (fun Y => decide (ante Y ∈ R))) A) :
    WRefutedCleanly G Ω (.circ Z) := by
  classical
  let U := Z :: R
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : WEvalI D Ω (f j) := by
      rcases List.mem_cons.mp (hfmem j) with e | hmem
      · exact e ▸ hz
      · exact hR _ hmem
    obtain ⟨Ξ, Θ, k₁, k₂, k₃⟩ := hev
    exact ⟨(Ξ, Θ), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set Ξ : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Θ : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStTh : ∀ j, D (.irr (Ξ j) (Θ j) (f j)) := fun j => (hg j).1
  have hStΩ : ∀ j, Ξ j ⊆ Ω := fun j => (hg j).2.1
  have hΩΞ : ∀ j, Ω ⊆ Ξ j ++ Θ j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hStTh j))
  have hups_sub : ∀ x ∈ U, x ∈ upsilon f := fun x hx => (E.spec x).mpr hx
  have hJ1 : ∀ i j, i ≠ j → Ξ i ⊆ Ξ j ++ Θ j :=
    fun i j _ => fun {_} hX => hΩΞ j (hStΩ i hX)
  have hcirc : unionAll (fun j => circPart (Ξ j)) = [] := by
    refine eq_nil_of_forall_not_mem (fun X hX => ?_)
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    obtain ⟨hmem, hc⟩ := List.mem_filter.mp hj
    exact absurd hc (by
      rw [not_isCirc_of_gHatAtImp (hΩ X (hStΩ j hmem))]
      exact fun h => Bool.noConfusion h)
  -- the zones
  set base := joinCtxOrVBase Ξ Θ with hbase
  set tail := restrict (thPool Θ) (upsilon f) with htail
  set stuckL := (thPool Θ).filter
    (fun Y => decide (Y ∈ Ω) && !decide (ante Y ∈ R)) with hstuckL
  have pool_isImp : ∀ X ∈ thPool Θ, X.isImp = true :=
    fun X hX => (List.mem_filter.mp hX).2
  -- membership combinators for the cover
  have hStabAt : ∀ {X : Form} {j}, X ∈ Ξ j → X.isPV = true → X ∈ base := by
    intro X j hX hpv
    exact List.mem_append_left _ (List.mem_append_left _
      (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hX, hpv⟩⟩))
  have hStabImp : ∀ {X : Form} {j}, X ∈ Ξ j → X.isImp = true → X ∈ base := by
    intro X j hX hi
    exact List.mem_append_right _
      (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hX, hi⟩⟩)
  have hΘat : ∀ {X : Form}, (∀ j, X ∈ Θ j) → X.isPV = true → X ∈ base := by
    intro X hall hpv
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hpv⟩)))
  have hpool : ∀ {X : Form}, (∀ j, X ∈ Θ j) → X.isImp = true →
      X ∈ thPool Θ := by
    intro X hall hi
    exact List.mem_filter.mpr ⟨mem_interAll.mpr hall, hi⟩
  -- `Ω₀` is `Clo`-derived by `base ++ tail`
  have hΩ₀clo : ∀ w ∈ atPart Ω ++
      (impPart Ω).filter (fun Y => decide (ante Y ∈ R)),
      Clo (base ++ tail) w := by
    intro w hw
    rcases List.mem_append.mp hw with hat | himpf
    · obtain ⟨hwΩ, hpv⟩ := List.mem_filter.mp hat
      by_cases hin : ∃ j, w ∈ Ξ j
      · obtain ⟨j, hj⟩ := hin
        exact .base (List.mem_append_left _ (hStabAt hj hpv))
      · have hall : ∀ j, w ∈ Θ j := fun j =>
          (List.mem_append.mp (hΩΞ j hwΩ)).resolve_left (fun h => hin ⟨j, h⟩)
        exact .base (List.mem_append_left _ (hΘat hall hpv))
    · obtain ⟨hwi, hante⟩ := List.mem_filter.mp himpf
      obtain ⟨hwΩ, hi⟩ := List.mem_filter.mp hwi
      have hanteR : ante w ∈ R := of_decide_eq_true hante
      by_cases hin : ∃ j, w ∈ Ξ j
      · obtain ⟨j, hj⟩ := hin
        exact .base (List.mem_append_left _ (hStabImp hj hi))
      · have hall : ∀ j, w ∈ Θ j := fun j =>
          (List.mem_append.mp (hΩΞ j hwΩ)).resolve_left (fun h => hin ⟨j, h⟩)
        match w, hi, hanteR, hall with
        | .imp A B, _, hanteR, hall =>
            refine .base (List.mem_append_right _ ?_)
            show Form.imp A B ∈ restrict (thPool Θ) (upsilon f)
            exact mem_restrict.mpr ⟨hpool hall rfl,
              hups_sub _ (List.mem_cons_of_mem _ hanteR)⟩
  -- lift a certificate over `Ω₀` to the join context
  have hlift : ∀ {A : Form},
      RefAt true (Z :: R)
        (atPart Ω ++ (impPart Ω).filter (fun Y => decide (ante Y ∈ R))) A →
      RefAt true (upsilon f) (base ++ tail) A := by
    intro A hc
    exact refAt_clo_mono hΩ₀clo (refAt_mono hups_sub (fun _ h => h) hc)
  -- the chain: stuck links over the restrict tail
  have hkc : KeptChain (upsilon f) base (thPool Θ) (stuckL ++ tail) := by
    refine keptChain_extend stuckL (keptChainRestrict base Θ)
      (fun x hx => (List.mem_filter.mp hx).1)
      (fun x hx => pool_isImp x (List.mem_filter.mp hx).1) ?_
    intro Y B hYmem
    obtain ⟨hYpool, hYcond⟩ := List.mem_filter.mp hYmem
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not] at hYcond
    rcases himp Y B hYcond.1 with hYR | hYcert
    · exact absurd hYR (by simpa [ante] using hYcond.2)
    · exact hlift hYcert
  refine ⟨base ++ (stuckL ++ tail), .barren,
    ⟨.joinCirc (fun j => d j) hJ1 ?_ hcirc hkc
      (.ups (hups_sub _ List.mem_cons_self)) hgoal (CtxEq.refl _)⟩,
    Or.inl rfl, ?_⟩
  · -- the relaxed (J2): Ξ-implications, refuted or certified
    intro A B hmem
    obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
    have hgrow : base ++ tail ⊆ base ++ (stuckL ++ tail) := by
      intro x hx
      rcases List.mem_append.mp hx with h' | h'
      · exact List.mem_append_left _ h'
      · exact List.mem_append_right _ (List.mem_append_right _ h')
    rcases himp A B hAB with hAR | hAcert
    · exact .ups (hups_sub _ (List.mem_cons_of_mem _ hAR))
    · exact refAt_mono (fun _ h => h) hgrow (hlift hAcert)
  · -- the cover
    intro X hX
    by_cases hin : ∃ j, X ∈ Ξ j
    · obtain ⟨j, hj⟩ := hin
      by_cases hi : X.isImp
      · exact .base (List.mem_append_left _ (hStabImp hj hi))
      · have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
        exact .base (List.mem_append_left _
          (hStabAt hj (List.mem_filter.mp this).2))
    · have hall : ∀ j, X ∈ Θ j := fun j =>
        (List.mem_append.mp (hΩΞ j hX)).resolve_left (fun h => hin ⟨j, h⟩)
      by_cases hi : X.isImp
      · by_cases hante : ante X ∈ R
        · match X, hi, hante, hall with
          | .imp A B, _, hante, hall =>
              refine .base (List.mem_append_right _
                (List.mem_append_right _ ?_))
              show Form.imp A B ∈ restrict (thPool Θ) (upsilon f)
              exact mem_restrict.mpr ⟨hpool hall rfl,
                hups_sub _ (List.mem_cons_of_mem _ hante)⟩
        · refine .base (List.mem_append_right _ (List.mem_append_left _ ?_))
          exact List.mem_filter.mpr ⟨hpool hall hi,
            by simp [hX, hante]⟩
      · have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
        exact .base (List.mem_append_left _
          (hΘat hall (List.mem_filter.mp this).2))

/-- The corner manufacture at a PRIME body: the single-row `⋈^◯` family
over the CONCRETE `axI` row, whose Ξ-zones are empty and whose kept
chain is the engine's greedy `keptOf` — so the cover hypothesis is the
full engine-strength retention, and it is decidable (`cloB`). -/
theorem refutedCleanly_circ_axI {G : Form} {Ω : List Form} {Z : Form}
    (hprime : Z.isPrime = true) (hZsf : Z ∈ sfR G)
    (hgoal : Form.circ Z ∈ sfR G)
    (hcov : ∀ X ∈ Ω,
      Clo (joinCtxOrVBase (fun _ : Fin 1 => [])
          (fun _ : Fin 1 => rm (gAt G) Z ++ gImp G ++ gCirc G) ++
        keptOf (upsilon (fun _ : Fin 1 => Z))
          (joinCtxOrVBase (fun _ : Fin 1 => [])
            (fun _ : Fin 1 => rm (gAt G) Z ++ gImp G ++ gCirc G))
          (thPool (fun _ : Fin 1 => rm (gAt G) Z ++ gImp G ++ gCirc G))) X) :
    WRefutedCleanly G Ω (.circ Z) := by
  refine ⟨_, .barren,
    ⟨.joinCirc (n := 0)
      (fun _ => .axI Z hprime hZsf (CtxEq.refl _))
      (fun i j hij => absurd (Fin.ext (by omega)) hij)
      (fun A B hmem => ?_) ?_ (keptOf_ok _ _ _)
      (.ups (List.mem_map.mpr ⟨0, List.mem_finRange 0, rfl⟩))
      hgoal (CtxEq.refl _)⟩,
    Or.inl rfl, hcov⟩
  · obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    exact absurd hj (by simp [impPart])
  · refine eq_nil_of_forall_not_mem (fun X hX => ?_)
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    exact absurd hj (by simp [circPart])


/-! ## The goal-set certificates (K1, 2026-09-01)

`RefAtG Ψ C P A`: a goal-relative refutation certificate for `A` —
bottoming at the CURRENT goal `C`, at a PENDING form in `P` (an
abandoned `∨`-sibling or a frozen goal), or at `⊥`; implication nodes
carry `Clo Ψ` side conditions.  The search threads one certificate per
visited (antecedent, goal) pair; every goal-descent substitutes at the
`goal`-leaves, `∨`-descents move the sibling into `P`, chase entries
freeze the old goal into `P`, and context growth is absorbed by
`Clo`-monotonicity.  At the `◯Z`-corner a certificate whose pending
leaves are all refuted (or the goal itself) converts into the `RefAt`
certificate the `⋈^◯` manufacture needs. -/

/-- Subformulas are transitive. -/
theorem sf_trans : ∀ {A X : Form}, X ∈ sf A → sf X ⊆ sf A := by
  intro A
  induction A with
  | atom p => intro X hX; simp [sf] at hX; subst hX; exact fun _ h => h
  | bot => intro X hX; simp [sf] at hX; subst hX; exact fun _ h => h
  | and A B ihA ihB =>
      intro X hX
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact fun _ h => h
      · rcases List.mem_append.mp hX' with h | h
        · exact fun y hy => List.mem_cons_of_mem _
            (List.mem_append_left _ (ihA h hy))
        · exact fun y hy => List.mem_cons_of_mem _
            (List.mem_append_right _ (ihB h hy))
  | or A B ihA ihB =>
      intro X hX
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact fun _ h => h
      · rcases List.mem_append.mp hX' with h | h
        · exact fun y hy => List.mem_cons_of_mem _
            (List.mem_append_left _ (ihA h hy))
        · exact fun y hy => List.mem_cons_of_mem _
            (List.mem_append_right _ (ihB h hy))
  | imp A B ihA ihB =>
      intro X hX
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact fun _ h => h
      · rcases List.mem_append.mp hX' with h | h
        · exact fun y hy => List.mem_cons_of_mem _
            (List.mem_append_left _ (ihA h hy))
        · exact fun y hy => List.mem_cons_of_mem _
            (List.mem_append_right _ (ihB h hy))
  | circ A ihA =>
      intro X hX
      rcases List.mem_cons.mp hX with rfl | hX'
      · exact fun _ h => h
      · exact fun y hy => List.mem_cons_of_mem _ (ihA hX' hy)

/-- Every `.base` leaf of a `Clo` derivation is a subformula of the
goal: the derivation restricts to the subformula support. -/
theorem clo_sf_support {Γ : List Form} :
    ∀ {X : Form}, Clo Γ X →
      Clo (Γ.filter (fun w => decide (w ∈ sf X))) X := by
  intro X h
  induction h with
  | base hX => exact .base (List.mem_filter.mpr
      ⟨hX, decide_eq_true (self_mem_sf _)⟩)
  | and _ _ ih₁ ih₂ =>
      exact .and
        (clo_mono (fun w hw => List.mem_filter.mpr
          ⟨(List.mem_filter.mp hw).1, decide_eq_true
            (sf_sub_and₁ (of_decide_eq_true (List.mem_filter.mp hw).2))⟩) ih₁)
        (clo_mono (fun w hw => List.mem_filter.mpr
          ⟨(List.mem_filter.mp hw).1, decide_eq_true
            (sf_sub_and₂ (of_decide_eq_true (List.mem_filter.mp hw).2))⟩) ih₂)
  | orR _ ih =>
      exact .orR (clo_mono (fun w hw => List.mem_filter.mpr
        ⟨(List.mem_filter.mp hw).1, decide_eq_true
          (sf_sub_or₂ (of_decide_eq_true (List.mem_filter.mp hw).2))⟩) ih)
  | orL _ ih =>
      exact .orL (clo_mono (fun w hw => List.mem_filter.mpr
        ⟨(List.mem_filter.mp hw).1, decide_eq_true
          (sf_sub_or₁ (of_decide_eq_true (List.mem_filter.mp hw).2))⟩) ih)
  | imp _ ih =>
      exact .imp (clo_mono (fun w hw => List.mem_filter.mpr
        ⟨(List.mem_filter.mp hw).1, decide_eq_true
          (sf_sub_imp₂ (of_decide_eq_true (List.mem_filter.mp hw).2))⟩) ih)
  | circ _ ih =>
      exact .circ (clo_mono (fun w hw => List.mem_filter.mpr
        ⟨(List.mem_filter.mp hw).1, decide_eq_true
          (sf_sub_circ (of_decide_eq_true (List.mem_filter.mp hw).2))⟩) ih)

/-- `RefAt` rebases on the subformula support: only the context members
inside `sf` of the target need `Clo`-derivations in the new context. -/
theorem refAt_clo_mono_sf {cone : Bool} {Υ ctx ctx' : List Form} :
    ∀ {X : Form}, RefAt cone Υ ctx X →
      (∀ w ∈ ctx, w ∈ sf X → Clo ctx' w) →
      RefAt cone Υ ctx' X := by
  intro X h
  induction h with
  | ups h => exact fun _ => .ups h
  | bot => exact fun _ => .bot
  | @imp A B hA _ ih =>
      intro hcl
      refine .imp ?_ (ih (fun w hw hs => hcl w hw (sf_sub_imp₂ hs)))
      have hsup := clo_sf_support hA
      refine clo_trans (fun w hw => ?_) hsup
      obtain ⟨hwc, hws⟩ := List.mem_filter.mp hw
      exact hcl w hwc (sf_sub_imp₁ (of_decide_eq_true hws))
  | circ hc _ ih =>
      exact fun hcl => .circ hc (ih (fun w hw hs => hcl w hw (sf_sub_circ hs)))
  | or _ _ ih₁ ih₂ =>
      exact fun hcl => .or
        (ih₁ (fun w hw hs => hcl w hw (sf_sub_or₁ hs)))
        (ih₂ (fun w hw hs => hcl w hw (sf_sub_or₂ hs)))
  | andL _ ih =>
      exact fun hcl => .andL (ih (fun w hw hs => hcl w hw (sf_sub_and₁ hs)))
  | andR _ ih =>
      exact fun hcl => .andR (ih (fun w hw hs => hcl w hw (sf_sub_and₂ hs)))

/-- The goal-relative certificate. -/
inductive RefAtG (Ψ : List Form) (C : Form) (P : List Form) : Form → Prop
  | goal : RefAtG Ψ C P C
  | pend {X : Form} : X ∈ P → RefAtG Ψ C P X
  | bot : RefAtG Ψ C P .bot
  | imp {A B : Form} : Clo Ψ A → RefAtG Ψ C P B → RefAtG Ψ C P (.imp A B)
  | circ {Z : Form} : RefAtG Ψ C P Z → RefAtG Ψ C P (.circ Z)
  | or {Z₁ Z₂ : Form} : RefAtG Ψ C P Z₁ → RefAtG Ψ C P Z₂ →
      RefAtG Ψ C P (.or Z₁ Z₂)
  | andL {Z₁ Z₂ : Form} : RefAtG Ψ C P Z₁ → RefAtG Ψ C P (.and Z₁ Z₂)
  | andR {Z₁ Z₂ : Form} : RefAtG Ψ C P Z₂ → RefAtG Ψ C P (.and Z₁ Z₂)

/-- Goal substitution: replace the `goal`-leaves by a certificate for
the OLD goal at the new goal and pending set. -/
theorem refAtG_subst {Ψ P P' : List Form} {C C' : Form}
    (hC : RefAtG Ψ C' P' C) (hPP : P ⊆ P') :
    ∀ {A : Form}, RefAtG Ψ C P A → RefAtG Ψ C' P' A := by
  intro A h
  induction h with
  | goal => exact hC
  | pend h => exact .pend (hPP h)
  | bot => exact .bot
  | imp hA _ ih => exact .imp hA ih
  | circ _ ih => exact .circ ih
  | or _ _ ih₁ ih₂ => exact .or ih₁ ih₂
  | andL _ ih => exact .andL ih
  | andR _ ih => exact .andR ih

/-- Context growth: certificates survive any context the old one
`Clo`-embeds into. -/
theorem refAtG_clo {Ψ Ψ' P : List Form} {C : Form}
    (hcl : ∀ w ∈ Ψ, Clo Ψ' w) :
    ∀ {A : Form}, RefAtG Ψ C P A → RefAtG Ψ' C P A := by
  intro A h
  induction h with
  | goal => exact .goal
  | pend h => exact .pend h
  | bot => exact .bot
  | imp hA _ ih => exact .imp (clo_trans hcl hA) ih
  | circ _ ih => exact .circ ih
  | or _ _ ih₁ ih₂ => exact .or ih₁ ih₂
  | andL _ ih => exact .andL ih
  | andR _ ih => exact .andR ih

/-- The corner conversion: at goal `◯Z`, a certificate whose pending
leaves are refuted or the goal itself becomes the `RefAt` certificate
over `Z :: R` at the SAME context. -/
theorem refAtG_to_refAt {Ψ P R : List Form} {Z : Form}
    (hP : ∀ L ∈ P, L ∈ R ∨ L = Form.circ Z) :
    ∀ {A : Form}, RefAtG Ψ (.circ Z) P A → RefAt true (Z :: R) Ψ A := by
  intro A h
  induction h with
  | goal => exact .circ rfl (.ups List.mem_cons_self)
  | pend h =>
      rcases hP _ h with hR | rfl
      · exact .ups (List.mem_cons_of_mem _ hR)
      · exact .circ rfl (.ups List.mem_cons_self)
  | bot => exact .bot
  | imp hA _ ih => exact .imp hA ih
  | circ _ ih => exact .circ rfl ih
  | or _ _ ih₁ ih₂ => exact .or ih₁ ih₂
  | andL _ ih => exact .andL ih
  | andR _ ih => exact .andR ih

private theorem le_foldr_max (f : Form → Nat) :
    ∀ (l : List Form) (x : Form), x ∈ l → f x ≤ (l.map f).foldr max 0
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_foldr_max f l x h') (Nat.le_max_right _ _)

/-- **The corner manufacture with full-context certificates.**  As
`refutedCleanly_circ_kept`, but the certificates for the stuck
implications are over `Ω` ITSELF (the shape the goal-set invariant
delivers).  The kept chain is built level by level on formula size:
a certificate's `Clo` leaves are subformulas of its target, hence
STRICTLY smaller than its implication, so every leaf that is itself a
stuck implication is already in the chain. -/
theorem refutedCleanly_circ_certs {G : Form} {D : WSeq → Prop}
    (hsat : WSaturated G D) {Ω : List Form} {Z : Form} {R : List Form}
    (hΩ : ∀ X ∈ Ω, X ∈ gAt G ++ gImp G)
    (hgoal : Form.circ Z ∈ sfR G)
    (hz : WEvalI D Ω Z)
    (hR : ∀ A ∈ R, WEvalI D Ω A)
    (himp : ∀ A B : Form, Form.imp A B ∈ Ω → A ∈ R ∨
      RefAt true (Z :: R) Ω A) :
    WRefutedCleanly G Ω (.circ Z) := by
  classical
  let U := Z :: R
  let E := enumOf U (by simp [U])
  let f := E.f
  have hfmem : ∀ j, f j ∈ U := fun j =>
    (E.spec (f j)).mp (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  have hwit : ∀ j, ∃ p : List Form × List Form,
      D (.irr p.1 p.2 (f j)) ∧ p.1 ⊆ Ω ∧ Ω ⊆ p.1 ++ p.2 := by
    intro j
    have hev : WEvalI D Ω (f j) := by
      rcases List.mem_cons.mp (hfmem j) with e | hmem
      · exact e ▸ hz
      · exact hR _ hmem
    obtain ⟨Ξ, Θ, k₁, k₂, k₃⟩ := hev
    exact ⟨(Ξ, Θ), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set Ξ : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Θ : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStTh : ∀ j, D (.irr (Ξ j) (Θ j) (f j)) := fun j => (hg j).1
  have hStΩ : ∀ j, Ξ j ⊆ Ω := fun j => (hg j).2.1
  have hΩΞ : ∀ j, Ω ⊆ Ξ j ++ Θ j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hStTh j))
  have hups_sub : ∀ x ∈ U, x ∈ upsilon f := fun x hx => (E.spec x).mpr hx
  have hJ1 : ∀ i j, i ≠ j → Ξ i ⊆ Ξ j ++ Θ j :=
    fun i j _ => fun {_} hX => hΩΞ j (hStΩ i hX)
  have hcirc : unionAll (fun j => circPart (Ξ j)) = [] := by
    refine eq_nil_of_forall_not_mem (fun X hX => ?_)
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    obtain ⟨hmem, hc⟩ := List.mem_filter.mp hj
    exact absurd hc (by
      rw [not_isCirc_of_gHatAtImp (hΩ X (hStΩ j hmem))]
      exact fun h => Bool.noConfusion h)
  set base := joinCtxOrVBase Ξ Θ with hbase
  set tail := restrict (thPool Θ) (upsilon f) with htail
  set stuckL := (thPool Θ).filter
    (fun Y => decide (Y ∈ Ω) && !decide (ante Y ∈ R)) with hstuckL
  have pool_isImp : ∀ X ∈ thPool Θ, X.isImp = true :=
    fun X hX => (List.mem_filter.mp hX).2
  have hStabAt : ∀ {X : Form} {j}, X ∈ Ξ j → X.isPV = true → X ∈ base := by
    intro X j hX hpv
    exact List.mem_append_left _ (List.mem_append_left _
      (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hX, hpv⟩⟩))
  have hStabImp : ∀ {X : Form} {j}, X ∈ Ξ j → X.isImp = true → X ∈ base := by
    intro X j hX hi
    exact List.mem_append_right _
      (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hX, hi⟩⟩)
  have hThAt : ∀ {X : Form}, (∀ j, X ∈ Θ j) → X.isPV = true → X ∈ base := by
    intro X hall hpv
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hpv⟩)))
  have hpool : ∀ {X : Form}, (∀ j, X ∈ Θ j) → X.isImp = true →
      X ∈ thPool Θ := by
    intro X hall hi
    exact List.mem_filter.mpr ⟨mem_interAll.mpr hall, hi⟩
  have hallTh : ∀ {X : Form}, X ∈ Ω → (¬ ∃ j, X ∈ Ξ j) → ∀ j, X ∈ Θ j :=
    fun {X} hX hin j =>
      (List.mem_append.mp (hΩΞ j hX)).resolve_left (fun h => hin ⟨j, h⟩)
  -- an Ω-member inside any kept superset of the stuck links of its size
  have hΩmem : ∀ {ks : List Form} {w : Form}, w ∈ Ω →
      (∀ v ∈ stuckL, v.size ≤ w.size → v ∈ ks) →
      Clo (base ++ (ks ++ tail)) w := by
    intro ks w hw hks
    by_cases hin : ∃ j, w ∈ Ξ j
    · obtain ⟨j, hj⟩ := hin
      by_cases hi : w.isImp
      · exact .base (List.mem_append_left _ (hStabImp hj hi))
      · have := mem_gAt_of_not_imp (hΩ w hw) (by simpa using hi)
        exact .base (List.mem_append_left _
          (hStabAt hj (List.mem_filter.mp this).2))
    · have hall := hallTh hw hin
      by_cases hi : w.isImp
      · by_cases hante : ante w ∈ R
        · match w, hi, hante, hall with
          | .imp A B, _, hante, hall =>
              refine .base (List.mem_append_right _
                (List.mem_append_right _ ?_))
              show Form.imp A B ∈ restrict (thPool Θ) (upsilon f)
              exact mem_restrict.mpr ⟨hpool hall rfl,
                hups_sub _ (List.mem_cons_of_mem _ hante)⟩
        · refine .base (List.mem_append_right _ (List.mem_append_left _ ?_))
          refine hks w ?_ (Nat.le_refl _)
          exact List.mem_filter.mpr ⟨hpool hall hi, by simp [hw, hante]⟩
      · have := mem_gAt_of_not_imp (hΩ w hw) (by simpa using hi)
        exact .base (List.mem_append_left _
          (hThAt hall (List.mem_filter.mp this).2))
  -- the chain, level by level on the link size
  have chain : ∀ n : Nat, ∃ ks : List Form,
      KeptChain (upsilon f) base (thPool Θ) (ks ++ tail) ∧
      (∀ x ∈ ks, x ∈ stuckL) ∧
      (∀ w ∈ stuckL, w.size ≤ n → w ∈ ks) := by
    intro n
    induction n with
    | zero =>
        refine ⟨[], keptChainRestrict base Θ,
          fun _ h => absurd h List.not_mem_nil, fun w _ h0 => ?_⟩
        exact absurd h0 (by cases w <;> simp [Form.size])
    | succ n ih =>
        obtain ⟨ks, hkc, hsub, hcov⟩ := ih
        refine ⟨stuckL.filter
          (fun w => decide (w.size = n + 1) && !decide (w ∈ ks)) ++ ks,
          ?_, ?_, ?_⟩
        · rw [List.append_assoc]
          refine keptChain_extend _ hkc
            (fun x hx => (List.mem_filter.mp
              (List.mem_filter.mp hx).1).1) ?_ ?_
          · intro x hx
            exact pool_isImp x (List.mem_filter.mp
              (List.mem_filter.mp hx).1).1
          · intro Y B hYmem
            obtain ⟨hYs, hYcond⟩ := List.mem_filter.mp hYmem
            obtain ⟨hYpool, hYc2⟩ := List.mem_filter.mp hYs
            simp only [Bool.and_eq_true, Bool.not_eq_true',
              decide_eq_true_eq, decide_eq_false_iff_not] at hYcond hYc2
            rcases himp Y B hYc2.1 with hYR | hYcert
            · exact absurd hYR (by simpa [ante] using hYc2.2)
            · refine refAt_clo_mono_sf
                (refAt_mono hups_sub (fun _ h => h) hYcert) ?_
              intro w hw hws
              refine hΩmem hw (fun v hv hvs => hcov v hv ?_)
              have h1 : w.size ≤ Y.size := size_le_of_mem_sf hws
              have h2 : Y.size < (Form.imp Y B).size := by
                simp only [Form.size]; omega
              omega
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact (List.mem_filter.mp h).1
          · exact hsub x h
        · intro w hw hwn
          by_cases hn : w.size ≤ n
          · exact List.mem_append_right _ (hcov w hw hn)
          · by_cases hks : w ∈ ks
            · exact List.mem_append_right _ hks
            · refine List.mem_append_left _ (List.mem_filter.mpr ⟨hw, ?_⟩)
              simp only [Bool.and_eq_true, Bool.not_eq_true',
                decide_eq_true_eq, decide_eq_false_iff_not]
              exact ⟨by omega, hks⟩
  obtain ⟨ks, hkc, hsub, hcov⟩ := chain ((stuckL.map Form.size).foldr max 0)
  have hcovAll : ∀ w ∈ stuckL, w ∈ ks :=
    fun w hw => hcov w hw (le_foldr_max Form.size _ w hw)
  refine ⟨base ++ (ks ++ tail), .barren,
    ⟨.joinCirc (fun j => d j) hJ1 ?_ hcirc hkc
      (.ups (hups_sub _ List.mem_cons_self)) hgoal (CtxEq.refl _)⟩,
    Or.inl rfl, ?_⟩
  · -- the relaxed (J2)
    intro A B hmem
    obtain ⟨j, hj⟩ := mem_unionAll.mp hmem
    have hAB : Form.imp A B ∈ Ω := hStΩ j (List.mem_filter.mp hj).1
    rcases himp A B hAB with hAR | hAcert
    · exact .ups (hups_sub _ (List.mem_cons_of_mem _ hAR))
    · refine refAt_clo_mono_sf
        (refAt_mono hups_sub (fun _ h => h) hAcert) ?_
      intro w hw _
      exact hΩmem hw (fun v hv _ => hcovAll v hv)
  · -- the cover
    intro X hX
    exact hΩmem hX (fun v hv _ => hcovAll v hv)

/-! ## Pins -/

/-- info: 'FRJ.Gbu.W.refutedCleanly_circ_kept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_circ_kept

/-- info: 'FRJ.Gbu.W.refutedCleanly_circ_axI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_circ_axI

/-- info: 'FRJ.Gbu.W.st_nil_of_prime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms st_nil_of_prime

/-- info: 'FRJ.Gbu.W.refutedCleanly_circ_certs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_circ_certs

end FRJ.Gbu.W
