/-
# The corner manufactures — the PROVED closure layer of the `searchW`
corner (hoisted 2026-09-01 so the record holds them independently of
the still-open induction)

On the RefAt-relaxed barren (J2) of `⋈^◯` (2026-09-01): the kept-chain
manufacture over the non-stuck part, the prime-body `axI`-family
manufacture with the engine's greedy `keptOf` as a decidable cover,
and the Σ-emptiness of prime-rhs irregular rows.
-/
import wip.gbu_frjw_circdb

namespace FRJ.Gbu.W

open FRJ Form FRJ.Gbu FRJ.Search

/-- Σ-emptiness at prime rhs: of the `FRJWi` constructors only `axI`
and `lift` produce a prime right-hand side, and both have an empty
stable zone.  Consequence: at a `◯`-critical corner with PRIME `Z`,
the single-row `⋈^◯` family drawn from `WEvalI D Ψ Z` is Σ-empty, so
the join's side conditions `hJ1`/`hJ2`/`hcirc` are vacuous. -/
theorem st_nil_of_prime {G : Form} {St Th : List Form} {F : Form}
    (d : FRJWi G St Th F) (hF : F.isPrime = true) : St = [] := by
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
    obtain ⟨St, Th, k₁, k₂, k₃⟩ := hev
    exact ⟨(St, Th), k₁, k₂, k₃⟩
  obtain ⟨g, hg⟩ := finEx hwit
  set St : Fin (E.n + 1) → List Form := fun j => (g j).1 with hStdef
  set Th : Fin (E.n + 1) → List Form := fun j => (g j).2 with hThdef
  have hStTh : ∀ j, D (.irr (St j) (Th j) (f j)) := fun j => (hg j).1
  have hStΩ : ∀ j, St j ⊆ Ω := fun j => (hg j).2.1
  have hΩSt : ∀ j, Ω ⊆ St j ++ Th j := fun j => (hg j).2.2
  obtain ⟨d⟩ := finPi (fun j => hsat.1 _ (hStTh j))
  have hups_sub : ∀ x ∈ U, x ∈ upsilon f := fun x hx => (E.spec x).mpr hx
  have hJ1 : ∀ i j, i ≠ j → St i ⊆ St j ++ Th j :=
    fun i j _ => fun {_} hX => hΩSt j (hStΩ i hX)
  have hcirc : unionAll (fun j => circPart (St j)) = [] := by
    refine eq_nil_of_forall_not_mem (fun X hX => ?_)
    obtain ⟨j, hj⟩ := mem_unionAll.mp hX
    obtain ⟨hmem, hc⟩ := List.mem_filter.mp hj
    exact absurd hc (by
      rw [not_isCirc_of_gHatAtImp (hΩ X (hStΩ j hmem))]
      exact fun h => Bool.noConfusion h)
  -- the zones
  set base := joinCtxOrVBase St Th with hbase
  set tail := restrict (thPool Th) (upsilon f) with htail
  set stuckL := (thPool Th).filter
    (fun Y => decide (Y ∈ Ω) && !decide (ante Y ∈ R)) with hstuckL
  have pool_isImp : ∀ X ∈ thPool Th, X.isImp = true :=
    fun X hX => (List.mem_filter.mp hX).2
  -- membership combinators for the cover
  have hStabAt : ∀ {X : Form} {j}, X ∈ St j → X.isPV = true → X ∈ base := by
    intro X j hX hpv
    exact List.mem_append_left _ (List.mem_append_left _
      (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hX, hpv⟩⟩))
  have hStabImp : ∀ {X : Form} {j}, X ∈ St j → X.isImp = true → X ∈ base := by
    intro X j hX hi
    exact List.mem_append_right _
      (mem_unionAll.mpr ⟨j, List.mem_filter.mpr ⟨hX, hi⟩⟩)
  have hΘat : ∀ {X : Form}, (∀ j, X ∈ Th j) → X.isPV = true → X ∈ base := by
    intro X hall hpv
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_interAll.mpr (fun j => List.mem_filter.mpr ⟨hall j, hpv⟩)))
  have hpool : ∀ {X : Form}, (∀ j, X ∈ Th j) → X.isImp = true →
      X ∈ thPool Th := by
    intro X hall hi
    exact List.mem_filter.mpr ⟨mem_interAll.mpr hall, hi⟩
  -- `Ω₀` is `Clo`-derived by `base ++ tail`
  have hΩ₀clo : ∀ w ∈ atPart Ω ++
      (impPart Ω).filter (fun Y => decide (ante Y ∈ R)),
      Clo (base ++ tail) w := by
    intro w hw
    rcases List.mem_append.mp hw with hat | himpf
    · obtain ⟨hwΩ, hpv⟩ := List.mem_filter.mp hat
      by_cases hin : ∃ j, w ∈ St j
      · obtain ⟨j, hj⟩ := hin
        exact .base (List.mem_append_left _ (hStabAt hj hpv))
      · have hall : ∀ j, w ∈ Th j := fun j =>
          (List.mem_append.mp (hΩSt j hwΩ)).resolve_left (fun h => hin ⟨j, h⟩)
        exact .base (List.mem_append_left _ (hΘat hall hpv))
    · obtain ⟨hwi, hante⟩ := List.mem_filter.mp himpf
      obtain ⟨hwΩ, hi⟩ := List.mem_filter.mp hwi
      have hanteR : ante w ∈ R := of_decide_eq_true hante
      by_cases hin : ∃ j, w ∈ St j
      · obtain ⟨j, hj⟩ := hin
        exact .base (List.mem_append_left _ (hStabImp hj hi))
      · have hall : ∀ j, w ∈ Th j := fun j =>
          (List.mem_append.mp (hΩSt j hwΩ)).resolve_left (fun h => hin ⟨j, h⟩)
        match w, hi, hanteR, hall with
        | .imp A B, _, hanteR, hall =>
            refine .base (List.mem_append_right _ ?_)
            show Form.imp A B ∈ restrict (thPool Th) (upsilon f)
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
  have hkc : KeptChain (upsilon f) base (thPool Th) (stuckL ++ tail) := by
    refine keptChain_extend stuckL (keptChainRestrict base Th)
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
  · -- the relaxed (J2): Σ-implications, refuted or certified
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
    by_cases hin : ∃ j, X ∈ St j
    · obtain ⟨j, hj⟩ := hin
      by_cases hi : X.isImp
      · exact .base (List.mem_append_left _ (hStabImp hj hi))
      · have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
        exact .base (List.mem_append_left _
          (hStabAt hj (List.mem_filter.mp this).2))
    · have hall : ∀ j, X ∈ Th j := fun j =>
        (List.mem_append.mp (hΩSt j hX)).resolve_left (fun h => hin ⟨j, h⟩)
      by_cases hi : X.isImp
      · by_cases hante : ante X ∈ R
        · match X, hi, hante, hall with
          | .imp A B, _, hante, hall =>
              refine .base (List.mem_append_right _
                (List.mem_append_right _ ?_))
              show Form.imp A B ∈ restrict (thPool Th) (upsilon f)
              exact mem_restrict.mpr ⟨hpool hall rfl,
                hups_sub _ (List.mem_cons_of_mem _ hante)⟩
        · refine .base (List.mem_append_right _ (List.mem_append_left _ ?_))
          exact List.mem_filter.mpr ⟨hpool hall hi,
            by simp [hX, hante]⟩
      · have := mem_gAt_of_not_imp (hΩ X hX) (by simpa using hi)
        exact .base (List.mem_append_left _
          (hΘat hall (List.mem_filter.mp this).2))

/-- The corner manufacture at a PRIME body: the single-row `⋈^◯` family
over the CONCRETE `axI` row, whose Σ-zones are empty and whose kept
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


/-! ## Pins -/

/-- info: 'FRJ.Gbu.W.refutedCleanly_circ_kept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_circ_kept

/-- info: 'FRJ.Gbu.W.refutedCleanly_circ_axI' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms refutedCleanly_circ_axI

/-- info: 'FRJ.Gbu.W.st_nil_of_prime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms st_nil_of_prime

end FRJ.Gbu.W
