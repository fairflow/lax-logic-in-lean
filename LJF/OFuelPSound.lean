/-
LJF◯ — soundness of the PARKING retention interpolant (route (B), N0e).

`eSoundP` / `aSoundP`: `LJF/OFuelSound.lean`'s `eSoundF` / `aSoundF`
templated to `interpP` (`LJF/OFuelP.lean`).

    eSoundP p : ∀ f todo done,   Inv (todo ++ done) [] .tru (interpP p f todo done none)
    aSoundP p : ∀ f todo done G, Inv (interpP p f todo done (some G) :: (todo ++ done)) [] .tru G

Three families of change, one per definitional change, and nothing else:

* **the three newly parked processing clauses.**  `(Q₁∨Q₂) ⊃ N`,
  `↓↑P′ ⊃ N` and `↓(M₁∧M₂) ⊃ N` now PARK, so their soundness cases are
  WEAKENING (`subPark`) exactly like the five clauses that already
  parked.  The three `simHyp` blocks that simulated the reshaped
  hypothesis (`invImpOr`/`invStrip`/`invCurry`'s proof-side counterparts)
  disappear: nothing is rewritten, so nothing has to be simulated.

* **the three new aggregate rows.**  Each goes through as the twelve
  modal rows do.  In the `∃p` aggregate the guard `A(done ⇒ ↑Q)` beside
  `done` yields `↑Q` by `aSoundP` at the FULL station, `unStable` turns
  it into the focus the fire needs, and the continuation is `eSoundP` at
  `[N] ++ rest` weakened.  In the `∀p` attack rows the handler is
  `atkPark`, which is `LJF/OCore.lean`'s `atkCimp` with the antecedent
  positive `↓◯Q′` generalised to an arbitrary `Q`; as there, it is
  instantiated at `rest := done`.

* **the Dyckhoff rows.**  Their guard is now `A(done ⇒ Q′ ⊃ N′)` at the
  full station, and `aSoundP p f [] done (Q′ ⊃ N′)` delivers it
  verbatim: on that side the residual simulator `resSim` and the
  crossed-station weakening both disappear.  `resSim` survives only in
  the unchanged E-side component `E(↓N′ ⊃ N :: rest)`.

Nothing in `LJF/OCore.lean`, `LJF/OFuel.lean`, `LJF/OFuelSound.lean` or
`LJF/OFuelP.lean` is touched; this module is purely additive.
-/
import LJF.OFuelP
import Meta.Audit

namespace LJFO

/-- **Attack via a parked implication `Q ⊃ N`, guard at the full station.**
`LJF/OCore.lean`'s `atkCimp` with the antecedent positive `↓◯Q′`
generalised to an arbitrary `Q`: the disjunct `A₁ ∧ A₂` supplies the `∀p`
of the antecedent's own goal `↑Q` (left component) and the continuation
interpolant (right component).  No residual simulator — the antecedent is
rebuilt from `A₁` directly, which is what retention at the full station
buys.  Used at `rest := done` for the four rows whose guard is retained
(`(Q₁∨Q₂) ⊃ N`, `↓↑P′ ⊃ N`, `↓(M₁∧M₂) ⊃ N`, `↓(Q′ ⊃ N′) ⊃ N`). -/
def atkPark {j : JD} {Q : Pos} {N A₁ A₂ G : Neg} {rest Γ' : List Neg}
    (hx : Neg.and A₁ A₂ ∈ Γ')
    (hX : Neg.imp Q N ∈ Γ')
    (hrest : Sub rest Γ')
    (D₁ : Inv (A₁ :: rest) [] .tru (.up Q))
    (D₂ : Inv (A₂ :: N :: rest) [] j G) : Inv Γ' [] j G :=
  let dM' : Inv Γ' [] .tru (.up Q) :=
    simHyp
      (fl := fun hs lf => .lfoc (hs _ hx) (.and1 lf))
      hrest
      D₁
  simHyp
    (fl := fun hs lf => .lfoc (hs _ hX)
      (.impL (unStable (dM'.wk hs)) lf))
    (Sub.refl Γ')
    (simHyp
      (fl := fun hs lf =>
        .lfoc (hs _ (List.mem_cons_of_mem _ hx)) (.and2 lf))
      (Sub.cons N hrest)
      D₂)

/-- `atkCimp` is the instance of `atkPark` at `Q := ↓◯Q′`; kept as a
check that the generalisation is faithful. -/
example {j : JD} {Q' : Pos} {N A₁ A₂ G : Neg} {rest Γ' : List Neg}
    (hx : Neg.and A₁ A₂ ∈ Γ')
    (hX : Neg.imp (.down (.circ Q')) N ∈ Γ')
    (hrest : Sub rest Γ')
    (D₁ : Inv (A₁ :: rest) [] .tru (.up (.down (.circ Q'))))
    (D₂ : Inv (A₂ :: N :: rest) [] j G) :
    atkPark hx hX hrest D₁ D₂ = atkCimp hx hX hrest D₁ D₂ := rfl

/-- The fire step of `aSoundP`, generic in the interpolant formula `A`:
`fireASound` (`LJF/OCore.lean`) with `interp p [N'] rest (some G)`
abstracted, since the term never inspects it.  One term for every goal
shape and every fuel. -/
def fireASoundP {done : List Neg} {a : String} {N' : Neg}
    {rest : List Neg} {G A : Neg}
    (hf : findFire done (splits done) = some (a, N', rest))
    (rec : Inv (A :: ([N'] ++ rest)) [] .tru G) :
    Inv (A :: done) [] .tru G :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_of_mem _
          (splits_mem (findFire_mem hf))))
        (.impL (.rfoc (.init (hs _ (List.mem_cons_of_mem _
          (atomMem_mem (findFire_atom hf)))))) lf))
    (Sub.cons _ (splits_sub (findFire_mem hf)))
    (rec.wk (by
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))

set_option maxHeartbeats 12000000 in
mutual

/-- **E1 at every fuel.**  The station derives its own `∃p`-approximant:

    Inv (todo ++ done) [] .tru (interpP p f todo done none)

`eSound`'s proof, clause for clause, at fuel `f+1`; `nTopIntro` at 0. -/
def eSoundP (p : String) : ∀ (f : Nat) (todo done : List Neg),
    Inv (todo ++ done) [] .tru (interpP p f todo done none)
  | 0, _, _ => by
      rw [interpP]
      exact nTopIntro
  | f+1, .up (.atom a) :: todo, done => by
      rw [interpP]
      exact (eSoundP p f todo (.up (.atom a) :: done)).wk subPark
  | f+1, .up .fls :: todo, done => by
      rw [interpP]
      exact .stable (.lfoc (List.mem_cons_self ..) (.rel .flsL))
  | f+1, .up (.or P Q) :: todo, done => by
      rw [interpP]
      refine upMerge _ (List.mem_cons_self ..) ?_
      intro b hb
      refine nOrAllIntro
        (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩)) ?_
      exact (eSoundP p f (b ++ todo) done).wk subBranch1
  | f+1, .up (.down M) :: todo, done => by
      rw [interpP]
      refine upMerge _ (List.mem_cons_self ..) ?_
      intro b hb
      simp only [invertPos, List.mem_singleton] at hb
      subst hb
      exact (eSoundP p f (M :: todo) done).wk (Sub.cons M (Sub.grow _))
  | f+1, .and M N :: todo, done => by
      rw [interpP]
      exact simHyp
        (fl := fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
        (Sub.refl _)
        (simHyp
          (fl := fun hs lf =>
            .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
              (.and1 lf))
          (Sub.cons N (Sub.grow _))
          (eSoundP p f (M :: N :: todo) done))
  | f+1, .imp .fls N :: todo, done => by
      rw [interpP]
      exact (eSoundP p f todo done).wk (Sub.grow _)
  | f+1, .imp (.atom a) N :: todo, done => by
      rw [interpP]
      exact (eSoundP p f todo (.imp (.atom a) N :: done)).wk subPark
  | f+1, .circ Q :: todo, done => by
      rw [interpP]
      exact (eSoundP p f todo (.circ Q :: done)).wk subPark
  | f+1, .imp (.down (.circ Q')) N :: todo, done => by
      rw [interpP]
      exact (eSoundP p f todo (.imp (.down (.circ Q')) N :: done)).wk subPark
  | f+1, .imp (.or Q₁ Q₂) N :: todo, done => by
      rw [interpP]
      exact (eSoundP p f todo (.imp (.or Q₁ Q₂) N :: done)).wk subPark
  | f+1, .imp (.down (.up P')) N :: todo, done => by
      rw [interpP]
      exact (eSoundP p f todo (.imp (.down (.up P')) N :: done)).wk subPark
  | f+1, .imp (.down (.and M₁ M₂)) N :: todo, done => by
      rw [interpP]
      exact (eSoundP p f todo (.imp (.down (.and M₁ M₂)) N :: done)).wk subPark
  | f+1, .imp (.down (.imp Q' N')) N :: todo, done => by
      rw [interpP]
      exact (eSoundP p f todo (.imp (.down (.imp Q' N')) N :: done)).wk subPark
  | f+1, [], done => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N, rest) =>
          simp only [hf]
          exact simHyp
            (fl := fun hs lf =>
              .lfoc (hs _ (splits_mem (findFire_mem hf)))
                (.impL (.rfoc (.init (hs _ (atomMem_mem (findFire_atom hf)))))
                  lf))
            (splits_sub (findFire_mem hf))
            (eSoundP p f [N] rest)
      | none =>
          simp only [hf]
          refine nAndAllIntro ?_
          intro x hx
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
          subst hEq
          cases X with
          | up P0 =>
              cases P0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]; exact nTopIntro
                  · simp only [pGuard, if_neg hap]
                    exact .stable (.rfoc (.init (splits_mem hXr)))
              | fls => exact nTopIntro
              | or _ _ => exact nTopIntro
              | down _ => exact nTopIntro
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]; exact nTopIntro
                  · simp only [pGuard, if_neg hap]
                    refine .impR (.atomL ?_)
                    exact simHyp
                      (fl := fun hs lf =>
                        .lfoc (hs _ (List.mem_cons_of_mem _ (splits_mem hXr)))
                          (.impL (.rfoc (.init (hs _ (List.mem_cons_self ..))))
                            lf))
                      (fun Z hZ =>
                        List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                      (eSoundP p f [N] rest)
              | fls => exact nTopIntro
              | or Qa Qb =>
                  -- newly parked `(Qa∨Qb) ⊃ N`: the ◯-implication row's form
                  refine .andR (.impR (.downL ?_))
                    ((eSoundP p f [] rest).wk (splits_sub hXr))
                  have dArg : Inv (interpP p f [] done
                      (some (.up (.or Qa Qb))) :: ([] ++ done)) [] .tru (.up (.or Qa Qb)) :=
                    aSoundP p f [] done (.up (.or Qa Qb))
                  exact simHyp
                    (fl := fun hs lf =>
                      .lfoc (hs _ (List.mem_cons_of_mem _ (splits_mem hXr)))
                        (.impL (unStable (dArg.wk hs)) lf))
                    (fun Z hZ =>
                      List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                    (eSoundP p f [N] rest)
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      -- newly parked `↓↑Pa ⊃ N`
                      refine .andR (.impR (.downL ?_))
                        ((eSoundP p f [] rest).wk (splits_sub hXr))
                      have dArg : Inv (interpP p f [] done
                          (some (.up (.down (.up Pa)))) :: ([] ++ done)) [] .tru (.up (.down (.up Pa))) :=
                        aSoundP p f [] done (.up (.down (.up Pa)))
                      exact simHyp
                        (fl := fun hs lf =>
                          .lfoc (hs _ (List.mem_cons_of_mem _ (splits_mem hXr)))
                            (.impL (unStable (dArg.wk hs)) lf))
                        (fun Z hZ =>
                          List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                        (eSoundP p f [N] rest)
                  | and Ma Mb =>
                      -- newly parked `↓(Ma∧Mb) ⊃ N`
                      refine .andR (.impR (.downL ?_))
                        ((eSoundP p f [] rest).wk (splits_sub hXr))
                      have dArg : Inv (interpP p f [] done
                          (some (.up (.down (.and Ma Mb)))) :: ([] ++ done)) [] .tru (.up (.down (.and Ma Mb))) :=
                        aSoundP p f [] done (.up (.down (.and Ma Mb)))
                      exact simHyp
                        (fl := fun hs lf =>
                          .lfoc (hs _ (List.mem_cons_of_mem _ (splits_mem hXr)))
                            (.impL (unStable (dArg.wk hs)) lf))
                        (fun Z hZ =>
                          List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                        (eSoundP p f [N] rest)

                  | circ Q' =>
                      -- the modal Dyckhoff pair: the fire guarded by the ∀p
                      -- of (done ⇒ ◯Q′) — the RETAINED station, where
                      -- `interp` guards at (rest ⇒ ◯Q′) — PAIRED with the
                      -- ∃p of rest; the argument comes from aSoundP at the
                      -- ◯-goal — the E1/A1 interlock
                      refine .andR (.impR (.downL ?_))
                        ((eSoundP p f [] rest).wk (splits_sub hXr))
                      -- RETENTION: the guard is `A(done ⇒ ↑↓◯Q′)`, at the FULL
                      -- station, so `aSoundP` at `done` delivers it verbatim —
                      -- no weakening from `rest` is needed here at all.
                      have dArg : Inv (interpP p f [] done (some (.up (.down (.circ Q')))) ::
                          ([] ++ done)) [] .tru (.up (.down (.circ Q'))) :=
                        aSoundP p f [] done (.up (.down (.circ Q')))
                      exact simHyp
                        (fl := fun hs lf =>
                          .lfoc (hs _ (List.mem_cons_of_mem _ (splits_mem hXr)))
                            (.impL (unStable (dArg.wk hs)) lf))
                        (fun Z hZ =>
                          List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                        (eSoundP p f [N] rest)
                  | imp Q' N' =>
                      -- RETENTION on the Dyckhoff row: the guard is
                      -- `A(done ⇒ Q′⊃N′)`, at the FULL station, so
                      -- `aSoundP` at `done` delivers it verbatim — the
                      -- residual simulator `resSim` is needed only for
                      -- the unchanged E-side component.
                      refine .andR (.impR (.downL ?_))
                        (simHyp (fl := resSim (splits_mem hXr))
                          (splits_sub hXr)
                          (eSoundP p f [.imp (.down N') N] rest))
                      have dM' : Inv (interpP p f [] done
                          (some (.imp Q' N')) :: ([] ++ done)) []
                          .tru (.imp Q' N') :=
                        aSoundP p f [] done (.imp Q' N')
                      exact simHyp
                        (fl := fun hs lf =>
                          .lfoc (hs _ (List.mem_cons_of_mem _
                              (splits_mem hXr)))
                            (.impL (.rfoc (.rel (dM'.wk hs))) lf))
                        (fun Z hZ =>
                          List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                        (eSoundP p f [N] rest)
          | and _ _ => exact nTopIntro
          | circ Q =>
              -- the box conjunct ◯(↓E(↑Q :: rest)): circR into the lax
              -- phase, open the parked box, invert per branch, laxOf at
              -- the leaf, and eSound at the opened station — uses of the
              -- whole ↑Q mediated by extract along the branch
              refine .circR (.stable (.lfoc (splits_mem hXr)
                (.circL (invBranches Q (fun b hb => ?_)))))
              refine .stable (.laxOf (.rfoc (.rel ?_)))
              exact simHyp (H := .up Q)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (fun Z hZ => List.mem_append_right b (splits_sub hXr Z hZ))
                (eSoundP p f [.up Q] rest)

  termination_by f _ _ => f
  decreasing_by all_goals (simp_wf; try omega)

/-- **A1 at every fuel.**  The `∀p`-approximant beside the station derives
the goal:

    Inv (interpP p f todo done (some G) :: (todo ++ done)) [] .tru G

`aSound`'s proof, clause for clause, at fuel `f+1`; `nBotElim` at 0. -/
def aSoundP (p : String) : ∀ (f : Nat) (todo done : List Neg) (G : Neg),
    Inv (interpP p f todo done (some G) :: (todo ++ done)) [] .tru G
  | 0, _, _, G => by
      rw [interpP]
      exact nBotElim G (List.mem_cons_self ..)
  | f+1, .up (.atom a) :: todo, done, G => by
      rw [interpP]
      exact (aSoundP p f todo (.up (.atom a) :: done) G).wk (Sub.cons _ subPark)
  | f+1, .up .fls :: todo, done, G => by
      rw [interpP]
      exact upMerge G (R := .fls)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (fun _ hb => by simp [invertPos] at hb)
  | f+1, .up (.or P Q) :: todo, done, G => by
      rw [interpP]
      refine upMerge G (R := .or P Q)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
      intro b hb
      exact simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_append_right _ (List.mem_cons_self ..)))
            (lfocAndAll (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩))
              (.impL
                (.rfoc (.rel ((eSoundP p f (b ++ todo) done).wk (fun Z hZ =>
                  hs _ (subBranch2 Z (by
                    rcases List.mem_append.mp hZ with hZ | hZ
                    · exact List.mem_append_left _ hZ
                    · exact List.mem_append_right _ hZ))))))
                lf)))
        (subBranch2)
        (aSoundP p f (b ++ todo) done G)
  | f+1, .up (.down M) :: todo, done, G => by
      rw [interpP]
      refine upMerge G (R := .down M)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
      intro b hb
      simp only [invertPos, List.mem_singleton] at hb
      subst hb
      exact (aSoundP p f (M :: todo) done G).wk (by
        intro Z hZ
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ hZ)))
  | f+1, .and M N :: todo, done, G => by
      rw [interpP]
      exact simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            (.and2 lf))
        (Sub.refl _)
        (simHyp
          (fl := fun hs lf =>
            .lfoc (hs _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (.and1 lf))
          (Sub.cons N (Sub.cons _ (Sub.grow _)))
          ((aSoundP p f (M :: N :: todo) done G).wk (by
            intro Z hZ
            rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_self ..))
            · rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ hZ)))))
  | f+1, .imp .fls N :: todo, done, G => by
      rw [interpP]
      exact (aSoundP p f todo done G).wk (Sub.cons _ (Sub.grow _))
  | f+1, .imp (.atom a) N :: todo, done, G => by
      rw [interpP]
      exact (aSoundP p f todo (.imp (.atom a) N :: done) G).wk (Sub.cons _ subPark)
  | f+1, .circ Q :: todo, done, G => by
      rw [interpP]
      exact (aSoundP p f todo (.circ Q :: done) G).wk (Sub.cons _ subPark)
  | f+1, .imp (.down (.circ Q')) N :: todo, done, G => by
      rw [interpP]
      exact (aSoundP p f todo (.imp (.down (.circ Q')) N :: done) G).wk
        (Sub.cons _ subPark)
  | f+1, .imp (.or Q₁ Q₂) N :: todo, done, G => by
      rw [interpP]
      exact (aSoundP p f todo (.imp (.or Q₁ Q₂) N :: done) G).wk
        (Sub.cons _ subPark)
  | f+1, .imp (.down (.up P')) N :: todo, done, G => by
      rw [interpP]
      exact (aSoundP p f todo (.imp (.down (.up P')) N :: done) G).wk
        (Sub.cons _ subPark)
  | f+1, .imp (.down (.and M₁ M₂)) N :: todo, done, G => by
      rw [interpP]
      exact (aSoundP p f todo (.imp (.down (.and M₁ M₂)) N :: done) G).wk
        (Sub.cons _ subPark)
  | f+1, .imp (.down (.imp Q' N')) N :: todo, done, G => by
      rw [interpP]
      exact (aSoundP p f todo (.imp (.down (.imp Q' N')) N :: done) G).wk
        (Sub.cons _ subPark)
  | f+1, [], done, .imp Q N => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.imp Q N))
      | none =>
          simp only [hf]
          refine .impR (invBranches Q ?_)
          intro b hb
          exact simHyp
            (fl := fun hs lf =>
              .lfoc (hs _ (List.mem_append_right _ (List.mem_cons_self ..)))
                (lfocAndAll
                  (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩))
                  (.impL
                    (.rfoc (.rel ((eSoundP p f b done).wk (fun Z hZ => hs _ (by
                      rcases List.mem_append.mp hZ with hZ | hZ
                      · exact List.mem_append_left _ hZ
                      · exact List.mem_append_right _
                          (List.mem_cons_of_mem _ hZ))))))
                    lf)))
            (fun Z hZ => by
              rcases List.mem_append.mp hZ with hZ | hZ
              · exact List.mem_append_left _ hZ
              · exact List.mem_append_right _ (List.mem_cons_of_mem _
                  (List.mem_append_right _ hZ)))
            (aSoundP p f b done N)
  | f+1, [], done, .and M N => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.and M N))
      | none =>
          simp only [hf]
          refine .andR ?_ ?_
          · exact simHyp
              (fl := fun hs lf =>
                .lfoc (hs _ (List.mem_cons_self ..)) (.and1 lf))
              (Sub.grow _)
              (aSoundP p f [] done M)
          · exact simHyp
              (fl := fun hs lf =>
                .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
              (Sub.grow _)
              (aSoundP p f [] done N)
  | f+1, [], done, .up (.atom q) => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.up (.atom q)))
      | none =>
          simp only [hf]
          by_cases hq : atomMem q done = true
          · simp only [hq, if_true]
            exact .stable (.rfoc (.init (List.mem_cons_of_mem _
              (atomMem_mem hq))))
          · simp only [hq, if_false]
            refine nOrAllElim _ (List.mem_cons_self ..) ?_
            intro x hx Γ' hsub
            if hx1 : x ∈ atomHead p q then
              by_cases hqp : q = p
              · simp [atomHead, hqp] at hx1
              · simp only [atomHead, if_neg hqp, List.mem_singleton] at hx1
                subst hx1
                exact .stable (.rfoc (.init (List.mem_cons_self ..)))
            else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.up (.atom q)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.up (.atom q))).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.up (.atom q))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.up (.atom q))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.up (.atom q))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.up (.atom q))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)
  | f+1, [], done, .up .fls => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.up .fls))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ ([] : List Neg) then
            exact absurd hx1 (List.not_mem_nil)
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.up .fls))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.up .fls)).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.up .fls)).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.up .fls)).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.up .fls)).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.up .fls)).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)
  | f+1, [], done, .up (.or P₁ P₂) => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.up (.or P₁ P₂)))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interpP p f [] done (some (.up P₁)),
              interpP p f [] done (some (.up P₂))] then
            if e1 : x = interpP p f [] done (some (.up P₁)) then
              subst e1
              exact .stable (stabOr1 (unStable ((aSoundP p f [] done
                (.up P₁)).wk (by
                  intro Z hZ
                  rcases List.mem_cons.mp hZ with rfl | hZ
                  · exact List.mem_cons_self ..
                  · exact List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ))))))
            else
              have e2 : x = interpP p f [] done (some (.up P₂)) := by
                rcases List.mem_cons.mp hx1 with h | h
                · exact absurd h e1
                · exact List.mem_singleton.mp h
              subst e2
              exact .stable (stabOr2 (unStable ((aSoundP p f [] done
                (.up P₂)).wk (by
                  intro Z hZ
                  rcases List.mem_cons.mp hZ with rfl | hZ
                  · exact List.mem_cons_self ..
                  · exact List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.up (.or P₁ P₂)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.up (.or P₁ P₂))).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.up (.or P₁ P₂))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.up (.or P₁ P₂))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.up (.or P₁ P₂))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.up (.or P₁ P₂))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)
  | f+1, [], done, .up (.down M) => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.up (.down M)))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interpP p f [] done (some M)] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .stable (.rfoc (.rel ((aSoundP p f [] done M).wk (by
              intro Z hZ
              rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _
                  (hsub _ (List.mem_cons_of_mem _ hZ))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.up (.down M)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.up (.down M))).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.up (.down M))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.up (.down M))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.up (.down M))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.up (.down M))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)

  | f+1, [], done, .circ (.atom q) => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.circ (.atom q)))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpP p f [] done (some (.up (.atom q)))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSoundP p f [] done (.up (.atom q))).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ)))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsubD _ ((splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsubD _ ((splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.circ (.atom q)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsubD _ (hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.circ (.atom q))).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.circ (.atom q))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.circ (.atom q))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.circ (.atom q))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.circ (.atom q))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundP), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundP there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpP p f [.up R] rest none))
                    (interpP p f [.up R] rest (some (.circ (.atom q)))) :: Γ')) []
                  .tru (interpP p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundP p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundP p f [.up R] rest (.circ (.atom q)))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpP p f [.up R] rest (some (.circ (.atom q))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))))
                  (circROf D))))


  | f+1, [], done, .circ .fls => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.circ .fls))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpP p f [] done (some (.up .fls))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSoundP p f [] done (.up .fls)).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ)))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsubD _ ((splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsubD _ ((splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.circ .fls))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsubD _ (hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.circ .fls)).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.circ .fls)).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.circ .fls)).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.circ .fls)).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.circ .fls)).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundP), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundP there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpP p f [.up R] rest none))
                    (interpP p f [.up R] rest (some (.circ .fls))) :: Γ')) []
                  .tru (interpP p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundP p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundP p f [.up R] rest (.circ .fls))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpP p f [.up R] rest (some (.circ .fls)))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))))
                  (circROf D))))


  | f+1, [], done, .circ (.or P₁ P₂) => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.circ (.or P₁ P₂)))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if he1 : x = interpP p f [] done (some (.circ P₁)) then
            subst he1
            exact .circR (.stable (stabOr1 (unStable (circROf
                ((aSoundP p f [] done (.circ P₁)).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ))))))))
          else if he2 : x = interpP p f [] done (some (.circ P₂)) then
            subst he2
            exact .circR (.stable (stabOr2 (unStable (circROf
                ((aSoundP p f [] done (.circ P₂)).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ))))))))
          else if he3 : x = interpP p f [] done (some (.up (.or P₁ P₂))) then
            subst he3
            exact .circR (.stable (.laxOf (unStable
              ((aSoundP p f [] done (.up (.or P₁ P₂))).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ)))))))
          else
          have hx2 := (List.mem_append.mp hx).resolve_left (by
            intro h
            rcases List.mem_cons.mp h with h | h
            · exact he1 h
            · rcases List.mem_cons.mp h with h | h
              · exact he2 h
              · exact he3 (List.mem_singleton.mp h))
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsubD _ ((splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsubD _ ((splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.circ (.or P₁ P₂)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsubD _ (hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.circ (.or P₁ P₂))).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.circ (.or P₁ P₂))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.circ (.or P₁ P₂))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.circ (.or P₁ P₂))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.circ (.or P₁ P₂))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundP), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundP there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpP p f [.up R] rest none))
                    (interpP p f [.up R] rest (some (.circ (.or P₁ P₂)))) :: Γ')) []
                  .tru (interpP p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundP p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundP p f [.up R] rest (.circ (.or P₁ P₂)))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpP p f [.up R] rest (some (.circ (.or P₁ P₂))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))))
                  (circROf D))))


  | f+1, [], done, .circ (.down (.up P')) => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.circ (.down (.up P'))))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpP p f [] done (some (.circ P'))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.rfoc (.rel (circROf
              ((aSoundP p f [] done (.circ P')).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ))))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsubD _ ((splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsubD _ ((splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.circ (.down (.up P'))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsubD _ (hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.circ (.down (.up P')))).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.circ (.down (.up P')))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.circ (.down (.up P')))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.circ (.down (.up P')))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.circ (.down (.up P')))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundP), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundP there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpP p f [.up R] rest none))
                    (interpP p f [.up R] rest (some (.circ (.down (.up P'))))) :: Γ')) []
                  .tru (interpP p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundP p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundP p f [.up R] rest (.circ (.down (.up P'))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpP p f [.up R] rest (some (.circ (.down (.up P')))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))))
                  (circROf D))))


  | f+1, [], done, .circ (.down (.circ P')) => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.circ (.down (.circ P'))))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpP p f [] done (some (.circ P'))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.rfoc (.rel (.circR (circROf
              ((aSoundP p f [] done (.circ P')).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ)))))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsubD _ ((splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsubD _ ((splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.circ (.down (.circ P'))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsubD _ (hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.circ (.down (.circ P')))).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.circ (.down (.circ P')))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.circ (.down (.circ P')))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.circ (.down (.circ P')))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.circ (.down (.circ P')))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundP), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundP there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpP p f [.up R] rest none))
                    (interpP p f [.up R] rest (some (.circ (.down (.circ P'))))) :: Γ')) []
                  .tru (interpP p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundP p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundP p f [.up R] rest (.circ (.down (.circ P'))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpP p f [.up R] rest (some (.circ (.down (.circ P')))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))))
                  (circROf D))))


  | f+1, [], done, .circ (.down (.and M₁ M₂)) => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.circ (.down (.and M₁ M₂))))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpP p f [] done (some (.up (.down (.and M₁ M₂))))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSoundP p f [] done (.up (.down (.and M₁ M₂)))).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ)))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsubD _ ((splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsubD _ ((splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.circ (.down (.and M₁ M₂))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsubD _ (hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.circ (.down (.and M₁ M₂)))).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.circ (.down (.and M₁ M₂)))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.circ (.down (.and M₁ M₂)))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.circ (.down (.and M₁ M₂)))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.circ (.down (.and M₁ M₂)))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundP), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundP there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpP p f [.up R] rest none))
                    (interpP p f [.up R] rest (some (.circ (.down (.and M₁ M₂))))) :: Γ')) []
                  .tru (interpP p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundP p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundP p f [.up R] rest (.circ (.down (.and M₁ M₂))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpP p f [.up R] rest (some (.circ (.down (.and M₁ M₂)))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))))
                  (circROf D))))


  | f+1, [], done, .circ (.down (.imp Q₀ N₀)) => by
      rw [interpP]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundP hf (aSoundP p f [N'] rest (.circ (.down (.imp Q₀ N₀))))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpP p f [] done (some (.up (.down (.imp Q₀ N₀))))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSoundP p f [] done (.up (.down (.imp Q₀ N₀)))).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ)))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsubD _ ((splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsubD _ ((splits_sub hXr Z hZ))))
                      (aSoundP p f [N] rest (.circ (.down (.imp Q₀ N₀))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or Qa Qb =>
                  exact atkPark (List.mem_cons_self ..)
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_mem hXr))))
                    (fun Z hZ => List.mem_cons_of_mem _
                      (hsubD _ (hZ)))
                    (aSoundP p f [] done (.up (.or Qa Qb)))
                    ((aSoundP p f [N] rest (.circ (.down (.imp Q₀ N₀)))).wk
                      (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
              | down M0 =>
                  cases M0 with
                  | up Pa =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.up Pa))))
                        ((aSoundP p f [N] rest (.circ (.down (.imp Q₀ N₀)))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | and Ma Mb =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.and Ma Mb))))
                        ((aSoundP p f [N] rest (.circ (.down (.imp Q₀ N₀)))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | imp Q' N' =>
                      exact atkPark (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (.stable (.rfoc (.rel (aSoundP p f [] done (.imp Q' N')))))
                        ((aSoundP p f [N] rest (.circ (.down (.imp Q₀ N₀)))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundP p f [] done (.up (.down (.circ Q'))))
                        ((aSoundP p f [N] rest (.circ (.down (.imp Q₀ N₀)))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundP), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundP there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpP p f [.up R] rest none))
                    (interpP p f [.up R] rest (some (.circ (.down (.imp Q₀ N₀))))) :: Γ')) []
                  .tru (interpP p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundP p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundP p f [.up R] rest (.circ (.down (.imp Q₀ N₀))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpP p f [.up R] rest (some (.circ (.down (.imp Q₀ N₀)))))
                  (fl := fun hs lf =>
                    .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_self ..))))
                      (.impL (.rfoc (.rel (dE.wk (fun Z hZ =>
                        hs Z (List.mem_cons_of_mem _ hZ))))) lf))
                  (fun Z hZ => by
                    rcases List.mem_cons.mp hZ with rfl | hZ
                    · exact List.mem_cons_self ..
                    · exact List.mem_cons_of_mem _ (List.mem_append_right b
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))))
                  (circROf D))))

  termination_by f _ _ _ => f
  decreasing_by all_goals (simp_wf; try omega)

end


/-! ## The two statements, witnessed -/

/-- E1 at every fuel, for `interpP`, as a type. -/
def ESoundP' (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg),
    Inv (todo ++ done) [] .tru (interpP p f todo done none)

/-- A1 at every fuel, for `interpP`, as a type. -/
def ASoundP' (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg) (G : Neg),
    Inv (interpP p f todo done (some G) :: (todo ++ done)) [] .tru G

/-- `ESoundP` is inhabited. -/
def eSoundPWitness (p : String) : ESoundP' p := eSoundP p

/-- `ASoundP` is inhabited. -/
def aSoundPWitness (p : String) : ASoundP' p := aSoundP p

end LJFO

/-! ## Pins

The commissioned bound first — `eSound`/`aSound`'s own pinned set — then
the MEASURED set, which is smaller, as it is for the `interpF` pair: the
fuel recursion spends no `Classical.choice`. -/

#axioms_within LJFO.atkPark [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.eSoundP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.aSoundP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.eSoundPWitness [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.aSoundPWitness [propext, Classical.choice, Quot.sound]

#axioms_within LJFO.atkPark [propext, Quot.sound]
#axioms_within LJFO.eSoundP [propext, Quot.sound]
#axioms_within LJFO.aSoundP [propext, Quot.sound]
#axioms_within LJFO.eSoundPWitness [propext, Quot.sound]
#axioms_within LJFO.aSoundPWitness [propext, Quot.sound]
