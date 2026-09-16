/-
LJF◯ — soundness of the fuel-founded retention interpolant (route (B),
layer 4b).

`eSoundF` / `aSoundF`: the two halves of `LJF/OCore.lean`'s `eSound` /
`aSound`, ported clause for clause to `interpF` (`LJF/OFuel.lean`).  The
statements are `wip/ui_routeB_statements.lean`'s `ESoundF` / `ASoundF`:

    eSoundF p : ∀ f todo done,   Inv (todo ++ done) [] .tru (interpF p f todo done none)
    aSoundF p : ∀ f todo done G, Inv (interpF p f todo done (some G) :: (todo ++ done)) [] .tru G

Three things differ from the weight-founded originals, and nothing else:

* **the recursion.**  `interpF` is founded on structural fuel, so the
  mutual is founded on the fuel too: `termination_by f`, every recursive
  call at `f`.  None of `interp`'s weight inequalities is spent, and the
  `ljf_dec_sound` farm is not needed.

* **fuel 0.**  `interpF p 0 _ _ none = nTop` and `interpF p 0 _ _ (some G)
  = nBot`, so the base cases are `nTopIntro` and `nBotElim` — every fuel
  level is sound by construction, which is the point of the defaults.

* **the twelve modal rows.**  `interpF` takes the `∀p`-guard of a parked
  `↓◯Q′ ⊃ N` at the FULL station `done`, where `interp` takes it at the
  residual `rest`.  The full station is a superset of the residual, so
  each row goes through by re-instantiating the attack handler at `done`
  and weakening the continuation instead of the guard.  In the ∃p row
  (`eSoundF`) the guard is `aSoundF p f [] done (↑↓◯Q′)` verbatim — the
  original's weakening `rest ⊆ done` disappears.  In the eleven ∀p rows
  the handler `atkCimp` is instantiated at `rest := done`, so its
  `hrest` drops a `splits_sub` and its `D₂` gains one.  No row needed
  anything beyond that.

Nothing in `LJF/OCore.lean` or `LJF/OFuel.lean` is touched; this module is
purely additive.
-/
import LJF.OFuel
import Meta.Audit

namespace LJFO

/-- The fire step of `aSoundF`, generic in the interpolant formula `A`:
`fireASound` (`LJF/OCore.lean`) with `interp p [N'] rest (some G)`
abstracted, since the term never inspects it.  One term for every goal
shape and every fuel. -/
def fireASoundF {done : List Neg} {a : String} {N' : Neg}
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

    Inv (todo ++ done) [] .tru (interpF p f todo done none)

`eSound`'s proof, clause for clause, at fuel `f+1`; `nTopIntro` at 0. -/
def eSoundF (p : String) : ∀ (f : Nat) (todo done : List Neg),
    Inv (todo ++ done) [] .tru (interpF p f todo done none)
  | 0, _, _ => by
      rw [interpF]
      exact nTopIntro
  | f+1, .up (.atom a) :: todo, done => by
      rw [interpF]
      exact (eSoundF p f todo (.up (.atom a) :: done)).wk subPark
  | f+1, .up .fls :: todo, done => by
      rw [interpF]
      exact .stable (.lfoc (List.mem_cons_self ..) (.rel .flsL))
  | f+1, .up (.or P Q) :: todo, done => by
      rw [interpF]
      refine upMerge _ (List.mem_cons_self ..) ?_
      intro b hb
      refine nOrAllIntro
        (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩)) ?_
      exact (eSoundF p f (b ++ todo) done).wk subBranch1
  | f+1, .up (.down M) :: todo, done => by
      rw [interpF]
      refine upMerge _ (List.mem_cons_self ..) ?_
      intro b hb
      simp only [invertPos, List.mem_singleton] at hb
      subst hb
      exact (eSoundF p f (M :: todo) done).wk (Sub.cons M (Sub.grow _))
  | f+1, .and M N :: todo, done => by
      rw [interpF]
      exact simHyp
        (fl := fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
        (Sub.refl _)
        (simHyp
          (fl := fun hs lf =>
            .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
              (.and1 lf))
          (Sub.cons N (Sub.grow _))
          (eSoundF p f (M :: N :: todo) done))
  | f+1, .imp .fls N :: todo, done => by
      rw [interpF]
      exact (eSoundF p f todo done).wk (Sub.grow _)
  | f+1, .imp (.atom a) N :: todo, done => by
      rw [interpF]
      exact (eSoundF p f todo (.imp (.atom a) N :: done)).wk subPark
  | f+1, .circ Q :: todo, done => by
      rw [interpF]
      exact (eSoundF p f todo (.circ Q :: done)).wk subPark
  | f+1, .imp (.down (.circ Q')) N :: todo, done => by
      rw [interpF]
      exact (eSoundF p f todo (.imp (.down (.circ Q')) N :: done)).wk subPark
  | f+1, .imp (.or Q₁ Q₂) N :: todo, done => by
      rw [interpF]
      exact simHyp (H := .imp Q₂ N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_self ..)) (.impL (stabOr2 s) lf1))
        (Sub.refl _)
        (simHyp (H := .imp Q₁ N)
          (fl := fun hs lf => match lf with
            | .impL s lf1 =>
                .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                  (.impL (stabOr1 s) lf1))
          (Sub.cons _ (Sub.grow _))
          (eSoundF p f (.imp Q₁ N :: .imp Q₂ N :: todo) done))
  | f+1, .imp (.down (.up P')) N :: todo, done => by
      rw [interpF]
      exact simHyp (H := .imp P' N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_self ..))
                (.impL (.rfoc (.rel (.stable s))) lf1))
        (Sub.grow _)
        (eSoundF p f (.imp P' N :: todo) done)
  | f+1, .imp (.down (.and M₁ M₂)) N :: todo, done => by
      rw [interpF]
      exact simHyp (H := .imp (.down M₁) (.imp (.down M₂) N))
        (fl := fun {Δa} {_} {_} hs lf => match lf with
          | LFoc.impL s₁ (LFoc.impL s₂ lf2) =>
              routeStabT (Δ₀ := Δa)
                (k := fun {Δb} hsb r₁ =>
                  routeStabT (Δ₀ := Δb)
                    (k := fun {Δc} hsc r₂ =>
                      .lfoc (hsc _ (hsb _ (hs _ (List.mem_cons_self ..))))
                        (.impL
                          (.rfoc (.rel (.andR ((relOf r₁).wk hsc) (relOf r₂))))
                          (lf2.wk (fun Z hZ => hsc _ (hsb _ hZ)))))
                    (Sub.refl _) (s₂.wk hsb))
                (Sub.refl _) s₁)
        (Sub.grow _)
        (eSoundF p f (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done)
  | f+1, .imp (.down (.imp Q' N')) N :: todo, done => by
      rw [interpF]
      exact (eSoundF p f todo (.imp (.down (.imp Q' N')) N :: done)).wk subPark
  | f+1, [], done => by
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N, rest) =>
          simp only [hf]
          exact simHyp
            (fl := fun hs lf =>
              .lfoc (hs _ (splits_mem (findFire_mem hf)))
                (.impL (.rfoc (.init (hs _ (atomMem_mem (findFire_atom hf)))))
                  lf))
            (splits_sub (findFire_mem hf))
            (eSoundF p f [N] rest)
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
                      (eSoundF p f [N] rest)
              | fls => exact nTopIntro
              | or _ _ => exact nTopIntro
              | down M0 =>
                  cases M0 with
                  | up _ => exact nTopIntro
                  | and _ _ => exact nTopIntro

                  | circ Q' =>
                      -- the modal Dyckhoff pair: the fire guarded by the ∀p
                      -- of (done ⇒ ◯Q′) — the RETAINED station, where
                      -- `interp` guards at (rest ⇒ ◯Q′) — PAIRED with the
                      -- ∃p of rest; the argument comes from aSoundF at the
                      -- ◯-goal — the E1/A1 interlock
                      refine .andR (.impR (.downL ?_))
                        ((eSoundF p f [] rest).wk (splits_sub hXr))
                      -- RETENTION: the guard is `A(done ⇒ ↑↓◯Q′)`, at the FULL
                      -- station, so `aSoundF` at `done` delivers it verbatim —
                      -- no weakening from `rest` is needed here at all.
                      have dArg : Inv (interpF p f [] done (some (.up (.down (.circ Q')))) ::
                          ([] ++ done)) [] .tru (.up (.down (.circ Q'))) :=
                        aSoundF p f [] done (.up (.down (.circ Q')))
                      exact simHyp
                        (fl := fun hs lf =>
                          .lfoc (hs _ (List.mem_cons_of_mem _ (splits_mem hXr)))
                            (.impL (unStable (dArg.wk hs)) lf))
                        (fun Z hZ =>
                          List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                        (eSoundF p f [N] rest)
                  | imp Q' N' =>
                      refine .andR (.impR (.downL ?_))
                        (simHyp (fl := resSim (splits_mem hXr))
                          (splits_sub hXr)
                          (eSoundF p f [.imp (.down N') N] rest))
                      have hXd : Neg.imp (.down (.imp Q' N')) N ∈
                          (interpF p f [.imp (.down N') N] rest
                            (some (.imp Q' N')) :: ([] ++ done)) :=
                        List.mem_cons_of_mem _ (splits_mem hXr)
                      have dM' : Inv (interpF p f [.imp (.down N') N] rest
                          (some (.imp Q' N')) :: ([] ++ done)) []
                          .tru (.imp Q' N') :=
                        simHyp (fl := resSim hXd) (Sub.refl _)
                          ((aSoundF p f [.imp (.down N') N] rest
                              (.imp Q' N')).wk (by
                            intro Z hZ
                            rcases List.mem_cons.mp hZ with rfl | hZ
                            · exact List.mem_cons_of_mem _
                                (List.mem_cons_self ..)
                            · rcases List.mem_cons.mp hZ with rfl | hZ
                              · exact List.mem_cons_self ..
                              · exact List.mem_cons_of_mem _
                                  (List.mem_cons_of_mem _
                                    (splits_sub hXr Z hZ))))
                      exact simHyp
                        (fl := fun hs lf =>
                          .lfoc (hs _ hXd)
                            (.impL (.rfoc (.rel (dM'.wk hs))) lf))
                        (fun Z hZ =>
                          List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                        (eSoundF p f [N] rest)
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
                (eSoundF p f [.up Q] rest)

  termination_by f _ _ => f
  decreasing_by all_goals (simp_wf; try omega)

/-- **A1 at every fuel.**  The `∀p`-approximant beside the station derives
the goal:

    Inv (interpF p f todo done (some G) :: (todo ++ done)) [] .tru G

`aSound`'s proof, clause for clause, at fuel `f+1`; `nBotElim` at 0. -/
def aSoundF (p : String) : ∀ (f : Nat) (todo done : List Neg) (G : Neg),
    Inv (interpF p f todo done (some G) :: (todo ++ done)) [] .tru G
  | 0, _, _, G => by
      rw [interpF]
      exact nBotElim G (List.mem_cons_self ..)
  | f+1, .up (.atom a) :: todo, done, G => by
      rw [interpF]
      exact (aSoundF p f todo (.up (.atom a) :: done) G).wk (Sub.cons _ subPark)
  | f+1, .up .fls :: todo, done, G => by
      rw [interpF]
      exact upMerge G (R := .fls)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (fun _ hb => by simp [invertPos] at hb)
  | f+1, .up (.or P Q) :: todo, done, G => by
      rw [interpF]
      refine upMerge G (R := .or P Q)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
      intro b hb
      exact simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_append_right _ (List.mem_cons_self ..)))
            (lfocAndAll (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩))
              (.impL
                (.rfoc (.rel ((eSoundF p f (b ++ todo) done).wk (fun Z hZ =>
                  hs _ (subBranch2 Z (by
                    rcases List.mem_append.mp hZ with hZ | hZ
                    · exact List.mem_append_left _ hZ
                    · exact List.mem_append_right _ hZ))))))
                lf)))
        (subBranch2)
        (aSoundF p f (b ++ todo) done G)
  | f+1, .up (.down M) :: todo, done, G => by
      rw [interpF]
      refine upMerge G (R := .down M)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
      intro b hb
      simp only [invertPos, List.mem_singleton] at hb
      subst hb
      exact (aSoundF p f (M :: todo) done G).wk (by
        intro Z hZ
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ hZ)))
  | f+1, .and M N :: todo, done, G => by
      rw [interpF]
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
          ((aSoundF p f (M :: N :: todo) done G).wk (by
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
      rw [interpF]
      exact (aSoundF p f todo done G).wk (Sub.cons _ (Sub.grow _))
  | f+1, .imp (.atom a) N :: todo, done, G => by
      rw [interpF]
      exact (aSoundF p f todo (.imp (.atom a) N :: done) G).wk (Sub.cons _ subPark)
  | f+1, .circ Q :: todo, done, G => by
      rw [interpF]
      exact (aSoundF p f todo (.circ Q :: done) G).wk (Sub.cons _ subPark)
  | f+1, .imp (.down (.circ Q')) N :: todo, done, G => by
      rw [interpF]
      exact (aSoundF p f todo (.imp (.down (.circ Q')) N :: done) G).wk
        (Sub.cons _ subPark)
  | f+1, .imp (.or Q₁ Q₂) N :: todo, done, G => by
      rw [interpF]
      exact simHyp (H := .imp Q₂ N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                (.impL (stabOr2 s) lf1))
        (Sub.refl _)
        (simHyp (H := .imp Q₁ N)
          (fl := fun hs lf => match lf with
            | .impL s lf1 =>
                .lfoc (hs _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
                  (.impL (stabOr1 s) lf1))
          (Sub.cons _ (Sub.cons _ (Sub.grow _)))
          ((aSoundF p f (.imp Q₁ N :: .imp Q₂ N :: todo) done G).wk (by
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
  | f+1, .imp (.down (.up P')) N :: todo, done, G => by
      rw [interpF]
      exact simHyp (H := .imp P' N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                (.impL (.rfoc (.rel (.stable s))) lf1))
        (Sub.refl _)
        ((aSoundF p f (.imp P' N :: todo) done G).wk (by
          intro Z hZ
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hZ))))
  | f+1, .imp (.down (.and M₁ M₂)) N :: todo, done, G => by
      rw [interpF]
      exact simHyp (H := .imp (.down M₁) (.imp (.down M₂) N))
        (fl := fun {Δa} {_} {_} hs lf => match lf with
          | LFoc.impL s₁ (LFoc.impL s₂ lf2) =>
              routeStabT (Δ₀ := Δa)
                (k := fun {Δb} hsb r₁ =>
                  routeStabT (Δ₀ := Δb)
                    (k := fun {Δc} hsc r₂ =>
                      .lfoc (hsc _ (hsb _ (hs _ (List.mem_cons_of_mem _
                          (List.mem_cons_self ..)))))
                        (.impL
                          (.rfoc (.rel (.andR ((relOf r₁).wk hsc) (relOf r₂))))
                          (lf2.wk (fun Z hZ => hsc _ (hsb _ hZ)))))
                    (Sub.refl _) (s₂.wk hsb))
                (Sub.refl _) s₁)
        (Sub.refl _)
        ((aSoundF p f (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done G).wk (by
          intro Z hZ
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hZ))))
  | f+1, .imp (.down (.imp Q' N')) N :: todo, done, G => by
      rw [interpF]
      exact (aSoundF p f todo (.imp (.down (.imp Q' N')) N :: done) G).wk
        (Sub.cons _ subPark)
  | f+1, [], done, .imp Q N => by
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.imp Q N))
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
                    (.rfoc (.rel ((eSoundF p f b done).wk (fun Z hZ => hs _ (by
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
            (aSoundF p f b done N)
  | f+1, [], done, .and M N => by
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.and M N))
      | none =>
          simp only [hf]
          refine .andR ?_ ?_
          · exact simHyp
              (fl := fun hs lf =>
                .lfoc (hs _ (List.mem_cons_self ..)) (.and1 lf))
              (Sub.grow _)
              (aSoundF p f [] done M)
          · exact simHyp
              (fl := fun hs lf =>
                .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
              (Sub.grow _)
              (aSoundF p f [] done N)
  | f+1, [], done, .up (.atom q) => by
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.up (.atom q)))
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
                      (aSoundF p f [N] rest (.up (.atom q)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.up (.atom q)))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.up (.atom q))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)
  | f+1, [], done, .up .fls => by
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.up .fls))
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
                      (aSoundF p f [N] rest (.up .fls))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.up .fls))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.up .fls)).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)
  | f+1, [], done, .up (.or P₁ P₂) => by
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.up (.or P₁ P₂)))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interpF p f [] done (some (.up P₁)),
              interpF p f [] done (some (.up P₂))] then
            if e1 : x = interpF p f [] done (some (.up P₁)) then
              subst e1
              exact .stable (stabOr1 (unStable ((aSoundF p f [] done
                (.up P₁)).wk (by
                  intro Z hZ
                  rcases List.mem_cons.mp hZ with rfl | hZ
                  · exact List.mem_cons_self ..
                  · exact List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ))))))
            else
              have e2 : x = interpF p f [] done (some (.up P₂)) := by
                rcases List.mem_cons.mp hx1 with h | h
                · exact absurd h e1
                · exact List.mem_singleton.mp h
              subst e2
              exact .stable (stabOr2 (unStable ((aSoundF p f [] done
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
                      (aSoundF p f [N] rest (.up (.or P₁ P₂)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.up (.or P₁ P₂)))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.up (.or P₁ P₂))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)
  | f+1, [], done, .up (.down M) => by
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.up (.down M)))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interpF p f [] done (some M)] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .stable (.rfoc (.rel ((aSoundF p f [] done M).wk (by
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
                      (aSoundF p f [N] rest (.up (.down M)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.up (.down M)))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.up (.down M))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ _ => exact nBotElim _ (List.mem_cons_self ..)

  | f+1, [], done, .circ (.atom q) => by
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.circ (.atom q)))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpF p f [] done (some (.up (.atom q)))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSoundF p f [] done (.up (.atom q))).wk (by
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
                      (aSoundF p f [N] rest (.circ (.atom q)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.circ (.atom q)))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.circ (.atom q))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundF), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundF there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpF p f [.up R] rest none))
                    (interpF p f [.up R] rest (some (.circ (.atom q)))) :: Γ')) []
                  .tru (interpF p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundF p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundF p f [.up R] rest (.circ (.atom q)))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpF p f [.up R] rest (some (.circ (.atom q))))
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
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.circ .fls))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpF p f [] done (some (.up .fls))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSoundF p f [] done (.up .fls)).wk (by
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
                      (aSoundF p f [N] rest (.circ .fls))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.circ .fls))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.circ .fls)).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundF), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundF there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpF p f [.up R] rest none))
                    (interpF p f [.up R] rest (some (.circ .fls))) :: Γ')) []
                  .tru (interpF p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundF p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundF p f [.up R] rest (.circ .fls))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpF p f [.up R] rest (some (.circ .fls)))
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
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.circ (.or P₁ P₂)))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if he1 : x = interpF p f [] done (some (.circ P₁)) then
            subst he1
            exact .circR (.stable (stabOr1 (unStable (circROf
                ((aSoundF p f [] done (.circ P₁)).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ))))))))
          else if he2 : x = interpF p f [] done (some (.circ P₂)) then
            subst he2
            exact .circR (.stable (stabOr2 (unStable (circROf
                ((aSoundF p f [] done (.circ P₂)).wk (by
                intro Z hZ
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _
                    (hsubD _ (hZ))))))))
          else if he3 : x = interpF p f [] done (some (.up (.or P₁ P₂))) then
            subst he3
            exact .circR (.stable (.laxOf (unStable
              ((aSoundF p f [] done (.up (.or P₁ P₂))).wk (by
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
                      (aSoundF p f [N] rest (.circ (.or P₁ P₂)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.circ (.or P₁ P₂)))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.circ (.or P₁ P₂))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundF), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundF there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpF p f [.up R] rest none))
                    (interpF p f [.up R] rest (some (.circ (.or P₁ P₂)))) :: Γ')) []
                  .tru (interpF p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundF p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundF p f [.up R] rest (.circ (.or P₁ P₂)))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpF p f [.up R] rest (some (.circ (.or P₁ P₂))))
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
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.circ (.down (.up P'))))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpF p f [] done (some (.circ P'))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.rfoc (.rel (circROf
              ((aSoundF p f [] done (.circ P')).wk (by
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
                      (aSoundF p f [N] rest (.circ (.down (.up P'))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.circ (.down (.up P'))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.circ (.down (.up P')))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundF), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundF there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpF p f [.up R] rest none))
                    (interpF p f [.up R] rest (some (.circ (.down (.up P'))))) :: Γ')) []
                  .tru (interpF p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundF p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundF p f [.up R] rest (.circ (.down (.up P'))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpF p f [.up R] rest (some (.circ (.down (.up P')))))
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
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.circ (.down (.circ P'))))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpF p f [] done (some (.circ P'))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.rfoc (.rel (.circR (circROf
              ((aSoundF p f [] done (.circ P')).wk (by
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
                      (aSoundF p f [N] rest (.circ (.down (.circ P'))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.circ (.down (.circ P'))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.circ (.down (.circ P')))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundF), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundF there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpF p f [.up R] rest none))
                    (interpF p f [.up R] rest (some (.circ (.down (.circ P'))))) :: Γ')) []
                  .tru (interpF p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundF p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundF p f [.up R] rest (.circ (.down (.circ P'))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpF p f [.up R] rest (some (.circ (.down (.circ P')))))
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
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.circ (.down (.and M₁ M₂))))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpF p f [] done (some (.up (.down (.and M₁ M₂))))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSoundF p f [] done (.up (.down (.and M₁ M₂)))).wk (by
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
                      (aSoundF p f [N] rest (.circ (.down (.and M₁ M₂))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.circ (.down (.and M₁ M₂))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.circ (.down (.and M₁ M₂)))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundF), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundF there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpF p f [.up R] rest none))
                    (interpF p f [.up R] rest (some (.circ (.down (.and M₁ M₂))))) :: Γ')) []
                  .tru (interpF p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundF p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundF p f [.up R] rest (.circ (.down (.and M₁ M₂))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpF p f [.up R] rest (some (.circ (.down (.and M₁ M₂)))))
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
      rw [interpF]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASoundF hf (aSoundF p f [N'] rest (.circ (.down (.imp Q₀ N₀))))
      | none =>
          simp only [hf]
          refine .circR (.stable (.lfoc (List.mem_cons_self ..)
            (.circL (.downL ?_))))
          refine nOrAllElimJ _ (List.mem_cons_self ..) (upSelf _ .lax) ?_
          intro x hx Γ' hsub
          have hsubD : ∀ Z ∈ done, Z ∈ Γ' := fun Z hZ =>
            hsub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
          refine circROf (j := .tru) ?_
          if hx1 : x ∈ [interpF p f [] done (some (.up (.down (.imp Q₀ N₀))))] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .circR (.stable (.laxOf (unStable
              ((aSoundF p f [] done (.up (.down (.imp Q₀ N₀)))).wk (by
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
                      (aSoundF p f [N] rest (.circ (.down (.imp Q₀ N₀))))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ ((splits_sub hXr Z hZ))))
                        (aSoundF p f [.imp (.down N') N] rest (.imp Q' N'))
                        (aSoundF p f [N] rest (.circ (.down (.imp Q₀ N₀))))
                  | circ Q' =>
                      exact atkCimp (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsubD _ ((splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsubD _ (hZ)))
                        (aSoundF p f [] done (.up (.down (.circ Q'))))
                        ((aSoundF p f [N] rest (.circ (.down (.imp Q₀ N₀)))).wk
                          (Sub.cons _ (Sub.cons _ (splits_sub hXr))))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
          | circ R =>
              -- THE E-GUARDED BOX-OPENING ROW, x = ↓E(↑R::rest) ⊃ A(↑R::rest ⇒ ◯Q):
              -- circR into the lax phase; open the station box; per branch of R,
              -- derive E at the opened station (extract-mediated eSoundF), feed the
              -- row to get the opened-station ∀p, close ◯Q by aSoundF there, and
              -- re-enter the lax phase through circROf.
              refine .circR (.stable (.lfoc
                (List.mem_cons_of_mem _
                  (hsubD _ ((splits_mem hXr))))
                (.circL (invBranches R (fun b hb => ?_)))))
              -- dE: the opened-station ∃p, over the branch products
              have dE : Inv (b ++ (Neg.imp
                    (.down (interpF p f [.up R] rest none))
                    (interpF p f [.up R] rest (some (.circ (.down (.imp Q₀ N₀))))) :: Γ')) []
                  .tru (interpF p f [.up R] rest none) :=
                simHyp (H := .up R)
                  (fl := fun hs lf => match lf with
                    | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                        (List.mem_append.mp hZ).elim
                          (fun h => hs Z (List.mem_append_left _ h)) id)))
                  (fun Z hZ => List.mem_append_right b
                    (List.mem_cons_of_mem _
                      (hsubD _ ((splits_sub hXr Z hZ)))))
                  (eSoundF p f [.up R] rest)
              -- the opened-station ∀p beside the opened station closes ◯Q
              have D := (aSoundF p f [.up R] rest (.circ (.down (.imp Q₀ N₀))))
              -- strip A (via the row fired with dE), then ↑R (via extract)
              refine .stable (unStable (simHyp (H := .up R)
                (fl := fun hs lf => match lf with
                  | .rel d' => unStable ((extract [] d' b hb).wk (fun Z hZ =>
                      (List.mem_append.mp hZ).elim
                        (fun h => hs Z (List.mem_append_left _ h)) id)))
                (Sub.refl _)
                (simHyp (H := interpF p f [.up R] rest (some (.circ (.down (.imp Q₀ N₀)))))
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

/-! ## The two route-(B) statements, witnessed

`ESoundF` and `ASoundF` are `wip/ui_routeB_statements.lean`'s typed
definitions; they are restated here so this module stands alone, and each
is inhabited by the corresponding proof above. -/

/-- E1 at every fuel, as a type. -/
def ESoundF' (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg),
    Inv (todo ++ done) [] .tru (interpF p f todo done none)

/-- A1 at every fuel, as a type. -/
def ASoundF' (p : String) : Type :=
  ∀ (f : Nat) (todo done : List Neg) (G : Neg),
    Inv (interpF p f todo done (some G) :: (todo ++ done)) [] .tru G

/-- `ESoundF` is inhabited. -/
def eSoundFWitness (p : String) : ESoundF' p := eSoundF p

/-- `ASoundF` is inhabited. -/
def aSoundFWitness (p : String) : ASoundF' p := aSoundF p

/-! ## Pins

The commissioned bound is `eSound`/`aSound`'s own pinned set
(`LJF/OAudit.lean`): a proof needing anything beyond it would be wrong. -/

#axioms_within eSoundF [propext, Classical.choice, Quot.sound]
#axioms_within aSoundF [propext, Classical.choice, Quot.sound]
#axioms_within eSoundFWitness [propext, Classical.choice, Quot.sound]
#axioms_within aSoundFWitness [propext, Classical.choice, Quot.sound]

/-! The MEASURED set is strictly smaller: `[propext, Quot.sound]`.
`Classical.choice` enters `eSound`/`aSound` through the well-founded
recursion on `2 * sum3 todo + sum3 done + goalW goal`; the fuel recursion
does not use it.  Pinned tightly here, so a regression that re-introduces
choice is an error rather than a silent widening. -/

#axioms_within eSoundF [propext, Quot.sound]
#axioms_within aSoundF [propext, Quot.sound]
#axioms_within eSoundFWitness [propext, Quot.sound]
#axioms_within aSoundFWitness [propext, Quot.sound]

end LJFO
