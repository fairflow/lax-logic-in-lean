/-
LJF◯ — uniform interpolation, the minimality development (Parts 5–8).

Imports only the frozen core (`LaxLogic.LJFOCore`); the auditability
property is unchanged — no mathlib and no other calculus can carry any of
the proof.  Contents: the inverse transformations, the saturated-case
statements `SatE2`/`SatA2`, the dispatch helpers, and the minimality
mega-mutual (`eMinF`/`aMinF` and the `T*`/`U*` traversal families),
conditional on the isolated modal obligation `CimpAnt`.
-/
import LaxLogic.LJFOCore

namespace LJFO

/-! # Part 5: the inverse transformations and the saturated-case statements

Each processing clause of `interp` has an *inverse* transformation —
replacing uses of the consumed hypothesis by uses of its residual — proved
as a `simulate` instance.  The saturated case is *named* by the statements
`SatE2`/`SatA2` (and the Dyckhoff dispatch by `DykAnt`); Part 6's inner
induction discharges them unconditionally (`satE2`/`satA2`/`dykAnt` at the
end of the file).  The parametrised minimality functions `eMin`/`aMin`
that historically lived here are superseded by `eMinF`/`aMinF` and
preserved in `Archive/ljf-simp-round1-superseded.lean`.

## The inverse transformations -/

/-! Forced-shape analysers, top level so the index specialises. -/

/-- A left focus on a conjunction projects. -/
def lfocAnd {Δ : List Neg} {j : JD} {M N : Neg} {P : Pos} :
    LFoc Δ (.and M N) j P → LFoc Δ M j P ⊕ LFoc Δ N j P
  | .and1 lf => .inl lf
  | .and2 lf => .inr lf

/-- A left focus on an implication is `impL`. -/
def lfocImp {Δ : List Neg} {j : JD} {Q : Pos} {N : Neg} {P : Pos} :
    LFoc Δ (.imp Q N) j P → Stab Δ .tru Q × LFoc Δ N j P
  | .impL s lf => (s, lf)

/-- A left focus on a shift is `rel`. -/
def lfocUp {Δ : List Neg} {j : JD} {Q : Pos} {P : Pos} :
    LFoc Δ (.up Q) j P → Inv Δ [Q] j (.up P)
  | .rel d => d

/-- There is no right focus on `⊥`. -/
def rfocFls {Δ : List Neg} {j : JD} {A : Sort _} : RFocus Δ j .fls → A := nofun

/-- A right focus on a disjunction picks a side. -/
def rfocOr {Δ : List Neg} {j : JD} {A B : Pos} :
    RFocus Δ j (.or A B) → RFocus Δ j A ⊕ RFocus Δ j B
  | .or1 r => .inl r
  | .or2 r => .inr r

/-- Uses of `M ∧ N` become uses of `M` and `N`. -/
def invAndHyp {M N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.and M N :: Γ) [] j C) : Inv (M :: N :: Γ) [] j C :=
  simHyp (H := .and M N)
    (fl := fun hs lf => match lfocAnd lf with
      | .inl lf' => .lfoc (hs _ (List.mem_cons_self ..)) lf'
      | .inr lf' =>
          .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) lf')
    (fun Z hZ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
    d

/-- Uses of `⊥ ⊃ N` are vacuous: the antecedent proof routes to nothing —
`RFocus _ ⊥` has no constructor. -/
def invImpFls {N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp .fls N :: Γ) [] j C) : Inv Γ [] j C :=
  simHyp (H := .imp .fls N)
    (fl := fun _ lf =>
      routeStabT (k := fun _ r => rfocFls r) (Sub.refl _) (lfocImp lf).1)
    (Sub.refl _)
    d

/-- Uses of `(Q₁∨Q₂) ⊃ N` route through the split residuals. -/
def invImpOr {Q₁ Q₂ : Pos} {N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp (.or Q₁ Q₂) N :: Γ) [] j C) :
    Inv (.imp Q₁ N :: .imp Q₂ N :: Γ) [] j C :=
  simHyp (H := .imp (.or Q₁ Q₂) N)
    (fl := fun hs lf =>
      routeStabT
        (k := fun hs' r => match rfocOr r with
          | .inl r₁ =>
              .lfoc (hs' _ (hs _ (List.mem_cons_self ..)))
                (.impL (.rfoc r₁) ((lfocImp lf).2.wk hs'))
          | .inr r₂ =>
              .lfoc (hs' _ (hs _ (List.mem_cons_of_mem _
                  (List.mem_cons_self ..))))
                (.impL (.rfoc r₂) ((lfocImp lf).2.wk hs')))
        (Sub.refl _) (lfocImp lf).1)
    (fun Z hZ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
    d

/-- Uses of `↓↑P′ ⊃ N` strip the double shift. -/
def invStrip {P' : Pos} {N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp (.down (.up P')) N :: Γ) [] j C) :
    Inv (.imp P' N :: Γ) [] j C :=
  simHyp (H := .imp (.down (.up P')) N)
    (fl := fun hs lf =>
      routeStabT
        (k := fun hs' r =>
          .lfoc (hs' _ (hs _ (List.mem_cons_self ..)))
            (.impL (unStable (relOf r)) ((lfocImp lf).2.wk hs')))
        (Sub.refl _) (lfocImp lf).1)
    (fun Z hZ => List.mem_cons_of_mem _ hZ)
    d

/-- Uses of `↓(M₁∧M₂) ⊃ N` fire the curried residual twice. -/
def invCurry {M₁ M₂ N : Neg} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.imp (.down (.and M₁ M₂)) N :: Γ) [] j C) :
    Inv (.imp (.down M₁) (.imp (.down M₂) N) :: Γ) [] j C :=
  simHyp (H := .imp (.down (.and M₁ M₂)) N)
    (fl := fun hs lf =>
      routeStabT
        (k := fun hs' r =>
          .lfoc (hs' _ (hs _ (List.mem_cons_self ..)))
            (.impL (.rfoc (.rel (andROf1 (relOf r))))
              (.impL (.rfoc (.rel (andROf2 (relOf r))))
                ((lfocImp lf).2.wk hs'))))
        (Sub.refl _) (lfocImp lf).1)
    (fun Z hZ => List.mem_cons_of_mem _ hZ)
    d

/-- Uses of a shifted hypothesis restrict to any one branch of its
inversion — the derivation already contains that branch (`extract`). -/
def invUp {R : Pos} {Γ : List Neg} {j : JD} {C : Neg}
    (d : Inv (.up R :: Γ) [] j C) (b : List Neg) (hb : b ∈ invertPos R) :
    Inv (b ++ Γ) [] j C :=
  simHyp (H := .up R)
    (fl := fun {Δ'} {_} {_} hs lf =>
      unStable ((extract [] (lfocUp lf) b hb).wk (fun Z hZ => by
        rcases List.mem_append.mp hZ with hZ | hZ
        · exact hs _ (List.mem_append_left _ hZ)
        · exact hZ)))
    (fun Z hZ => List.mem_append_right _ hZ)
    d

end LJFO

namespace LJFO

/-! ## Splitting a context member -/

theorem splits_mem_split {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → ∀ Z ∈ Γ, Z = X ∨ Z ∈ rest := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h Z hZ
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨W, rest'⟩, hW, hEq⟩
      · cases h
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact .inl rfl
        · exact .inr hZ
      · cases hEq
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact .inr (List.mem_cons_self ..)
        · rcases ih hW Z hZ with e | hZ
          · exact .inl e
          · exact .inr (List.mem_cons_of_mem _ hZ)

/-- Uses of a fired implication become uses of its conclusion. -/
def invFireHyp {a : String} {N : Neg} {done rest Δext : List Neg} {j : JD}
    {C : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done)
    (d : Inv (done ++ Δext) [] j C) : Inv (N :: (rest ++ Δext)) [] j C :=
  simInv (H := .imp (.atom a) N)
    (fl := fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (lfocImp lf).2)
    (fun Z hZ => by
      rcases List.mem_append.mp hZ with hZ | hZ
      · rcases splits_mem_split h Z hZ with e | hZ
        · exact .inl e
        · exact .inr (List.mem_cons_of_mem _ (List.mem_append_left _ hZ))
      · exact .inr (List.mem_cons_of_mem _ (List.mem_append_right _ hZ)))
    (Sub.refl _) d

/-! ## Context shuffles for the minimality reductions -/

theorem subParkOut {X : Neg} {t d Δ : List Neg} :
    Sub (((X :: t) ++ d) ++ Δ) ((t ++ X :: d) ++ Δ) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · exact List.mem_append_left _ (subParkInv _ hZ)
  · exact List.mem_append_right _ hZ

theorem subHeadOut {X : Neg} {t d Δ : List Neg} :
    Sub (((X :: t) ++ d) ++ Δ) (X :: ((t ++ d) ++ Δ)) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · rcases List.mem_cons.mp hZ with rfl | hZ
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hZ)
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ hZ)

theorem subChainIn {b t d Δ : List Neg} :
    Sub (b ++ ((t ++ d) ++ Δ)) (((b ++ t) ++ d) ++ Δ) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hZ))
  · rcases List.mem_append.mp hZ with hZ | hZ
    · rcases List.mem_append.mp hZ with hZ | hZ
      · exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ hZ))
      · exact List.mem_append_left _ (List.mem_append_right _ hZ)
    · exact List.mem_append_right _ hZ

/-! ## The two open obligations, and minimality modulo them -/

/-- The context is `p`-free. -/
def PFreeCtx (p : String) (Δ : List Neg) : Prop := ∀ N ∈ Δ, PFreeN p N

/-- Saturation: no parked implication can fire. -/
def Saturated (done : List Neg) : Prop :=
  findFire done (splits done) = none

/-- Every member appears in `splits`. -/
theorem splits_of_mem {Γ : List Neg} {X : Neg} (h : X ∈ Γ) :
    ∃ rest, (X, rest) ∈ splits Γ := by
  induction Γ with
  | nil => simp at h
  | cons Y Γ ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨Γ, List.mem_cons_self ..⟩
      · obtain ⟨rest, hr⟩ := ih h
        exact ⟨Y :: rest, List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun zr => (zr.1, Y :: zr.2)) hr)⟩

/-- The three shapes parking can produce.  `SatE2`/`SatA2` are FALSE without
this restriction (e.g. `done = [↑q ∧ ↑q]` is saturated but its `∃p`
interpolant is the default `⊤`, which does not prove `q`); the recursion
only ever reaches saturated contexts of these shapes, so the restriction
costs nothing. -/
inductive ParkedN : Neg → Prop
  | atom (a : String) : ParkedN (.up (.atom a))
  | qimp (a : String) (N : Neg) : ParkedN (.imp (.atom a) N)
  | dyk (Q' : Pos) (N' N : Neg) : ParkedN (.imp (.down (.imp Q' N')) N)
  | box (Q : Pos) : ParkedN (.circ Q)
  | cimp (Q' : Pos) (N : Neg) : ParkedN (.imp (.down (.circ Q')) N)

/-- Every member is a parked shape. -/
def ParkedCtx (done : List Neg) : Prop := ∀ X ∈ done, ParkedN X

theorem ParkedCtx.nil : ParkedCtx [] := fun _ h => absurd h (List.not_mem_nil)

theorem ParkedCtx.cons {X : Neg} {done : List Neg}
    (hX : ParkedN X) (h : ParkedCtx done) : ParkedCtx (X :: done) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hX
  · exact h Z hZ

theorem ParkedCtx.sub {done rest : List Neg}
    (hs : Sub rest done) (h : ParkedCtx done) : ParkedCtx rest :=
  fun Z hZ => h Z (hs Z hZ)

/-- What `findFire = none` says about each scanned pair. -/
theorem findFire_none_spec {full : List Neg} :
    ∀ {l : List (Neg × List Neg)}, findFire full l = none →
      ∀ {a N rest}, (Neg.imp (.atom a) N, rest) ∈ l →
        atomMem a full = false := by
  intro l
  induction l with
  | nil => intro _ a N rest h; simp at h
  | cons XR more ih =>
      intro hn a N rest h
      obtain ⟨X, R⟩ := XR
      rcases List.mem_cons.mp h with hEq | h
      · cases hEq
        simp only [findFire] at hn
        by_cases hM : atomMem a full
        · simp [hM] at hn
        · simpa using hM
      · refine ih ?_ h
        match X, hn with
        | .imp (.atom b) N', hn => ?_
        | .up P, hn => exact hn
        | .imp .fls N', hn => exact hn
        | .imp (.or Q₁ Q₂) N', hn => exact hn
        | .imp (.down M) N', hn => exact hn
        | .and M₁ M₂, hn => exact hn
        | .circ P, hn => exact hn
        simp only [findFire] at hn
        by_cases hM : atomMem b full
        · simp [hM] at hn
        · simpa [hM] using hn

/-- At a saturated context, a parked implication's atom is absent.  In
particular a `p ⊃ N` member excludes `↑p`. -/
theorem saturated_atom_absent {done : List Neg} (hsat : Saturated done)
    {a : String} {N : Neg} (h : Neg.imp (.atom a) N ∈ done) :
    atomMem a done = false := by
  obtain ⟨rest, hr⟩ := splits_of_mem h
  exact findFire_none_spec hsat hr

/-- `atomMem` is complete for membership. -/
theorem atomMem_of_mem {a : String} {Γ : List Neg}
    (h : Neg.up (.atom a) ∈ Γ) : atomMem a Γ = true := by
  simp only [atomMem, List.any_eq_true]
  exact ⟨_, h, by simp⟩

/-- The goal of a sequent, adjusted for its judgment: a lax sequent with a
shifted goal is interpolated at the `◯`-goal (the lax judgment is
definable), and `tru` sequents keep their goal. -/
def jGoal : JD → Neg → Neg
  | j, .up P => match j with | .tru => .up P | .lax => .circ P
  | _, G => G

theorem jGoal_tru : ∀ {G : Neg}, jGoal .tru G = G
  | .up _ => rfl
  | .imp _ _ => rfl
  | .and _ _ => rfl
  | .circ _ => rfl

/-- The wrapper at the `jGoal` boundary: identity at `tru`, the modality
at `lax` (forced change #3 — the ◯-goal aggregate is box-wrapped). -/
def jBox : JD → Neg → Neg
  | .tru, X => X
  | .lax, X => .circ (.down X)

/-- Minimality of `∃p` at a saturated context — the inner induction over
derivations at saturated sequents, the heart of Pitts' argument.
Discharged unconditionally by `satE2` at the end of the file. -/
def SatE2 (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ → PFreeN p ψ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j ψ →
      Inv (interp p [] done none :: Δ) [] j ψ

/-- Minimality of `∀p` at a saturated context.  Discharged unconditionally
by `satA2` at the end of the file. -/
def SatA2 (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ →
    ∀ {j : JD}, Inv (done ++ Δ) [] j G →
    Inv (interp p [] done none :: Δ) [] .tru
      (interp p [] done (some (jGoal j G)))


end LJFO

namespace LJFO

/-! # Part 6: the saturated case — the inner induction

The plan, fixed by the analysis of 2026-08-09:

* One traversal over the four judgments, structural in the derivation, at a
  fixed saturated parked station `done`, with the context split as
  `done`-part plus a `p`-free kept part `K`.
* Uses of `done`-members are dispatched through the matching conjunct of the
  interpolant; the continuation after a fire is packaged as a derivation
  over the fired context (`d_cont`), cleaned of residual uses of the fired
  member, and handed to the minimality function at strictly smaller measure.
* Proofs of the atom `p` at the main line are eliminated by **composition**:
  `init` on `↑p` is impossible (saturation excludes `↑p` beside `p ⊃ M`;
  the kept side is `p`-free), so every such proof bottoms out in a fire
  whose body releases the `p`-material — and at that node all pieces exist
  to compose the outer `p ⊃ M` use with the inner fire directly.
* The single dispatch that does not close by these means is the Dyckhoff
  antecedent — deriving `∀p` of the antecedent at the residual station from
  a main-line stable proof of it.  It is isolated as `DykAnt`, one
  statement serving both modes.

## Preliminaries -/

/-- `p`-freeness for a pending list. -/
def PFreeΩ (p : String) (Ω : List Pos) : Prop := ∀ Q ∈ Ω, PFreeP p Q

theorem PFreeΩ.nil {p : String} : PFreeΩ p [] := fun _ h => absurd h (List.not_mem_nil)

theorem PFreeΩ.cons {p : String} {Q : Pos} {Ω : List Pos}
    (hQ : PFreeP p Q) (h : PFreeΩ p Ω) : PFreeΩ p (Q :: Ω) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hQ
  · exact h Z hZ

theorem PFreeΩ.head {p : String} {Q : Pos} {Ω : List Pos}
    (h : PFreeΩ p (Q :: Ω)) : PFreeP p Q := h Q (List.mem_cons_self ..)

theorem PFreeΩ.tail {p : String} {Q : Pos} {Ω : List Pos}
    (h : PFreeΩ p (Q :: Ω)) : PFreeΩ p Ω :=
  fun Z hZ => h Z (List.mem_cons_of_mem _ hZ)

/-- Locate a member's split, constructively. -/
def splitAt : (Γ : List Neg) → (X : Neg) → X ∈ Γ → {rest // (X, rest) ∈ splits Γ}
  | Y :: Γ, X, h =>
      if e : X = Y then
        ⟨Γ, by cases e; exact List.mem_cons_self ..⟩
      else
        have h' : X ∈ Γ := by
          rcases List.mem_cons.mp h with rfl | h'
          · exact absurd rfl e
          · exact h'
        let ⟨rest, hr⟩ := splitAt Γ X h'
        ⟨Y :: rest, List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun zr => (zr.1, Y :: zr.2)) hr)⟩

/-- The `∃p` conjunct of a `q`-implication member, and its membership in the
interpolant's conjunction list. -/
theorem qimpConjMem {p : String} {done : List Neg} {a : String} {N : Neg}
    {rest : List Neg} (hXr : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    pGuard p a nTop (.imp (.atom a) (interp p [N] rest none)) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- Likewise for a surviving atom. -/
theorem atomConjMem {p : String} {done : List Neg} {a : String}
    {rest : List Neg} (hXr : (Neg.up (.atom a), rest) ∈ splits done) :
    pGuard p a nTop (.up (.atom a)) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- And for a Dyckhoff member. -/
theorem dykConjMem {p : String} {done : List Neg} {Q' : Pos} {N' N : Neg}
    {rest : List Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
           (interp p [N] rest none))
      (interp p [.imp (.down N') N] rest none) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- And for a parked box. -/
theorem boxConjMem {p : String} {done : List Neg} {Q : Pos}
    {rest : List Neg}
    (hXr : (Neg.circ Q, rest) ∈ splits done) :
    Neg.circ (.down (interp p [.up Q] rest none)) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- And for a `◯`-implication member. -/
theorem cimpConjMem {p : String} {done : List Neg} {Q' : Pos} {N : Neg}
    {rest : List Neg}
    (hXr : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interp p [] rest (some (.circ Q'))))
           (interp p [N] rest none))
      (interp p [] rest none) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- **The isolated obligation** — the Dyckhoff antecedent dispatch: from a
main-line stable proof of the antecedent `↓(Q′ ⊃ N′)`, derive the `∀p`
interpolant of the antecedent at the residual station, on the interpolant
side.  One statement serves both modes.  This is Pitts' hardest case
(the `(A⊃B)⊃C` commute), and everything else below is proved outright. -/
def DykAnt (p : String) : Type :=
  ∀ (done rest K Γ' : List Neg) (Q' : Pos) (N' N : Neg),
    Saturated done → ParkedCtx done →
    (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
    (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
    Stab Γ' .tru (.down (.imp Q' N')) →
    Inv (interp p [] done none :: K) [] .tru
        (interp p [.imp (.down N') N] rest (some (.imp Q' N')))

end LJFO

namespace LJFO

/-! ## Part 6b: the dispatch helpers

Each is a plain `simulate`/assembly instance — no recursion into the coming
mutual block, so they compile standalone. -/

variable {p : String}

/-- **Fired-context cleanup.**  After a fire of `Q₀ ⊃ N`, residual uses of
the fired implication are redundant: the body `N` is now a hypothesis, so
`impL`-uses drop their antecedent and use `N` directly. -/
def fireClean {Q₀ : Pos} {N : Neg} {Γ' rest K : List Neg} {j : JD} {C : Neg}
    (hsplit : ∀ Z ∈ Γ', Z = Neg.imp Q₀ N ∨ Z ∈ rest ∨ Z ∈ K)
    (d : Inv (N :: Γ') [] j C) : Inv ((N :: rest) ++ K) [] j C :=
  simInv (H := .imp Q₀ N)
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_append_left _ (List.mem_cons_self ..)))
        (lfocImp lf).2)
    (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact .inr (List.mem_append_left _ (List.mem_cons_self ..))
      · rcases hsplit Z hZ with e | hZ | hZ
        · exact .inl e
        · exact .inr (List.mem_append_left _ (List.mem_cons_of_mem _ hZ))
        · exact .inr (List.mem_append_right _ hZ))
    (Sub.refl _) d

/-- **Opened-box cleanup.**  After a box `◯Q` is opened, residual `circL`
uses of the box re-derive their content from the released hypothesis `↑Q`
directly. -/
def boxClean {Q : Pos} {Γ' rest K : List Neg} {j : JD} {C : Neg}
    (hsplit : ∀ Z ∈ Γ', Z = Neg.circ Q ∨ Z ∈ rest ∨ Z ∈ K)
    (d : Inv (Neg.up Q :: Γ') [] j C) : Inv ((Neg.up Q :: rest) ++ K) [] j C :=
  simInv (H := .circ Q)
    (fl := fun hs lf =>
      match lf with
      | .circL dQ =>
          .lfoc (hs _ (List.mem_append_left _ (List.mem_cons_self ..)))
            (.rel dQ))
    (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact .inr (List.mem_append_left _ (List.mem_cons_self ..))
      · rcases hsplit Z hZ with e | hZ | hZ
        · exact .inl e
        · exact .inr (List.mem_append_left _ (List.mem_cons_of_mem _ hZ))
        · exact .inr (List.mem_append_right _ hZ))
    (Sub.refl _) d


/-- The saturated `∃p` aggregate, as an equation. -/
theorem interpE_eq {p : String} {done : List Neg} (hsat : Saturated done) :
    interp p [] done none = nAndAll ((splits done).attach.map
      (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | .circ Q =>
            .circ (.down (interp p [.up Q] rest none))
        | .imp (.down (.circ Q')) N =>
            nAnd
              (.imp (.down (interp p [] rest (some (.circ Q'))))
                   (interp p [N] rest none))
              (interp p [] rest none)
        | _ => nTop)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-- Project a surviving atom from the interpolant. -/
def atomAssemble {done K : List Neg} {a : String} {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : pGuard p a nTop (.up (.atom a)) ∈ L) (hap : ¬ a = p) :
    Stab (interp p [] done none :: K) .tru (.atom a) :=
  .lfoc (List.mem_cons_self ..)
    (hE.symm ▸ lfocAndAll hmem (by
      simp only [pGuard]; rw [if_neg hap]
      exact LFoc.rel (idPos (.atom a) _ _)))


/-- The context split after locating a member: `done`-side members are the
member itself or in its complement. -/
theorem splitHyp {done K Γ' rest : List Neg} {X : Neg}
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K)
    (hXr : (X, rest) ∈ splits done) :
    ∀ Z ∈ Γ', Z = X ∨ Z ∈ rest ∨ Z ∈ K := by
  intro Z hZ
  rcases hm Z hZ with hd | hK
  · rcases splits_mem_split hXr Z hd with e | hr
    · exact .inl e
    · exact .inr (.inl hr)
  · exact .inr (.inr hK)

end LJFO

namespace LJFO

/-! ## Part 6c: the inner induction, `∃p` side

The mutual block: `eMinF` (minimality, as before, but with the saturated
case discharged inline) and the traversal components.  Structural in the
derivation at a fixed station; every station-crossing goes through `eMinF`
at strictly smaller measure, so the lexicographic pair `(μ, size)` carries
the whole block. -/


theorem hmConsDone {done K Γ' : List Neg} {M : Neg} (hMd : M ∈ done)
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) :
    ∀ Z ∈ M :: Γ', Z ∈ done ∨ Z ∈ K := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact .inl hMd
  · exact hm Z hZ

theorem hmConsK {done K Γ' : List Neg} {M : Neg}
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) :
    ∀ Z ∈ M :: Γ', Z ∈ done ∨ Z ∈ M :: K := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact .inr (List.mem_cons_self ..)
  · exact (hm Z hZ).imp id (List.mem_cons_of_mem _)

theorem PFreeCtx.cons {p : String} {K : List Neg} {M : Neg}
    (hM : PFreeN p M) (hK : PFreeCtx p K) : PFreeCtx p (M :: K) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hM
  · exact hK Z hZ

/-- The weight inequalities for the traversal's station crossings. -/
theorem dec_fireT {done rest : List Neg} {a : String} {N : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := 1 + wNeg N + 1) (by omega)
  omega

theorem dec_dykT {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; have := wNeg_pos N'; omega)
  omega



/-! ## Part 7: shift release and the Dyckhoff commute

`relStab`: CPS release of a stable proof of `↓M` — the continuation receives
an inversion of `M` at every point one is produced.  `negOfDownStab` closes
the loop into a plain derivation of `M`, by recursion on `M` (the mirror of
`upMerge`).  `dykCommute` then converts a mixed-context stable proof of the
Dyckhoff antecedent into a derivation over the residual station — uses of
the full hypothesis are manufactured from the residual, because under the
antecedent's own inversion the goal-branch is in context (Dyckhoff's
observation, in focused form). -/

mutual

/-- CPS release of a stable `↓M`-proof. -/
def relStab {Δ₀ : List Neg} {j : JD} {M : Neg} {P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → Inv Δ' [] .tru M → Stab Δ' j P₀) :
    ∀ {Δ : List Neg}, Sub Δ₀ Δ → Stab Δ .tru (.down M) → Stab Δ j P₀
  | _, hs, .rfoc r => k hs (relOf r)
  | _, hs, .lfoc h lf => .lfoc h (relLF k hs lf)
termination_by Δ hs s => szS s
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Release below a left focus. -/
def relLF {Δ₀ : List Neg} {j : JD} {M : Neg} {P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → Inv Δ' [] .tru M → Stab Δ' j P₀) :
    ∀ {Δ : List Neg} {H : Neg}, Sub Δ₀ Δ →
      LFoc Δ H .tru (.down M) → LFoc Δ H j P₀
  | _, _, hs, .rel d => .rel (relInv k hs d)
  | _, _, hs, .impL s lf => .impL s (relLF k hs lf)
  | _, _, hs, .and1 lf => .and1 (relLF k hs lf)
  | _, _, hs, .and2 lf => .and2 (relLF k hs lf)
termination_by Δ H hs lf => szL lf
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

/-- Release through inversion; the goal is a shift, so the traversal is
total. -/
def relInv {Δ₀ : List Neg} {j : JD} {M : Neg} {P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → Inv Δ' [] .tru M → Stab Δ' j P₀) :
    ∀ {Δ : List Neg} {Ω : List Pos}, Sub Δ₀ Δ →
      Inv Δ Ω .tru (.up (.down M)) → Inv Δ Ω j (.up P₀)
  | _, _, hs, .stable s => .stable (relStab k hs s)
  | _, _, hs, .orL d₁ d₂ => .orL (relInv k hs d₁) (relInv k hs d₂)
  | _, _, _, .flsL => .flsL
  | _, _, hs, .downL d => .downL (relInv k (hs.trans (Sub.grow _)) d)
  | _, _, hs, .atomL d => .atomL (relInv k (hs.trans (Sub.grow _)) d)
termination_by Δ Ω hs d => szI d
decreasing_by all_goals (simp_wf; simp only [szS, szR, szL, szI]; omega)

end

/-- **A stable proof of `↓M` yields a derivation of `M`** — by recursion on
`M`, releasing at each stage. -/
def negOfDownStab : ∀ (M : Neg) {Δ : List Neg},
    Stab Δ .tru (.down M) → Inv Δ [] .tru M
  | .up P, _, s =>
      .stable (relStab (fun _ d => unStable d) (Sub.refl _) s)
  | .imp Q N, _, s =>
      .impR (invBranches Q (fun c hc =>
        negOfDownStab N (relStab
          (fun {Δ'} hs d =>
            .rfoc (.rel ((extract [] (impROf d) c hc).wk (fun Z hZ => by
              rcases List.mem_append.mp hZ with hZ | hZ
              · exact hs _ (List.mem_append_left _ hZ)
              · exact hZ))))
          (Sub.refl _)
          (s.wk (fun Z hZ => List.mem_append_right c hZ)))))
  | .and M₁ M₂, _, s =>
      .andR
        (negOfDownStab M₁ (relStab
          (fun _ d => .rfoc (.rel (andROf1 d))) (Sub.refl _) s))
        (negOfDownStab M₂ (relStab
          (fun _ d => .rfoc (.rel (andROf2 d))) (Sub.refl _) s))
  | .circ P, _, s =>
      .circR (.stable (relStab (fun _ d => unStable (circROf d))
        (Sub.refl _) s))

/-- **The Dyckhoff commute.**  A mixed-context stable proof of the antecedent
`↓(Q′ ⊃ N′)` becomes a derivation of `Q′ ⊃ N′` over the residual station:
uses of the full hypothesis `X = ↓(Q′⊃N′) ⊃ N` are replaced by fires of the
residual `↓N′ ⊃ N`, whose antecedent is recovered because the branch of `Q′`
currently in context closes the released implication (`extract`). -/
def dykCommute {p : String} {Q' : Pos} {N' N : Neg}
    {done rest K Γ' : List Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done)
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K)
    (s : Stab Γ' .tru (.down (.imp Q' N'))) :
    Inv ((Neg.imp (.down N') N :: rest) ++ K) [] .tru (.imp Q' N') :=
  .impR (invBranches Q' (fun b hb =>
    negOfDownStab N'
      (routeStabT
        (k := fun {Δ''} hs' r =>
          .rfoc (.rel ((extract [] (impROf (relOf r)) b hb).wk (fun Z hZ => by
            rcases List.mem_append.mp hZ with hZ | hZ
            · exact hs' _ (List.mem_append_left _ hZ)
            · exact hZ))))
        (Sub.refl _)
        (simStab (H := Neg.imp (.down (.imp Q' N')) N)
          (fl := fun {Δ'} {_} {_} hs lf =>
            .lfoc
              (hs _ (List.mem_append_right b (List.mem_append_left _
                (List.mem_cons_self ..))))
              (.impL
                (routeStabT
                  (k := fun {Δ''} hs' r =>
                    .rfoc (.rel ((extract [] (impROf (relOf r)) b hb).wk
                      (fun Z hZ => by
                        rcases List.mem_append.mp hZ with hZ | hZ
                        · exact hs' _ (hs _ (List.mem_append_left _ hZ))
                        · exact hZ))))
                  (Sub.refl _) (lfocImp lf).1)
                (lfocImp lf).2))
          (fun Z hZ => by
            rcases List.mem_append.mp hZ with hZ | hZ
            · exact .inr (List.mem_append_left _ hZ)
            · rcases hm Z hZ with hd | hk
              · rcases splits_mem_split hXr Z hd with e | hr
                · exact .inl e
                · exact .inr (List.mem_append_right b
                    (List.mem_append_left _ (List.mem_cons_of_mem _ hr)))
              · exact .inr (List.mem_append_right b
                  (List.mem_append_right _ hk)))
          (Sub.refl _)
          (s.wk (fun Z hZ => List.mem_append_right b hZ))))))



/-! ## Part 8: A-side prelude -/

/-- The positive under a list disjunction. -/
def orChain : List Neg → Pos
  | [] => .fls
  | x :: l => .or (.down x) (.down (nOrAll l))

theorem nOrAll_eq (L : List Neg) : nOrAll L = .up (orChain L) := by
  cases L <;> rfl

/-- The positive concluded by a rebuilt focus inside the `∀p` value: the
disjunction chain at `tru`, the shifted disjunction under the box at
`lax`. -/
def jChain : JD → List Neg → Pos
  | .tru, L => orChain L
  | .lax, L => .down (nOrAll L)

/-- Emit one disjunct of the (possibly box-wrapped) `∀p` value from a
`tru` derivation of the row. -/
def emitJ {Γ : List Neg} {x : Neg} {L : List Neg} : ∀ (j : JD), x ∈ L →
    Inv Γ [] .tru x → Inv Γ [] .tru (jBox j (nOrAll L))
  | .tru, hx, d => nOrAllIntro hx d
  | .lax, hx, d => .circR (.stable (.laxOf (.rfoc (.rel (nOrAllIntro hx d)))))

/-- Close the value from a rebuilt kept-hypothesis focus. -/
def keepFold {Γ : List Neg} {H : Neg} {L : List Neg} : ∀ {j : JD},
    H ∈ Γ → LFoc Γ H j (jChain j L) → Inv Γ [] .tru (jBox j (nOrAll L))
  | .tru, hm, lf => (nOrAll_eq _).symm ▸ Inv.stable (.lfoc hm lf)
  | .lax, hm, lf => .circR (.stable (.lfoc hm lf))

/-- Re-enter the inversion phase from the value. -/
def stabFold {Γ : List Neg} {L : List Neg} : ∀ {j : JD},
    Inv Γ [] .tru (jBox j (nOrAll L)) → Inv Γ [] j (.up (jChain j L))
  | .tru, d => nOrAll_eq _ ▸ d
  | .lax, d => circROf d

theorem p3_succ (m : Nat) : (3:Nat) ^ (m + 1) = 3 ^ m * 3 := Nat.pow_succ ..

/-- The station drop for the Dyckhoff pipeline, with generous slack. -/
theorem dec_dykC {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * 3 ^ (wNeg N' + 1 + wNeg N + 1) + sum3 rest +
      3 ^ (wPos Q' + wNeg N' + 1) + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have h1 := p3_mono (a := wNeg N' + 1 + wNeg N + 1)
    (b := wPos Q' + wNeg N' + 1 + wNeg N) (by have := wPos_pos Q'; omega)
  have h2 := p3_mono (a := wPos Q' + wNeg N' + 1)
    (b := wPos Q' + wNeg N' + 1 + wNeg N) (by have := wNeg_pos N; omega)
  have h3 : (3:Nat) ^ (wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1) =
      3 ^ (wPos Q' + wNeg N' + 1 + wNeg N) * 3 * 3 := by
    rw [show wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1 =
        wPos Q' + wNeg N' + 1 + wNeg N + 1 + 1 from by omega,
      p3_succ, p3_succ]
  have h5 := p3_mono (a := 1) (b := wPos Q' + wNeg N' + 1 + wNeg N)
    (by have := wPos_pos Q'; omega)
  omega

/-- The fire drop, with slack. -/
theorem dec_fireS {done rest : List Neg} {a : String} {N : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  rw [show 1 + wNeg N + 1 = wNeg N + 1 + 1 from by omega] at hs
  have h1 := p3_succ (wNeg N)
  have h2 := p3_succ (wNeg N + 1)
  have h3 := p3_mono (a := 1) (b := wNeg N) (wNeg_pos N)
  omega

/-- The box-opening station drop, with slack `2`. -/
theorem dec_boxF {done rest : List Neg} {Q : Pos}
    (h : (Neg.circ Q, rest) ∈ splits done) :
    2 * 3 ^ wPos Q + sum3 rest + 2 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg] at hs
  have h1 := p3_succ (wPos Q)
  have h2 := p3_mono (a := 1) (b := wPos Q) (wPos_pos Q)
  omega

/-- The `◯`-implication fire drop, with slack. -/
theorem dec_cimpF {done rest : List Neg} {Q' : Pos} {N : Neg}
    (h : (Neg.imp (Pos.down (Neg.circ Q')) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have h1 := p3_mono (a := wNeg N + 1 + 1)
    (b := wPos Q' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; omega)
  have h2 := p3_succ (wNeg N)
  have h3 := p3_succ (wNeg N + 1)
  have h4 := p3_mono (a := 1) (b := wNeg N) (wNeg_pos N)
  omega

/-- The Dyckhoff-fire drop, with slack. -/
theorem dec_dykS {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have h1 := p3_mono (a := wNeg N + 1 + 1)
    (b := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; have := wNeg_pos N'; omega)
  have h2 := p3_succ (wNeg N)
  have h3 := p3_succ (wNeg N + 1)
  have h4 := p3_mono (a := 1) (b := wNeg N) (wNeg_pos N)
  omega

/-- The goal-inversion drop, with slack. -/
theorem dec_ainvS {Q : Pos} {b : List Neg} {N : Neg}
    (hb : b ∈ invertPos Q) :
    2 * sum3 b + 3 ^ wNeg N + 9 < 3 ^ (wPos Q + wNeg N + 1) := by
  have h1 := invertPos_le Q b hb
  have hD := p3_succ (wPos Q + wNeg N - 1)
  rw [show wPos Q + wNeg N - 1 + 1 = wPos Q + wNeg N from by
    have := wPos_pos Q; omega] at hD
  have hC := p3_succ (wPos Q + wNeg N)
  have hA := p3_mono (a := wPos Q) (b := wPos Q + wNeg N - 1)
    (by have := wNeg_pos N; omega)
  have hB := p3_mono (a := wNeg N) (b := wPos Q + wNeg N)
    (by have := wPos_pos Q; omega)
  have hDp := p3_mono (a := 1) (b := wPos Q + wNeg N - 1)
    (by have := wPos_pos Q; have := wNeg_pos N; omega)
  omega

variable {p : String}

/-- Fire the `q`-implication conjunct: the atom from `sa`, the recursively
interpolated body consumed through `δ`. -/
def qAssembleN {done rest K : List Neg} {a : String} {N : Neg} {C : Neg}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : pGuard p a nTop (.imp (.atom a) (interp p [N] rest none)) ∈ L)
    (hap : ¬ a = p)
    (sa : Stab (interp p [] done none :: K) .tru (.atom a))
    {j : JD} (δ : Inv (interp p [N] rest none :: K) [] j C) :
    Inv (interp p [] done none :: K) [] j C :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem (by
          simp only [pGuard]; rw [if_neg hap]
          exact LFoc.impL (sa.wk hs) lf)))
    (Sub.grow _) δ

/-- Fire the Dyckhoff conjunct: the antecedent interpolant from `sant`, the
recursively interpolated body consumed through `δ`. -/
def dykAssembleN {done rest K : List Neg} {Q' : Pos} {N' N : Neg} {C : Neg}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : nAnd
        (.imp (.down (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
             (interp p [N] rest none))
        (interp p [.imp (.down N') N] rest none) ∈ L)
    (sant : Inv (interp p [] done none :: K) [] .tru
      (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
    {j : JD} (δ : Inv (interp p [N] rest none :: K) [] j C) :
    Inv (interp p [] done none :: K) [] j C :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem
          (.and1 (.impL (.rfoc (.rel (sant.wk hs))) lf))))
    (Sub.grow _) δ

/-- Open the box conjunct: at a lax goal, `circL` on the boxed `∃p` of the
opened station puts that interpolant straight into context — no simulation
needed. -/
def boxAssembleN {done rest K : List Neg} {Q : Pos} {P : Pos}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : Neg.circ (.down (interp p [.up Q] rest none)) ∈ L)
    (δ : Inv (interp p [.up Q] rest none :: K) [] .lax (.up P)) :
    Stab (interp p [] done none :: K) .lax P :=
  .lfoc (List.mem_cons_self ..)
    (hE.symm ▸ lfocAndAll hmem
      (.circL (.downL (δ.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))))

/-- Fire the `◯`-implication conjunct: the antecedent's `∀p` from `sant`,
the recursively interpolated body consumed through `δ`. -/
def cimpAssembleN {done rest K : List Neg} {Q' : Pos} {N : Neg} {C : Neg}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : nAnd
        (.imp (.down (interp p [] rest (some (.circ Q'))))
             (interp p [N] rest none))
        (interp p [] rest none) ∈ L)
    (sant : Inv (interp p [] done none :: K) [] .tru
      (interp p [] rest (some (.circ Q'))))
    {j : JD} (δ : Inv (interp p [N] rest none :: K) [] j C) :
    Inv (interp p [] done none :: K) [] j C :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem
          (.and1 (.impL (.rfoc (.rel (sant.wk hs))) lf))))
    (Sub.grow _) δ


/-! The `∀p` aggregates as equations, at each goal shape (stated outside any
mutual block so the elaborator reuses `interp`'s own compiled matchers). -/

theorem interpA_atom_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : ¬ atomMem q done = true) :
    interp p [] done (some (.up (.atom q))) =
      nOrAll (atomHead p q ++ (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up (.atom q))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp only [hq, if_false, Bool.false_eq_true]; rfl

theorem interpA_atomT_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : atomMem q done = true) :
    interp p [] done (some (.up (.atom q))) = nTop := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp [hq]

theorem interpA_fls_eq {p : String} {done : List Neg}
    (hsat : Saturated done) :
    interp p [] done (some (.up .fls)) =
      nOrAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up .fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up .fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up .fls)))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_or_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P₁ P₂ : Pos) :
    interp p [] done (some (.up (.or P₁ P₂))) =
      nOrAll ([interp p [] done (some (.up P₁)),
               interp p [] done (some (.up P₂))] ++ (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up (.or P₁ P₂))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_down_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M : Neg) :
    interp p [] done (some (.up (.down M))) =
      nOrAll ([interp p [] done (some M)] ++ (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (.down M)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (.down M))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.up (.down M))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_imp_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (Q : Pos) (N : Neg) :
    interp p [] done (some (.imp Q N)) =
      nAndAll ((invertPos Q).attach.map
        (fun ⟨b, hb⟩ =>
          .imp (.down (interp p b done none))
            (interp p b done (some N)))) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_and_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M N : Neg) :
    interp p [] done (some (.and M N)) =
      nAnd (interp p [] done (some M)) (interp p [] done (some N)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl


variable {p : String}

theorem interpA_circAtom_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} :
    interp p [] done (some (.circ (.atom q))) = .circ (.down (nOrAll ([interp p [] done (some (.up (.atom q)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.atom q))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.atom q))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.atom q))))
              | _, _ => nBot)))) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circFls_eq {p : String} {done : List Neg}
    (hsat : Saturated done) :
    interp p [] done (some (.circ .fls)) = .circ (.down (nOrAll ([interp p [] done (some (.up .fls))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ .fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ .fls)))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ .fls)))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ .fls)))
              | _, _ => nBot)))) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circOr_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P₁ P₂ : Pos) :
    interp p [] done (some (.circ (.or P₁ P₂))) = .circ (.down (nOrAll ([interp p [] done (some (.circ P₁)),
                     interp p [] done (some (.circ P₂)),
                     interp p [] done (some (.up (.or P₁ P₂)))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.or P₁ P₂))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.or P₁ P₂))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.or P₁ P₂))))
              | _, _ => nBot)))) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownUp_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P' : Pos) :
    interp p [] done (some (.circ (.down (.up P')))) = .circ (.down (nOrAll ([interp p [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.up P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.up P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.up P')))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.up P')))))
              | _, _ => nBot)))) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownCirc_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P' : Pos) :
    interp p [] done (some (.circ (.down (.circ P')))) = .circ (.down (nOrAll ([interp p [] done (some (.circ P'))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.circ P'))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.circ P')))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.circ P')))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.circ P')))))
              | _, _ => nBot)))) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownAnd_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M₁ M₂ : Neg) :
    interp p [] done (some (.circ (.down (.and M₁ M₂)))) = .circ (.down (nOrAll ([interp p [] done (some (.up (.down (.and M₁ M₂))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.and M₁ M₂))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.and M₁ M₂)))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.and M₁ M₂)))))
              | _, _ => nBot)))) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_circDownImp_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (Q₀ : Pos) (N₀ : Neg) :
    interp p [] done (some (.circ (.down (.imp Q₀ N₀)))) = .circ (.down (nOrAll ([interp p [] done (some (.up (.down (.imp Q₀ N₀))))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀))))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .imp (.down (.circ Q')) N, hXr =>
                  nAnd (interp p [] rest (some (.circ Q')))
                       (interp p [N] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | .circ R, hXr =>
                  .imp (.down (interp p [.up R] rest none))
                       (interp p [.up R] rest (some (.circ (.down (.imp Q₀ N₀)))))
              | _, _ => nBot)))) := by
  conv => lhs; rw [interp]
  split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-- Every ◯-goal aggregate is box-wrapped: the row list, with its
equation.  One case per goal shape, so callers with an abstract positive
can still cross the wrapper. -/
def interpCircShape {p : String} {done : List Neg} (hsat : Saturated done) :
    ∀ (P₀ : Pos), Σ' L, interp p [] done (some (.circ P₀)) = .circ (.down (nOrAll L))
  | .atom _ => ⟨_, interpA_circAtom_eq hsat⟩
  | .fls => ⟨_, interpA_circFls_eq hsat⟩
  | .or P₁ P₂ => ⟨_, interpA_circOr_eq hsat P₁ P₂⟩
  | .down (.up P') => ⟨_, interpA_circDownUp_eq hsat P'⟩
  | .down (.circ P') => ⟨_, interpA_circDownCirc_eq hsat P'⟩
  | .down (.and M₁ M₂) => ⟨_, interpA_circDownAnd_eq hsat M₁ M₂⟩
  | .down (.imp Q₀ N₀) => ⟨_, interpA_circDownImp_eq hsat Q₀ N₀⟩

/-- **The isolated modal obligation** — the ◯-implication antecedent
dispatch, the modal-descent miner: from a main-line stable proof of the
antecedent `↓◯Q′` over a mixed context, derive the `∀p` interpolant of
`◯Q′` at the residual station, on the interpolant side.  Isolated as a
typed hypothesis exactly as `DykAnt` was in the intuitionistic
development; the mutual below is conditional on it, and it is discharged
separately (the modal descent of plan §3(e)). -/
def CimpAnt (p : String) : Type :=
  ∀ (done rest K Γ' : List Neg) (Q' : Pos) (N : Neg),
    Saturated done → ParkedCtx done →
    (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
    (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
    Stab Γ' .tru (.down (.circ Q')) →
    Inv (interp p [] done none :: K) [] .tru
      (interp p [] rest (some (.circ Q')))

variable (cAnt : CimpAnt p)

set_option maxHeartbeats 8000000 in
mutual

/-- Minimality of `∃p`, with the saturated case discharged inline —
conditional only on the Dyckhoff antecedent dispatch `dyk`. -/
def eMinF : ∀ (todo done Δ : List Neg) (ψ : Neg), ParkedCtx done →
    PFreeCtx p Δ → PFreeN p ψ → ∀ {j : JD},
    Inv ((todo ++ done) ++ Δ) [] j ψ →
    Inv (interp p todo done none :: Δ) [] j ψ
  | .up (.atom a) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo (.up (.atom a) :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.atom a) hP) hΔ hψ
        (d.wk subParkOut)
  | .up .fls :: todo, done, Δ, ψ, _, _, _, _, d => by
      rw [interp]
      exact nBotElimJ _ (List.mem_cons_self ..) d
  | .up (.or P Q) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      refine nOrAllElimJ _ (List.mem_cons_self ..) d ?_
      intro x hx Γ' hsub
      obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      refine ((eMinF (b ++ todo) done Δ ψ hP hΔ hψ
        ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hsub _ (List.mem_cons_of_mem _ hZ))
  | .up (.down M) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF (M :: todo) done Δ ψ hP hΔ hψ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
  | .and M N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF (M :: N :: todo) done Δ ψ hP hΔ hψ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
  | .imp .fls N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo done Δ ψ hP hΔ hψ (invImpFls (d.wk subHeadOut))
  | .imp (.atom a) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo (.imp (.atom a) N :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.qimp a N) hP) hΔ hψ
        (d.wk subParkOut)
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF (.imp Q₁ N :: .imp Q₂ N :: todo) done Δ ψ hP hΔ hψ
        ((invImpOr (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp Q₁ N, .imp Q₂ N])))
  | .imp (.down (.up P')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF (.imp P' N :: todo) done Δ ψ hP hΔ hψ
        ((invStrip (d.wk subHeadOut)).wk (subChainIn (b := [.imp P' N])))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done Δ ψ
        hP hΔ hψ
        ((invCurry (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp (.down M₁) (.imp (.down M₂) N)])))
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo (.imp (.down (.imp Q' N')) N :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.dyk Q' N' N) hP) hΔ hψ
        (d.wk subParkOut)
  | .circ Q :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo (.circ Q :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.box Q) hP) hΔ hψ
        (d.wk subParkOut)
  | .imp (.down (.circ Q')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d => by
      rw [interp]
      exact eMinF todo (.imp (.down (.circ Q')) N :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.cimp Q' N) hP) hΔ hψ
        (d.wk subParkOut)
  | [], done, Δ, ψ, hP, hΔ, hψ, _, d => by
      match hf : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [interpFire_eq hf none]
          exact eMinF [N] rest Δ ψ
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ hψ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact TInv done hf hP
            (fun Z hZ => List.mem_append.mp hZ)
            (fun Z hZ => List.mem_append_left _ hZ)
            hΔ (fun _ h => absurd h (List.not_mem_nil)) hψ d
  termination_by todo done Δ ψ hP hΔ hψ j d =>
    (2 * sum3 todo + sum3 done + 1, 0)
  decreasing_by ljf_dec_e


/-- Inversion-phase traversal. -/
def TInv (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {Ω : List Pos} {C : Neg} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeΩ p Ω → PFreeN p C →
      Inv Γ' Ω j C → Inv (interp p [] done none :: K) Ω j C
  | _, _, _, _, _, hm, hm2, hK, hΩ, hC, .impR d =>
      .impR (TInv done hsat hP hm hm2 hK (hΩ.cons hC.1) hC.2 d)
  | _, _, _, _, _, hm, hm2, hK, hΩ, hC, .andR d e =>
      .andR (TInv done hsat hP hm hm2 hK hΩ hC.1 d)
            (TInv done hsat hP hm hm2 hK hΩ hC.2 e)
  | _, _, _, _, _, hm, hm2, hK, hΩ, hC, .circR d =>
      .circR (TInv done hsat hP hm hm2 hK hΩ hC d)
  | _, _, _, _, _, hm, hm2, hK, _, hC, .stable s =>
      .stable (TStab done hsat hP hm hm2 hK hC s)
  | _, _, .or P₁ Q₁ :: _, _, _, hm, hm2, hK, hΩ, hC, .orL d₁ d₂ =>
      have hor : PFreeP p (.or P₁ Q₁) := hΩ.head
      .orL (TInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.1) hC d₁)
           (TInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.2) hC d₂)
  | _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, .down M₀ :: _, _, _, hm, hm2, hK, hΩ, hC, .downL d =>
      have hM : PFreeN p M₀ := hΩ.head
      .downL (((TInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hM hK) hΩ.tail hC d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, .atom a :: _, _, _, hm, hm2, hK, hΩ, hC, .atomL d =>
      .atomL (((TInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom a)) from hΩ.head) hK)
          hΩ.tail hC d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K Ω C j hm hm2 hK hΩ hC d => (2 * sum3 [] + sum3 done, sizeOf d)
  decreasing_by ljf_dec_e


/-- Stable-phase traversal: the dispatch point. -/
def TStab (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P →
      Stab Γ' j P → Stab (interp p [] done none :: K) j P
  | _, _, _, _, hm, hm2, hK, hp, .rfoc r => TRF done hsat hP hm hm2 hK hp r
  | _, _, _, _, hm, hm2, hK, hp, .laxOf s =>
      .laxOf (TStab done hsat hP hm hm2 hK hp s)
  | _, _, _, _, hm, hm2, hK, hp, @Stab.lfoc _ _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom a), _, hd, .rel (.atomL (.stable s')) =>
            TStab done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hp s'
        | .imp (.atom a) N, _, hd, .impL s_a lf' =>
            if hap : a = p then
              TpElim done hsat hP hm hm2 hK hp hap hap hd lf' s_a
            else
              let ⟨rest, hXr⟩ := splitAt done _ hd
              unStable (qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hap
                (TStab done hsat hP hm hm2 hK hap s_a)
                (eMinF [N] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hp
                  (fireClean (splitHyp hm hXr)
                    (.stable (.lfoc (List.mem_cons_self ..)
                      (lf'.wk (Sub.grow _)))))))
        | .circ Q, _, hd, .circL d =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            boxAssembleN (interpE_eq hsat) (boxConjMem hXr)
              (eMinF [.up Q] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hp
                (boxClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (.rel (d.wk (Sub.grow _)))))))
        | .imp (.down (.circ Q')) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            unStable (cimpAssembleN (interpE_eq hsat) (cimpConjMem hXr)
              (cAnt done rest _ _ Q' N hsat hP hXr hm hm2 hK s_d)
              (eMinF [N] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _)))))))
        | .imp (.down (.imp Q' N')) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            unStable (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
              (dykAntC done rest _ _ Q' N' N hsat hP hXr hm hm2 hK s_d)
              (eMinF [N] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _)))))))
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        .lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
          (TLF done hsat hP hm hm2 hK
            (hK _ ((hm _ h).resolve_left hd)) hp lf)
  termination_by Γ' K P j hm hm2 hK hp s => (2 * sum3 [] + sum3 done, sizeOf s)
  decreasing_by ljf_dec_e


/-- Right-focus traversal. -/
def TRF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P →
      RFocus Γ' j P → Stab (interp p [] done none :: K) j P
  | _, _, .atom a, _, hm, _, hK, hp, .init h => by
      by_cases hd : Neg.up (.atom a) ∈ done
      · exact
          let w := splitAt done _ hd
          Stab.ofTru _ (atomAssemble (interpE_eq hsat) (atomConjMem w.2) hp)
      · exact .rfoc (.init (List.mem_cons_of_mem _
          ((hm _ h).resolve_left hd)))
  | _, _, _, _, hm, hm2, hK, hp, .or1 r =>
      stabOr1 (TRF done hsat hP hm hm2 hK hp.1 r)
  | _, _, _, _, hm, hm2, hK, hp, .or2 r =>
      stabOr2 (TRF done hsat hP hm hm2 hK hp.2 r)
  | _, _, _, _, hm, hm2, hK, hp, .rel d =>
      .rfoc (.rel (TInv done hsat hP hm hm2 hK
        (fun _ h => absurd h (List.not_mem_nil)) hp d))
  termination_by Γ' K P j hm hm2 hK hp r => (2 * sum3 [] + sum3 done, sizeOf r)
  decreasing_by ljf_dec_e


/-- Left-focus traversal on a kept hypothesis. -/
def TLF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {H : Neg} {P : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeN p H → PFreeP p P →
      LFoc Γ' H j P → LFoc (interp p [] done none :: K) H j P
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .rel d =>
      .rel (TInv done hsat hP hm hm2 hK
        (PFreeΩ.cons hH PFreeΩ.nil) hp d)
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .circL d =>
      .circL (TInv done hsat hP hm hm2 hK
        (PFreeΩ.cons hH PFreeΩ.nil) hp d)
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (TLF done hsat hP hm hm2 hK hH.2 hp lf)
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .and1 lf =>
      .and1 (TLF done hsat hP hm hm2 hK hH.1 hp lf)
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .and2 lf =>
      .and2 (TLF done hsat hP hm hm2 hK hH.2 hp lf)
  termination_by Γ' K H P j hm hm2 hK hH hp lf => (2 * sum3 [] + sum3 done, sizeOf lf)
  decreasing_by ljf_dec_e


/-- The `p`-fire eliminator: a main-line proof of the atom `p`, plus the
outer `p ⊃ M` package, yields the target directly — `init` on `↑p` is
impossible, kept chains rebuild, nested `p`-fires shortcut to their own
premise, and every other fire composes the package with the fire's body. -/
def TpElim (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {a b : String} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      Stab Γ' .tru (.atom b) → Stab (interp p [] done none :: K) j P₀
  | _, _, _, _, _, _, _, hm, _, hK, _, ha, hb, hXpkg, _, .rfoc (.init h) =>
      False.elim (by
        rcases hm _ h with hd | hk
        · have h1 := atomMem_of_mem hd
          have h2 := saturated_atom_absent hsat hXpkg
          rw [hb.trans ha.symm] at h1
          rw [h1] at h2; cases h2
        · exact (hK _ hk) hb)
  | _, _, _, _, a, b, _, hm, hm2, hK, hpT, ha, hb, hXpkg, lfP, @Stab.lfoc _ _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            TpElim done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hpT ha hb
              hXpkg (lfP.wk (Sub.grow _)) s'
        | .imp (.atom c) N_b, _, hd, .impL s_b lf_b =>
            if hcp : c = p then
              TpElim done hsat hP hm hm2 hK hpT ha hcp hXpkg lfP s_b
            else
              let ⟨rest, hXr⟩ := splitAt done _ hd
              unStable (qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hcp
                (TStab done hsat hP hm hm2 hK hcp s_b)
                (eMinF [N_b] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hpT
                  (fireClean (splitHyp hm hXr) (.stable
                    (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                      (.impL
                        ((hb.trans ha.symm) ▸
                          Stab.lfoc (List.mem_cons_self ..)
                            (lf_b.wk (Sub.grow _)))
                        (lfP.wk (Sub.grow _))))))))
        | .imp (.down (.imp Q' N')) N_d, _, hd, .impL s_d lf_d =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            unStable (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
              (dykAntC done rest _ _ Q' N' N_d hsat hP hXr hm hm2 hK s_d)
              (eMinF [N_d] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_d.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _))))))))
        | .imp (.down (.circ Q')) N_c, _, hd, .impL s_c lf_c =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            unStable (cimpAssembleN (interpE_eq hsat) (cimpConjMem hXr)
              (cAnt done rest _ _ Q' N_c hsat hP hXr hm hm2 hK s_c)
              (eMinF [N_c] rest _ (.up _) (hP.sub (splits_sub hXr)) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_c.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _))))))))
        | .circ _, _, _, lf => nomatch lf
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        .lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
          (TpLF done hsat hP hm hm2 hK
            (hK _ ((hm _ h).resolve_left hd)) hpT ha hb hXpkg lfP lf)
  termination_by Γ' K M P₀ a b j hm hm2 hK hpT ha hb hXpkg lfP s =>
    (2 * sum3 [] + sum3 done, sizeOf s)
  decreasing_by ljf_dec_e


/-- Left focus on a kept hypothesis, inside a `p`-proof. -/
def TpLF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {H : Neg} {a b : String} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeN p H → PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      LFoc Γ' H .tru (.atom b) → LFoc (interp p [] done none :: K) H j P₀
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .rel d =>
      .rel (TpInv done hsat hP hm hm2 hK
        (PFreeΩ.cons hH PFreeΩ.nil)
        hpT ha hb hXpkg lfP d)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (TpLF done hsat hP hm hm2 hK hH.2 hpT ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .and1 lf =>
      .and1 (TpLF done hsat hP hm hm2 hK hH.1 hpT ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .and2 lf =>
      .and2 (TpLF done hsat hP hm hm2 hK hH.2 hpT ha hb hXpkg lfP lf)
  termination_by Γ' K M P₀ H a b j hm hm2 hK hH hpT ha hb hXpkg lfP lf =>
    (2 * sum3 [] + sum3 done, sizeOf lf)
  decreasing_by ljf_dec_e


/-- Inversion inside a `p`-proof, with the goal re-targeted. -/
def TpInv (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {Ω : List Pos} {a b : String} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeΩ p Ω → PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      Inv Γ' Ω .tru (.up (.atom b)) → Inv (interp p [] done none :: K) Ω j (.up P₀)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, _, hpT, ha, hb, hXpkg, lfP, .stable s =>
      .stable (TpElim done hsat hP hm hm2 hK hpT ha hb hXpkg lfP s)
  | _, _, _, _, .or P₁ Q₁ :: _, _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg, lfP, .orL d₁ d₂ =>
      have hor : PFreeP p (.or P₁ Q₁) := hΩ.head
      .orL (TpInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.1)
              hpT ha hb hXpkg lfP d₁)
           (TpInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.2)
              hpT ha hb hXpkg lfP d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, .down M₀ :: _, _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg, lfP, .downL d =>
      have hM : PFreeN p M₀ := hΩ.head
      .downL (((TpInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hM hK) hΩ.tail hpT ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, _, _, .atom c :: _, _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg, lfP, .atomL d =>
      .atomL (((TpInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom c)) from hΩ.head) hK) hΩ.tail hpT ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K M P₀ Ω a b j hm hm2 hK hΩ hpT ha hb hXpkg lfP d =>
    (2 * sum3 [] + sum3 done, sizeOf d)
  decreasing_by ljf_dec_e


/-- Minimality of `∀p`, with the saturated case discharged inline. -/
def aMinF : ∀ (todo done Δ : List Neg) (G : Neg), ParkedCtx done →
    PFreeCtx p Δ → ∀ {j : JD},
    Inv ((todo ++ done) ++ Δ) [] j G →
    Inv (interp p todo done none :: Δ) [] .tru
      (interp p todo done (some (jGoal j G)))
  | .up (.atom a) :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo (.up (.atom a) :: done) Δ G
        (ParkedCtx.cons (ParkedN.atom a) hP) hΔ (d.wk subParkOut)
  | .up .fls :: todo, done, Δ, G, _, _, _, _ => by
      rw [interp, interp]
      exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or P Q) :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      refine nAndAllIntro ?_
      intro x hx
      obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      refine .impR (.downL ?_)
      refine ((aMinF (b ++ todo) done Δ G hP hΔ
        ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)
  | .up (.down M) :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF (M :: todo) done Δ G hP hΔ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
  | .and M N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF (M :: N :: todo) done Δ G hP hΔ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
  | .imp .fls N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo done Δ G hP hΔ (invImpFls (d.wk subHeadOut))
  | .imp (.atom a) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo (.imp (.atom a) N :: done) Δ G
        (ParkedCtx.cons (ParkedN.qimp a N) hP) hΔ
        (d.wk subParkOut)
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF (.imp Q₁ N :: .imp Q₂ N :: todo) done Δ G hP hΔ
        ((invImpOr (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp Q₁ N, .imp Q₂ N])))
  | .imp (.down (.up P')) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF (.imp P' N :: todo) done Δ G hP hΔ
        ((invStrip (d.wk subHeadOut)).wk (subChainIn (b := [.imp P' N])))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done Δ G
        hP hΔ
        ((invCurry (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp (.down M₁) (.imp (.down M₂) N)])))
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo (.imp (.down (.imp Q' N')) N :: done) Δ G
        (ParkedCtx.cons (ParkedN.dyk Q' N' N) hP) hΔ
        (d.wk subParkOut)
  | .circ Q :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo (.circ Q :: done) Δ G
        (ParkedCtx.cons (ParkedN.box Q) hP) hΔ
        (d.wk subParkOut)
  | .imp (.down (.circ Q')) N :: todo, done, Δ, G, hP, hΔ, _, d => by
      rw [interp, interp]
      exact aMinF todo (.imp (.down (.circ Q')) N :: done) Δ G
        (ParkedCtx.cons (ParkedN.cimp Q' N) hP) hΔ
        (d.wk subParkOut)
  | [], done, Δ, G, hP, hΔ, j, d => by
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          rw [interpFire_eq hf none, interpFire_eq hf (some (jGoal j G))]
          exact aMinF [N'] rest Δ G
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact UEntry done hf hP
            (fun Z hZ => List.mem_append.mp hZ)
            (fun Z hZ => List.mem_append_left _ hZ)
            hΔ G d
  termination_by todo done Δ G hP hΔ j d =>
    (2 * sum3 todo + sum3 done + 3 ^ wNeg G + 4, 0)
  decreasing_by ljf_dec_a


/-- The `∀p` interpolant of any goal over a mixed saturated context. -/
def UEntry (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      ∀ (G : Neg) {j : JD}, Inv Γ' [] j G →
      Inv (interp p [] done none :: K) [] .tru
        (interp p [] done (some (jGoal j G)))
  | _, _, hm, hm2, hK, .imp Q N, _, .impR d₁ => by
      show Inv _ [] .tru (interp p [] done (some (.imp Q N)))
      rw [interpA_imp_eq hsat Q N]
      refine nAndAllIntro ?_
      intro x hx
      obtain ⟨w, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      have hb : w.1 ∈ invertPos Q := w.2
      refine .impR (.downL ?_)
      have haux := (aMinF w.1 done _ N hP hK
        ((extract [] d₁ w.1 hb).wk (fun Z hZ => by
          rcases List.mem_append.mp hZ with hZ | hZ
          · exact List.mem_append_left _ (List.mem_append_left _ hZ)
          · rcases hm Z hZ with hd | hk
            · exact List.mem_append_left _ (List.mem_append_right _ hd)
            · exact List.mem_append_right _ hk)))
      rw [jGoal_tru] at haux
      refine (haux.wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)
  | _, _, hm, hm2, hK, .and M N, _, .andR d₁ d₂ => by
      show Inv _ [] .tru (interp p [] done (some (.and M N)))
      rw [interpA_and_eq hsat M N]
      have h₁ := UEntry done hsat hP hm hm2 hK M d₁
      have h₂ := UEntry done hsat hP hm hm2 hK N d₂
      rw [jGoal_tru] at h₁ h₂
      exact .andR h₁ h₂
  | _, _, hm, hm2, hK, .circ P, _, .circR d =>
      UEntry done hsat hP hm hm2 hK (.up P) d
  | _, _, hm, hm2, hK, .up (.atom q), .tru, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.up (.atom q))))
      by_cases hq : atomMem q done = true
      · rw [interpA_atomT_eq hsat hq]; exact nTopIntro
      · rw [interpA_atom_eq hsat hq]
        exact UStab (j := .tru) done hsat hP hm hm2 hK (interpA_atom_eq hsat hq)
          (fun {c Nc rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun hj => nomatch hj)
          s
  | _, _, hm, hm2, hK, .up .fls, .tru, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.up .fls)))
      rw [interpA_fls_eq hsat]
      exact UStab (j := .tru) done hsat hP hm hm2 hK (interpA_fls_eq hsat)
        (fun {c Nc rest} hsp =>
          List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
        (fun {Q' N' N rest} hsp =>
          List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
        (fun {Q' N rest} hsp =>
          List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
        (fun hj => nomatch hj)
        s
  | _, _, hm, hm2, hK, .up (.or P₁ P₂), .tru, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.up (.or P₁ P₂))))
      rw [interpA_or_eq hsat P₁ P₂]
      exact UStab (j := .tru) done hsat hP hm hm2 hK (interpA_or_eq hsat P₁ P₂)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun hj => nomatch hj)
        s
  | _, _, hm, hm2, hK, .up (.down M), .tru, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.up (.down M))))
      rw [interpA_down_eq hsat M]
      exact UStab (j := .tru) done hsat hP hm hm2 hK (interpA_down_eq hsat M)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun hj => nomatch hj)
        s
  | _, _, hm, hm2, hK, .up (.atom q), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.atom q))))
      rw [interpA_circAtom_eq hsat]
      exact UStab (j := .lax) done hsat hP hm hm2 hK (interpA_circAtom_eq hsat)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up .fls, .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ .fls)))
      rw [interpA_circFls_eq hsat]
      exact UStab (j := .lax) done hsat hP hm hm2 hK (interpA_circFls_eq hsat)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.or P₁ P₂), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.or P₁ P₂))))
      rw [interpA_circOr_eq hsat P₁ P₂]
      exact UStab (j := .lax) done hsat hP hm hm2 hK (interpA_circOr_eq hsat P₁ P₂)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.down (.up P')), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.up P')))))
      rw [interpA_circDownUp_eq hsat P']
      exact UStab (j := .lax) done hsat hP hm hm2 hK (interpA_circDownUp_eq hsat P')
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.down (.circ P')), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.circ P')))))
      rw [interpA_circDownCirc_eq hsat P']
      exact UStab (j := .lax) done hsat hP hm hm2 hK (interpA_circDownCirc_eq hsat P')
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.down (.and M₁ M₂)), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.and M₁ M₂)))))
      rw [interpA_circDownAnd_eq hsat M₁ M₂]
      exact UStab (j := .lax) done hsat hP hm hm2 hK (interpA_circDownAnd_eq hsat M₁ M₂)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.down (.imp Q₀ N₀)), .lax, .stable s => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.imp Q₀ N₀)))))
      rw [interpA_circDownImp_eq hsat Q₀ N₀]
      exact UStab (j := .lax) done hsat hP hm hm2 hK (interpA_circDownImp_eq hsat Q₀ N₀)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun _ {R rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  termination_by Γ' K hm hm2 hK G j d =>
    (2 * sum3 [] + sum3 done + 3 ^ wNeg G + 3, 0)
  decreasing_by ljf_dec_a


/-- Stable-phase `∀p` traversal: attack emission, into the possibly
box-wrapped value (forced change #3). -/
def UStab (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD} {L : List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (jGoal j (.up P₀))) = jBox j (nOrAll L) →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (jGoal j (.up P₀))))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N : Neg} {rest : List Neg},
        (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
        nAnd (interp p [] rest (some (.circ Q')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (j = .lax → ∀ {R : Pos} {rest : List Neg},
        (Neg.circ R, rest) ∈ splits done →
        Neg.imp (.down (interp p [.up R] rest none))
          (interp p [.up R] rest (some (jGoal j (.up P₀)))) ∈ L) →
      Stab Γ' j P₀ → Inv (interp p [] done none :: K) [] .tru (jBox j (nOrAll L))
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, .rfoc r =>
      hV ▸ URF done hsat hP hm hm2 hK r
  | _, _, .atom q, _, L, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, .laxOf s => by
      have hV' : interp p [] done (some (.circ (.atom q)))
          = .circ (.down (nOrAll L)) := hV
      obtain rfl := nOrAll_inj (Pos.down.inj (Neg.circ.inj
        ((interpA_circAtom_eq hsat).symm.trans hV')))
      refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
      by_cases hq : atomMem q done = true
      · rw [interpA_atomT_eq hsat hq]; exact nTopIntro
      · rw [interpA_atom_eq hsat hq]
        exact UStab (j := .tru) done hsat hP hm hm2 hK (interpA_atom_eq hsat hq)
          (fun {c Nc rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun hj => nomatch hj)
          s
  | _, _, .fls, _, L, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, .laxOf s => by
      have hV' : interp p [] done (some (.circ .fls))
          = .circ (.down (nOrAll L)) := hV
      obtain rfl := nOrAll_inj (Pos.down.inj (Neg.circ.inj
        ((interpA_circFls_eq hsat).symm.trans hV')))
      refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
      rw [interpA_fls_eq hsat]
      exact UStab (j := .tru) done hsat hP hm hm2 hK (interpA_fls_eq hsat)
        (fun {c Nc rest} hsp =>
            List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
          (fun {Q' N' N rest} hsp =>
            List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
          (fun {Q' N rest} hsp =>
            List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
          (fun hj => nomatch hj)
        s
  | _, _, .or P₁ P₂, _, L, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, .laxOf s => by
      have hV' : interp p [] done (some (.circ (.or P₁ P₂)))
          = .circ (.down (nOrAll L)) := hV
      obtain rfl := nOrAll_inj (Pos.down.inj (Neg.circ.inj
        ((interpA_circOr_eq hsat P₁ P₂).symm.trans hV')))
      refine emitJ .lax (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..)))) ?_
      rw [interpA_or_eq hsat P₁ P₂]
      exact UStab (j := .tru) done hsat hP hm hm2 hK (interpA_or_eq hsat P₁ P₂)
        (fun {c Nc rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun hj => nomatch hj)
        s
  | _, _, .down (.up P'), _, L, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, .laxOf s => by
      have hV' : interp p [] done (some (.circ (.down (.up P'))))
          = .circ (.down (nOrAll L)) := hV
      obtain rfl := nOrAll_inj (Pos.down.inj (Neg.circ.inj
        ((interpA_circDownUp_eq hsat P').symm.trans hV')))
      exact emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..))
        (UEntry done hsat hP hm hm2 hK (.up P')
          (.stable (.laxOf (unStable (negOfDownStab (.up P') s)))))
  | _, _, .down (.circ P'), _, L, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, .laxOf s => by
      have hV' : interp p [] done (some (.circ (.down (.circ P'))))
          = .circ (.down (nOrAll L)) := hV
      obtain rfl := nOrAll_inj (Pos.down.inj (Neg.circ.inj
        ((interpA_circDownCirc_eq hsat P').symm.trans hV')))
      exact emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..))
        (UEntry done hsat hP hm hm2 hK (.circ P') (negOfDownStab (.circ P') s))
  | _, _, .down (.and M₁ M₂), _, L, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, .laxOf s => by
      have hV' : interp p [] done (some (.circ (.down (.and M₁ M₂))))
          = .circ (.down (nOrAll L)) := hV
      obtain rfl := nOrAll_inj (Pos.down.inj (Neg.circ.inj
        ((interpA_circDownAnd_eq hsat M₁ M₂).symm.trans hV')))
      refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
      rw [interpA_down_eq hsat (.and M₁ M₂)]
      exact UStab (j := .tru) done hsat hP hm hm2 hK (interpA_down_eq hsat (.and M₁ M₂))
        (fun {c Nc rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun hj => nomatch hj)
        s
  | _, _, .down (.imp Q₀ N₀), _, L, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, .laxOf s => by
      have hV' : interp p [] done (some (.circ (.down (.imp Q₀ N₀))))
          = .circ (.down (nOrAll L)) := hV
      obtain rfl := nOrAll_inj (Pos.down.inj (Neg.circ.inj
        ((interpA_circDownImp_eq hsat Q₀ N₀).symm.trans hV')))
      refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
      rw [interpA_down_eq hsat (.imp Q₀ N₀)]
      exact UStab (j := .tru) done hsat hP hm hm2 hK (interpA_down_eq hsat (.imp Q₀ N₀))
        (fun {c Nc rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun hj => nomatch hj)
        s
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, @Stab.lfoc _ _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            UStab done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK
              hV qmem dmem cmem bmem s'
        | .imp (.atom c) Nc, _, hd, .impL s_c lf' =>
            if hcp : c = p then
              UpElim done hsat hP hm hm2 hK hV qmem dmem cmem bmem
                hcp hcp hd lf' s_c
            else by
              obtain ⟨rest, hXr⟩ := splitAt done _ hd
              exact emitJ _ (qmem hXr) (by
                simp only [pGuard]; rw [if_neg hcp]
                refine .andR
                  (.stable (TStab done hsat hP hm hm2 hK hcp s_c)) ?_
                exact qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hcp
                  (TStab done hsat hP hm hm2 hK hcp s_c)
                  (aMinF [Nc] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr)
                      (.stable (.lfoc (List.mem_cons_self ..)
                        (lf'.wk (Sub.grow _)))))))
        | .imp (.down (.imp Q' N')) N, _, hd, .impL s_d lf' => by
            obtain ⟨rest, hXr⟩ := splitAt done _ hd
            exact emitJ _ (dmem hXr)
              (.andR
                (dykAntC done rest _ _ Q' N' N hsat hP hXr hm hm2 hK s_d)
                (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
                  (dykAntC done rest _ _ Q' N' N hsat hP hXr hm hm2 hK s_d)
                  (aMinF [N] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr)
                      (.stable (.lfoc (List.mem_cons_self ..)
                        (lf'.wk (Sub.grow _))))))))
        | .imp (.down (.circ Q')) N, _, hd, .impL s_d lf' => by
            obtain ⟨rest, hXr⟩ := splitAt done _ hd
            exact emitJ _ (cmem hXr)
              (.andR
                (cAnt done rest _ _ Q' N hsat hP hXr hm hm2 hK s_d)
                (cimpAssembleN (interpE_eq hsat) (cimpConjMem hXr)
                  (cAnt done rest _ _ Q' N hsat hP hXr hm hm2 hK s_d)
                  (aMinF [N] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr)
                      (.stable (.lfoc (List.mem_cons_self ..)
                        (lf'.wk (Sub.grow _))))))))
        | .circ Q, _, hd, .circL d => by
            obtain ⟨rest, hXr⟩ := splitAt done _ hd
            have haux := aMinF [.up Q] rest _ (.up _)
              (hP.sub (splits_sub hXr)) hK
              (boxClean (splitHyp hm hXr)
                (.stable (.lfoc (List.mem_cons_self ..)
                  (.rel (d.wk (Sub.grow _))))))
            exact emitJ .lax (bmem rfl hXr)
              (.impR (.downL (haux.wk (fun Z hZ => by
                rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))))
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        keepFold (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
          (ULF done hsat hP hm hm2 hK hV qmem dmem cmem bmem
            (hK _ ((hm _ h).resolve_left hd)) lf)
  termination_by Γ' K P₀ j L hm hm2 hK hV qmem dmem cmem bmem s =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf s)
  decreasing_by ljf_dec_a


/-- Right-focus `∀p` traversal: the goal-driven disjuncts, in value form. -/
def URF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      RFocus Γ' j P₀ →
      Inv (interp p [] done none :: K) [] .tru
        (interp p [] done (some (jGoal j (.up P₀))))
  | _, _, .atom q, .tru, hm, hm2, hK, .init h => by
      show Inv _ [] .tru (interp p [] done (some (.up (.atom q))))
      by_cases hq : atomMem q done = true
      · rw [interpA_atomT_eq hsat hq]; exact nTopIntro
      · have hk : Neg.up (.atom q) ∈ _ :=
          (hm _ h).resolve_left (fun hd => hq (atomMem_of_mem hd))
        have hqp : ¬ q = p := fun e => (hK _ hk) e
        rw [interpA_atom_eq hsat hq]
        refine nOrAllIntro (List.mem_append_left _ ?_)
          (.stable (.rfoc (.init (List.mem_cons_of_mem _ hk))))
        rw [atomHead, if_neg hqp]
        exact List.mem_cons_self ..
  | _, _, .atom q, .lax, hm, hm2, hK, .init h => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.atom q))))
      rw [interpA_circAtom_eq hsat]
      refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
      by_cases hq : atomMem q done = true
      · rw [interpA_atomT_eq hsat hq]; exact nTopIntro
      · have hk : Neg.up (.atom q) ∈ _ :=
          (hm _ h).resolve_left (fun hd => hq (atomMem_of_mem hd))
        have hqp : ¬ q = p := fun e => (hK _ hk) e
        rw [interpA_atom_eq hsat hq]
        refine nOrAllIntro (List.mem_append_left _ ?_)
          (.stable (.rfoc (.init (List.mem_cons_of_mem _ hk))))
        rw [atomHead, if_neg hqp]
        exact List.mem_cons_self ..
  | _, _, .or P₁ P₂, .tru, hm, hm2, hK, .or1 r₁ => by
      show Inv _ [] .tru (interp p [] done (some (.up (.or P₁ P₂))))
      rw [interpA_or_eq hsat P₁ P₂]
      exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..))
        (URF done hsat hP hm hm2 hK r₁)
  | _, _, .or P₁ P₂, .lax, hm, hm2, hK, .or1 r₁ => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.or P₁ P₂))))
      rw [interpA_circOr_eq hsat P₁ P₂]
      exact emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..))
        (URF done hsat hP hm hm2 hK r₁)
  | _, _, .or P₁ P₂, .tru, hm, hm2, hK, .or2 r₂ => by
      show Inv _ [] .tru (interp p [] done (some (.up (.or P₁ P₂))))
      rw [interpA_or_eq hsat P₁ P₂]
      exact nOrAllIntro (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (URF done hsat hP hm hm2 hK r₂)
  | _, _, .or P₁ P₂, .lax, hm, hm2, hK, .or2 r₂ => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.or P₁ P₂))))
      rw [interpA_circOr_eq hsat P₁ P₂]
      exact emitJ .lax (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (URF done hsat hP hm hm2 hK r₂)
  | _, _, .down M, .tru, hm, hm2, hK, .rel dI => by
      show Inv _ [] .tru (interp p [] done (some (.up (.down M))))
      rw [interpA_down_eq hsat M]
      have h₁ := UEntry done hsat hP hm hm2 hK M dI
      rw [jGoal_tru] at h₁
      exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..)) h₁
  | _, _, .down (.up P'), .lax, hm, hm2, hK, .rel dI => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.up P')))))
      rw [interpA_circDownUp_eq hsat P']
      exact emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..))
        (UEntry done hsat hP hm hm2 hK (.up P') dI)
  | _, _, .down (.circ P'), .lax, hm, hm2, hK, .rel dI => by
      show Inv _ [] .tru (interp p [] done (some (.circ (.down (.circ P')))))
      rw [interpA_circDownCirc_eq hsat P']
      exact emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..))
        (UEntry done hsat hP hm hm2 hK (.circ P') dI)
  | _, _, .down (.and _ _), .lax, _, _, _, .rel dI => nomatch dI
  | _, _, .down (.imp _ _), .lax, _, _, _, .rel dI => nomatch dI
  termination_by Γ' K P₀ j hm hm2 hK r =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf r)
  decreasing_by ljf_dec_a


/-- Left focus on a kept hypothesis, `∀p` mode: rebuilt at the flag,
concluding the `jChain` positive. -/
def ULF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD} {L : List Neg} {H : Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (jGoal j (.up P₀))) = jBox j (nOrAll L) →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (jGoal j (.up P₀))))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N : Neg} {rest : List Neg},
        (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
        nAnd (interp p [] rest (some (.circ Q')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (j = .lax → ∀ {R : Pos} {rest : List Neg},
        (Neg.circ R, rest) ∈ splits done →
        Neg.imp (.down (interp p [.up R] rest none))
          (interp p [.up R] rest (some (jGoal j (.up P₀)))) ∈ L) →
      PFreeN p H →
      LFoc Γ' H j P₀ → LFoc (interp p [] done none :: K) H j (jChain j L)
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, .rel d =>
      .rel (UInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
        (PFreeΩ.cons hH PFreeΩ.nil) d)
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, .circL d =>
      .circL (UInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
        (PFreeΩ.cons hH PFreeΩ.nil) d)
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (ULF done hsat hP hm hm2 hK hV qmem dmem cmem bmem hH.2 lf)
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, .and1 lf =>
      .and1 (ULF done hsat hP hm hm2 hK hV qmem dmem cmem bmem hH.1 lf)
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, .and2 lf =>
      .and2 (ULF done hsat hP hm hm2 hK hV qmem dmem cmem bmem hH.2 lf)
  termination_by Γ' K P₀ j L H hm hm2 hK hV qmem dmem cmem bmem hH lf =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf lf)
  decreasing_by ljf_dec_a


/-- Inversion, `∀p` mode, goal re-targeted to the `jChain` positive. -/
def UInvG (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD} {L : List Neg} {Ω : List Pos},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (jGoal j (.up P₀))) = jBox j (nOrAll L) →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (jGoal j (.up P₀))))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N : Neg} {rest : List Neg},
        (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
        nAnd (interp p [] rest (some (.circ Q')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (j = .lax → ∀ {R : Pos} {rest : List Neg},
        (Neg.circ R, rest) ∈ splits done →
        Neg.imp (.down (interp p [.up R] rest none))
          (interp p [.up R] rest (some (jGoal j (.up P₀)))) ∈ L) →
      PFreeΩ p Ω →
      Inv Γ' Ω j (.up P₀) →
      Inv (interp p [] done none :: K) Ω j (.up (jChain j L))
  | _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, _, .stable s =>
      stabFold (UStab done hsat hP hm hm2 hK hV qmem dmem cmem bmem s)
  | _, _, _, _, _, .or PA PB :: _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hΩ, .orL d₁ d₂ =>
      .orL (UInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
              (hΩ.tail.cons hΩ.head.1) d₁)
           (UInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
              (hΩ.tail.cons hΩ.head.2) d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, _, .down M₀ :: _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hΩ, .downL d =>
      .downL (((UInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hΩ.head hK) hV qmem dmem cmem bmem hΩ.tail d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, _, _, _, .atom a :: _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hΩ, .atomL d =>
      .atomL (((UInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom a)) from hΩ.head) hK)
          hV qmem dmem cmem bmem hΩ.tail d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K P₀ j L Ω hm hm2 hK hV qmem dmem cmem bmem hΩ d =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf d)
  decreasing_by ljf_dec_a


/-- The `p`-fire eliminator, `∀p` mode: same composition, attack emission. -/
def UpElim (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {j : JD} {L : List Neg} {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (jGoal j (.up P₀))) = jBox j (nOrAll L) →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (jGoal j (.up P₀))))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N : Neg} {rest : List Neg},
        (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
        nAnd (interp p [] rest (some (.circ Q')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (j = .lax → ∀ {R : Pos} {rest : List Neg},
        (Neg.circ R, rest) ∈ splits done →
        Neg.imp (.down (interp p [.up R] rest none))
          (interp p [.up R] rest (some (jGoal j (.up P₀)))) ∈ L) →
      a = p → b = p → Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      Stab Γ' .tru (.atom b) →
      Inv (interp p [] done none :: K) [] .tru (jBox j (nOrAll L))
  | _, _, _, _, _, _, a, b, hm, _, hK, _, _, _, _, _, ha, hb, hXpkg, _, .rfoc (.init h) =>
      False.elim (by
        rcases hm _ h with hd | hk
        · have h1 := atomMem_of_mem hd
          have h2 := saturated_atom_absent hsat hXpkg
          rw [hb.trans ha.symm] at h1
          rw [h1] at h2; cases h2
        · exact (hK _ hk) hb)
  | _, _, _, _, _, _, a, b, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, ha, hb, hXpkg, lfP,
      @Stab.lfoc _ _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            UpElim done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK
              hV qmem dmem cmem bmem
              ha hb hXpkg (lfP.wk (Sub.grow _)) s'
        | .imp (.atom c) Nc, _, hd, .impL s_c lf_c =>
            if hcp : c = p then
              UpElim done hsat hP hm hm2 hK hV qmem dmem cmem bmem
                ha hcp hXpkg lfP s_c
            else by
              obtain ⟨rest, hXr⟩ := splitAt done _ hd
              exact emitJ _ (qmem hXr) (by
                simp only [pGuard]; rw [if_neg hcp]
                refine .andR
                  (.stable (TStab done hsat hP hm hm2 hK hcp s_c)) ?_
                exact qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hcp
                  (TStab done hsat hP hm hm2 hK hcp s_c)
                  (aMinF [Nc] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr) (.stable
                      (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                        (.impL
                          ((hb.trans ha.symm) ▸
                            Stab.lfoc (List.mem_cons_self ..)
                              (lf_c.wk (Sub.grow _)))
                          (lfP.wk (Sub.grow _))))))))
        | .imp (.down (.imp Q' N')) N_d, _, hd, .impL s_d lf_d => by
            obtain ⟨rest, hXr⟩ := splitAt done _ hd
            exact emitJ _ (dmem hXr)
              (.andR
                (dykAntC done rest _ _ Q' N' N_d hsat hP hXr hm hm2 hK s_d)
                (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
                  (dykAntC done rest _ _ Q' N' N_d hsat hP hXr hm hm2 hK s_d)
                  (aMinF [N_d] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr) (.stable
                      (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                        (.impL
                          ((hb.trans ha.symm) ▸
                            Stab.lfoc (List.mem_cons_self ..)
                              (lf_d.wk (Sub.grow _)))
                          (lfP.wk (Sub.grow _)))))))))
        | .imp (.down (.circ Q')) N_c, _, hd, .impL s_c lf_c => by
            obtain ⟨rest, hXr⟩ := splitAt done _ hd
            exact emitJ _ (cmem hXr)
              (.andR
                (cAnt done rest _ _ Q' N_c hsat hP hXr hm hm2 hK s_c)
                (cimpAssembleN (interpE_eq hsat) (cimpConjMem hXr)
                  (cAnt done rest _ _ Q' N_c hsat hP hXr hm hm2 hK s_c)
                  (aMinF [N_c] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr) (.stable
                      (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                        (.impL
                          ((hb.trans ha.symm) ▸
                            Stab.lfoc (List.mem_cons_self ..)
                              (lf_c.wk (Sub.grow _)))
                          (lfP.wk (Sub.grow _)))))))))
        | .circ _, _, _, lf => nomatch lf
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        keepFold (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
          (UpLF done hsat hP hm hm2 hK hV qmem dmem cmem bmem
            (hK _ ((hm _ h).resolve_left hd)) ha hb hXpkg lfP lf)
  termination_by Γ' K M P₀ j L a b hm hm2 hK hV qmem dmem cmem bmem ha hb hXpkg lfP s =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf s)
  decreasing_by ljf_dec_a


/-- Left focus on a kept hypothesis, inside an `∀p`-mode `p`-proof. -/
def UpLF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {j : JD} {L : List Neg} {H : Neg}
      {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (jGoal j (.up P₀))) = jBox j (nOrAll L) →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (jGoal j (.up P₀))))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N : Neg} {rest : List Neg},
        (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
        nAnd (interp p [] rest (some (.circ Q')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (j = .lax → ∀ {R : Pos} {rest : List Neg},
        (Neg.circ R, rest) ∈ splits done →
        Neg.imp (.down (interp p [.up R] rest none))
          (interp p [.up R] rest (some (jGoal j (.up P₀)))) ∈ L) →
      PFreeN p H → a = p → b = p → Neg.imp (.atom a) M ∈ done →
      LFoc Γ' M j P₀ →
      LFoc Γ' H .tru (.atom b) → LFoc (interp p [] done none :: K) H j (jChain j L)
  | _, _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, ha, hb, hXpkg,
      lfP, .rel d =>
      .rel (UpInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
        (PFreeΩ.cons hH PFreeΩ.nil) ha hb hXpkg lfP d)
  | _, _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, ha, hb, hXpkg,
      lfP, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (UpLF done hsat hP hm hm2 hK hV qmem dmem cmem bmem hH.2 ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, ha, hb, hXpkg,
      lfP, .and1 lf =>
      .and1 (UpLF done hsat hP hm hm2 hK hV qmem dmem cmem bmem hH.1 ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hH, ha, hb, hXpkg,
      lfP, .and2 lf =>
      .and2 (UpLF done hsat hP hm hm2 hK hV qmem dmem cmem bmem hH.2 ha hb hXpkg lfP lf)
  termination_by Γ' K M P₀ j L H a b hm hm2 hK hV qmem dmem cmem bmem hH ha hb hXpkg lfP lf =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf lf)
  decreasing_by ljf_dec_a


/-- Inversion inside an `∀p`-mode `p`-proof. -/
def UpInvG (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {j : JD} {L : List Neg} {Ω : List Pos}
      {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (jGoal j (.up P₀))) = jBox j (nOrAll L) →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (jGoal j (.up P₀))))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N : Neg} {rest : List Neg},
        (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
        nAnd (interp p [] rest (some (.circ Q')))
             (interp p [N] rest (some (jGoal j (.up P₀)))) ∈ L) →
      (j = .lax → ∀ {R : Pos} {rest : List Neg},
        (Neg.circ R, rest) ∈ splits done →
        Neg.imp (.down (interp p [.up R] rest none))
          (interp p [.up R] rest (some (jGoal j (.up P₀)))) ∈ L) →
      PFreeΩ p Ω → a = p → b = p → Neg.imp (.atom a) M ∈ done →
      LFoc Γ' M j P₀ →
      Inv Γ' Ω .tru (.up (.atom b)) →
      Inv (interp p [] done none :: K) Ω j (.up (jChain j L))
  | _, _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, _, ha, hb, hXpkg,
      lfP, .stable s =>
      stabFold (UpElim done hsat hP hm hm2 hK hV qmem dmem cmem bmem ha hb hXpkg lfP s)
  | _, _, _, _, _, _, .or PA PB :: _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hΩ, ha, hb, hXpkg,
      lfP, .orL d₁ d₂ =>
      .orL (UpInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
              (hΩ.tail.cons hΩ.head.1) ha hb hXpkg lfP d₁)
           (UpInvG done hsat hP hm hm2 hK hV qmem dmem cmem bmem
              (hΩ.tail.cons hΩ.head.2) ha hb hXpkg lfP d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, _, _, .down M₀ :: _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hΩ, ha, hb, hXpkg,
      lfP, .downL d =>
      .downL (((UpInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hΩ.head hK) hV qmem dmem cmem bmem hΩ.tail ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, _, _, _, _, .atom c :: _, _, _, hm, hm2, hK, hV, qmem, dmem, cmem, bmem, hΩ, ha, hb, hXpkg,
      lfP, .atomL d =>
      .atomL (((UpInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom c)) from hΩ.head) hK)
          hV qmem dmem cmem bmem hΩ.tail ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K M P₀ j L Ω a b hm hm2 hK hV qmem dmem cmem bmem hΩ ha hb hXpkg lfP d =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf d)
  decreasing_by ljf_dec_a


/-- The Dyckhoff antecedent dispatch, discharged: commute, interpolate at
the residual station, project the E-res conjunct. -/
def dykAntC : ∀ (done rest K Γ' : List Neg) (Q' : Pos) (N' N : Neg),
    Saturated done → ParkedCtx done →
    (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
    (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
    Stab Γ' .tru (.down (.imp Q' N')) →
    Inv (interp p [] done none :: K) [] .tru
        (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
  | done, rest, K, Γ', Q', N', N, hsat, hP, hXr, hm, hm2, hK, s =>
      simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_cons_self ..))
            ((interpE_eq hsat).symm ▸ lfocAndAll (dykConjMem hXr) (.and2 lf)))
        (Sub.grow _)
        (aMinF [.imp (.down N') N] rest K (.imp Q' N')
          (ParkedCtx.sub (splits_sub hXr) hP) hK
          (dykCommute (p := p) hXr hm s))
  termination_by done rest K Γ' Q' N' N hsat hP hXr hm hm2 hK s =>
    (2 * sum3 [Neg.imp (Pos.down N') N] + sum3 rest +
      3 ^ wNeg (Neg.imp Q' N') + 5, 0)
  decreasing_by ljf_dec_a


end

/-- **SatE2, conditional on the isolated modal obligation.** -/
def satE2 : SatE2 p := fun done Δ ψ hsat hP hΔ hψ {j} d =>
  TInv cAnt done hsat hP (fun Z hZ => List.mem_append.mp hZ)
    (fun Z hZ => List.mem_append_left _ hZ) hΔ
    (fun _ h => absurd h (List.not_mem_nil)) hψ d

/-- **SatA2, conditional on the isolated modal obligation.** -/
def satA2 : SatA2 p := fun done Δ G hsat hP hΔ {j} d =>
  UEntry cAnt done hsat hP (fun Z hZ => List.mem_append.mp hZ)
    (fun Z hZ => List.mem_append_left _ hZ) hΔ G d

/-- **The Dyckhoff antecedent dispatch, as originally isolated.** -/
def dykAnt : DykAnt p :=
  fun done rest K Γ' Q' N' N hsat hP hXr hm hm2 hK s =>
    dykAntC cAnt done rest K Γ' Q' N' N hsat hP hXr hm hm2 hK s

end LJFO
