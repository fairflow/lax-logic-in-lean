/-
LJF◯ — the cofinality FAMILY for the parking interpolant `interpP`
(route (B), node N0c over node N0e).

`LJF/O.lean`'s weight-founded minimality family (an 18-definition mutual,
`eMinF` … `dykAntC`), re-authored in fuel-carrying form over `interpP`.
`LJF/OFuelPCof.lean` states the two entry points `TInvP`/`UEntryP` and
proves everything downstream of them; this module inhabits them.

## What changes against `LJF/O.lean`

`interpP` has no chain-monotonicity lemma, so no traversal can return a
derivation at one fuel: every value is an upward-closed witness
(`UpFrom` on the `∃p` side, `UpFrom2` on the `∀p` side,
`LJF/OFuelMin.lean` Part 1), every clause with more than one sub-result
combines thresholds by `max`, and every `interpP` unfolding peels one
fuel unit (`UpFrom.mk1` / `UpFrom2.mk1`).  `LJF/OFuelPMin.lean`'s
`eMinPP`/`aMinPP` are the worked precedent for the processing phase;
this module is the same bookkeeping through the saturated phase.

Three further differences, all forced by `interpP`'s definition
(`LJF/OFuelP.lean`):

* the station carries EIGHT parked shapes (`ParkedNP`), not five, so the
  three `nomatch` arms of `LJF/O.lean`'s dispatch that refuted
  `(Q₁∨Q₂) ⊃ N`, `↓↑P′ ⊃ N` and `↓(M₁∧M₂) ⊃ N` become real clauses, of
  the same form as the ◯-implication clause;
* the row list of a `∀p` aggregate is fuel-indexed: `UStab`'s parameter
  block `L`/`hV`/`qmem`/… becomes `L : Nat → List Neg` with the
  memberships quantified over the fuel;
* the antecedent guard of every parked implication sits at the FULL
  station, so `dykCommute` and `negOfDownStab` are never called.

## What is conditional, and why

Two typed obligations, in the `CimpAnt` idiom of `LJF/O.lean` (a
`def … : Type`, never a sorried theorem):

* `ParkAntP` (`LJF/OFuelPCof.lean`) — the antecedent guard of the four
  parked implications whose antecedent is a POSITIVE, at goal `↑Q`.  It
  is an instance of `∀p`-cofinality itself at the same station
  (`parkAntP_of_satA2P`, proved), and `LJF/OFuelHeight.lean` §10.4 is the
  height fact that makes it a legitimate recursive call.  Taking it as a
  recursive call requires re-founding the family on
  `μ = (normalised height, station weight, size)`; this module is founded
  on `LJF/O.lean`'s `(station weight, size)` pair, so it takes the
  obligation as a parameter.
* `DykAntP` (below) — the same for the Dyckhoff shape
  `↓(Q′ ⊃ N′) ⊃ N`.  It is NOT an instance of `ParkAntP`: `interpP`'s
  Dyckhoff row guards its fire by `A(done ⇒ Q′ ⊃ N′)`, a NEGATIVE goal,
  while the dispatch of §10.4 supplies `A(done ⇒ ↑↓(Q′ ⊃ N′))`, and the
  `↑↓` aggregate is a DISJUNCTION with the wanted formula as one
  disjunct (`interpPA_down_eq`), so it does not project.  Bridging the
  two would need `negOfDownStab` at an implication body, whose height
  rise is unbounded (`LJF/OFuelHeight.lean` §7.3).  Recorded here as an
  obligation rather than papered over.

Nothing in `LJF/OCore.lean`, `LJF/O.lean`, `LJF/OFuel*.lean` is touched;
this module is purely additive.
-/
import LJF.OFuelPCof

namespace LJFO

/-! # Part 1: the generic station-descent lemmas

`LJF/O.lean`'s descent farm names one lemma per parked shape
(`dec_fireT`/`dec_fireS` for `a ⊃ N`, `dec_dykT`/`dec_dykS` for the
Dyckhoff shape, `dec_cimpF` for the ◯-implication).  `interpP` parks
three more, and all eight fire the same way, so the lemma is stated once,
generic in the antecedent positive: the only fact used is
`1 ≤ wPos Q`. -/

/-- **The generic parked-implication fire drop.**  Firing `Q ⊃ N` at a
station moves `3^(wPos Q + wNeg N + 1)` out and `2·3^(wNeg N)` in. -/
theorem dec_parkT {done rest : List Neg} {Q : Pos} {N : Neg}
    (h : (Neg.imp Q N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg] at hs
  have := p3_2 (a := wNeg N) (c := wPos Q + wNeg N + 1)
    (by have := wPos_pos Q; omega)
  omega

/-- The same drop with slack `9`, the shape the `∀p` measures need. -/
theorem dec_parkS {done rest : List Neg} {Q : Pos} {N : Neg}
    (h : (Neg.imp Q N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg] at hs
  have h1 := p3_mono (a := wNeg N + 1 + 1) (b := wPos Q + wNeg N + 1)
    (by have := wPos_pos Q; omega)
  have h2 := p3_succ (wNeg N)
  have h3 := p3_succ (wNeg N + 1)
  have h4 := p3_mono (a := 1) (b := wNeg N) (wNeg_pos N)
  omega

/-- Removing any member shrinks the station (the E-res component). -/
theorem dec_restT {done rest : List Neg} {X : Neg}
    (h : (X, rest) ∈ splits done) : sum3 rest < sum3 done := by
  have hs := splits_sum h
  have := p3_pos (wNeg X)
  omega

/-! # Part 2: the fuel-carrying assemblers

`LJF/O.lean`'s `atomAssemble`, `qAssembleN`, `boxAssembleN` transposed to
`interpP`.  The ◯-implication assembler `cimpAssembleN` is already
generic in `LJF/OFuelPCof.lean` (`parkAssembleP`, with `parkFireE` its
`UpFrom` form); Part 3 adds the `UpFrom2` form the `∀p` side needs. -/

variable {p : String}

/-- A surviving atom's own row, at fuel `f+1`. -/
def atomAssembleP {f : Nat} {done K : List Neg} {a : String} {L : List Neg}
    (hE : interpP p (f + 1) [] done none = nAndAll L)
    (hmem : pGuard p a nTop (.up (.atom a)) ∈ L) (hap : ¬ a = p) :
    Stab (interpP p (f + 1) [] done none :: K) .tru (.atom a) :=
  .lfoc (List.mem_cons_self ..)
    (hE.symm ▸ lfocAndAll hmem (by
      simp only [pGuard]; rw [if_neg hap]
      exact LFoc.rel (idPos (.atom a) _ _)))

/-- Fire a parked `a ⊃ N` whose atom has arrived, at fuel `f+1`. -/
def qAssembleP {f : Nat} {done rest K : List Neg} {a : String} {N C : Neg}
    {L : List Neg}
    (hE : interpP p (f + 1) [] done none = nAndAll L)
    (hmem : pGuard p a nTop (.imp (.atom a) (interpP p f [N] rest none)) ∈ L)
    (hap : ¬ a = p)
    (sa : Stab (interpP p (f + 1) [] done none :: K) .tru (.atom a))
    {j : JD} (δ : Inv (interpP p f [N] rest none :: K) [] j C) :
    Inv (interpP p (f + 1) [] done none :: K) [] j C :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem (by
          simp only [pGuard]; rw [if_neg hap]
          exact LFoc.impL (sa.wk hs) lf)))
    (Sub.grow _) δ

/-- Open a parked box, at fuel `f+1`. -/
def boxAssembleP {f : Nat} {done rest K : List Neg} {Q P : Pos}
    {L : List Neg}
    (hE : interpP p (f + 1) [] done none = nAndAll L)
    (hmem : Neg.circ (.down (interpP p f [.up Q] rest none)) ∈ L)
    (δ : Inv (interpP p f [.up Q] rest none :: K) [] .lax (.up P)) :
    Stab (interpP p (f + 1) [] done none :: K) .lax P :=
  .lfoc (List.mem_cons_self ..)
    (hE.symm ▸ lfocAndAll hmem
      (.circL (.downL (δ.wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))))

/-! # Part 3: the `∀p` attack rows, in two-fuel form

The `∃p` side has `parkFireE` (`LJF/OFuelPCof.lean`).  These are its
`∀p` counterparts: the row of a `∀p` aggregate is `A(guard) ∧ A(fire)`,
so a clause emits the row by `emitJ` and proves both conjuncts, the
second through the `∃p` assembler.  The row list is fuel-indexed
(`L : Nat → List Neg`), with `hV` identifying the aggregate at fuel
`f+1` with the rows at fuel `f`. -/

/-- **The attack row of a parked implication**, all five shapes: the
retained guard, the fire through the `∃p` row, the residual ignored. -/
def parkFireA {done rest K : List Neg} {G' N : Neg} {P₀ : Pos}
    {R : Nat → Neg} {j : JD} {L : Nat → List Neg}
    (hsat : Saturated done)
    (hV : ∀ f, interpP p (f + 1) [] done (some (jGoal j (.up P₀)))
      = jBox j (nOrAll (L f)))
    (hmemE : ∀ f, nAnd (.imp (.down (interpP p f [] done (some G')))
                             (interpP p f [N] rest none)) (R f)
              ∈ eConjRowsP p f done)
    (hmemA : ∀ f, nAnd (interpP p f [] done (some G'))
                       (interpP p f [N] rest (some (jGoal j (.up P₀))))
              ∈ L f)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some G'))))
    (cont : UpFrom2 (fun e f => Inv (interpP p e [N] rest none :: K) [] .tru
              (interpP p f [N] rest (some (jGoal j (.up P₀)))))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (interpP p f [] done (some (jGoal j (.up P₀))))) :=
  UpFrom2.mk1 (max want.1 cont.1) (fun e' f' he' hf' => by
    have hw : want.1 ≤ e' := Nat.le_trans (Nat.le_max_left _ _) he'
    have hw' : want.1 ≤ f' := Nat.le_trans (Nat.le_max_left _ _) hf'
    have hc : cont.1 ≤ e' := Nat.le_trans (Nat.le_max_right _ _) he'
    have hc' : cont.1 ≤ f' := Nat.le_trans (Nat.le_max_right _ _) hf'
    rw [hV f']
    exact emitJ j (hmemA f')
      (.andR (want.2 (e' + 1) f' (Nat.le_trans hw (Nat.le_succ _)) hw')
        (parkAssembleP (interpPE_eq hsat) (hmemE e')
          (want.2 (e' + 1) e' (Nat.le_trans hw (Nat.le_succ _)) hw)
          (cont.2 e' f' hc hc'))))

/-- **The attack row of a parked `a ⊃ N` whose atom has arrived.** -/
def qFireA {done rest K : List Neg} {a : String} {N : Neg} {P₀ : Pos}
    {j : JD} {L : Nat → List Neg}
    (hsat : Saturated done) (hap : ¬ a = p)
    (hV : ∀ f, interpP p (f + 1) [] done (some (jGoal j (.up P₀)))
      = jBox j (nOrAll (L f)))
    (hXr : (Neg.imp (.atom a) N, rest) ∈ splits done)
    (hmemA : ∀ f, pGuard p a nBot (nAnd (.up (.atom a))
      (interpP p f [N] rest (some (jGoal j (.up P₀))))) ∈ L f)
    (sa : UpFrom (fun e => Stab (interpP p e [] done none :: K) .tru (.atom a)))
    (cont : UpFrom2 (fun e f => Inv (interpP p e [N] rest none :: K) [] .tru
              (interpP p f [N] rest (some (jGoal j (.up P₀)))))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (interpP p f [] done (some (jGoal j (.up P₀))))) :=
  UpFrom2.mk1 (max sa.1 cont.1) (fun e' f' he' hf' => by
    have hs : sa.1 ≤ e' + 1 :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) he') (Nat.le_succ _)
    have hc : cont.1 ≤ e' := Nat.le_trans (Nat.le_max_right _ _) he'
    have hc' : cont.1 ≤ f' := Nat.le_trans (Nat.le_max_right _ _) hf'
    rw [hV f']
    refine emitJ j (hmemA f') ?_
    simp only [pGuard]; rw [if_neg hap]
    exact .andR (.stable (sa.2 (e' + 1) hs))
      (qAssembleP (interpPE_eq hsat) (qimpConjMemP hXr) hap (sa.2 (e' + 1) hs)
        (cont.2 e' f' hc hc')))

/-- **The attack row of a parked box** — the lax-only one. -/
def boxFireA {done rest K : List Neg} {Q : Pos} {P₀ : Pos}
    {L : Nat → List Neg}
    (hV : ∀ f, interpP p (f + 1) [] done (some (jGoal (.lax) (.up P₀)))
      = jBox .lax (nOrAll (L f)))
    (hmemA : ∀ f, Neg.imp (.down (interpP p f [.up Q] rest none))
      (interpP p f [.up Q] rest (some (jGoal (.lax) (.up P₀)))) ∈ L f)
    (cont : UpFrom2 (fun e f => Inv (interpP p e [.up Q] rest none :: K) [] .tru
              (interpP p f [.up Q] rest (some (jGoal (.lax) (.up P₀)))))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (interpP p f [] done (some (jGoal (.lax) (.up P₀))))) :=
  UpFrom2.mk1 cont.1 (fun e' f' he' hf' => by
    rw [hV f']
    exact emitJ .lax (hmemA f')
      (.impR (.downL ((cont.2 f' f' hf' hf').wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))))

/-! # Part 4: the Dyckhoff antecedent obligation

`interpP`'s Dyckhoff rows guard their fire by `A(done ⇒ Q′ ⊃ N′)` — the
antecedent's own NEGATIVE goal at the full station (`LJF/OFuelP.lean`
(c)).  The generic dispatch of `LJF/OFuelHeight.lean` §10.4 delivers
`A(done ⇒ ↑Q)` for an antecedent POSITIVE `Q`, which at `Q = ↓(Q′ ⊃ N′)`
is `A(done ⇒ ↑↓(Q′ ⊃ N′))`; by `interpPA_down_eq` that aggregate is a
DISJUNCTION whose first disjunct is the wanted `A(done ⇒ Q′ ⊃ N′)`, so it
does not project, and the only transformer that would bridge the two —
`negOfDownStab` at an implication body — rises unboundedly
(`LJF/OFuelHeight.lean` §7.3).  So the Dyckhoff guard is isolated, as
`CimpAnt` is in `LJF/O.lean`. -/

/-- **The Dyckhoff antecedent dispatch obligation.** -/
def DykAntP (p : String) : Type :=
  ∀ (done K Γ' : List Neg) (Q' : Pos) (N' N : Neg),
    Saturated done → ParkedCtxP done →
    Neg.imp (.down (.imp Q' N')) N ∈ done →
    (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
    Stab Γ' .tru (.down (.imp Q' N')) →
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (interpP p f [] done (some (.imp Q' N'))))

end LJFO

/-! ### Axiom audit -/

#axioms_within LJFO.dec_parkT [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.dec_parkS [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.dec_restT [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.atomAssembleP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.qAssembleP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.boxAssembleP [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.parkFireA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.qFireA [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.boxFireA [propext, Classical.choice, Quot.sound]

#axioms_within LJFO.dec_parkT [propext, Quot.sound]
#axioms_within LJFO.dec_parkS [propext, Quot.sound]
#axioms_within LJFO.dec_restT [propext, Quot.sound]
#axioms_within LJFO.qAssembleP [propext, Quot.sound]
#axioms_within LJFO.boxAssembleP [propext, Quot.sound]
#axioms_within LJFO.parkFireA [propext, Quot.sound]
#axioms_within LJFO.qFireA [propext, Quot.sound]
#axioms_within LJFO.boxFireA [propext, Quot.sound]
