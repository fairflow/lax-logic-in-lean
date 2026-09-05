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

/-- `dec_park` at a shared goal offset: parking the head of `todo` pays
`3^(wNeg X)` out of the doubled `todo` side.  `LJF/O.lean`'s farm names
the offset-free form and then one `p3_pos` alternative per parked shape;
the three shapes `interpP` adds are covered by stating the offset. -/
theorem dec_parkG {t d e g : Nat} :
    2 * t + (3 ^ e + d) + g < 2 * (3 ^ e + t) + d + g := by
  have := p3_pos e; omega

/-- `dec_parkG` at the `∀p` measure, whose offset is a SUM (the goal
weight and the family's constant). -/
theorem dec_parkG2 {t d e g h : Nat} :
    2 * t + (3 ^ e + d) + g + h < 2 * (3 ^ e + t) + d + g + h := by
  have := p3_pos e; omega

/-- Removing any member shrinks the station (the E-res component). -/
theorem dec_restT {done rest : List Neg} {X : Neg}
    (h : (X, rest) ∈ splits done) : sum3 rest < sum3 done := by
  have hs := splits_sum h
  have := p3_pos (wNeg X)
  omega

set_option hygiene false in
/-- **The descent farm for the parking family.**  `LJF/O.lean`'s two
farms, extended by the drops its shape-by-shape alternatives do not cover:
the generic parked-implication fire (`dec_parkS`/`dec_parkT`), the generic
parking drop at one and at two goal offsets (`dec_parkG`/`dec_parkG2`,
where `LJF/O.lean` names one `p3_pos` alternative per parked shape), the
`↓◯P′` release (two `p3_succ` steps, where `LJF/O.lean` released through
`negOfDownStab` at `◯P′` and needed one), and each of these behind
`Prod.Lex.left` for the pairs whose second components differ. -/
macro "ljf_dec_p" : tactic => `(tactic| (
    all_goals first
      | ljf_dec_e
      | ljf_dec_a
      | (simp_wf
         try simp only [sum3, sum3_append, goalW, wNeg, wPos]
         first
           | exact dec_parkG
           | exact dec_parkG2
           | (have h1 := dec_parkS (by assumption); omega)
           | (have h1 := dec_parkT (by assumption); omega)
           | (have h1 := dec_restT (by assumption); omega)
           | (have h1 := p3_succ (wPos P'); have h2 := p3_succ (wPos P' + 1)
              have h3 := p3_pos (wPos P'); omega)
           | (refine Prod.Lex.left _ _ ?_
              first
                | omega
                | exact dec_parkG
                | exact dec_parkG2
                | (have h1 := dec_parkS (by assumption); omega)
                | (have h1 := dec_parkT (by assumption); omega)
                | (have h1 := dec_restT (by assumption); omega)
                | (have h1 := p3_succ (wPos P')
                   have h2 := p3_succ (wPos P' + 1)
                   have h3 := p3_pos (wPos P'); omega)))))

/-- Two fuel units at once: a clause that opens a ◯-goal aggregate AND
then one of its prefix rows spends two, because the prefix of a ◯-goal
row list sits one fuel BELOW the aggregate and the row equations are
stated at a successor. -/
def UpFrom2.mk2 {P : Nat → Nat → Type} (n : Nat)
    (k : ∀ e' f', n ≤ e' → n ≤ f' → P (e' + 2) (f' + 2)) : UpFrom2 P :=
  UpFrom2.mk1 (n + 1) (fun e' f' he' hf' =>
    match e', f', he', hf' with
    | 0, _, he, _ => absurd he (by omega)
    | _ + 1, 0, _, hf => absurd hf (by omega)
    | e'' + 1, f'' + 1, he, hf => k e'' f'' (by omega) (by omega))

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
retained guard, the fire through the `∃p` row, the residual ignored.

The value is stated at the ROW index — `jBox j (nOrAll (L f))`, not the
aggregate — so that the fuel of the aggregate equation is spent ONCE, by
the caller that owns `hV` (`UEntryQ`), and every row of a clause is read
at one index. -/
def parkFireA {done rest K : List Neg} {G' N : Neg} {P₀ : Pos}
    {R : Nat → Neg} {j : JD} {L : Nat → List Neg}
    (hsat : Saturated done)
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
      (jBox j (nOrAll (L f)))) :=
  UpFrom2.mk1 (max want.1 cont.1) (fun e' f' he' hf' => by
    have hw : want.1 ≤ e' := Nat.le_trans (Nat.le_max_left _ _) he'
    have hw' : want.1 ≤ f' := Nat.le_trans (Nat.le_max_left _ _) hf'
    have hc : cont.1 ≤ e' := Nat.le_trans (Nat.le_max_right _ _) he'
    have hc' : cont.1 ≤ f' := Nat.le_trans (Nat.le_max_right _ _) hf'
    exact emitJ j (hmemA (f' + 1))
      (.andR (want.2 (e' + 1) (f' + 1) (Nat.le_trans hw (Nat.le_succ _))
                (Nat.le_trans hw' (Nat.le_succ _)))
        (parkAssembleP (interpPE_eq hsat) (hmemE e')
          (want.2 (e' + 1) e' (Nat.le_trans hw (Nat.le_succ _)) hw)
          (cont.2 e' (f' + 1) hc (Nat.le_trans hc' (Nat.le_succ _))))))

/-- **The attack row of a parked `a ⊃ N` whose atom has arrived.** -/
def qFireA {done rest K : List Neg} {a : String} {N : Neg} {P₀ : Pos}
    {j : JD} {L : Nat → List Neg}
    (hsat : Saturated done) (hap : ¬ a = p)
    (hXr : (Neg.imp (.atom a) N, rest) ∈ splits done)
    (hmemA : ∀ f, pGuard p a nBot (nAnd (.up (.atom a))
      (interpP p f [N] rest (some (jGoal j (.up P₀))))) ∈ L f)
    (sa : UpFrom (fun e => Stab (interpP p e [] done none :: K) .tru (.atom a)))
    (cont : UpFrom2 (fun e f => Inv (interpP p e [N] rest none :: K) [] .tru
              (interpP p f [N] rest (some (jGoal j (.up P₀)))))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (jBox j (nOrAll (L f)))) :=
  UpFrom2.mk1 (max sa.1 cont.1) (fun e' f' he' hf' => by
    have hs : sa.1 ≤ e' + 1 :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) he') (Nat.le_succ _)
    have hc : cont.1 ≤ e' := Nat.le_trans (Nat.le_max_right _ _) he'
    have hc' : cont.1 ≤ f' + 1 :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hf') (Nat.le_succ _)
    refine emitJ j (hmemA (f' + 1)) ?_
    simp only [pGuard]; rw [if_neg hap]
    exact .andR (.stable (sa.2 (e' + 1) hs))
      (qAssembleP (interpPE_eq hsat) (qimpConjMemP hXr) hap (sa.2 (e' + 1) hs)
        (cont.2 e' (f' + 1) hc hc')))

/-- **The attack row of a parked box** — the lax-only one.  Both
components of the row sit at the same fuel, so no unit is spent. -/
def boxFireA {done rest K : List Neg} {Q : Pos} {P₀ : Pos}
    {L : Nat → List Neg}
    (hmemA : ∀ f, Neg.imp (.down (interpP p f [.up Q] rest none))
      (interpP p f [.up Q] rest (some (jGoal (.lax) (.up P₀)))) ∈ L f)
    (cont : UpFrom2 (fun e f => Inv (interpP p e [.up Q] rest none :: K) [] .tru
              (interpP p f [.up Q] rest (some (jGoal (.lax) (.up P₀)))))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (jBox .lax (nOrAll (L f)))) :=
  ⟨cont.1, fun e' f' _ hf' =>
    emitJ .lax (hmemA f')
      (.impR (.downL ((cont.2 f' f' hf' hf').wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))))⟩

/-! The five `parkFireA` instances, one per parked implication shape, each
pinning the `∃p` row's residual component. -/

/-- `↓◯Q′ ⊃ N`. -/
def cimpFireA {done rest K : List Neg} {Q' : Pos} {N : Neg} {P₀ : Pos}
    {j : JD} {L : Nat → List Neg} (hsat : Saturated done)
    (hXr : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done)
    (hmemA : ∀ f, nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
      (interpP p f [N] rest (some (jGoal j (.up P₀)))) ∈ L f)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some (.up (.down (.circ Q')))))))
    (cont : UpFrom2 (fun e f => Inv (interpP p e [N] rest none :: K) [] .tru
              (interpP p f [N] rest (some (jGoal j (.up P₀)))))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (jBox j (nOrAll (L f)))) :=
  parkFireA hsat (fun _ => cimpConjMemP hXr) hmemA want cont

/-- `↓(Q′ ⊃ N′) ⊃ N` — the guard at the FULL station. -/
def dykFireA {done rest K : List Neg} {Q' : Pos} {N' N : Neg} {P₀ : Pos}
    {j : JD} {L : Nat → List Neg} (hsat : Saturated done)
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done)
    (hmemA : ∀ f, nAnd (interpP p f [] done (some (.imp Q' N')))
      (interpP p f [N] rest (some (jGoal j (.up P₀)))) ∈ L f)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some (.imp Q' N')))))
    (cont : UpFrom2 (fun e f => Inv (interpP p e [N] rest none :: K) [] .tru
              (interpP p f [N] rest (some (jGoal j (.up P₀)))))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (jBox j (nOrAll (L f)))) :=
  parkFireA hsat (fun _ => dykConjMemP hXr) hmemA want cont

/-- `(Qa ∨ Qb) ⊃ N`. -/
def orimpFireA {done rest K : List Neg} {Qa Qb : Pos} {N : Neg} {P₀ : Pos}
    {j : JD} {L : Nat → List Neg} (hsat : Saturated done)
    (hXr : (Neg.imp (.or Qa Qb) N, rest) ∈ splits done)
    (hmemA : ∀ f, nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
      (interpP p f [N] rest (some (jGoal j (.up P₀)))) ∈ L f)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some (.up (.or Qa Qb))))))
    (cont : UpFrom2 (fun e f => Inv (interpP p e [N] rest none :: K) [] .tru
              (interpP p f [N] rest (some (jGoal j (.up P₀)))))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (jBox j (nOrAll (L f)))) :=
  parkFireA hsat (fun _ => orimpConjMemP hXr) hmemA want cont

/-- `↓↑Pa ⊃ N`. -/
def shimpFireA {done rest K : List Neg} {Pa : Pos} {N : Neg} {P₀ : Pos}
    {j : JD} {L : Nat → List Neg} (hsat : Saturated done)
    (hXr : (Neg.imp (.down (.up Pa)) N, rest) ∈ splits done)
    (hmemA : ∀ f, nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
      (interpP p f [N] rest (some (jGoal j (.up P₀)))) ∈ L f)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some (.up (.down (.up Pa)))))))
    (cont : UpFrom2 (fun e f => Inv (interpP p e [N] rest none :: K) [] .tru
              (interpP p f [N] rest (some (jGoal j (.up P₀)))))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (jBox j (nOrAll (L f)))) :=
  parkFireA hsat (fun _ => shimpConjMemP hXr) hmemA want cont

/-- `↓(Ma ∧ Mb) ⊃ N`. -/
def andimpFireA {done rest K : List Neg} {Ma Mb N : Neg} {P₀ : Pos}
    {j : JD} {L : Nat → List Neg} (hsat : Saturated done)
    (hXr : (Neg.imp (.down (.and Ma Mb)) N, rest) ∈ splits done)
    (hmemA : ∀ f, nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
      (interpP p f [N] rest (some (jGoal j (.up P₀)))) ∈ L f)
    (want : UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
              (interpP p f [] done (some (.up (.down (.and Ma Mb)))))))
    (cont : UpFrom2 (fun e f => Inv (interpP p e [N] rest none :: K) [] .tru
              (interpP p f [N] rest (some (jGoal j (.up P₀)))))) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (jBox j (nOrAll (L f)))) :=
  parkFireA hsat (fun _ => andimpConjMemP hXr) hmemA want cont

/-! ## The row kit

`LJF/O.lean`'s `UStab` carries the row list `L` and four membership
facts as a parameter block, threaded unchanged through `UStab`, `ULF`,
`UInvG`, `UpElim`, `UpLF`, `UpInvG`.  In fuel form the list is
FUEL-INDEXED and there are EIGHT facts, so the block is bundled. -/

/-- The row facts of a `∀p` aggregate over a saturated station, at every
fuel: the aggregate equation and one membership per parked shape that can
attack the goal. -/
structure RowKit (p : String) (done : List Neg) (j : JD) (P₀ : Pos)
    (L : Nat → List Neg) : Prop where
  /-- The aggregate at fuel `f+1` is the box-wrapped disjunction of the
  rows at fuel `f`. -/
  hV : ∀ f, interpP p (f + 1) [] done (some (jGoal j (.up P₀)))
    = jBox j (nOrAll (L f))
  /-- The fired `q`-implication row. -/
  qmem : ∀ (f : Nat) {c : String} {Nc : Neg} {rest : List Neg},
    (Neg.imp (.atom c) Nc, rest) ∈ splits done →
    pGuard p c nBot (nAnd (.up (.atom c))
      (interpP p f [Nc] rest (some (jGoal j (.up P₀))))) ∈ L f
  /-- The Dyckhoff row. -/
  dmem : ∀ (f : Nat) {Q' : Pos} {N' N : Neg} {rest : List Neg},
    (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
    nAnd (interpP p f [] done (some (.imp Q' N')))
         (interpP p f [N] rest (some (jGoal j (.up P₀)))) ∈ L f
  /-- The ◯-implication row. -/
  cmem : ∀ (f : Nat) {Q' : Pos} {N : Neg} {rest : List Neg},
    (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done →
    nAnd (interpP p f [] done (some (.up (.down (.circ Q')))))
         (interpP p f [N] rest (some (jGoal j (.up P₀)))) ∈ L f
  /-- The `(Qa∨Qb) ⊃ N` row. -/
  omem : ∀ (f : Nat) {Qa Qb : Pos} {N : Neg} {rest : List Neg},
    (Neg.imp (.or Qa Qb) N, rest) ∈ splits done →
    nAnd (interpP p f [] done (some (.up (.or Qa Qb))))
         (interpP p f [N] rest (some (jGoal j (.up P₀)))) ∈ L f
  /-- The `↓↑Pa ⊃ N` row. -/
  smem : ∀ (f : Nat) {Pa : Pos} {N : Neg} {rest : List Neg},
    (Neg.imp (.down (.up Pa)) N, rest) ∈ splits done →
    nAnd (interpP p f [] done (some (.up (.down (.up Pa)))))
         (interpP p f [N] rest (some (jGoal j (.up P₀)))) ∈ L f
  /-- The `↓(Ma∧Mb) ⊃ N` row. -/
  amem : ∀ (f : Nat) {Ma Mb N : Neg} {rest : List Neg},
    (Neg.imp (.down (.and Ma Mb)) N, rest) ∈ splits done →
    nAnd (interpP p f [] done (some (.up (.down (.and Ma Mb)))))
         (interpP p f [N] rest (some (jGoal j (.up P₀)))) ∈ L f
  /-- The opened-box row, lax only. -/
  bmem : j = .lax → ∀ (f : Nat) {R : Pos} {rest : List Neg},
    (Neg.circ R, rest) ∈ splits done →
    Neg.imp (.down (interpP p f [.up R] rest none))
      (interpP p f [.up R] rest (some (jGoal j (.up P₀)))) ∈ L f

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

/-! # Part 5: the `∃p` side of the family

`LJF/O.lean`'s `eMinF`, `TInv`, `TStab`, `TRF`, `TLF`, `TpElim`, `TpLF`,
`TpInv`, in fuel-carrying form over `interpP`.  The station measure is
`LJF/O.lean`'s unchanged — the antecedent guards are the two parameters,
so no clause calls the `∀p` side and no clause moves at a fixed station.

Every value is an `UpFrom` witness; every clause with two sub-results
combines by `UpFrom.map₂`; every `interpP` unfolding peels one fuel unit
(`UpFrom.mk1`), the row projections reading the sub-witnesses at `f` and
the context at `f+1`. -/

/-- `p`-freeness is blind to the shift/box wrapper: `PFreeN p (◯P)` and
`PFreeN p (↑P)` are both `PFreeP p P`.  Named so that a `circR` clause can
FIX the premise's goal, which passing the raw hypothesis does not (it
fixes the conclusion's instead). -/
theorem pfreeCircUp {p : String} {P : Pos} (h : PFreeN p (.circ P)) :
    PFreeN p (.up P) := h

variable (pant : ParkAntP p) (dant : DykAntP p)

set_option maxHeartbeats 8000000 in
mutual

/-- Minimality of `∃p`, processing phase, at fuel — `eMinPP` with the
saturated case taken from the traversal below rather than as a
hypothesis. -/
def eMinQ : ∀ (todo done Δ : List Neg) (ψ : Neg), ParkedCtxP done →
    PFreeCtx p Δ → PFreeN p ψ → ∀ {j : JD},
    Inv ((todo ++ done) ++ Δ) [] j ψ →
    UpFrom (fun e => Inv (interpP p e todo done none :: Δ) [] j ψ)
  | .up (.atom a) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ todo (.up (.atom a) :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.atom a) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .up .fls :: todo, done, Δ, ψ, _, _, _, _, d =>
      UpFrom.mk1 0 (fun e' _ => by
        rw [interpP]; exact nBotElimJ _ (List.mem_cons_self ..) d)
  | .up (.or P Q) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      UpFrom.mk1
        (maxOver (fun (bh : {b // b ∈ invertPos (Pos.or P Q)}) =>
          match bh with
          | ⟨b', hb'⟩ =>
            (eMinQ (b' ++ todo) done Δ ψ hP hΔ hψ
              ((invUp (d.wk subHeadOut) b' hb').wk subChainIn)).1)
          (invertPos (Pos.or P Q)).attach)
        (fun e' he' => by
        rw [interpP]
        refine nOrAllElimJ _ (List.mem_cons_self ..) d ?_
        intro x hx Γ' hsub
        obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
        subst hEq
        have hle := Nat.le_trans (le_maxOver hmem) he'
        refine (((eMinQ (b ++ todo) done Δ ψ hP hΔ hψ
          ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).2 e' hle).wk ?_)
        intro Z hZ
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsub _ (List.mem_cons_of_mem _ hZ)))
  | .up (.down M) :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ (M :: todo) done Δ ψ hP hΔ hψ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .and M N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ (M :: N :: todo) done Δ ψ hP hΔ hψ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp .fls N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ todo done Δ ψ hP hΔ hψ (invImpFls (d.wk subHeadOut))
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.atom a) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ todo (.imp (.atom a) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.qimp a N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ todo (.imp (.or Q₁ Q₂) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.oimp Q₁ Q₂ N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.down (.up P')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ todo (.imp (.down (.up P')) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.simp P' N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ todo (.imp (.down (.and M₁ M₂)) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.aimp M₁ M₂ N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ todo (.imp (.down (.imp Q' N')) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.dyk Q' N' N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .circ Q :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ todo (.circ Q :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.box Q) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | .imp (.down (.circ Q')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, _, d =>
      let w := eMinQ todo (.imp (.down (.circ Q')) N :: done) Δ ψ
        (ParkedCtxP.cons (ParkedNP.cimp Q' N) hP) hΔ hψ (d.wk subParkOut)
      UpFrom.mk1 w.1 (fun e' he' => by rw [interpP]; exact w.2 e' he')
  | [], done, Δ, ψ, hP, hΔ, hψ, _, d =>
      match hf : findFire done (splits done) with
      | some (a, N, rest) =>
          let w := eMinQ [N] rest Δ ψ
            (ParkedCtxP.sub (splits_sub (findFire_mem hf)) hP) hΔ hψ
            (invFireHyp (findFire_mem hf) d)
          UpFrom.mk1 w.1 (fun e' he' => by
            rw [interpPFire_eq hf none]; exact w.2 e' he')
      | none =>
          TInvQ done hf hP
            (fun Z hZ => List.mem_append.mp hZ)
            (fun Z hZ => List.mem_append_left _ hZ)
            hΔ PFreeΩ.nil hψ d
  termination_by todo done Δ ψ hP hΔ hψ j d =>
    (2 * sum3 todo + sum3 done + 1, 0)
  decreasing_by ljf_dec_p


/-- Inversion-phase traversal, at fuel. -/
def TInvQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {Ω : List Pos} {C : Neg} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeΩ p Ω → PFreeN p C →
      Inv Γ' Ω j C →
      UpFrom (fun e => Inv (interpP p e [] done none :: K) Ω j C)
  | _, _, _, _, _, hm, hm2, hK, hΩ, hC, .impR d =>
      (TInvQ done hsat hP hm hm2 hK (hΩ.cons hC.1) hC.2 d).map
        (fun _ x => .impR x)
  | _, _, _, _, _, hm, hm2, hK, hΩ, hC, .andR d e =>
      UpFrom.map₂ (fun _ x y => .andR x y)
        (TInvQ done hsat hP hm hm2 hK hΩ hC.1 d)
        (TInvQ done hsat hP hm hm2 hK hΩ hC.2 e)
  | _, _, _, _, _, hm, hm2, hK, hΩ, hC, .circR d =>
      let w := TInvQ done hsat hP hm hm2 hK hΩ (pfreeCircUp hC) d
      ⟨w.1, fun e' he' => .circR (w.2 e' he')⟩
  | _, _, _, _, _, hm, hm2, hK, _, hC, .stable s =>
      (TStabQ done hsat hP hm hm2 hK hC s).map (fun _ x => .stable x)
  | _, _, .or P₁ Q₁ :: _, _, _, hm, hm2, hK, hΩ, hC, .orL d₁ d₂ =>
      have hor : PFreeP p (.or P₁ Q₁) := hΩ.head
      UpFrom.map₂ (fun _ x y => .orL x y)
        (TInvQ done hsat hP hm hm2 hK (hΩ.tail.cons hor.1) hC d₁)
        (TInvQ done hsat hP hm hm2 hK (hΩ.tail.cons hor.2) hC d₂)
  | _, _, _, _, _, _, _, _, _, _, .flsL => ⟨0, fun _ _ => .flsL⟩
  | _, _, .down M₀ :: _, _, _, hm, hm2, hK, hΩ, hC, .downL d =>
      have hM : PFreeN p M₀ := hΩ.head
      (TInvQ done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hM hK) hΩ.tail hC d).map (fun _ x =>
        .downL (x.wk (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))
  | _, _, .atom a :: _, _, _, hm, hm2, hK, hΩ, hC, .atomL d =>
      (TInvQ done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom a)) from hΩ.head) hK)
          hΩ.tail hC d).map (fun _ x =>
        .atomL (x.wk (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))
  termination_by Γ' K Ω C j hm hm2 hK hΩ hC d =>
    (2 * sum3 [] + sum3 done, sizeOf d)
  decreasing_by ljf_dec_e


/-- Stable-phase traversal, at fuel: the dispatch point.  Eight parked
shapes, five of them implications that fire through a retained guard. -/
def TStabQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {P : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P →
      Stab Γ' j P →
      UpFrom (fun e => Stab (interpP p e [] done none :: K) j P)
  | _, _, _, _, hm, hm2, hK, hp, .rfoc r => TRFQ done hsat hP hm hm2 hK hp r
  | _, _, _, _, hm, hm2, hK, hp, .laxOf s =>
      (TStabQ done hsat hP hm hm2 hK hp s).map (fun _ x => .laxOf x)
  | _, _, _, _, hm, hm2, hK, hp, @Stab.lfoc _ _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom a), _, hd, .rel (.atomL (.stable s')) =>
            TStabQ done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hp s'
        | .imp (.atom a) N, _, hd, .impL s_a lf' =>
            if hap : a = p then
              TpElimQ done hsat hP hm hm2 hK hp hap hap hd lf' s_a
            else
              let ⟨rest, hXr⟩ := splitAt done _ hd
              let sa := TStabQ done hsat hP hm hm2 hK
                (show PFreeP p (Pos.atom a) from hap) s_a
              let cont := eMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _)))))
              UpFrom.mk1 (max sa.1 cont.1) (fun f' hf' =>
                unStable (qAssembleP (interpPE_eq hsat) (qimpConjMemP hXr) hap
                  (sa.2 (f' + 1) (Nat.le_trans
                    (Nat.le_trans (Nat.le_max_left _ _) hf') (Nat.le_succ _)))
                  (cont.2 f' (Nat.le_trans (Nat.le_max_right _ _) hf'))))
        | .circ Q, _, hd, .circL d =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            let cont := eMinQ [.up Q] rest _ (.up _)
              (ParkedCtxP.sub (splits_sub hXr) hP) hK hp
              (boxClean (splitHyp hm hXr)
                (.stable (.lfoc (List.mem_cons_self ..)
                  (.rel (d.wk (Sub.grow _))))))
            UpFrom.mk1 cont.1 (fun f' hf' =>
              boxAssembleP (interpPE_eq hsat) (boxConjMemP hXr)
                (cont.2 f' hf'))
        | .imp (.down (.circ Q')) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            (cimpFireE hsat hXr
              (parkAntGuard pant hsat hP hd hm hm2 hK s_d)
              (eMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _))))))).map (fun _ x => unStable x)
        | .imp (.down (.imp Q' N')) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            (dykFireE hsat hXr
              (dant done _ _ Q' N' N hsat hP hd hm hm2 hK s_d)
              (eMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _))))))).map (fun _ x => unStable x)
        | .imp (.or Qa Qb) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            (orimpFireE hsat hXr
              (parkAntGuard pant hsat hP hd hm hm2 hK s_d)
              (eMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _))))))).map (fun _ x => unStable x)
        | .imp (.down (.up Pa)) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            (shimpFireE hsat hXr
              (parkAntGuard pant hsat hP hd hm hm2 hK s_d)
              (eMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _))))))).map (fun _ x => unStable x)
        | .imp (.down (.and Ma Mb)) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            (andimpFireE hsat hXr
              (parkAntGuard pant hsat hP hd hm hm2 hK s_d)
              (eMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _))))))).map (fun _ x => unStable x)
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        (TLFQ done hsat hP hm hm2 hK
          (hK _ ((hm _ h).resolve_left hd)) hp lf).map (fun _ x =>
            .lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd)) x)
  termination_by Γ' K P j hm hm2 hK hp s =>
    (2 * sum3 [] + sum3 done, sizeOf s)
  decreasing_by ljf_dec_p


/-- Right-focus traversal, at fuel. -/
def TRFQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {P : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P →
      RFocus Γ' j P →
      UpFrom (fun e => Stab (interpP p e [] done none :: K) j P)
  | _, _, .atom a, _, hm, _, hK, hp, .init h => by
      by_cases hd : Neg.up (.atom a) ∈ done
      · exact
          let w := splitAt done _ hd
          UpFrom.mk1 0 (fun f' _ =>
            Stab.ofTru _ (atomAssembleP (interpPE_eq hsat)
              (atomConjMemP w.2) hp))
      · exact ⟨0, fun _ _ =>
          .rfoc (.init (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd)))⟩
  | _, _, _, _, hm, hm2, hK, hp, .or1 r =>
      (TRFQ done hsat hP hm hm2 hK hp.1 r).map (fun _ x => stabOr1 x)
  | _, _, _, _, hm, hm2, hK, hp, .or2 r =>
      (TRFQ done hsat hP hm hm2 hK hp.2 r).map (fun _ x => stabOr2 x)
  | _, _, _, _, hm, hm2, hK, hp, .rel d =>
      (TInvQ done hsat hP hm hm2 hK PFreeΩ.nil hp d).map
        (fun _ x => .rfoc (.rel x))
  termination_by Γ' K P j hm hm2 hK hp r =>
    (2 * sum3 [] + sum3 done, sizeOf r)
  decreasing_by ljf_dec_e


/-- Left-focus traversal on a kept hypothesis, at fuel. -/
def TLFQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {H : Neg} {P : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeN p H → PFreeP p P →
      LFoc Γ' H j P →
      UpFrom (fun e => LFoc (interpP p e [] done none :: K) H j P)
  | _, _, _, P₁, _, hm, hm2, hK, hH, hp, .rel d =>
      let w := TInvQ done hsat hP hm hm2 hK (PFreeΩ.cons hH PFreeΩ.nil)
        (show PFreeN p (.up P₁) from hp) d
      ⟨w.1, fun e' he' => .rel (w.2 e' he')⟩
  | _, _, _, P₁, _, hm, hm2, hK, hH, hp, .circL d =>
      let w := TInvQ done hsat hP hm hm2 hK (PFreeΩ.cons hH PFreeΩ.nil)
        (show PFreeN p (.up P₁) from hp) d
      ⟨w.1, fun e' he' => .circL (w.2 e' he')⟩
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .impL s lf =>
      UpFrom.map₂ (fun _ x y => .impL x y)
        (TStabQ done hsat hP hm hm2 hK hH.1 s)
        (TLFQ done hsat hP hm hm2 hK hH.2 hp lf)
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .and1 lf =>
      (TLFQ done hsat hP hm hm2 hK hH.1 hp lf).map (fun _ x => .and1 x)
  | _, _, _, _, _, hm, hm2, hK, hH, hp, .and2 lf =>
      (TLFQ done hsat hP hm hm2 hK hH.2 hp lf).map (fun _ x => .and2 x)
  termination_by Γ' K H P j hm hm2 hK hH hp lf =>
    (2 * sum3 [] + sum3 done, sizeOf lf)
  decreasing_by ljf_dec_e


/-- The `p`-fire eliminator, at fuel. -/
def TpElimQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {a b : String} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      Stab Γ' .tru (.atom b) →
      UpFrom (fun e => Stab (interpP p e [] done none :: K) j P₀)
  | _, _, _, _, _, _, _, hm, _, hK, _, ha, hb, hXpkg, _, .rfoc (.init h) =>
      False.elim (by
        rcases hm _ h with hd | hk
        · have h1 := atomMem_of_mem hd
          have h2 := saturated_atom_absent hsat hXpkg
          rw [hb.trans ha.symm] at h1
          rw [h1] at h2; cases h2
        · exact (hK _ hk) hb)
  | _, _, _, _, a, b, _, hm, hm2, hK, hpT, ha, hb, hXpkg, lfP,
      @Stab.lfoc _ _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            TpElimQ done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hpT ha hb
              hXpkg (lfP.wk (Sub.grow _)) s'
        | .imp (.atom c) N_b, _, hd, .impL s_b lf_b =>
            if hcp : c = p then
              TpElimQ done hsat hP hm hm2 hK hpT ha hcp hXpkg lfP s_b
            else
              let ⟨rest, hXr⟩ := splitAt done _ hd
              let sa := TStabQ done hsat hP hm hm2 hK
                (show PFreeP p (Pos.atom c) from hcp) s_b
              let cont := eMinQ [N_b] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_b.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _))))))
              UpFrom.mk1 (max sa.1 cont.1) (fun f' hf' =>
                unStable (qAssembleP (interpPE_eq hsat) (qimpConjMemP hXr) hcp
                  (sa.2 (f' + 1) (Nat.le_trans
                    (Nat.le_trans (Nat.le_max_left _ _) hf') (Nat.le_succ _)))
                  (cont.2 f' (Nat.le_trans (Nat.le_max_right _ _) hf'))))
        | .imp (.down (.imp Q' N')) N_d, _, hd, .impL s_d lf_d =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            (dykFireE hsat hXr
              (dant done _ _ Q' N' N_d hsat hP hd hm hm2 hK s_d)
              (eMinQ [N_d] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_d.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _)))))))).map (fun _ x => unStable x)
        | .imp (.down (.circ Q')) N_c, _, hd, .impL s_c lf_c =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            (cimpFireE hsat hXr
              (parkAntGuard pant hsat hP hd hm hm2 hK s_c)
              (eMinQ [N_c] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_c.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _)))))))).map (fun _ x => unStable x)
        | .imp (.or Qa Qb) N_o, _, hd, .impL s_o lf_o =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            (orimpFireE hsat hXr
              (parkAntGuard pant hsat hP hd hm hm2 hK s_o)
              (eMinQ [N_o] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_o.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _)))))))).map (fun _ x => unStable x)
        | .imp (.down (.up Pa)) N_s, _, hd, .impL s_s lf_s =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            (shimpFireE hsat hXr
              (parkAntGuard pant hsat hP hd hm hm2 hK s_s)
              (eMinQ [N_s] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_s.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _)))))))).map (fun _ x => unStable x)
        | .imp (.down (.and Ma Mb)) N_a, _, hd, .impL s_a lf_a =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            (andimpFireE hsat hXr
              (parkAntGuard pant hsat hP hd hm hm2 hK s_a)
              (eMinQ [N_a] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_a.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _)))))))).map (fun _ x => unStable x)
        | .circ _, _, _, lf => nomatch lf
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        (TpLFQ done hsat hP hm hm2 hK
          (hK _ ((hm _ h).resolve_left hd)) hpT ha hb hXpkg lfP lf).map
          (fun _ x =>
            .lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd)) x)
  termination_by Γ' K M P₀ a b j hm hm2 hK hpT ha hb hXpkg lfP s =>
    (2 * sum3 [] + sum3 done, sizeOf s)
  decreasing_by ljf_dec_p


/-- Left focus on a kept hypothesis, inside a `p`-proof, at fuel. -/
def TpLFQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {H : Neg} {a b : String}
      {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeN p H → PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      LFoc Γ' H .tru (.atom b) →
      UpFrom (fun e => LFoc (interpP p e [] done none :: K) H j P₀)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .rel d =>
      (TpInvQ done hsat hP hm hm2 hK (PFreeΩ.cons hH PFreeΩ.nil)
        hpT ha hb hXpkg lfP d).map (fun _ x => .rel x)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP,
      .impL s lf =>
      UpFrom.map₂ (fun _ x y => .impL x y)
        (TStabQ done hsat hP hm hm2 hK hH.1 s)
        (TpLFQ done hsat hP hm hm2 hK hH.2 hpT ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP,
      .and1 lf =>
      (TpLFQ done hsat hP hm hm2 hK hH.1 hpT ha hb hXpkg lfP lf).map
        (fun _ x => .and1 x)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP,
      .and2 lf =>
      (TpLFQ done hsat hP hm hm2 hK hH.2 hpT ha hb hXpkg lfP lf).map
        (fun _ x => .and2 x)
  termination_by Γ' K M P₀ H a b j hm hm2 hK hH hpT ha hb hXpkg lfP lf =>
    (2 * sum3 [] + sum3 done, sizeOf lf)
  decreasing_by ljf_dec_e


/-- Inversion inside a `p`-proof, goal re-targeted, at fuel. -/
def TpInvQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {Ω : List Pos} {a b : String}
      {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeΩ p Ω → PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      Inv Γ' Ω .tru (.up (.atom b)) →
      UpFrom (fun e => Inv (interpP p e [] done none :: K) Ω j (.up P₀))
  | _, _, _, _, _, _, _, _, hm, hm2, hK, _, hpT, ha, hb, hXpkg, lfP, .stable s =>
      (TpElimQ done hsat hP hm hm2 hK hpT ha hb hXpkg lfP s).map
        (fun _ x => .stable x)
  | _, _, _, _, .or P₁ Q₁ :: _, _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg,
      lfP, .orL d₁ d₂ =>
      have hor : PFreeP p (.or P₁ Q₁) := hΩ.head
      UpFrom.map₂ (fun _ x y => .orL x y)
        (TpInvQ done hsat hP hm hm2 hK (hΩ.tail.cons hor.1)
          hpT ha hb hXpkg lfP d₁)
        (TpInvQ done hsat hP hm hm2 hK (hΩ.tail.cons hor.2)
          hpT ha hb hXpkg lfP d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .flsL =>
      ⟨0, fun _ _ => .flsL⟩
  | _, _, _, _, .down M₀ :: _, _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg,
      lfP, .downL d =>
      have hM : PFreeN p M₀ := hΩ.head
      (TpInvQ done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hM hK) hΩ.tail hpT ha hb hXpkg
          (lfP.wk (Sub.grow _)) d).map (fun _ x =>
        .downL (x.wk (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))
  | _, _, _, _, .atom c :: _, _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg,
      lfP, .atomL d =>
      (TpInvQ done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom c)) from hΩ.head) hK)
          hΩ.tail hpT ha hb hXpkg (lfP.wk (Sub.grow _)) d).map (fun _ x =>
        .atomL (x.wk (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))
  termination_by Γ' K M P₀ Ω a b j hm hm2 hK hΩ hpT ha hb hXpkg lfP d =>
    (2 * sum3 [] + sum3 done, sizeOf d)
  decreasing_by ljf_dec_e

end


/-! # Part 6: the `∀p` side of the family

`LJF/O.lean`'s `aMinF`, `UEntry`, `UStab`, `URF`, `ULF`, `UInvG`,
`UpElim`, `UpLF`, `UpInvG`, in fuel-carrying form.  Two conventions make
the bookkeeping local:

* the row-carrying traversals (`UStabQ`, `ULFQ`, `UInvGQ`, `UpElimQ`,
  `UpLFQ`, `UpInvGQ`) are stated at the ROW index — `jBox j (nOrAll (L f))`
  and `jChain j (L f)` — and only `UEntryQ` and `UStabQ`'s `rfoc` clause
  cross to the aggregate, by spending the fuel unit of `kit.hV`;
* the two release sites use `laxReleaseUp` / `laxReleaseCirc`
  (`LJF/OFuelHeight.lean` §10.6), which land on the same `∀p` row as
  `negOfDownStab` did and do not raise the height. -/

set_option maxHeartbeats 8000000 in
mutual

/-- Minimality of `∀p`, processing phase, at fuel. -/
def aMinQ : ∀ (todo done Δ : List Neg) (G : Neg), ParkedCtxP done →
    PFreeCtx p Δ → ∀ {j : JD},
    Inv ((todo ++ done) ++ Δ) [] j G →
    UpFrom2 (fun e f => Inv (interpP p e todo done none :: Δ) [] .tru
      (interpP p f todo done (some (jGoal j G))))
  | .up (.atom a) :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ todo (.up (.atom a) :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.atom a) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .up .fls :: todo, done, Δ, G, _, _, _, _ =>
      UpFrom2.mk1 0 (fun e' f' _ _ => by
        rw [interpP, interpP]; exact nBotElim _ (List.mem_cons_self ..))
  | .up (.or P Q) :: todo, done, Δ, G, hP, hΔ, _, d =>
      UpFrom2.mk1
        (maxOver (fun (bh : {b // b ∈ invertPos (Pos.or P Q)}) =>
          match bh with
          | ⟨b', hb'⟩ =>
            (aMinQ (b' ++ todo) done Δ G hP hΔ
              ((invUp (d.wk subHeadOut) b' hb').wk subChainIn)).1)
          (invertPos (Pos.or P Q)).attach)
        (fun e' f' he' hf' => by
        rw [interpP, interpP]
        refine nAndAllIntro ?_
        intro x hx
        obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
        subst hEq
        refine .impR (.downL ?_)
        have hlf := Nat.le_trans (le_maxOver hmem) hf'
        refine (((aMinQ (b ++ todo) done Δ G hP hΔ
          ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).2 f' f' hlf hlf).wk ?_)
        intro Z hZ
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
  | .up (.down M) :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ (M :: todo) done Δ G hP hΔ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .and M N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ (M :: N :: todo) done Δ G hP hΔ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp .fls N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ todo done Δ G hP hΔ (invImpFls (d.wk subHeadOut))
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.atom a) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ todo (.imp (.atom a) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.qimp a N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ todo (.imp (.or Q₁ Q₂) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.oimp Q₁ Q₂ N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.down (.up P')) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ todo (.imp (.down (.up P')) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.simp P' N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ todo (.imp (.down (.and M₁ M₂)) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.aimp M₁ M₂ N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ todo (.imp (.down (.imp Q' N')) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.dyk Q' N' N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .circ Q :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ todo (.circ Q :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.box Q) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | .imp (.down (.circ Q')) N :: todo, done, Δ, G, hP, hΔ, _, d =>
      let w := aMinQ todo (.imp (.down (.circ Q')) N :: done) Δ G
        (ParkedCtxP.cons (ParkedNP.cimp Q' N) hP) hΔ (d.wk subParkOut)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [interpP, interpP]; exact w.2 e' f' he' hf')
  | [], done, Δ, G, hP, hΔ, j, d =>
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          let w := aMinQ [N'] rest Δ G
            (ParkedCtxP.sub (splits_sub (findFire_mem hf)) hP) hΔ
            (invFireHyp (findFire_mem hf) d)
          UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
            rw [interpPFire_eq hf none, interpPFire_eq hf (some (jGoal j G))]
            exact w.2 e' f' he' hf')
      | none =>
          UEntryQ done hf hP
            (fun Z hZ => List.mem_append.mp hZ)
            (fun Z hZ => List.mem_append_left _ hZ)
            hΔ G d
  termination_by todo done Δ G hP hΔ j d =>
    (2 * sum3 todo + sum3 done + 3 ^ wNeg G + 4, 0)
  decreasing_by ljf_dec_p


/-- The `∀p` interpolant of any goal over a mixed saturated station. -/
def UEntryQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      ∀ (G : Neg) {j : JD}, Inv Γ' [] j G →
      UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
        (interpP p f [] done (some (jGoal j G))))
  | _, _, hm, hm2, hK, .imp Q N, _, .impR d₁ =>
      UpFrom2.mk1
        (maxOver (fun (bh : {b // b ∈ invertPos Q}) =>
          match bh with
          | ⟨b', hb'⟩ =>
            (aMinQ b' done _ N hP hK
              ((extract [] d₁ b' hb').wk (fun Z hZ => by
                rcases List.mem_append.mp hZ with hZ | hZ
                · exact List.mem_append_left _ (List.mem_append_left _ hZ)
                · rcases hm Z hZ with hd | hk
                  · exact List.mem_append_left _ (List.mem_append_right _ hd)
                  · exact List.mem_append_right _ hk))).1)
          (invertPos Q).attach)
        (fun e' f' he' hf' => by
          show Inv _ [] .tru (interpP p (f' + 1) [] done (some (.imp Q N)))
          rw [interpPA_imp_eq hsat Q N]
          refine nAndAllIntro ?_
          intro x hx
          obtain ⟨w, hmem, hEq⟩ := memMapWitness _ _ x hx
          subst hEq
          have hb : w.1 ∈ invertPos Q := w.2
          refine .impR (.downL ?_)
          have hlf := Nat.le_trans (le_maxOver hmem) hf'
          have haux := (aMinQ w.1 done _ N hP hK
            ((extract [] d₁ w.1 hb).wk (fun Z hZ => by
              rcases List.mem_append.mp hZ with hZ | hZ
              · exact List.mem_append_left _ (List.mem_append_left _ hZ)
              · rcases hm Z hZ with hd | hk
                · exact List.mem_append_left _ (List.mem_append_right _ hd)
                · exact List.mem_append_right _ hk))).2 f' f' hlf hlf
          rw [jGoal_tru] at haux
          refine (haux.wk ?_)
          intro Z hZ
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
  | _, _, hm, hm2, hK, .and M N, _, .andR d₁ d₂ =>
      let w₁ := UEntryQ done hsat hP hm hm2 hK M d₁
      let w₂ := UEntryQ done hsat hP hm hm2 hK N d₂
      UpFrom2.mk1 (max w₁.1 w₂.1) (fun e' f' he' hf' => by
        show Inv _ [] .tru (interpP p (f' + 1) [] done (some (.and M N)))
        rw [interpPA_and_eq hsat M N]
        have h₁ := w₁.2 (e' + 1) f'
          (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) he') (Nat.le_succ _))
          (Nat.le_trans (Nat.le_max_left _ _) hf')
        have h₂ := w₂.2 (e' + 1) f'
          (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) he') (Nat.le_succ _))
          (Nat.le_trans (Nat.le_max_right _ _) hf')
        rw [jGoal_tru] at h₁ h₂
        exact .andR h₁ h₂)
  | _, _, hm, hm2, hK, .circ P, _, .circR d =>
      UEntryQ done hsat hP hm hm2 hK (.up P) d
  | _, _, hm, hm2, hK, .up (.atom q), .tru, .stable s => by
      by_cases hq : atomMem q done = true
      · exact UpFrom2.mk1 0 (fun e' f' _ _ => by
          show Inv _ [] .tru (interpP p (f' + 1) [] done (some (.up (.atom q))))
          rw [interpPA_atomT_eq hsat hq]; exact nTopIntro)
      · exact
          let kit : RowKit p done .tru (.atom q)
              (fun f => atomHead p q ++ truStationRowsP p f done (.atom q)) :=
            { hV := fun _ => interpPA_atom_eq hsat hq
              qmem := fun _ _ _ _ hsp => rowMemR hsp
              dmem := fun _ _ _ _ _ hsp => rowMemR hsp
              cmem := fun _ _ _ _ hsp => rowMemR hsp
              omem := fun _ _ _ _ _ hsp => rowMemR hsp
              smem := fun _ _ _ _ hsp => rowMemR hsp
              amem := fun _ _ _ _ _ hsp => rowMemR hsp
              bmem := fun hj => nomatch hj }
          let w := UStabQ (j := .tru) done hsat hP hm hm2 hK kit s
          UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
            show Inv _ [] .tru (interpP p (f' + 1) [] done (some (.up (.atom q))))
            rw [interpPA_atom_eq hsat hq]
            exact w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf')
  | _, _, hm, hm2, hK, .up .fls, .tru, .stable s =>
      let kit : RowKit p done .tru .fls
          (fun f => truStationRowsP p f done .fls) :=
        { hV := fun _ => interpPA_fls_eq hsat
          qmem := fun _ _ _ _ hsp => rowMem hsp
          dmem := fun _ _ _ _ _ hsp => rowMem hsp
          cmem := fun _ _ _ _ hsp => rowMem hsp
          omem := fun _ _ _ _ _ hsp => rowMem hsp
          smem := fun _ _ _ _ hsp => rowMem hsp
          amem := fun _ _ _ _ _ hsp => rowMem hsp
          bmem := fun hj => nomatch hj }
      let w := UStabQ (j := .tru) done hsat hP hm hm2 hK kit s
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru (interpP p (f' + 1) [] done (some (.up .fls)))
        rw [interpPA_fls_eq hsat]
        exact w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf')
  | _, _, hm, hm2, hK, .up (.or P₁ P₂), .tru, .stable s =>
      let kit : RowKit p done .tru (.or P₁ P₂)
          (fun f => [interpP p f [] done (some (.up P₁)),
                     interpP p f [] done (some (.up P₂))] ++
                    truStationRowsP p f done (.or P₁ P₂)) :=
        { hV := fun _ => interpPA_or_eq hsat P₁ P₂
          qmem := fun _ _ _ _ hsp => rowMemR hsp
          dmem := fun _ _ _ _ _ hsp => rowMemR hsp
          cmem := fun _ _ _ _ hsp => rowMemR hsp
          omem := fun _ _ _ _ _ hsp => rowMemR hsp
          smem := fun _ _ _ _ hsp => rowMemR hsp
          amem := fun _ _ _ _ _ hsp => rowMemR hsp
          bmem := fun hj => nomatch hj }
      let w := UStabQ (j := .tru) done hsat hP hm hm2 hK kit s
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru
          (interpP p (f' + 1) [] done (some (.up (.or P₁ P₂))))
        rw [interpPA_or_eq hsat P₁ P₂]
        exact w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf')
  | _, _, hm, hm2, hK, .up (.down M), .tru, .stable s =>
      let kit : RowKit p done .tru (.down M)
          (fun f => [interpP p f [] done (some M)] ++
                    truStationRowsP p f done (.down M)) :=
        { hV := fun _ => interpPA_down_eq hsat M
          qmem := fun _ _ _ _ hsp => rowMemR hsp
          dmem := fun _ _ _ _ _ hsp => rowMemR hsp
          cmem := fun _ _ _ _ hsp => rowMemR hsp
          omem := fun _ _ _ _ _ hsp => rowMemR hsp
          smem := fun _ _ _ _ hsp => rowMemR hsp
          amem := fun _ _ _ _ _ hsp => rowMemR hsp
          bmem := fun hj => nomatch hj }
      let w := UStabQ (j := .tru) done hsat hP hm hm2 hK kit s
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru
          (interpP p (f' + 1) [] done (some (.up (.down M))))
        rw [interpPA_down_eq hsat M]
        exact w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf')
  | _, _, hm, hm2, hK, .up P₀, .lax, .stable s =>
      let kit : RowKit p done .lax P₀ (fun f => laxRowsP p f done P₀) :=
        { hV := fun _ => interpP_circ_laxRows hsat P₀
          qmem := fun _ _ _ _ hsp => rowMemR hsp
          dmem := fun _ _ _ _ _ hsp => rowMemR hsp
          cmem := fun _ _ _ _ hsp => rowMemR hsp
          omem := fun _ _ _ _ _ hsp => rowMemR hsp
          smem := fun _ _ _ _ hsp => rowMemR hsp
          amem := fun _ _ _ _ _ hsp => rowMemR hsp
          bmem := fun _ _ _ _ hsp => rowMemR hsp }
      let w := UStabQ (j := .lax) done hsat hP hm hm2 hK kit s
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru (interpP p (f' + 1) [] done (some (.circ P₀)))
        rw [interpP_circ_laxRows hsat P₀]
        exact w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf')
  termination_by Γ' K hm hm2 hK G j d =>
    (2 * sum3 [] + sum3 done + 3 ^ wNeg G + 3, 0)
  decreasing_by ljf_dec_a


/-- Stable-phase `∀p` traversal: attack emission, at the row index. -/
def UStabQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD} {L : Nat → List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      RowKit p done j P₀ L →
      Stab Γ' j P₀ →
      UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
        (jBox j (nOrAll (L f))))
  | _, _, _, _, _, hm, hm2, hK, kit, .rfoc r =>
      let w := URFQ done hsat hP hm hm2 hK r
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [← kit.hV (f' + 1)]
        exact w.2 (e' + 1) (f' + 2) (Nat.le_trans he' (Nat.le_succ _))
          (Nat.le_trans (Nat.le_trans hf' (Nat.le_succ _)) (Nat.le_succ _)))
  | _, _, .atom q, _, _, hm, hm2, hK, kit, .laxOf s => by
      by_cases hq : atomMem q done = true
      · exact UpFrom2.mk1 0 (fun _ f' _ _ => by
          rw [laxRowsP_of_eq hsat (.atom q) (kit.hV (f' + 1))]
          refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
          rw [interpPA_atomT_eq hsat hq]
          exact nTopIntro)
      · exact
          let kit2 : RowKit p done .tru (.atom q)
              (fun f => atomHead p q ++ truStationRowsP p f done (.atom q)) :=
            { hV := fun _ => interpPA_atom_eq hsat hq
              qmem := fun _ _ _ _ hsp => rowMemR hsp
              dmem := fun _ _ _ _ _ hsp => rowMemR hsp
              cmem := fun _ _ _ _ hsp => rowMemR hsp
              omem := fun _ _ _ _ _ hsp => rowMemR hsp
              smem := fun _ _ _ _ hsp => rowMemR hsp
              amem := fun _ _ _ _ _ hsp => rowMemR hsp
              bmem := fun hj => nomatch hj }
          let w := UStabQ (j := .tru) done hsat hP hm hm2 hK kit2 s
          UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
            rw [laxRowsP_of_eq hsat (.atom q) (kit.hV (f' + 1))]
            refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
            rw [interpPA_atom_eq hsat hq]
            exact w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf')
  | _, _, .fls, _, _, hm, hm2, hK, kit, .laxOf s =>
      let kit2 : RowKit p done .tru .fls
          (fun f => truStationRowsP p f done .fls) :=
        { hV := fun _ => interpPA_fls_eq hsat
          qmem := fun _ _ _ _ hsp => rowMem hsp
          dmem := fun _ _ _ _ _ hsp => rowMem hsp
          cmem := fun _ _ _ _ hsp => rowMem hsp
          omem := fun _ _ _ _ _ hsp => rowMem hsp
          smem := fun _ _ _ _ hsp => rowMem hsp
          amem := fun _ _ _ _ _ hsp => rowMem hsp
          bmem := fun hj => nomatch hj }
      let w := UStabQ (j := .tru) done hsat hP hm hm2 hK kit2 s
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [laxRowsP_of_eq hsat .fls (kit.hV (f' + 1))]
        refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
        rw [interpPA_fls_eq hsat]
        exact w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf')
  | _, _, .or P₁ P₂, _, _, hm, hm2, hK, kit, .laxOf s =>
      let kit2 : RowKit p done .tru (.or P₁ P₂)
          (fun f => [interpP p f [] done (some (.up P₁)),
                     interpP p f [] done (some (.up P₂))] ++
                    truStationRowsP p f done (.or P₁ P₂)) :=
        { hV := fun _ => interpPA_or_eq hsat P₁ P₂
          qmem := fun _ _ _ _ hsp => rowMemR hsp
          dmem := fun _ _ _ _ _ hsp => rowMemR hsp
          cmem := fun _ _ _ _ hsp => rowMemR hsp
          omem := fun _ _ _ _ _ hsp => rowMemR hsp
          smem := fun _ _ _ _ hsp => rowMemR hsp
          amem := fun _ _ _ _ _ hsp => rowMemR hsp
          bmem := fun hj => nomatch hj }
      let w := UStabQ (j := .tru) done hsat hP hm hm2 hK kit2 s
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [laxRowsP_of_eq hsat (.or P₁ P₂) (kit.hV (f' + 1))]
        refine emitJ .lax (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_self ..)))) ?_
        rw [interpPA_or_eq hsat P₁ P₂]
        exact w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf')
  -- The two RELEASE sites.  `LJF/OFuelHeight.lean` Part 9: the `laxOf`
  -- the goal is about to acquire is spent INSIDE the release
  -- continuation, so the height does not rise; `negOfDownStab` at these
  -- two bodies rises by `+1`/`+2` and at a conjunction unboundedly.  Both
  -- replacements land on the SAME `∀p` row, because
  -- `jGoal .lax (↑P′) = ◯P′ = jGoal .tru (◯P′)`.
  | _, _, .down (.up P'), _, _, hm, hm2, hK, kit, .laxOf s =>
      let w := UEntryQ done hsat hP hm hm2 hK (.up P') (laxReleaseUp s)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [laxRowsP_of_eq hsat (.down (.up P')) (kit.hV (f' + 1))]
        exact emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..))
          (w.2 (e' + 1) (f' + 1) (Nat.le_trans he' (Nat.le_succ _))
            (Nat.le_trans hf' (Nat.le_succ _))))
  | _, _, .down (.circ P'), _, _, hm, hm2, hK, kit, .laxOf s =>
      let w := UEntryQ done hsat hP hm hm2 hK (.up P') (laxReleaseCirc s)
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [laxRowsP_of_eq hsat (.down (.circ P')) (kit.hV (f' + 1))]
        exact emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..))
          (w.2 (e' + 1) (f' + 1) (Nat.le_trans he' (Nat.le_succ _))
            (Nat.le_trans hf' (Nat.le_succ _))))
  | _, _, .down (.and M₁ M₂), _, _, hm, hm2, hK, kit, .laxOf s =>
      let kit2 : RowKit p done .tru (.down (.and M₁ M₂))
          (fun f => [interpP p f [] done (some (.and M₁ M₂))] ++
                    truStationRowsP p f done (.down (.and M₁ M₂))) :=
        { hV := fun _ => interpPA_down_eq hsat (.and M₁ M₂)
          qmem := fun _ _ _ _ hsp => rowMemR hsp
          dmem := fun _ _ _ _ _ hsp => rowMemR hsp
          cmem := fun _ _ _ _ hsp => rowMemR hsp
          omem := fun _ _ _ _ _ hsp => rowMemR hsp
          smem := fun _ _ _ _ hsp => rowMemR hsp
          amem := fun _ _ _ _ _ hsp => rowMemR hsp
          bmem := fun hj => nomatch hj }
      let w := UStabQ (j := .tru) done hsat hP hm hm2 hK kit2 s
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [laxRowsP_of_eq hsat (.down (.and M₁ M₂)) (kit.hV (f' + 1))]
        refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
        rw [interpPA_down_eq hsat (.and M₁ M₂)]
        exact w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf')
  | _, _, .down (.imp Q₀ N₀), _, _, hm, hm2, hK, kit, .laxOf s =>
      let kit2 : RowKit p done .tru (.down (.imp Q₀ N₀))
          (fun f => [interpP p f [] done (some (.imp Q₀ N₀))] ++
                    truStationRowsP p f done (.down (.imp Q₀ N₀))) :=
        { hV := fun _ => interpPA_down_eq hsat (.imp Q₀ N₀)
          qmem := fun _ _ _ _ hsp => rowMemR hsp
          dmem := fun _ _ _ _ _ hsp => rowMemR hsp
          cmem := fun _ _ _ _ hsp => rowMemR hsp
          omem := fun _ _ _ _ _ hsp => rowMemR hsp
          smem := fun _ _ _ _ hsp => rowMemR hsp
          amem := fun _ _ _ _ _ hsp => rowMemR hsp
          bmem := fun hj => nomatch hj }
      let w := UStabQ (j := .tru) done hsat hP hm hm2 hK kit2 s
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        rw [laxRowsP_of_eq hsat (.down (.imp Q₀ N₀)) (kit.hV (f' + 1))]
        refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
        rw [interpPA_down_eq hsat (.imp Q₀ N₀)]
        exact w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf')
  | _, _, _, _, _, hm, hm2, hK, kit, @Stab.lfoc _ _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            UStabQ done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK kit s'
        | .imp (.atom c) Nc, _, hd, .impL s_c lf' =>
            if hcp : c = p then
              UpElimQ done hsat hP hm hm2 hK kit hcp hcp hd lf' s_c
            else
              let ⟨rest, hXr⟩ := splitAt done _ hd
              qFireA hsat hcp hXr (fun f => kit.qmem f hXr)
                (TStabQ pant dant done hsat hP hm hm2 hK
                  (show PFreeP p (Pos.atom c) from hcp) s_c)
                (aMinQ [Nc] rest _ (.up _)
                  (ParkedCtxP.sub (splits_sub hXr) hP) hK
                  (fireClean (splitHyp hm hXr)
                    (.stable (.lfoc (List.mem_cons_self ..)
                      (lf'.wk (Sub.grow _))))))
        | .imp (.down (.imp Q' N')) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            dykFireA hsat hXr (fun f => kit.dmem f hXr)
              (dant done _ _ Q' N' N hsat hP hd hm hm2 hK s_d)
              (aMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _))))))
        | .imp (.down (.circ Q')) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            cimpFireA hsat hXr (fun f => kit.cmem f hXr)
              (parkAntGuard pant hsat hP hd hm hm2 hK s_d)
              (aMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _))))))
        | .imp (.or Qa Qb) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            orimpFireA hsat hXr (fun f => kit.omem f hXr)
              (parkAntGuard pant hsat hP hd hm hm2 hK s_d)
              (aMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _))))))
        | .imp (.down (.up Pa)) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            shimpFireA hsat hXr (fun f => kit.smem f hXr)
              (parkAntGuard pant hsat hP hd hm hm2 hK s_d)
              (aMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _))))))
        | .imp (.down (.and Ma Mb)) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            andimpFireA hsat hXr (fun f => kit.amem f hXr)
              (parkAntGuard pant hsat hP hd hm hm2 hK s_d)
              (aMinQ [N] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _))))))
        | .circ Q, _, hd, .circL d =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            boxFireA (fun f => kit.bmem rfl f hXr)
              (aMinQ [.up Q] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (boxClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (.rel (d.wk (Sub.grow _)))))))
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        let w := ULFQ done hsat hP hm hm2 hK kit
          (hK _ ((hm _ h).resolve_left hd)) lf
        ⟨w.1, fun e' f' he' hf' =>
          keepFold (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
            (w.2 e' f' he' hf')⟩
  termination_by Γ' K P₀ j L hm hm2 hK kit s =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf s)
  decreasing_by ljf_dec_p


/-- Right-focus `∀p` traversal, at the aggregate. -/
def URFQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      RFocus Γ' j P₀ →
      UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
        (interpP p f [] done (some (jGoal j (.up P₀)))))
  | _, _, .atom q, .tru, hm, hm2, hK, .init h => by
      by_cases hq : atomMem q done = true
      · exact UpFrom2.mk1 0 (fun _ f' _ _ => by
          show Inv _ [] .tru (interpP p (f' + 1) [] done (some (.up (.atom q))))
          rw [interpPA_atomT_eq hsat hq]; exact nTopIntro)
      · exact UpFrom2.mk1 0 (fun _ f' _ _ => by
          show Inv _ [] .tru (interpP p (f' + 1) [] done (some (.up (.atom q))))
          have hk : Neg.up (.atom q) ∈ _ :=
            (hm _ h).resolve_left (fun hd => hq (atomMem_of_mem hd))
          have hqp : ¬ q = p := fun e => (hK _ hk) e
          rw [interpPA_atom_eq hsat hq]
          refine nOrAllIntro (List.mem_append_left _ ?_)
            (.stable (.rfoc (.init (List.mem_cons_of_mem _ hk))))
          rw [atomHead, if_neg hqp]
          exact List.mem_cons_self ..)
  | _, _, .atom q, .lax, hm, hm2, hK, .init h => by
      by_cases hq : atomMem q done = true
      · exact UpFrom2.mk2 0 (fun _ f' _ _ => by
          show Inv _ [] .tru (interpP p (f' + 2) [] done (some (.circ (.atom q))))
          rw [interpP_circ_laxRows hsat (.atom q)]
          refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
          rw [interpPA_atomT_eq hsat hq]; exact nTopIntro)
      · exact UpFrom2.mk2 0 (fun _ f' _ _ => by
          show Inv _ [] .tru (interpP p (f' + 2) [] done (some (.circ (.atom q))))
          rw [interpP_circ_laxRows hsat (.atom q)]
          refine emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..)) ?_
          have hk : Neg.up (.atom q) ∈ _ :=
            (hm _ h).resolve_left (fun hd => hq (atomMem_of_mem hd))
          have hqp : ¬ q = p := fun e => (hK _ hk) e
          rw [interpPA_atom_eq hsat hq]
          refine nOrAllIntro (List.mem_append_left _ ?_)
            (.stable (.rfoc (.init (List.mem_cons_of_mem _ hk))))
          rw [atomHead, if_neg hqp]
          exact List.mem_cons_self ..)
  | _, _, .or P₁ P₂, .tru, hm, hm2, hK, .or1 r₁ =>
      let w := URFQ done hsat hP hm hm2 hK r₁
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru
          (interpP p (f' + 1) [] done (some (.up (.or P₁ P₂))))
        rw [interpPA_or_eq hsat P₁ P₂]
        exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..))
          (w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf'))
  | _, _, .or P₁ P₂, .lax, hm, hm2, hK, .or1 r₁ =>
      let w := URFQ done hsat hP hm hm2 hK r₁
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru
          (interpP p (f' + 1) [] done (some (.circ (.or P₁ P₂))))
        rw [interpP_circ_laxRows hsat (.or P₁ P₂)]
        exact emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..))
          (w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf'))
  | _, _, .or P₁ P₂, .tru, hm, hm2, hK, .or2 r₂ =>
      let w := URFQ done hsat hP hm hm2 hK r₂
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru
          (interpP p (f' + 1) [] done (some (.up (.or P₁ P₂))))
        rw [interpPA_or_eq hsat P₁ P₂]
        exact nOrAllIntro (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          (w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf'))
  | _, _, .or P₁ P₂, .lax, hm, hm2, hK, .or2 r₂ =>
      let w := URFQ done hsat hP hm hm2 hK r₂
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru
          (interpP p (f' + 1) [] done (some (.circ (.or P₁ P₂))))
        rw [interpP_circ_laxRows hsat (.or P₁ P₂)]
        exact emitJ .lax (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          (w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf'))
  | _, _, .down M, .tru, hm, hm2, hK, .rel dI =>
      let w := UEntryQ done hsat hP hm hm2 hK M dI
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru (interpP p (f' + 1) [] done (some (.up (.down M))))
        rw [interpPA_down_eq hsat M]
        have h₁ := w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf'
        rw [jGoal_tru] at h₁
        exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..)) h₁)
  | _, _, .down (.up P'), .lax, hm, hm2, hK, .rel dI =>
      let w := UEntryQ done hsat hP hm hm2 hK (.up P') dI
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru
          (interpP p (f' + 1) [] done (some (.circ (.down (.up P')))))
        rw [interpP_circ_laxRows hsat (.down (.up P'))]
        exact emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..))
          (w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf'))
  | _, _, .down (.circ P'), .lax, hm, hm2, hK, .rel dI =>
      let w := UEntryQ done hsat hP hm hm2 hK (.circ P') dI
      UpFrom2.mk1 w.1 (fun e' f' he' hf' => by
        show Inv _ [] .tru
          (interpP p (f' + 1) [] done (some (.circ (.down (.circ P')))))
        rw [interpP_circ_laxRows hsat (.down (.circ P'))]
        exact emitJ .lax (List.mem_append_left _ (List.mem_cons_self ..))
          (w.2 (e' + 1) f' (Nat.le_trans he' (Nat.le_succ _)) hf'))
  | _, _, .down (.and _ _), .lax, _, _, _, .rel dI => nomatch dI
  | _, _, .down (.imp _ _), .lax, _, _, _, .rel dI => nomatch dI
  termination_by Γ' K P₀ j hm hm2 hK r =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf r)
  decreasing_by ljf_dec_a


/-- Left focus on a kept hypothesis, `∀p` mode, at the row index. -/
def ULFQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD} {L : Nat → List Neg} {H : Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      RowKit p done j P₀ L → PFreeN p H →
      LFoc Γ' H j P₀ →
      UpFrom2 (fun e f => LFoc (interpP p e [] done none :: K) H j
        (jChain j (L f)))
  | _, _, _, _, _, _, hm, hm2, hK, kit, hH, .rel d =>
      let w := UInvGQ done hsat hP hm hm2 hK kit
        (PFreeΩ.cons hH PFreeΩ.nil) d
      ⟨w.1, fun e' f' he' hf' => .rel (w.2 e' f' he' hf')⟩
  | _, _, _, _, _, _, hm, hm2, hK, kit, hH, .circL d =>
      let w := UInvGQ done hsat hP hm hm2 hK kit
        (PFreeΩ.cons hH PFreeΩ.nil) d
      ⟨w.1, fun e' f' he' hf' => .circL (w.2 e' f' he' hf')⟩
  | _, _, _, _, _, _, hm, hm2, hK, kit, hH, .impL s lf =>
      UpFrom2.map₂ (fun _ _ x y => .impL x y)
        (UpFrom.toUpFrom2 (TStabQ pant dant done hsat hP hm hm2 hK hH.1 s))
        (ULFQ done hsat hP hm hm2 hK kit hH.2 lf)
  | _, _, _, _, _, _, hm, hm2, hK, kit, hH, .and1 lf =>
      let w := ULFQ done hsat hP hm hm2 hK kit hH.1 lf
      ⟨w.1, fun e' f' he' hf' => .and1 (w.2 e' f' he' hf')⟩
  | _, _, _, _, _, _, hm, hm2, hK, kit, hH, .and2 lf =>
      let w := ULFQ done hsat hP hm hm2 hK kit hH.2 lf
      ⟨w.1, fun e' f' he' hf' => .and2 (w.2 e' f' he' hf')⟩
  termination_by Γ' K P₀ j L H hm hm2 hK kit hH lf =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf lf)
  decreasing_by ljf_dec_a


/-- Inversion, `∀p` mode, goal re-targeted to the `jChain` positive. -/
def UInvGQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {j : JD} {L : Nat → List Neg}
      {Ω : List Pos},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      RowKit p done j P₀ L → PFreeΩ p Ω →
      Inv Γ' Ω j (.up P₀) →
      UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) Ω j
        (.up (jChain j (L f))))
  | _, _, _, _, _, _, hm, hm2, hK, kit, _, .stable s =>
      let w := UStabQ done hsat hP hm hm2 hK kit s
      ⟨w.1, fun e' f' he' hf' => stabFold (w.2 e' f' he' hf')⟩
  | _, _, _, _, _, .or PA PB :: _, hm, hm2, hK, kit, hΩ, .orL d₁ d₂ =>
      UpFrom2.map₂ (fun _ _ x y => .orL x y)
        (UInvGQ done hsat hP hm hm2 hK kit (hΩ.tail.cons hΩ.head.1) d₁)
        (UInvGQ done hsat hP hm hm2 hK kit (hΩ.tail.cons hΩ.head.2) d₂)
  | _, _, _, _, _, _, _, _, _, _, _, .flsL => ⟨0, fun _ _ _ _ => .flsL⟩
  | _, _, _, _, _, .down M₀ :: _, hm, hm2, hK, kit, hΩ, .downL d =>
      UpFrom2.map (fun _ _ x =>
          .downL (x.wk (fun Z hZ => by
            rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
            · rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))
        (UInvGQ done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hΩ.head hK) kit hΩ.tail d)
  | _, _, _, _, _, .atom a :: _, hm, hm2, hK, kit, hΩ, .atomL d =>
      UpFrom2.map (fun _ _ x =>
          .atomL (x.wk (fun Z hZ => by
            rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
            · rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))
        (UInvGQ done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom a)) from hΩ.head) hK)
          kit hΩ.tail d)
  termination_by Γ' K P₀ j L Ω hm hm2 hK kit hΩ d =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf d)
  decreasing_by ljf_dec_a


/-- The `p`-fire eliminator, `∀p` mode. -/
def UpElimQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {j : JD} {L : Nat → List Neg}
      {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      RowKit p done j P₀ L →
      a = p → b = p → Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      Stab Γ' .tru (.atom b) →
      UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
        (jBox j (nOrAll (L f))))
  | _, _, _, _, _, _, _, _, hm, _, hK, _, ha, hb, hXpkg, _, .rfoc (.init h) =>
      False.elim (by
        rcases hm _ h with hd | hk
        · have h1 := atomMem_of_mem hd
          have h2 := saturated_atom_absent hsat hXpkg
          rw [hb.trans ha.symm] at h1
          rw [h1] at h2; cases h2
        · exact (hK _ hk) hb)
  | _, _, _, _, _, _, a, b, hm, hm2, hK, kit, ha, hb, hXpkg, lfP,
      @Stab.lfoc _ _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            UpElimQ done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK kit
              ha hb hXpkg (lfP.wk (Sub.grow _)) s'
        | .imp (.atom c) Nc, _, hd, .impL s_c lf_c =>
            if hcp : c = p then
              UpElimQ done hsat hP hm hm2 hK kit ha hcp hXpkg lfP s_c
            else
              let ⟨rest, hXr⟩ := splitAt done _ hd
              qFireA hsat hcp hXr (fun f => kit.qmem f hXr)
                (TStabQ pant dant done hsat hP hm hm2 hK
                  (show PFreeP p (Pos.atom c) from hcp) s_c)
                (aMinQ [Nc] rest _ (.up _)
                  (ParkedCtxP.sub (splits_sub hXr) hP) hK
                  (fireClean (splitHyp hm hXr) (.stable
                    (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                      (.impL
                        ((hb.trans ha.symm) ▸
                          Stab.lfoc (List.mem_cons_self ..)
                            (lf_c.wk (Sub.grow _)))
                        (lfP.wk (Sub.grow _)))))))
        | .imp (.down (.imp Q' N')) N_d, _, hd, .impL s_d lf_d =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            dykFireA hsat hXr (fun f => kit.dmem f hXr)
              (dant done _ _ Q' N' N_d hsat hP hd hm hm2 hK s_d)
              (aMinQ [N_d] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_d.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _)))))))
        | .imp (.down (.circ Q')) N_c, _, hd, .impL s_c lf_c =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            cimpFireA hsat hXr (fun f => kit.cmem f hXr)
              (parkAntGuard pant hsat hP hd hm hm2 hK s_c)
              (aMinQ [N_c] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_c.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _)))))))
        | .imp (.or Qa Qb) N_o, _, hd, .impL s_o lf_o =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            orimpFireA hsat hXr (fun f => kit.omem f hXr)
              (parkAntGuard pant hsat hP hd hm hm2 hK s_o)
              (aMinQ [N_o] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_o.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _)))))))
        | .imp (.down (.up Pa)) N_s, _, hd, .impL s_s lf_s =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            shimpFireA hsat hXr (fun f => kit.smem f hXr)
              (parkAntGuard pant hsat hP hd hm hm2 hK s_s)
              (aMinQ [N_s] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_s.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _)))))))
        | .imp (.down (.and Ma Mb)) N_a, _, hd, .impL s_a lf_a =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            andimpFireA hsat hXr (fun f => kit.amem f hXr)
              (parkAntGuard pant hsat hP hd hm hm2 hK s_a)
              (aMinQ [N_a] rest _ (.up _)
                (ParkedCtxP.sub (splits_sub hXr) hP) hK
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_a.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _)))))))
        | .circ _, _, _, lf => nomatch lf
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        let w := UpLFQ done hsat hP hm hm2 hK kit
          (hK _ ((hm _ h).resolve_left hd)) ha hb hXpkg lfP lf
        ⟨w.1, fun e' f' he' hf' =>
          keepFold (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
            (w.2 e' f' he' hf')⟩
  termination_by Γ' K M P₀ j L a b hm hm2 hK kit ha hb hXpkg lfP s =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf s)
  decreasing_by ljf_dec_p


/-- Left focus on a kept hypothesis, inside an `∀p`-mode `p`-proof. -/
def UpLFQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {j : JD} {L : Nat → List Neg}
      {H : Neg} {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      RowKit p done j P₀ L → PFreeN p H →
      a = p → b = p → Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      LFoc Γ' H .tru (.atom b) →
      UpFrom2 (fun e f => LFoc (interpP p e [] done none :: K) H j
        (jChain j (L f)))
  | _, _, _, _, _, _, _, _, _, hm, hm2, hK, kit, hH, ha, hb, hXpkg, lfP, .rel d =>
      let w := UpInvGQ done hsat hP hm hm2 hK kit
        (PFreeΩ.cons hH PFreeΩ.nil) ha hb hXpkg lfP d
      ⟨w.1, fun e' f' he' hf' => .rel (w.2 e' f' he' hf')⟩
  | _, _, _, _, _, _, _, _, _, hm, hm2, hK, kit, hH, ha, hb, hXpkg, lfP,
      .impL s lf =>
      UpFrom2.map₂ (fun _ _ x y => .impL x y)
        (UpFrom.toUpFrom2 (TStabQ pant dant done hsat hP hm hm2 hK hH.1 s))
        (UpLFQ done hsat hP hm hm2 hK kit hH.2 ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, _, hm, hm2, hK, kit, hH, ha, hb, hXpkg, lfP,
      .and1 lf =>
      let w := UpLFQ done hsat hP hm hm2 hK kit hH.1 ha hb hXpkg lfP lf
      ⟨w.1, fun e' f' he' hf' => .and1 (w.2 e' f' he' hf')⟩
  | _, _, _, _, _, _, _, _, _, hm, hm2, hK, kit, hH, ha, hb, hXpkg, lfP,
      .and2 lf =>
      let w := UpLFQ done hsat hP hm hm2 hK kit hH.2 ha hb hXpkg lfP lf
      ⟨w.1, fun e' f' he' hf' => .and2 (w.2 e' f' he' hf')⟩
  termination_by Γ' K M P₀ j L H a b hm hm2 hK kit hH ha hb hXpkg lfP lf =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf lf)
  decreasing_by ljf_dec_a


/-- Inversion inside an `∀p`-mode `p`-proof. -/
def UpInvGQ (done : List Neg) (hsat : Saturated done) (hP : ParkedCtxP done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {j : JD} {L : Nat → List Neg}
      {Ω : List Pos} {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      RowKit p done j P₀ L → PFreeΩ p Ω →
      a = p → b = p → Neg.imp (.atom a) M ∈ done → LFoc Γ' M j P₀ →
      Inv Γ' Ω .tru (.up (.atom b)) →
      UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) Ω j
        (.up (jChain j (L f))))
  | _, _, _, _, _, _, _, _, _, hm, hm2, hK, kit, _, ha, hb, hXpkg, lfP,
      .stable s =>
      let w := UpElimQ done hsat hP hm hm2 hK kit ha hb hXpkg lfP s
      ⟨w.1, fun e' f' he' hf' => stabFold (w.2 e' f' he' hf')⟩
  | _, _, _, _, _, _, .or PA PB :: _, _, _, hm, hm2, hK, kit, hΩ, ha, hb,
      hXpkg, lfP, .orL d₁ d₂ =>
      UpFrom2.map₂ (fun _ _ x y => .orL x y)
        (UpInvGQ done hsat hP hm hm2 hK kit (hΩ.tail.cons hΩ.head.1)
          ha hb hXpkg lfP d₁)
        (UpInvGQ done hsat hP hm hm2 hK kit (hΩ.tail.cons hΩ.head.2)
          ha hb hXpkg lfP d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .flsL =>
      ⟨0, fun _ _ _ _ => .flsL⟩
  | _, _, _, _, _, _, .down M₀ :: _, _, _, hm, hm2, hK, kit, hΩ, ha, hb,
      hXpkg, lfP, .downL d =>
      UpFrom2.map (fun _ _ x =>
          .downL (x.wk (fun Z hZ => by
            rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
            · rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))
        (UpInvGQ done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hΩ.head hK) kit hΩ.tail ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)
  | _, _, _, _, _, _, .atom c :: _, _, _, hm, hm2, hK, kit, hΩ, ha, hb,
      hXpkg, lfP, .atomL d =>
      UpFrom2.map (fun _ _ x =>
          .atomL (x.wk (fun Z hZ => by
            rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
            · rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))))
        (UpInvGQ done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom c)) from hΩ.head) hK)
          kit hΩ.tail ha hb hXpkg (lfP.wk (Sub.grow _)) d)
  termination_by Γ' K M P₀ j L Ω a b hm hm2 hK kit hΩ ha hb hXpkg lfP d =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf d)
  decreasing_by ljf_dec_a

end


/-! # Part 7: the two entry points, and the chain

`LJF/OFuelPCof.lean`'s `TInvP`/`UEntryP` are inhabited by the two
traversals above.  Both are conditional on the antecedent dispatches, in
the `CimpAnt` idiom: parameters, never assumptions.

The conditionality is a FIXPOINT requirement, not a gap in the
bookkeeping.  `parkAntP_of_satA2P` (proved, `LJF/OFuelPCof.lean`) derives
`ParkAntP p` from `SatA2P p`, which `satA2P_of_uentryP` derives from
`UEntryP p` — so the four positive-antecedent dispatches are instances of
the family's own `∀p` entry at the SAME station, applied to the
antecedent's own subderivation, and `LJF/OFuelHeight.lean` §10.4 is the
height fact that makes them legitimate recursive calls.  Taking them as
such requires re-founding the family on
`μ = (normalised height, station weight, size)`; the family above is
founded on `LJF/O.lean`'s station pair, which cannot pay for a call at an
unchanged station (`docs/ui-ljfo-clause-table.md` §4.11).  `DykAntP` is a
different matter: it is not an instance of the `∀p` entry at all
(Part 4). -/

/-- **The `∃p` traversal**, conditional on the two dispatches. -/
def tinvP_of (pant : ParkAntP p) (dant : DykAntP p) : TInvP p :=
  TInvQ pant dant

/-- **The `∀p` entry**, conditional on the two dispatches. -/
def uentryP_of (pant : ParkAntP p) (dant : DykAntP p) : UEntryP p :=
  UEntryQ pant dant

/-- `SatE2P` follows. -/
def satE2P_of (pant : ParkAntP p) (dant : DykAntP p) : SatE2P p :=
  satE2P_of_tinvP (tinvP_of pant dant)

/-- `SatA2P` follows. -/
def satA2P_of (pant : ParkAntP p) (dant : DykAntP p) : SatA2P p :=
  satA2P_of_uentryP (uentryP_of pant dant)

/-- And so does the antecedent dispatch the family took as a parameter —
which is what makes `ParkAntP` a fixpoint requirement rather than an
independent obligation. -/
def parkAntP_of (pant : ParkAntP p) (dant : DykAntP p) : ParkAntP p :=
  parkAntP_of_satA2P (satA2P_of pant dant)

/-! # Part 8: what the height-first re-founding needs, and what it does
not reach

The remaining step for node N0c is to replace the `pant` parameter by a
NATIVE call and re-found the family on
`μ = (normalised height, station weight, size)`.  Two facts about that
step are settled here, so that the next run starts from them. -/

/-- **The native dispatch typechecks.**  At the dispatch site the family
already holds `hm`, `hm2`, `hK` and `s_d : Stab Γ′ .tru Q`, so the
antecedent guard of the four positive-antecedent shapes is the `∀p` entry
at the SAME station applied to `Inv.stable s_d` — no weakening, no
reshaping.  This term is what a re-founded family would inline where
`parkAntGuard pant …` now stands, and its type is `parkAntGuard`'s
exactly.  So the obstruction is the MEASURE, not the statement. -/
def nativeParkAnt (pant : ParkAntP p) (dant : DykAntP p)
    {done K Γ' : List Neg} {Q : Pos}
    (hsat : Saturated done) (hP : ParkedCtxP done)
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) (hm2 : Sub done Γ')
    (hK : PFreeCtx p K) (s : Stab Γ' .tru Q) :
    UpFrom2 (fun e f => Inv (interpP p e [] done none :: K) [] .tru
      (interpP p f [] done (some (.up Q)))) :=
  UEntryQ pant dant done hsat hP hm hm2 hK (.up Q) (Inv.stable s)

/-- **And its height edge is strict**, with the station unchanged: the
argument `Inv.stable s_d` is strictly below the focus
`Stab.lfoc h (.impL s_d lf′)` in normalised height.  `hgt_antDispatch`
states this through a weakening; weakening is height-exact
(`hgt_wk`), so it holds for the unweakened argument the native call
takes. -/
theorem nativeParkAnt_edge {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg}
    {P : Pos} (h : Neg.imp Q N ∈ Γ) (s_d : Stab Γ .tru Q)
    (lf' : LFoc Γ N j P) :
    hgtI (Inv.stable s_d) < hgtS (Stab.lfoc h (.impL s_d lf')) := by
  have h1 := hgt_antDispatch (Sub.refl Γ) h s_d lf'
  have h2 := hgt_wk (Sub.refl Γ) (Inv.stable s_d)
  omega

/-! ## The cell that exercises `DykAntP`

The re-founding does NOT reach the Dyckhoff dispatch, and the smallest
station that shows it is one parked Dyckhoff implication:

    done = [ ↓(c ⊃ ↑a) ⊃ ↑e ],   goal  ↑e

`done` is saturated (no parked `q`-implication has its atom present), and
its single `∃p` row is

    ( A(done ⇒ c ⊃ ↑a) ⊃ E(↑e :: []) )  ∧  E(↓↑a ⊃ ↑e :: [])

whose guard is the `∀p` interpolant at the NEGATIVE goal `c ⊃ ↑a`.  A
stable proof that focuses on the member supplies
`s_d : Stab Γ′ .tru (↓(c ⊃ ↑a))`, and `LJF/OFuelHeight.lean` §10.4 turns
that into `A(done ⇒ ↑↓(c ⊃ ↑a))` — by `interpPA_down_eq` a DISJUNCTION
with `A(done ⇒ c ⊃ ↑a)` as its head disjunct, which does not project.
`negOfDownStab` at the body `c ⊃ ↑a` would bridge the two and rises
without bound (§7.3, `ceCyD`: 29 → 40, and the measured family
`szI = 10n + 25`).  Hence `DykAntP`. -/

/-- The station of the cell above. -/
def dykCell : List Neg :=
  [ .imp (.down (.imp (.atom "c") (.up (.atom "a")))) (.up (.atom "e")) ]

/-- It is saturated, so the `∃p` read-off applies to it. -/
theorem dykCell_saturated : Saturated dykCell := rfl

/-- And it carries the Dyckhoff shape. -/
theorem dykCell_parked : ParkedCtxP dykCell := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact ParkedNP.dyk _ _ _
  · exact absurd hZ List.not_mem_nil

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
/-! Part 5, the `∃p` side of the family. -/

#axioms_within LJFO.eMinQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.TInvQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.TStabQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.TRFQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.TLFQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.TpElimQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.TpLFQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.TpInvQ [propext, Classical.choice, Quot.sound]

/-! Part 6, the `∀p` side of the family. -/

#axioms_within LJFO.aMinQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.UEntryQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.UStabQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.URFQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.ULFQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.UInvGQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.UpElimQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.UpLFQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.UpInvGQ [propext, Classical.choice, Quot.sound]

/-! Part 7, the two entry points and the chain. -/

#axioms_within LJFO.tinvP_of [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.uentryP_of [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.satE2P_of [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.satA2P_of [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.parkAntP_of [propext, Classical.choice, Quot.sound]

/-! Part 8, the re-founding evidence. -/

#axioms_within LJFO.nativeParkAnt [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.nativeParkAnt_edge [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.dykCell_saturated [propext]
#axioms_within LJFO.dykCell_parked [propext]

#axioms_within LJFO.qAssembleP [propext, Quot.sound]
#axioms_within LJFO.boxAssembleP [propext, Quot.sound]
#axioms_within LJFO.parkFireA [propext, Quot.sound]
#axioms_within LJFO.qFireA [propext, Quot.sound]
#axioms_within LJFO.boxFireA [propext, Quot.sound]
