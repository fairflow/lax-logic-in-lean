/-
LJF◯ — the termination kit of the cofinality family for `interpP`
(route (B), node N0c over node N0e).

Split out of `LJF/OFuelPFam.lean` on 2026-09-05 so that the two farms can
be exercised without re-elaborating the family, which costs a quarter of
an hour.  Nothing here is new mathematics: Part 1 is the generic
station-descent lemmas and the descent farm `ljf_dec_p` as they stood,
Part 4b is the height side of the founding.
-/
import LJF.OFuelPCof

namespace LJFO

variable {p : String}

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

/-! # Part 4b: the height-first founding

The family below is ordered by

    μ := (normalised derivation height, station weight, `sizeOf`)

lexicographically, with the height of `LJF/OFuelHeight.lean` Part 10
(`hgtI d = szI d`, `hgtS s = szS s + 1`, `hgtL lf = szL lf + 2`,
`hgtR r = szR r + 2`, so that the phase constructors are height-neutral).
The second and third components are exactly the pair the earlier draft was
founded on, so every station obligation is unchanged; what the height
buys is the ONE edge a station-first order cannot pay for — the antecedent
dispatch of a parked implication, a call at an UNCHANGED station on a
strict subderivation (`hgt_antDispatch`, `nativeParkAnt_edge`).

Two facts shape the kit.

* At the many height-EQUAL sites (every parking, every phase change,
  every `wk`) the equality is only propositional (`hgt_wk` and its kin),
  so `Prod.Lex.right` does not apply syntactically.  `lex3_of_le` is the
  step that takes a height bound `≤` and the old pair proof.
* The six `p`-eliminator traversals carry an EXTRA derivation `lfP`
  beside the one they recurse on, and splice it into the argument of
  their fire call, so the height of that argument is not bounded by the
  recursion argument alone.  Their first component is therefore the SUM
  `hgt(recursion argument) + hgtL lfP`; under it every edge into, out of
  and inside the group is bounded (the fire edge becomes strict, the
  entry edge from `TStabQ`/`UStabQ` exact).  This is the one thing Part 10
  does not state, and it is stated here because it is a fact about the
  family's argument lists, not about the transformers. -/

/-- The lexicographic step at a height that does not RISE: the station
weight and `sizeOf` pay, exactly as they do in `LJF/O.lean`.  Stated with
the inner relation open so that the residual goal is byte-for-byte the one
`ljf_dec_e` / `ljf_dec_a` / `ljf_dec_p` already discharge. -/
theorem lex3_of_le {s : Nat × Nat → Nat × Nat → Prop} {h h' : Nat}
    {a b : Nat × Nat} (hle : h' ≤ h) (hpair : s a b) :
    Prod.Lex (fun x y : Nat => x < y) s (h', a) (h, b) := by
  rcases Nat.lt_or_ge h' h with hlt | hge
  · exact Prod.Lex.left _ _ hlt
  · cases Nat.le_antisymm hle hge
    exact Prod.Lex.right _ hpair

/-- The same step where `simp_wf` has already unfolded the lexicographic
relation into its disjunctive form, which it does whenever it can decide
the tail component. -/
theorem lex3_or_of_le {P : Prop} {h h' : Nat} (hle : h' ≤ h) (hp : P) :
    h' < h ∨ h' = h ∧ P := by
  rcases Nat.lt_or_ge h' h with hlt | hge
  · exact Or.inl hlt
  · exact Or.inr ⟨Nat.le_antisymm hle hge, hp⟩

/-- The cast the `p`-eliminators put on the refired atom's own stable
proof, named so that its height is a rewrite rather than a `subst`.  The
two `p`-eliminators know `a = p` and `b = p` and must present a proof of
`↑a` where they hold one of `↑b`. -/
def stabAtomCast {Γ : List Neg} {j : JD} {a b : String} (h : b = a)
    (s : Stab Γ j (.atom b)) : Stab Γ j (.atom a) := h ▸ s

@[simp] theorem szS_stabAtomCast {Γ : List Neg} {j : JD} {a b : String}
    (h : b = a) (s : Stab Γ j (.atom b)) :
    szS (stabAtomCast h s) = szS s := by cases h; rfl

/-- One non-increasing transformer on the left of a `<` or a `≤` goal. -/
macro "hgt_step" t:term : tactic => `(tactic|
  (first
    | refine Nat.lt_of_le_of_lt $t ?_
    | refine Nat.le_trans $t ?_))

set_option hygiene false in
/-- Finish a height goal: compute every constructor height, discharge the
weakenings and the atom cast, and let `omega` close. -/
macro "hgt_close" : tactic => `(tactic| (
    try simp only [List.nil_append, List.cons_append, List.append_nil,
      szI, szS, szL, szR, szI_wk, szS_wk, szL_wk, szR_wk,
      szS_stabAtomCast]
    omega))

/-- **The antecedent dispatch as a NATIVE recursive call.**
`hgt_antDispatch` states the edge through a weakening; the family's own
arm takes the unweakened `Inv.stable s_d`, and weakening is height-exact
(`hgt_wk`), so the edge holds there too.  This is `nativeParkAnt_edge` of
`LJF/OFuelPFam.lean` Part 8, stated here because the farm needs it. -/
theorem hgt_antDispatchN {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg}
    {P : Pos} (h : Neg.imp Q N ∈ Γ) (s_d : Stab Γ .tru Q)
    (lf' : LFoc Γ N j P) :
    hgtI (Inv.stable s_d) < hgtS (Stab.lfoc h (.impL s_d lf')) := by
  have h1 := hgt_antDispatch (Sub.refl Γ) h s_d lf'
  have h2 := hgt_wk (Sub.refl Γ) (Inv.stable s_d)
  omega

set_option hygiene false in
/-- The computing half of a height goal: unfold the normalised heights and
the four weakening equations, then either compute outright (every
structural edge, every phase change, the antecedent dispatch) or peel one
of the nine non-increasing transformers the family builds its arguments
with (`LJF/OFuelHeight.lean` Parts 3, 6 and 9) and compute. -/
macro "hgt_body" : tactic => `(tactic| (
    try simp only [hgtI, hgtS, hgtL, hgtR, szI_wk, szS_wk, szL_wk, szR_wk,
      szS_stabAtomCast]
    first
      | hgt_close
      | (hgt_step (szI_fireClean _ _); hgt_close)
      | (hgt_step (szI_boxClean _ _); hgt_close)
      | (hgt_step (szI_invUp (by intro a; simp) _ _ _); hgt_close)
      | (hgt_step (szI_invAndHyp _); hgt_close)
      | (hgt_step (szI_invImpFls _); hgt_close)
      | (hgt_step (szI_invFireHyp _ _); hgt_close)
      | (hgt_step (szI_invFireHyp (findFire_mem (by assumption)) _); hgt_close)
      | (hgt_step (szI_extract _ _ _ _); hgt_close)
      | (hgt_step (szI_extract [] _ _ _); hgt_close)
      | (hgt_step (szI_laxReleaseUp _); hgt_close)
      | (hgt_step (szI_laxReleaseCirc _); hgt_close)))

set_option hygiene false in
/-- **The height side of a `decreasing_by` goal.**  The named Part-10
bounds first, in the shape the family's own arms present them; then the
computing half. -/
macro "hgt_dec" : tactic => `(tactic| (
    first
      | hgt_body
      | exact hgt_goalInv _ _ _ _
      | exact hgt_antDispatch _ _ _ _
      | exact hgt_antDispatchN _ _ _
      | exact hgt_releaseUp _
      | exact hgt_releaseCirc _
      | exact hgt_fireCont _ _ _ _ _ _
      | exact hgt_boxRow _ _ _ _ _))

set_option hygiene false in
/-- The station-and-size side of a `decreasing_by` goal: the pair the
family was founded on before the height was put in front of it, handed to
`LJF/O.lean`'s farms and to `ljf_dec_p` unchanged. -/
macro "ljf_dec_pair" : tactic => `(tactic| (
    first
      | ljf_dec_e
      | ljf_dec_a
      | ljf_dec_p))

set_option hygiene false in
/-- **The decreasing farm of the height-founded family.**  A strict height
drop takes `Prod.Lex.left`; a height that does not rise hands the goal on
to the station farms unchanged through `lex3_of_le`. -/
macro "ljf_dec_h" : tactic => `(tactic| (
    all_goals simp_wf
    all_goals
      first
        | (refine Prod.Lex.left _ _ ?_; hgt_dec)
        | (refine Prod.Lex.right _ ?_; ljf_dec_pair)
        | (refine lex3_of_le ?_ ?_
           · hgt_dec
           · ljf_dec_pair)
        | (refine Or.inl ?_; hgt_dec)
        | (refine lex3_or_of_le ?_ ?_
           · hgt_dec
           · ljf_dec_pair)
        | ljf_dec_pair
        | guard_target = True))


end LJFO
