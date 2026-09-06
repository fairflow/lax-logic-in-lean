/-
LJF◯: POLARISATION INVARIANCE, and the composition principle `CutInv`.

Route (B)'s `CutInv` obligation (`docs/ui-ljfo-clause-table.md` §4.19) closes
through the erasure bridge as soon as the CONVERSE arrow is available at the
polarised sequents route (B) actually writes down — sequents carrying the two
shapes outside the image of `posOfO`/`negOfO`,

    ↓↑P   the POSITIVE DELAY          ↑↓N   the NEGATIVE DELAY

(`docs/cutinv-cases.md` §1).  The refutation stage settled the case list with
26 designed cells (`wip/cutinv_cells.lean`); this file proves the lemmas those
cells test.

Write

    ⟦N⟧ = canN N = negOfO (eraseNeg N)      ⟦P⟧ = canP P = posOfO (erasePos P)

for the canonical form.  `erase_polarise` gives `⌊⟦N⟧⌋ = ⌊N⌋`, so `⟦N⟧` is `N`
with every delay removed; the transfer block below moves derivations between
the two, in the direction the bridge needs.

The block is ONE mutual recursion on the formula (§2), five functions:

    bLL : LFoc Δ ⟦N⟧ j P      → LFoc Δ N j P                (hypothesis side)
    gA  : Inv Γ [] j ⟦N⟧      → Inv Γ [] j N                (goal side)
    sD  : Stab Γ j ⟦P⟧        → Stab Γ j P                  (focused positive)
    fT  : the branches of `⟦R⟧` are covered by any branch of `R`  (goal `.tru`)
    fS  : the same, at a stable sequent, at either flag

and it needs NO ◯-free restriction: `circ` is handled in `bLL`/`gA`/`sD`
exactly as `up`/`or` are, and the `lax` flag costs only the two emptiness
lemmas `laxImpEmpty`/`laxAndEmpty` (S14 of `docs/cutinv-cases.md`) at `gA`'s
`impR`/`andR` arms.  The ◯-free fragment is therefore delivered as a
SPECIALISATION (§5), not as a separate development.

The CONVERSES of the block — `Inv Γ Ω j N → Inv Γ Ω j ⟦N⟧` and its relatives —
are NOT proved here, and the goal-side converse is FALSE: cell 14.3 inhabits
`Inv [] [] .lax ↑↓(↑⊥ ⊃ ↑⊥)` while `⟦↑↓(↑⊥ ⊃ ↑⊥)⟧ = ↑⊥ ⊃ ↑⊥` and
`Inv Γ [] .lax (Q ⊃ N)` is empty.  See `notCanGoalConverse` (§2b).  Only the
un-primed directions are needed, and only those are true.

§4 assembles `polInvT` and the composition principle at the truth flag,
`cutInvT`; §4b adds the modal steps — `polInvL` and `cutInv` at every flag;
§5 states the truth-flag results for the ◯-free fragment, which is
Liang–Miller's "delays are inert" for the ◯-free part of LJF◯.  ONE axiom beyond the
development's usual `[propext, Quot.sound]` is spent, and only where a
derivation is wanted as DATA: focalization (`LJFO.FocalizationPLL`) factors
through `PLLND.SCh`, which is a `Prop`, so the bridge can only return
`Nonempty (Inv …)`.  Every `Nonempty`-valued statement here — which is where
the mathematical content sits — pins at `[propext, Quot.sound]`.
-/
import LJF.OCore
import LJF.OBridge
import Meta.Audit

namespace LJFO

open PLLND

universe u

/-! ## 1. The canonical form -/

/-- `⟦N⟧` — the canonical polarisation of `N`'s erasure.  Delays vanish:
`⟦↑↓M⟧ = ⟦M⟧` and `⟦↓↑P⟧ = ⟦P⟧`. -/
abbrev canN (N : Neg) : Neg := negOfO (eraseNeg N)

/-- `⟦P⟧` — the canonical polarisation of `P`'s erasure. -/
abbrev canP (P : Pos) : Pos := posOfO (erasePos P)

/-- A canonical context. -/
abbrev canCtx (Γ : List Neg) : List Neg := Γ.map canN

/-! ### The clause table of `canN`/`canP`

Every one of these is `rfl`; they are recorded so the case analysis of §2 can
be read off, and so a reader can see where the two delays collapse. -/

theorem canP_atom (a : String) : canP (.atom a) = .atom a := rfl
theorem canP_fls : canP .fls = .fls := rfl
theorem canP_or (P Q : Pos) : canP (.or P Q) = .or (canP P) (canP Q) := rfl
/-- **The positive delay collapses.** -/
theorem canP_down_up (P : Pos) : canP (.down (.up P)) = canP P := rfl
theorem canP_down_imp (Q : Pos) (N : Neg) :
    canP (.down (.imp Q N)) = .down (canN (.imp Q N)) := rfl
theorem canP_down_and (M N : Neg) :
    canP (.down (.and M N)) = .down (canN (.and M N)) := rfl
theorem canP_down_circ (P : Pos) :
    canP (.down (.circ P)) = .down (canN (.circ P)) := rfl

theorem canN_up_atom (a : String) : canN (.up (.atom a)) = .up (.atom a) := rfl
theorem canN_up_fls : canN (.up .fls) = .up .fls := rfl
theorem canN_up_or (P Q : Pos) :
    canN (.up (.or P Q)) = .up (.or (canP P) (canP Q)) := rfl
/-- **The negative delay collapses.** -/
theorem canN_up_down (M : Neg) : canN (.up (.down M)) = canN M := rfl
theorem canN_imp (Q : Pos) (N : Neg) : canN (.imp Q N) = .imp (canP Q) (canN N) := rfl
theorem canN_and (M N : Neg) : canN (.and M N) = .and (canN M) (canN N) := rfl
theorem canN_circ (P : Pos) : canN (.circ P) = .circ (canP P) := rfl

/-! ### The two emptiness facts of the `lax` flag

`docs/cutinv-cases.md` S14: at `Ω = []`, `j = .lax` and a goal that is neither
a shift nor a box, no constructor of `Inv` applies. -/

/-- `Inv Γ [] .lax (Q ⊃ N)` is EMPTY. -/
theorem laxImpEmpty {Γ : List Neg} {Q : Pos} {N : Neg} :
    Inv Γ [] .lax (.imp Q N) → False := fun d => by cases d

/-- `Inv Γ [] .lax (M ∧ N)` is EMPTY. -/
theorem laxAndEmpty {Γ : List Neg} {M N : Neg} :
    Inv Γ [] .lax (.and M N) → False := fun d => by cases d

/-! ### `invertPos` unfolded

`invertPos` is a well-founded recursion, so its clauses are not definitional;
the four equations are recorded once, and the canonical branch families follow
from them because `canP` reduces on every head. -/

theorem invertPos_atom (a : String) :
    invertPos (.atom a) = [[Neg.up (Pos.atom a)]] := by simp [invertPos]
theorem invertPos_fls : invertPos .fls = [] := by simp [invertPos]
theorem invertPos_or (P Q : Pos) :
    invertPos (.or P Q) = invertPos P ++ invertPos Q := by simp [invertPos]
theorem invertPos_down (M : Neg) : invertPos (.down M) = [[M]] := by
  simp [invertPos]

theorem invertPos_canP_atom (a : String) :
    invertPos (canP (.atom a)) = [[Neg.up (Pos.atom a)]] := invertPos_atom _
theorem invertPos_canP_or (P Q : Pos) :
    invertPos (canP (.or P Q)) = invertPos (canP P) ++ invertPos (canP Q) :=
  invertPos_or _ _
theorem invertPos_canP_down_imp (Q : Pos) (N : Neg) :
    invertPos (canP (.down (.imp Q N))) = [[canN (.imp Q N)]] := invertPos_down _
theorem invertPos_canP_down_and (M N : Neg) :
    invertPos (canP (.down (.and M N))) = [[canN (.and M N)]] := invertPos_down _
theorem invertPos_canP_down_circ (P : Pos) :
    invertPos (canP (.down (.circ P))) = [[canN (.circ P)]] := invertPos_down _

/-! ### Forced shapes of a left focus

The two `LFoc` inversions the block needs; both are single pattern matches,
for the same reason `unStable`/`circInv` are. -/

/-- A left focus on a shifted hypothesis is `rel`. -/
def upLFocInv {Δ : List Neg} {Q : Pos} {j : JD} {P : Pos} :
    LFoc Δ (.up Q) j P → Inv Δ [Q] j (.up P)
  | .rel d => d

/-- A right focus on a disjunction chose a disjunct. -/
def orFocSplit {Δ : List Neg} {j : JD} {A B : Pos} {C : Sort u}
    (k₁ : RFocus Δ j A → C) (k₂ : RFocus Δ j B → C) :
    RFocus Δ j (.or A B) → C
  | .or1 r => k₁ r
  | .or2 r => k₂ r

/-! ### Three closures used by the recursion, taken as parameters

Each takes the relevant clause of the recursion as an argument, so it can sit
OUTSIDE the mutual block and the recursion stays syntactically simple. -/

/-- **Right delay introduction** (cells 1.2, 5.1, 5.2, 9.1): every right focus
on `P` is rewrapped, and the `lfoc`/`laxOf` spine is traversed by
`routeStab`. -/
def delayIntro {Γ : List Neg} {j : JD} {P : Pos} (s : Stab Γ j P) :
    Stab Γ j (.down (.up P)) :=
  routeStab (Δ₀ := Γ) (fun _ r => .rfoc (.rel (.stable (.rfoc r)))) (Sub.refl Γ) s

/-- Relay a stable proof of `↓⟦M⟧` to one of `↓M`, given the goal-side
transfer at `M`. -/
def relayDown {M : Neg} {Γ : List Neg} {j : JD}
    (ga : ∀ {Δ' : List Neg} {j' : JD}, Inv Δ' [] j' (canN M) → Inv Δ' [] j' M)
    (s : Stab Γ j (.down (canN M))) : Stab Γ j (.down M) :=
  routeStab (Δ₀ := Γ) (fun _ r => .rfoc (.rel (ga (relOf r)))) (Sub.refl Γ) s

/-- Discharge the canonical hypothesis `⟦M⟧` against the real one `M`, at a
stable sequent. -/
def peelDownStab {M : Neg} {Δ : List Neg} {j : JD} {P₀ : Pos}
    (bl : ∀ {Δ' : List Neg} {j' : JD} {P' : Pos},
      LFoc Δ' (canN M) j' P' → LFoc Δ' M j' P')
    (hM : M ∈ Δ) (s : Stab (canN M :: Δ) j P₀) : Stab Δ j P₀ :=
  simStab (H := canN M) (Δ₀ := Δ) (fl := fun hs lf => .lfoc (hs _ hM) (bl lf))
    (fun _ hX => (List.mem_cons.mp hX).imp id id) (Sub.refl Δ) s

/-- The same, at an inversion with an empty pending zone. -/
def peelDownInv {M : Neg} {Δ : List Neg} {j : JD} {C : Neg}
    (bl : ∀ {Δ' : List Neg} {j' : JD} {P' : Pos},
      LFoc Δ' (canN M) j' P' → LFoc Δ' M j' P')
    (hM : M ∈ Δ) (d : Inv (canN M :: Δ) [] j C) : Inv Δ [] j C :=
  simHyp (H := canN M) (Δ₀ := Δ) (fl := fun hs lf => .lfoc (hs _ hM) (bl lf))
    (Sub.refl Δ) d

/-! ## 2. The transfer block

One mutual recursion on the formula.  `sizeNeg`/`sizePos` are the measure; no
derivation height is needed, because every recursive call is at a strict
subformula. -/

mutual

/-- **(B) Hypothesis transfer, at a left focus.**  A left focus on the
canonical form `⟦N⟧` is a left focus on `N`.

* `N = ↑↓M`: `rel`/`downL`, then the real hypothesis `M` is focusable — cells
  1.1, 4.1, 10.2, 12.3;
* `N = ↑(a ∨ b)` and `N = ◯P`: the pending positive `⟦P⟧` is replayed branch
  by branch against the branches of `P` (`fS`) — cell 6.1;
* `N = Q ⊃ M`: the left premise is a focused positive, transferred by `sD`. -/
def bLL : ∀ (N : Neg) {Δ : List Neg} {j : JD} {P : Pos},
    LFoc Δ (canN N) j P → LFoc Δ N j P
  | .up (.atom _), _, _, _, lf => lf
  | .up .fls, _, _, _, lf => lf
  | .up (.or P₁ P₂), Δ, _, _, lf =>
      .rel (invBranches (.or P₁ P₂) (fun c hc =>
        .stable (fS (.or P₁ P₂) c hc (fun _ hX => List.mem_append_left _ hX)
          (fun b' hb' =>
            (unStable (extract [] (upLFocInv lf) b' hb')).wk (fun _ hZ => by
              rcases List.mem_append.mp hZ with hZ | hZ
              · exact List.mem_append_left _ hZ
              · exact List.mem_append_right _ (List.mem_append_right _ hZ))))))
  | .up (.down M), _, _, _, lf =>
      .rel (.downL (.stable (.lfoc (List.mem_cons_self ..)
        (bLL M (LFoc.wk (Sub.grow M) lf)))))
  | .imp Q M, _, _, _, .impL s lf => .impL (sD Q s) (bLL M lf)
  | .and M₁ _, _, _, _, .and1 lf => .and1 (bLL M₁ lf)
  | .and _ M₂, _, _, _, .and2 lf => .and2 (bLL M₂ lf)
  | .circ P₀, _, _, _, .circL e =>
      .circL (invBranches P₀ (fun c hc =>
        .stable (fS P₀ c hc (fun _ hX => List.mem_append_left _ hX)
          (fun b' hb' =>
            (unStable (extract [] e b' hb')).wk (fun _ hZ => by
              rcases List.mem_append.mp hZ with hZ | hZ
              · exact List.mem_append_left _ hZ
              · exact List.mem_append_right _ (List.mem_append_right _ hZ))))))
termination_by N => sizeNeg N
decreasing_by all_goals (simp only [sizeNeg, sizePos]; omega)

/-- **(A) Goal transfer.**  A derivation of the canonical goal `⟦N⟧` is a
derivation of `N`.

* `N = ↑↓M`: `stable`/`rfoc`/`rel`, then (A) at `M` — cells 3.1, 11.3;
* `N = ◯P`: `circR` into `lax`, then (D) at `P` — cells 11.1, 11.2, 12.1;
* `N = Q ⊃ M` at `j = .lax`: the source is EMPTY (S14). -/
def gA : ∀ (N : Neg) {Γ : List Neg} {j : JD},
    Inv Γ [] j (canN N) → Inv Γ [] j N
  | .up (.atom _), _, _, d => d
  | .up .fls, _, _, d => d
  | .up (.or P₁ P₂), _, _, d => .stable (sD (.or P₁ P₂) (unStable d))
  | .up (.down M), _, _, d => .stable (.rfoc (.rel (gA M d)))
  | .imp Q M, Γ, .tru, d =>
      .impR (invBranches Q (fun c hc =>
        fT Q c hc (fun _ hX => List.mem_append_left _ hX)
          (fun b' hb' =>
            (gA M (extract [] (impROf d) b' hb')).wk (fun _ hZ => by
              rcases List.mem_append.mp hZ with hZ | hZ
              · exact List.mem_append_left _ hZ
              · exact List.mem_append_right _ (List.mem_append_right _ hZ)))))
  | .imp _ _, _, .lax, d => (laxImpEmpty d).elim
  | .and M₁ M₂, _, .tru, d => .andR (gA M₁ (andROf1 d)) (gA M₂ (andROf2 d))
  | .and _ _, _, .lax, d => (laxAndEmpty d).elim
  | .circ P₀, _, _, d => .circR (.stable (sD P₀ (unStable (circInv d))))
termination_by N => sizeNeg N
decreasing_by all_goals (simp only [sizeNeg, sizePos]; omega)

/-- **(D) Focused-positive transfer.**  `↓↑P` is closed by `delayIntro`
(cells 1.2, 5.1, 5.2, 9.1); `↓M` relays through (A) at `M`. -/
def sD : ∀ (P : Pos) {Γ : List Neg} {j : JD}, Stab Γ j (canP P) → Stab Γ j P
  | .atom _, _, _, s => s
  | .fls, _, _, s => s
  | .or P₁ P₂, Γ, _, s =>
      routeStab (Δ₀ := Γ)
        (fun _ r =>
          orFocSplit (fun r₁ => stabOr1 (sD P₁ (.rfoc r₁)))
            (fun r₂ => stabOr2 (sD P₂ (.rfoc r₂))) r)
        (Sub.refl Γ) s
  | .down (.up P'), _, _, s => delayIntro (sD P' s)
  | .down (.imp Q M), _, _, s => relayDown (fun d => gA (.imp Q M) d) s
  | .down (.and M₁ M₂), _, _, s => relayDown (fun d => gA (.and M₁ M₂) d) s
  | .down (.circ Q), _, _, s => relayDown (fun d => gA (.circ Q) d) s
termination_by P => sizePos P
decreasing_by all_goals (simp only [sizeNeg, sizePos]; omega)

/-- **(C) Branch covering, at a negative goal and `j = .tru`.**  A context
already holding one branch `b` of `R` can case-split on the branches of `⟦R⟧`:
the single delayed branch `invertPos (↓↑P) = [[↑P]]` COVERS every canonical
branch, by `stableFire`/`upMerge` — cell 6.1. -/
def fT : ∀ (R : Pos) {Δ : List Neg} {G : Neg} (b : List Neg),
    b ∈ invertPos R → (∀ X ∈ b, X ∈ Δ) →
    (∀ b' ∈ invertPos (canP R), Inv (b' ++ Δ) [] .tru G) → Inv Δ [] .tru G
  | .atom a, _, _, b, hb, hsub, h =>
      have hb' : b = [Neg.up (Pos.atom a)] := by
        simp only [invertPos_atom, List.mem_singleton] at hb; exact hb
      (h [Neg.up (Pos.atom a)]
          (by rw [invertPos_canP_atom]; exact List.mem_cons_self ..)).wk
        (fun Z hZ => by
          rcases List.mem_append.mp hZ with hZ | hZ
          · exact hsub Z (hb' ▸ hZ)
          · exact hZ)
  | .fls, _, _, _, hb, _, _ => by rw [invertPos_fls] at hb; exact absurd hb (by simp)
  | .or R₁ R₂, _, _, b, hb, hsub, h =>
      if h1 : b ∈ invertPos R₁ then
        fT R₁ b h1 hsub (fun b' hb' => h b' (by
          rw [invertPos_canP_or]; exact List.mem_append_left _ hb'))
      else
        fT R₂ b
          (by rw [invertPos_or] at hb; exact (List.mem_append.mp hb).resolve_left h1)
          hsub
          (fun b' hb' => h b' (by
            rw [invertPos_canP_or]; exact List.mem_append_right _ hb'))
  | .down (.up P'), Δ, G, b, hb, hsub, h =>
      have hb' : b = [Neg.up P'] := by
        simp only [invertPos_down, List.mem_singleton] at hb; exact hb
      have hmem : Neg.up P' ∈ Δ := hsub _ (hb' ▸ List.mem_cons_self ..)
      upMerge G hmem (fun c hc =>
        fT P' c hc (fun _ hX => List.mem_append_left _ hX)
          (fun b' hb'' => (h b' hb'').wk (fun _ hZ => by
            rcases List.mem_append.mp hZ with hZ | hZ
            · exact List.mem_append_left _ hZ
            · exact List.mem_append_right _ (List.mem_append_right _ hZ))))
  | .down (.imp Q M), _, _, b, hb, hsub, h =>
      have hb' : b = [Neg.imp Q M] := by
        simp only [invertPos_down, List.mem_singleton] at hb; exact hb
      peelDownInv (M := .imp Q M) (fun lf => bLL (.imp Q M) lf)
        (hsub _ (hb' ▸ List.mem_cons_self ..))
        (h _ (by rw [invertPos_canP_down_imp]; exact List.mem_cons_self ..))
  | .down (.and M₁ M₂), _, _, b, hb, hsub, h =>
      have hb' : b = [Neg.and M₁ M₂] := by
        simp only [invertPos_down, List.mem_singleton] at hb; exact hb
      peelDownInv (M := .and M₁ M₂) (fun lf => bLL (.and M₁ M₂) lf)
        (hsub _ (hb' ▸ List.mem_cons_self ..))
        (h _ (by rw [invertPos_canP_down_and]; exact List.mem_cons_self ..))
  | .down (.circ Q), _, _, b, hb, hsub, h =>
      have hb' : b = [Neg.circ Q] := by
        simp only [invertPos_down, List.mem_singleton] at hb; exact hb
      peelDownInv (M := .circ Q) (fun lf => bLL (.circ Q) lf)
        (hsub _ (hb' ▸ List.mem_cons_self ..))
        (h _ (by rw [invertPos_canP_down_circ]; exact List.mem_cons_self ..))
termination_by R => sizePos R
decreasing_by all_goals (simp only [sizeNeg, sizePos]; omega)

/-- **(C) Branch covering, at a stable sequent, at either flag.**  The same
recursion as `fT`, with `stableFire` in place of `upMerge` — which is why the
`lax` flag costs nothing here. -/
def fS : ∀ (R : Pos) {Δ : List Neg} {j : JD} {P₀ : Pos} (b : List Neg),
    b ∈ invertPos R → (∀ X ∈ b, X ∈ Δ) →
    (∀ b' ∈ invertPos (canP R), Stab (b' ++ Δ) j P₀) → Stab Δ j P₀
  | .atom a, _, _, _, b, hb, hsub, h =>
      have hb' : b = [Neg.up (Pos.atom a)] := by
        simp only [invertPos_atom, List.mem_singleton] at hb; exact hb
      (h [Neg.up (Pos.atom a)]
          (by rw [invertPos_canP_atom]; exact List.mem_cons_self ..)).wk
        (fun Z hZ => by
          rcases List.mem_append.mp hZ with hZ | hZ
          · exact hsub Z (hb' ▸ hZ)
          · exact hZ)
  | .fls, _, _, _, _, hb, _, _ => by
      rw [invertPos_fls] at hb; exact absurd hb (by simp)
  | .or R₁ R₂, _, _, _, b, hb, hsub, h =>
      if h1 : b ∈ invertPos R₁ then
        fS R₁ b h1 hsub (fun b' hb' => h b' (by
          rw [invertPos_canP_or]; exact List.mem_append_left _ hb'))
      else
        fS R₂ b
          (by rw [invertPos_or] at hb; exact (List.mem_append.mp hb).resolve_left h1)
          hsub
          (fun b' hb' => h b' (by
            rw [invertPos_canP_or]; exact List.mem_append_right _ hb'))
  | .down (.up P'), Δ, _, _, b, hb, hsub, h =>
      have hb' : b = [Neg.up P'] := by
        simp only [invertPos_down, List.mem_singleton] at hb; exact hb
      have hmem : Neg.up P' ∈ Δ := hsub _ (hb' ▸ List.mem_cons_self ..)
      stableFire hmem (fun c hc =>
        fS P' c hc (fun _ hX => List.mem_append_left _ hX)
          (fun b' hb'' => (h b' hb'').wk (fun _ hZ => by
            rcases List.mem_append.mp hZ with hZ | hZ
            · exact List.mem_append_left _ hZ
            · exact List.mem_append_right _ (List.mem_append_right _ hZ))))
  | .down (.imp Q M), _, _, _, b, hb, hsub, h =>
      have hb' : b = [Neg.imp Q M] := by
        simp only [invertPos_down, List.mem_singleton] at hb; exact hb
      peelDownStab (M := .imp Q M) (fun lf => bLL (.imp Q M) lf)
        (hsub _ (hb' ▸ List.mem_cons_self ..))
        (h _ (by rw [invertPos_canP_down_imp]; exact List.mem_cons_self ..))
  | .down (.and M₁ M₂), _, _, _, b, hb, hsub, h =>
      have hb' : b = [Neg.and M₁ M₂] := by
        simp only [invertPos_down, List.mem_singleton] at hb; exact hb
      peelDownStab (M := .and M₁ M₂) (fun lf => bLL (.and M₁ M₂) lf)
        (hsub _ (hb' ▸ List.mem_cons_self ..))
        (h _ (by rw [invertPos_canP_down_and]; exact List.mem_cons_self ..))
  | .down (.circ Q), _, _, _, b, hb, hsub, h =>
      have hb' : b = [Neg.circ Q] := by
        simp only [invertPos_down, List.mem_singleton] at hb; exact hb
      peelDownStab (M := .circ Q) (fun lf => bLL (.circ Q) lf)
        (hsub _ (hb' ▸ List.mem_cons_self ..))
        (h _ (by rw [invertPos_canP_down_circ]; exact List.mem_cons_self ..))
termination_by R => sizePos R
decreasing_by all_goals (simp only [sizeNeg, sizePos]; omega)

end


/-! ## 2b. The converse direction is FALSE

`docs/cutinv-cases.md` §5's lemma list also asks for the primed directions
`Inv Γ Ω j N → Inv Γ Ω j ⟦N⟧` and its relatives.  The goal-side one is
refuted by the same judgment-form fact that refuted `PolInv` (S14), on cell
14.3's sequent: `⇒ˡ ↑↓(↑⊥ ⊃ ↑⊥)` is derivable, its canonical form
`⟦↑↓(↑⊥ ⊃ ↑⊥)⟧ = ↑⊥ ⊃ ↑⊥` is an implication, and `Inv Γ [] .lax (Q ⊃ N)` is
empty.  So the block above is stated one-way ON PURPOSE, and only the
un-primed directions are used. -/

/-- Cell 14.3: `⇒ˡ ↑↓(↑⊥ ⊃ ↑⊥)`. -/
def laxContrast : Inv [] [] .lax (.up (.down nTop)) :=
  .stable (.laxOf (.rfoc (.rel (.impR .flsL))))

/-- **The goal-side converse (A′) is REFUTED**, even in its `Nonempty` form. -/
theorem notCanGoalConverse :
    ¬ (∀ (Γ : List Neg) (Ω : List Pos) (j : JD) (N : Neg),
        Inv Γ Ω j N → Nonempty (Inv Γ Ω j (canN N))) := by
  intro h
  obtain ⟨d⟩ := h [] [] .lax (.up (.down nTop)) laxContrast
  exact laxImpEmpty d

/-! ## 3. From one hypothesis to the whole context -/

/-- **(B) Hypothesis transfer.**  `simHyp` strips the canonical hypothesis
`⟦N⟧`, every left focus on it being simulated by the real hypothesis `N`. -/
def bHyp (N : Neg) {Γ Δ : List Neg} {j : JD} {C : Neg}
    (hΓ : Sub Γ Δ) (hN : N ∈ Δ) (d : Inv (canN N :: Γ) [] j C) : Inv Δ [] j C :=
  simHyp (H := canN N) (Δ₀ := Δ) (fl := fun hs lf => .lfoc (hs _ hN) (bLL N lf))
    hΓ d

/-- The same, along a canonical prefix, one hypothesis at a time. -/
def bCtxAux : ∀ (Γ : List Neg) {Θ : List Neg} {j : JD} {C : Neg},
    Inv (canCtx Γ ++ Θ) [] j C → Inv (Γ ++ Θ) [] j C
  | [], _, _, _, d => d
  | N :: Γ', Θ, _, _, d =>
      have d₁ : Inv (canCtx Γ' ++ (N :: Θ)) [] _ _ :=
        (bHyp N (Γ := canCtx Γ' ++ Θ) (Δ := N :: (canCtx Γ' ++ Θ))
          (Sub.grow N) (List.mem_cons_self ..) d).wk (fun Z hZ => by
            rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_append_right _ (List.mem_cons_self ..)
            · rcases List.mem_append.mp hZ with hZ | hZ
              · exact List.mem_append_left _ hZ
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ hZ))
      (bCtxAux Γ' d₁).wk (fun Z hZ => by
        rcases List.mem_append.mp hZ with hZ | hZ
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hZ)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ hZ))

/-- **(B), whole context.**  A derivation over the canonical context is a
derivation over the real one. -/
def bCtx (Γ : List Neg) {j : JD} {C : Neg} (d : Inv (canCtx Γ) [] j C) :
    Inv Γ [] j C :=
  (bCtxAux Γ (Θ := []) (d.wk (fun _ hZ => List.mem_append_left _ hZ))).wk
    (fun _ hZ => (List.mem_append.mp hZ).resolve_right (by simp))

/-! ## 4. `PolInvT`, and composition at the truth flag -/

/-- Polarising an erased context gives the canonical context. -/
theorem map_negOfO_eraseCtx (Γ : List Neg) :
    (eraseCtx Γ).map negOfO = canCtx Γ := by
  simp [eraseCtx, canCtx, List.map_map, Function.comp_def]

/-- **`PolInvT`** — the converse of the erasure bridge at the truth flag, at
EVERY polarised sequent, not merely those in the image of `negOfO`.  This is
what `focalizeSCO` could not supply on its own: `FocalizationPLL` lands on the
canonical polarisation, and the transfer block moves it to the sequent route
(B) actually writes down.

    ∀ Γ ψ,  Nonempty (LaxND ⌊Γ⌋ ⌊ψ⌋) → Nonempty (Inv Γ [] .tru ψ)
-/
theorem polInvT (Γ : List Neg) (ψ : Neg)
    (h : Nonempty (LaxND (eraseCtx Γ) (eraseNeg ψ))) :
    Nonempty (Inv Γ [] .tru ψ) := by
  obtain ⟨d⟩ := FocalizationPLL (eraseCtx Γ) (eraseNeg ψ) h
  rw [map_negOfO_eraseCtx] at d
  exact ⟨bCtx Γ (gA ψ d)⟩

/-- Contexts erase over `++`. -/
theorem eraseCtx_append (Γ Δ : List Neg) :
    eraseCtx (Γ ++ Δ) = eraseCtx Γ ++ eraseCtx Δ := List.map_append ..

/-- **The composition principle at the truth flag.**  Erase both premises
(`Inv.sound`), compose in natural deduction (`subst1` — `⊃`-intro then
`⊃`-elim, so no cut is used), and re-focalise with `polInvT`. -/
theorem cutInvT (Γ Δ : List Neg) (N ψ : Neg)
    (d₁ : Inv Γ [] .tru N) (d₂ : Inv (N :: Δ) [] .tru ψ) :
    Nonempty (Inv (Γ ++ Δ) [] .tru ψ) := by
  have e₁ : LaxND (eraseCtx (Γ ++ Δ)) (eraseNeg N) :=
    (Inv.sound d₁).rename (fun _ hχ => by
      rw [eraseCtx_append]; exact List.mem_append_left _ hχ)
  have e₂ : LaxND (eraseNeg N :: eraseCtx (Γ ++ Δ)) (eraseNeg ψ) :=
    (Inv.sound d₂).rename (fun _ hχ => by
      rcases List.mem_cons.mp hχ with rfl | hχ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (by
          rw [eraseCtx_append]; exact List.mem_append_right _ hχ))
  exact polInvT (Γ ++ Δ) ψ ⟨subst1 e₂ e₁⟩

/-! ## 4b. The modal steps: the lax flag, and `CutInv`

Three facts fix the lax half.  `Inv Γ [] .lax N` is reached by the calculus
only with `N` a shift or a box (`circR`'s premise), so at `lax` the goal shapes
`⊃` and `∧` are empty (`laxImpEmpty`/`laxAndEmpty`); the shift goal is
`polInvL`; and the box goal reduces to the shift goal by `circR`, its erasure
`◯◯φ` collapsing to `◯φ` by `laxElim`. -/

/-- **`PolInvL`** — the converse of the erasure bridge at the lax flag, at the
SHIFTED goals `circR` produces:

    ∀ Γ P,  Nonempty (LaxND ⌊Γ⌋ (◯⌊P⌋)) → Nonempty (Inv Γ [] .lax (↑P))

The unrestricted lax statement `PolInv` is REFUTED (`docs/cutinv-cases.md`
S14, cells 14.1/14.2); this is the restriction `CutInv` actually needs.  The
route is `FocalizationPLL` at the box `◯⌊P⌋`, whose polarisation is
`◯⟦P⟧`, then `circInv`, then the transfer block. -/
theorem polInvL (Γ : List Neg) (P : Pos)
    (h : Nonempty (LaxND (eraseCtx Γ) (.somehow (erasePos P)))) :
    Nonempty (Inv Γ [] .lax (.up P)) := by
  obtain ⟨d⟩ := FocalizationPLL (eraseCtx Γ) (.somehow (erasePos P)) h
  rw [map_negOfO_eraseCtx] at d
  exact ⟨bCtx Γ (.stable (sD P (unStable (circInv d))))⟩

/-- **The composition principle, `Nonempty` form, at every flag.**

    ∀ Γ Δ j N ψ,  Inv Γ [] .tru N → Inv (N :: Δ) [] j ψ →
                  Nonempty (Inv (Γ ++ Δ) [] j ψ)

At `tru` this is `cutInvT`.  At `lax`: the `⊃` and `∧` goals make the SECOND
PREMISE empty, so those cases are vacuous and need no converse at all; the
shift goal is `polInvL`; the box goal is `polInvL` under `circR`, after
`laxElim` collapses `◯◯⌊P⌋` to `◯⌊P⌋`. -/
theorem cutInvNE (Γ Δ : List Neg) (j : JD) (N ψ : Neg)
    (d₁ : Inv Γ [] .tru N) (d₂ : Inv (N :: Δ) [] j ψ) :
    Nonempty (Inv (Γ ++ Δ) [] j ψ) := by
  cases j with
  | tru => exact cutInvT Γ Δ N ψ d₁ d₂
  | lax =>
      have e₁ : LaxND (eraseCtx (Γ ++ Δ)) (eraseNeg N) :=
        (Inv.sound d₁).rename (fun _ hχ => by
          rw [eraseCtx_append]; exact List.mem_append_left _ hχ)
      have e₂ : LaxND (eraseNeg N :: eraseCtx (Γ ++ Δ))
          (.somehow (eraseNeg ψ)) :=
        (Inv.sound d₂).rename (fun _ hχ => by
          rcases List.mem_cons.mp hχ with rfl | hχ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (by
              rw [eraseCtx_append]; exact List.mem_append_right _ hχ))
      have e : LaxND (eraseCtx (Γ ++ Δ)) (.somehow (eraseNeg ψ)) := subst1 e₂ e₁
      cases ψ with
      | up P => exact polInvL (Γ ++ Δ) P ⟨e⟩
      | circ P =>
          obtain ⟨c⟩ := polInvL (Γ ++ Δ) P
            ⟨LaxND.laxElim e (.iden (List.mem_cons_self ..))⟩
          exact ⟨.circR c⟩
      | imp _ _ => exact (laxImpEmpty d₂).elim
      | and _ _ => exact (laxAndEmpty d₂).elim

/-- **`CutInv`** — definitionally the obligation `LJFO.CutInv` of
`wip/ui_routeB_n3.lean`:

    ∀ Γ Δ j N ψ,  Inv Γ [] .tru N → Inv (N :: Δ) [] j ψ → Inv (Γ ++ Δ) [] j ψ

`cutInvNE` carries the content; this declaration only turns
`Nonempty (Inv …)` into data, which is where — and the ONLY place where —
`Classical.choice` is spent.  It cannot be avoided along this route:
`FocalizationPLL` factors through `PLLND.ND_to_SC` into `PLLND.SCh`, which is
a `Prop`, so no re-focalisation in this development returns a derivation. -/
noncomputable def cutInv : ∀ (Γ Δ : List Neg) (j : JD) (N ψ : Neg),
    Inv Γ [] .tru N → Inv (N :: Δ) [] j ψ → Inv (Γ ++ Δ) [] j ψ :=
  fun Γ Δ j N ψ d₁ d₂ => (cutInvNE Γ Δ j N ψ d₁ d₂).some

/-! ## 5. The ◯-free fragment, as a result in its own right

Liang–Miller's "delays are inert", for the ◯-free part of LJF◯ at judgment
`tru`.  The transfer block of §2 does not need the restriction — `circ` is
handled in `bLL`/`gA`/`sD` exactly as `up`/`or` are, and the `lax` flag costs
only `laxImpEmpty`/`laxAndEmpty` — so the hypotheses below are INERT.  The
statements carry them anyway, because the ◯-free fragment is the part that is
Liang–Miller's theorem and is reported as such. -/

mutual
/-- `P` contains no `circ`. -/
def CircFreeP : Pos → Prop
  | .atom _ => True
  | .fls => True
  | .or P Q => CircFreeP P ∧ CircFreeP Q
  | .down N => CircFreeN N
/-- `N` contains no `circ`. -/
def CircFreeN : Neg → Prop
  | .up P => CircFreeP P
  | .imp Q N => CircFreeP Q ∧ CircFreeN N
  | .and M N => CircFreeN M ∧ CircFreeN N
  | .circ _ => False
end

/-- Every hypothesis is ◯-free. -/
def CircFreeCtx (Γ : List Neg) : Prop := ∀ N ∈ Γ, CircFreeN N

/-- **Polarisation invariance for the ◯-free fragment**, judgment `tru`: a PLL
derivation of the erasure of a ◯-free polarised sequent is matched by a focused
LJF◯ derivation of that very sequent, delays and all. -/
theorem polInvT_circFree (Γ : List Neg) (ψ : Neg)
    (_hΓ : CircFreeCtx Γ) (_hψ : CircFreeN ψ)
    (h : Nonempty (LaxND (eraseCtx Γ) (eraseNeg ψ))) :
    Nonempty (Inv Γ [] .tru ψ) := polInvT Γ ψ h

/-- **Composition for the ◯-free fragment**, judgment `tru`, `Nonempty`
form. -/
theorem cutInvNE_circFree (Γ Δ : List Neg) (N ψ : Neg)
    (_hΓ : CircFreeCtx Γ) (_hΔ : CircFreeCtx Δ) (_hN : CircFreeN N)
    (_hψ : CircFreeN ψ)
    (d₁ : Inv Γ [] .tru N) (d₂ : Inv (N :: Δ) [] .tru ψ) :
    Nonempty (Inv (Γ ++ Δ) [] .tru ψ) := cutInvT Γ Δ N ψ d₁ d₂

/-- **Composition for the ◯-free fragment**, as data.  `Classical.choice` is
spent here and only here: `cutInvNE_circFree` carries the content, and
focalization factors through `PLLND.SCh`, a `Prop`. -/
noncomputable def cutInv_circFree (Γ Δ : List Neg) (N ψ : Neg)
    (hΓ : CircFreeCtx Γ) (hΔ : CircFreeCtx Δ) (hN : CircFreeN N)
    (hψ : CircFreeN ψ)
    (d₁ : Inv Γ [] .tru N) (d₂ : Inv (N :: Δ) [] .tru ψ) :
    Inv (Γ ++ Δ) [] .tru ψ :=
  (cutInvNE_circFree Γ Δ N ψ hΓ hΔ hN hψ d₁ d₂).some

end LJFO

/-! ## 6. Pins

Measured with `#axioms_within_pin`, not retyped. -/

#axioms_within LJFO.laxImpEmpty []
#axioms_within LJFO.laxAndEmpty []
#axioms_within LJFO.upLFocInv []
#axioms_within LJFO.orFocSplit []
#axioms_within LJFO.delayIntro [propext, Quot.sound]
#axioms_within LJFO.relayDown [propext, Quot.sound]
#axioms_within LJFO.peelDownStab [propext, Quot.sound]
#axioms_within LJFO.peelDownInv [propext, Quot.sound]

-- The transfer block.
#axioms_within LJFO.bLL [propext, Quot.sound]
#axioms_within LJFO.gA [propext, Quot.sound]
#axioms_within LJFO.sD [propext, Quot.sound]
#axioms_within LJFO.fT [propext, Quot.sound]
#axioms_within LJFO.fS [propext, Quot.sound]

-- The refuted converse: both halves axiom-free.
#axioms_within LJFO.laxContrast []
#axioms_within LJFO.notCanGoalConverse []

#axioms_within LJFO.bHyp [propext, Quot.sound]
#axioms_within LJFO.bCtxAux [propext, Quot.sound]
#axioms_within LJFO.bCtx [propext, Quot.sound]
#axioms_within LJFO.map_negOfO_eraseCtx [propext]
#axioms_within LJFO.eraseCtx_append [propext]
#axioms_within LJFO.polInvT [propext, Quot.sound]
#axioms_within LJFO.cutInvT [propext, Quot.sound]

-- The modal steps.  `Classical.choice` enters at `cutInv` and nowhere else.
#axioms_within LJFO.polInvL [propext, Quot.sound]
#axioms_within LJFO.cutInvNE [propext, Quot.sound]
#axioms_within LJFO.cutInv [propext, Classical.choice, Quot.sound]

-- The ◯-free fragment.
#axioms_within LJFO.CircFreeP []
#axioms_within LJFO.CircFreeN []
#axioms_within LJFO.CircFreeCtx []
#axioms_within LJFO.polInvT_circFree [propext, Quot.sound]
#axioms_within LJFO.cutInvNE_circFree [propext, Quot.sound]
#axioms_within LJFO.cutInv_circFree [propext, Classical.choice, Quot.sound]
