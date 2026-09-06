/-
Route (B), node **N4**, WP8, stage 2: what the loop-checked recursion buys,
and the two obligations it leaves.

Stage 1 (`wip/ui_routeB_n4q.lean`, `wip/ui_routeB_n4q_cells.lean`) built
`interpQ` and certified LITERAL constancy on twelve designed cells — the six
◯-free cells on which `interpP`'s literal chain is REFUTED, five modal shapes,
and the running cell S1.  This module states and proves what turns that into
N4, and types exactly what is missing.

**(a) Literal stabilisation from a measure.**  `interpG` is written in step
form, so "the recursion bottoms out" is one statement about `stepQ`:

    QFounded rst p μ  :=  ∀ prev₁ prev₂ s,
        (∀ t, μ t < μ s → prev₁ t = prev₂ t) →
        stepQ rst p prev₁ s = stepQ rst p prev₂ s

— the step at `s` consults the level below only at states of strictly smaller
`μ`.  From it, literal stabilisation follows by strong induction on `μ`
(`interpG_founded_eq`), with the explicit threshold `μ s + 1`.  That
implication is PROVED here, axiom-free.  Exhibiting a `μ` is the OPEN part.
Its shape is forced: `μ = (K - |seen|, ν)` lexicographic, with
`ν = 2·sum3 todo + sum3 done + 3^(wNeg goal)` — the measure `eMinPP`/`aMinPP`
already run on — and `K` a bound on the number of distinct guard antecedents
reachable at the cell.  `seen` is extended ONLY at a guard call and only with
an antecedent not already in it, so it is monotone along every edge and
strictly increasing on exactly the edges where `ν` rises; what is left to
build is the subformula-closure invariant that bounds `K`, and the per-clause
`ν` descent.  `docs/n4-loopcheck.md` §4.

**(b) The relation to `interpP`.**  `PQEquiv` — the two interpolants are
interderivable at every fuel and every cell — is the redundancy lemma of
`docs/n4-circfree-cases.md` §3.3, stated as data.  From it and (a), N4
follows for `interpP` by four applications of `cutInv`
(`n4_of_interpQ`).  `PQEquiv` is OPEN; the two easy halves and the two hard
halves are separated in §3 below, and the hard halves are exactly the
redundancy claim.

Nothing here is claimed as PROVED that is not a named declaration with a
measured pin.  The two obligations are `Type`-valued parameters, never
`sorry` (rule 1).
-/
import wip.ui_routeB_n4q_cells
import wip.ui_routeB_n4
import Meta.Audit

set_option autoImplicit false

namespace LJFO

/-! # Part 1 · Literal stabilisation from a measure -/

/-- A state of the recursion: `(todo, done, goal, seen)`. -/
abbrev QState : Type := List Neg × List Neg × Option Neg × List Pos

/-- An approximant read at a state. -/
def atSt (F : List Neg → List Neg → Option Neg → List Pos → Neg) (s : QState) : Neg :=
  F s.1 s.2.1 s.2.2.1 s.2.2.2

/-- **The measure obligation.**  `μ` FOUNDS the loop-checked recursion: the
step function at a state consults the level below only at states of strictly
smaller `μ`.  For `interpP` no such `μ` exists — the guard row at the goal
`↑Q` calls the same state one fuel down (`not_fuelStep1A`) — and the loop
check is exactly the change that can make one exist.  See the module
docstring for the shape `μ` must have. -/
def QFounded (rst : List Pos → List Pos) (p : String) (μ : QState → Nat) : Prop :=
  ∀ (prev₁ prev₂ : ApproxQ) (s : QState),
    (∀ t : QState, μ t < μ s → atSt prev₁ t = atSt prev₂ t) →
    atSt (stepQ rst p prev₁) s = atSt (stepQ rst p prev₂) s

/-- **Two levels above the measure agree.**  Strong induction on `μ s`: the
step at `s` reads the two levels only below `μ s`, where the induction
hypothesis applies. -/
theorem interpG_founded_eq {rst : List Pos → List Pos} {p : String}
    {μ : QState → Nat} (h : QFounded rst p μ) :
    ∀ (n : Nat) (s : QState), μ s ≤ n → ∀ f g : Nat, n ≤ f → n ≤ g →
      atSt (interpG rst p (f + 1)) s = atSt (interpG rst p (g + 1)) s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs f g hf hg
    show atSt (stepQ rst p (interpG rst p f)) s
       = atSt (stepQ rst p (interpG rst p g)) s
    refine h _ _ s ?_
    intro t ht
    -- `μ t < μ s ≤ n`, so `n ≥ 1` and `f`, `g` are successors
    have hn : 1 ≤ n := by omega
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    exact ih (n - 1) (by omega) t (by omega) f' g' (by omega) (by omega)

/-- The chain at a state is literally constant from `μ s + 1` on. -/
theorem interpG_stab_of_founded {rst : List Pos → List Pos} {p : String}
    {μ : QState → Nat} (h : QFounded rst p μ) (s : QState) :
    ∀ f, μ s + 1 ≤ f →
      atSt (interpG rst p f) s = atSt (interpG rst p (μ s + 1)) s := by
  intro f hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  exact interpG_founded_eq h (μ s) s (Nat.le_refl _) f' (μ s) (by omega) (Nat.le_refl _)

/-- **A bound for the loop-checked recursion**, as data: a measure and the
proof that it founds `interpQ`.  OPEN — no term of this type is built here. -/
def QBound (p : String) : Type :=
  Σ' μ : QState → Nat, QFounded id p μ

/-- Literal stabilisation of the loop-checked `∃p` chain at a station. -/
def QStabLitE (p : String) (done : List Neg) : Type :=
  Σ' f₀ : Nat, ∀ f, f₀ ≤ f →
    interpQ p f [] done none [] = interpQ p f₀ [] done none []

/-- Literal stabilisation of the loop-checked `∀p` chain at a station. -/
def QStabLitA (p : String) (done : List Neg) (G : Neg) : Type :=
  Σ' f₀ : Nat, ∀ f, f₀ ≤ f →
    interpQ p f [] done (some G) [] = interpQ p f₀ [] done (some G) []

/-- **(a), plumbed**: a bound gives literal stabilisation of the `∃p` chain at
EVERY station — no saturation hypothesis, since the bound is a statement about
the recursion, not about a cell. -/
def qStabLitE_of_bound {p : String} (bd : QBound p) (done : List Neg) :
    QStabLitE p done :=
  ⟨bd.1 ([], done, none, []) + 1, fun f hf =>
    interpG_stab_of_founded bd.2 ([], done, none, []) f hf⟩

/-- The same for the `∀p` chain. -/
def qStabLitA_of_bound {p : String} (bd : QBound p) (done : List Neg) (G : Neg) :
    QStabLitA p done G :=
  ⟨bd.1 ([], done, some G, []) + 1, fun f hf =>
    interpG_stab_of_founded bd.2 ([], done, some G, []) f hf⟩

/-! # Part 2 · The relation to `interpP` -/

/-- Interderivability of two interpolants, as data. -/
def IDeriv (M N : Neg) : Type := Inv [M] [] .tru N × Inv [N] [] .tru M

/-- **The redundancy obligation.**  The loop check removes no consequence: at
every fuel and every cell the two interpolants are interderivable.  The EASY
halves are `interpQ ⊢ interpP` on the `∀p` side (the dropped disjunct is `⊥`)
and `interpP ⊢ interpQ` on the `∃p` side (the dropped conjunct is `⊤`); the
HARD halves are the redundancy claim of `docs/n4-circfree-cases.md` §3.3 — the
self-attack disjunct is implied by the retained ones.  The polarity of the
occurrences (`docs/n4-loopcheck.md` §3) makes the four halves ONE simultaneous
induction, which is why the obligation is stated as a single interderivability
and not as two implications.  OPEN. -/
def PQEquiv (p : String) : Type :=
  ∀ (f : Nat) (done : List Neg) (g : Option Neg),
    IDeriv (interpP p f [] done g) (interpQ p f [] done g [])

/-- Composition of two one-hypothesis derivations, through `cutInv`. -/
noncomputable def chain1 {M N R : Neg}
    (d₁ : Inv [M] [] .tru N) (d₂ : Inv [N] [] .tru R) : Inv [M] [] .tru R := by
  have := cutInv [M] [] .tru N R d₁ d₂
  simpa using this

/-- Interderivability is transitive. -/
noncomputable def IDeriv.trans {M N R : Neg} (a : IDeriv M N) (b : IDeriv N R) :
    IDeriv M R :=
  ⟨chain1 a.1 b.1, chain1 b.2 a.2⟩

/-- Interderivability is symmetric. -/
def IDeriv.symm {M N : Neg} (a : IDeriv M N) : IDeriv N M := ⟨a.2, a.1⟩

/-- **The two `interpP` levels are interderivable**, given the equivalence and
the loop-checked chain's literal constancy. -/
noncomputable def pLevels_iderivE {p : String} (eq : PQEquiv p)
    {done : List Neg} (st : QStabLitE p done) :
    ∀ f, st.1 ≤ f →
      IDeriv (interpP p st.1 [] done none) (interpP p f [] done none) :=
  fun f hf =>
    (eq st.1 done none).trans (by
      rw [← st.2 f hf]
      exact (eq f done none).symm)

/-- The same at a goal. -/
noncomputable def pLevels_iderivA {p : String} (eq : PQEquiv p)
    {done : List Neg} {G : Neg} (st : QStabLitA p done G) :
    ∀ f, st.1 ≤ f →
      IDeriv (interpP p st.1 [] done (some G)) (interpP p f [] done (some G)) :=
  fun f hf =>
    (eq st.1 done (some G)).trans (by
      rw [← st.2 f hf]
      exact (eq f done (some G)).symm)

/-- **N1 for the `∃p` chain, interderivably**, from the two obligations. -/
noncomputable def eStabilises_of_interpQ {p : String} (eq : PQEquiv p)
    (bd : QBound p) (done : List Neg) : EStabilises p done :=
  let st := qStabLitE_of_bound bd done
  ⟨st.1, fun f hf =>
    ⟨(pLevels_iderivE eq st f hf).1, (pLevels_iderivE eq st f hf).2⟩⟩

/-- **N1 for the `∀p` chain, interderivably** (E-relativised, as
`AStabilises`): the `∃p` hypothesis is carried and discharged by weakening. -/
noncomputable def aStabilises_of_interpQ {p : String} (eq : PQEquiv p)
    (bd : QBound p) (done : List Neg) (G : Neg) : AStabilises p done G :=
  let st := qStabLitA_of_bound bd done G
  ⟨st.1, fun f hf =>
    ⟨(pLevels_iderivA eq st f hf).1.wk
       (fun _ h => by
          rcases List.mem_singleton.mp h with rfl
          exact List.mem_cons_of_mem _ (List.mem_cons_self ..)),
     (pLevels_iderivA eq st f hf).2.wk
       (fun _ h => by
          rcases List.mem_singleton.mp h with rfl
          exact List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩⟩

/-- **N4 for PLL, from the loop-checked recursion.**  Both chains of `interpP`
stabilise up to interderivability at EVERY cell, given the measure and the
redundancy obligation.  No saturation, no parking, no ◯-freeness: the two
obligations are statements about the recursion itself. -/
noncomputable def n4_of_interpQ {p : String} (eq : PQEquiv p) (bd : QBound p)
    (done : List Neg) (G : Neg) : EStabilises p done × AStabilises p done G :=
  ⟨eStabilises_of_interpQ eq bd done, aStabilises_of_interpQ eq bd done G⟩

/-- **The uniform-interpolant pair at a saturated parked station**, from the
loop-checked recursion, over the cofinality statements as variables — the form
every work package since WP2 uses. -/
noncomputable def hasUI_of_interpQ {p : String} (s2 : SatE2P p) (a2 : SatA2P p)
    (eq : PQEquiv p) (bd : QBound p) {done : List Neg} {G : Neg}
    (hsat : Saturated done) (hpk : ParkedCtxP done) : HasUI p done G :=
  hasUI_of_stabilises s2 a2 hsat hpk
    (eStabilises_of_interpQ eq bd done) (aStabilises_of_interpQ eq bd done G)

/-! # Part 3 · The ◯-free instance, and the cross-check

On ◯-free stations N4 is already PROVED unconditionally by transport from
Pitts (`n4_circFree_uncond`, `wip/ui_routeB_n4.lean`).  The loop-checked route
gives the SAME conclusion from the two obligations, so on ◯-free cells it adds
nothing — that is the point of the cross-check below: it is the modal case the
route is for, and the ◯-free instance is where the obligations can be tested
against a theorem that is already known. -/

/-- The ◯-free instance of the loop-checked route. -/
noncomputable def n4_circFree_intrinsic {p : String} (eq : PQEquiv p)
    (bd : QBound p) {done : List Neg} {G : Neg}
    (_hsat : Saturated done) (_hpk : ParkedCtxP done)
    (_hcf : CircFreeCtx done) (_hcg : CircFreeN G) :
    EStabilises p done × AStabilises p done G :=
  n4_of_interpQ eq bd done G

/-- **The cross-check, by elaboration**: the conclusion of the loop-checked
◯-free instance is ALREADY inhabited there, unconditionally, by the Pitts
transport — the same type, from `n4_circFree_uncond`, over the same
cofinality variables and with `PQEquiv`/`QBound` NOT among the hypotheses.  So
the two obligations cannot be inconsistent with a machine-checked theorem on
the ◯-free fragment, and the loop-checked route buys nothing there; the modal
case is what it is for. -/
noncomputable def n4_circFree_byPitts {p : String} {done : List Neg} {G : Neg}
    (s2 : SatE2P p) (a2 : SatA2P p)
    (hsat : Saturated done) (hpk : ParkedCtxP done)
    (hcf : CircFreeCtx done) (hcg : CircFreeN G) :
    EStabilises p done × AStabilises p done G :=
  n4_circFree_uncond s2 a2 hsat hpk hcf hcg

end LJFO

/-! ## Pins -/

#axioms_within LJFO.interpG_founded_eq [propext, Quot.sound]
#axioms_within LJFO.interpG_stab_of_founded [propext, Quot.sound]
#axioms_within LJFO.qStabLitE_of_bound [propext, Quot.sound]
#axioms_within LJFO.qStabLitA_of_bound [propext, Quot.sound]
#axioms_within LJFO.IDeriv.symm []
#axioms_within LJFO.chain1 [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.IDeriv.trans [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.n4_of_interpQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.hasUI_of_interpQ [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.n4_circFree_intrinsic [propext, Classical.choice, Quot.sound]
#axioms_within LJFO.n4_circFree_byPitts [propext, Classical.choice, Quot.sound]
