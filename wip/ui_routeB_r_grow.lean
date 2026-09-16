/-
Route (B), node **N4**, WP12d: **the station-growth repair is REFUTED**.

`docs/n4-pair-family.md` §4 leaves one step of the family without a clause:
the escape has no way across the `p`-free binders the inversion phase
creates (`Inv.downL` after `Inv.impR`, or after an `Inv.orL`, or after a
left-focus chain).  §6 proposes a repair that would remove the need for the
crossing altogether — **park the bound hypothesis into the STATION instead
of into the `p`-free context**.  Then the station below the binder is
strictly larger as a set, `sameSet` fails, the loop test cannot fire there,
and no cut site lies below a binder at all.

That repair needs exactly one new lemma.  At the binder the conclusion is
built at the old station and the recursive call returns at the new one, so
the clause must supply

    E^R(done | seen),  M₀   ⊢   E^R([M₀], done | seen)          (grow)

for `p`-free `M₀` — the ∃p interpolant is monotone under adding a `p`-free
hypothesis to the station.  The measure would survive it: the station
component is second and the height component drops at the binder, so a
station INCREASE is affordable there, and the step that uses `(grow)` builds
the CONCLUSION, whose height nothing constrains.

**`(grow)` is false**, and the reason is the record.  At a record that has
already cut a fire row, `E^R(done | seen)` has LOST that row; at the larger
station the recorded pair is no longer set-equal, so the loop test does not
fire and `E^R([M₀], done | seen)` HAS the row back.  The larger station's
interpolant is therefore strictly stronger, and the extra strength is not
recoverable from `M₀`.

The instance is the cell of `wip/ui_routeB_r_bindcell.lean`, with
`M₀ := ↑a` — the hypothesis its goal-antecedent binder binds:

    done  = [X, ↑p]           X = ↓↑a ⊃ ↑n,  seen = [(Qa, done)]
    doneA = [↑a, X, ↑p]       the station after parking M₀

`E^R(done | seen)` is `⊤`-built (`Refute.ev_interpR_done`), `↑a` holds, and
`E^R([↑a], done | seen)` is FALSE in the one-world model with `a` true and
`n` false, because at `doneA` the row of `X` is back: its guard is `⊤` there
(the atom `a` is now in the station, so the ∀p approximant of `↑↓↑a`
has a `⊤` disjunct) and its fire delivers `↑n`.

    growE_refuted : Inv [↑a, E^R(done | seen)] [] .tru (E^R([↑a], done | seen))
                    → False

for every fuel of the hypothesis and every fuel `≥ 4` of the conclusion.

So §6(b) is closed.  §6(a) and §6(c) stand.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_escw
import Meta.Audit

set_option autoImplicit false

namespace LJFO

namespace Grow

/-- The station after parking `M₀ = ↑a`: strictly larger than `done` as a
set, so the recorded pair is no longer set-equal to it. -/
def doneA : List Neg := Neg.up (.atom "a") :: BindCell.done

/-- The record as extended by the guard call at the larger station. -/
def seenA : SeenR := (BindCell.Qa, doneA) :: BindCell.seen

/-! # Part 1 · The row list at the larger station

The loop test does NOT fire at `doneA`, so the row of `X` is the guarded
fire, not `⊤`.  Compare `BindCell.cellRows`, where it is `⊤`. -/

theorem rowsA (prev : ApproxR) :
    eRowsR id "p" prev doneA BindCell.seen
      = [Neg.up (.atom "a"),
         nAnd (.imp (.down (prev [] doneA (some (.up BindCell.Qa)) seenA))
                    (prev [Neg.up (.atom "n")]
                         [Neg.up (.atom "a"), Neg.up (.atom "p")] none
                         BindCell.seen))
              (prev [] [Neg.up (.atom "a"), Neg.up (.atom "p")] none
                    BindCell.seen),
         nTop] := rfl

/-! # Part 2 · The guard is `⊤` at the larger station, the fire is not -/

/-- **The guard of `X`'s row at `doneA` holds.**  Its head disjunct is the
∀p approximant of `↑a` at a station that CONTAINS `↑a`, which is `nTop`. -/
theorem ev_guard (l : Nat) :
    evN Refute.vVal
      (interpR "p" (l + 2) [] doneA (some (.up BindCell.Qa)) seenA) = true := by
  have h : interpR "p" (l + 2) [] doneA (some (.up BindCell.Qa)) seenA
      = nOrAll ([interpR "p" (l + 1) [] doneA
                   (some (Neg.up (.atom "a"))) seenA] ++
          aRowsR id "p" (interpGR id "p" (l + 1)) doneA
            (.up BindCell.Qa) false seenA) := rfl
  have hhead : interpR "p" (l + 1) [] doneA (some (Neg.up (.atom "a"))) seenA
      = nTop := rfl
  rw [h, hhead]
  simp [nOrAll, nOr, nTop, evN, evP]

/-- **The fire of `X`'s row at `doneA` fails.**  It delivers the interpolant
of a station containing `↑n`, whose row for `↑n` is `↑n` itself. -/
theorem ev_fire (l : Nat) :
    evN Refute.vVal
      (interpR "p" (l + 2) [Neg.up (.atom "n")]
        [Neg.up (.atom "a"), Neg.up (.atom "p")] none BindCell.seen)
      = false := by
  have h : interpR "p" (l + 2) [Neg.up (.atom "n")]
        [Neg.up (.atom "a"), Neg.up (.atom "p")] none BindCell.seen
      = nAndAll [Neg.up (.atom "n"), Neg.up (.atom "a"), nTop] := rfl
  rw [h]; rfl

/-! # Part 3 · The larger station's interpolant fails in the model -/

/-- **`E^R([↑a], done | seen)` is FALSE** where `E^R(done | seen)` and `↑a`
are true: the row of `X` is back, its guard holds and its fire does not. -/
theorem ev_grow (f : Nat) :
    evN Refute.vVal
      (interpR "p" (f + 4) [Neg.up (.atom "a")] BindCell.done none
        BindCell.seen) = false := by
  have h1 : interpR "p" (f + 4) [Neg.up (.atom "a")] BindCell.done none
        BindCell.seen
      = nAndAll (eRowsR id "p" (interpGR id "p" (f + 2)) doneA
          BindCell.seen) := rfl
  rw [h1, rowsA]
  have hg := ev_guard f
  have hf := ev_fire f
  simp only [nAndAll, List.foldr_cons, List.foldr_nil, nAnd, nTop, evN, evP,
    Refute.vVal, hg, hf, Bool.not_true, Bool.or_false, Bool.false_and,
    Bool.and_false]

/-! # Part 4 · The refutation -/

/-- **The station-growth lemma the repair needs is REFUTED.**  At the cell's
record, the interpolant of the larger station is not a consequence of the
interpolant of the smaller one together with the parked hypothesis. -/
theorem growE_refuted (e f : Nat)
    (d : Inv [Neg.up (.atom "a"),
              interpR "p" e [] BindCell.done none BindCell.seen] [] .tru
           (interpR "p" (f + 4) [Neg.up (.atom "a")] BindCell.done none
             BindCell.seen)) : False :=
  no_inv_of_model (v := Refute.vVal)
    (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · simp only [evN, evP, Refute.vVal]; rfl
      · rcases List.mem_cons.mp hZ with rfl | hZ
        · exact Refute.ev_interpR_done Refute.vVal e
        · exact absurd hZ List.not_mem_nil)
    (ev_grow f) d

end Grow

end LJFO

/-! ## Pins -/

#axioms_within LJFO.Grow.rowsA [propext]
#axioms_within LJFO.Grow.ev_guard [propext]
#axioms_within LJFO.Grow.ev_fire [propext]
#axioms_within LJFO.Grow.ev_grow [propext]
#axioms_within LJFO.Grow.growE_refuted [propext, Quot.sound]
