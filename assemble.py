import pathlib
W = pathlib.Path("/Users/matthew/Lean/Sources/lax-logic-in-lean/.claude/worktrees/agent-ae24d1b90e438b3fa")
e = (W / "e.txt").read_text()
a = (W / "a.txt").read_text()

# ---- the one E-side modal row: the ∀p-guard is taken at the FULL station ----
OLD = """                      have dArg : Inv (interpF p f [] rest (some (.up (.down (.circ Q')))) ::
                          ([] ++ done)) [] .tru (.up (.down (.circ Q'))) :=
                        (aSoundF p f [] rest (.up (.down (.circ Q')))).wk (by
                          intro Z hZ
                          rcases List.mem_cons.mp hZ with rfl | hZ
                          · exact List.mem_cons_self ..
                          · exact List.mem_cons_of_mem _
                              (splits_sub hXr Z hZ))
"""
NEW = """                      -- RETENTION: the guard is `A(done ⇒ ↑↓◯Q′)`, at the FULL
                      -- station, so `aSoundF` at `done` delivers it verbatim —
                      -- no weakening from `rest` is needed here at all.
                      have dArg : Inv (interpF p f [] done (some (.up (.down (.circ Q')))) ::
                          ([] ++ done)) [] .tru (.up (.down (.circ Q'))) :=
                        aSoundF p f [] done (.up (.down (.circ Q')))
"""
assert OLD in e
e = e.replace(OLD, NEW)

HEADER = r'''/-
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
'''

MIDDLE = r'''  termination_by f _ _ => f
  decreasing_by all_goals (simp_wf; omega)

/-- **A1 at every fuel.**  The `∀p`-approximant beside the station derives
the goal:

    Inv (interpF p f todo done (some G) :: (todo ++ done)) [] .tru G

`aSound`'s proof, clause for clause, at fuel `f+1`; `nBotElim` at 0. -/
def aSoundF (p : String) : ∀ (f : Nat) (todo done : List Neg) (G : Neg),
    Inv (interpF p f todo done (some G) :: (todo ++ done)) [] .tru G
  | 0, _, _, G => by
      rw [interpF]
      exact nBotElim G (List.mem_cons_self ..)
'''

TAIL = r'''  termination_by f _ _ _ => f
  decreasing_by all_goals (simp_wf; omega)

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

end LJFO

/-! ## Pins

The bound is `eSound`/`aSound`'s own pinned set (`LJF/OAudit.lean`).  A
proof needing anything beyond it would be wrong. -/

#axioms_within eSoundF [propext, Classical.choice, Quot.sound]
#axioms_within aSoundF [propext, Classical.choice, Quot.sound]
#axioms_within eSoundFWitness [propext, Classical.choice, Quot.sound]
#axioms_within aSoundFWitness [propext, Classical.choice, Quot.sound]
'''

out = HEADER + e + "\n" + MIDDLE + a + "\n" + TAIL
(W / "LJF/OFuelSound.lean").write_text(out)
print("wrote", len(out.split("\n")), "lines")
