/-
Route (B), node **N4**, WP12c: **the recording-site loop, concretely**.

`wip/ui_routeB_r_escd.lean` shows the escape design abstractly (`escapeLoop`
is recursion on a natural number).  This module builds the loop the family
will actually run, over the `∀p` entry as a typed parameter, in the types the
guard call has.

**The site.**  At a parked implication `Qa ⊃ N ∈ done` whose loop test does
not fire, both rows of `interpR` emit a guard call at the EXTENDED record
`(Qa, done) :: seen` — and, by `parkRowER_record` / `parkRowAR_record`, that
extension reaches nothing else.  The traversal discharges the guard by the
`∀p` entry applied to the antecedent sub-derivation `s`.  With
derivation-level escapes the entry may instead return

* `EscD.here gd hlt` — an escape for the pair JUST recorded, carrying a
  derivation `gd` of the same guard sequent with `hgtI gd < hgtI s`: the site
  RESTARTS with `gd`;
* `EscD.there e` — an escape for an older pair: the site passes it up, at the
  record and height book it had.

**The loop terminates** because each restart strictly decreases `hgtI` of the
guard derivation in hand.  `guardLoop` below is that recursion, with
`hgtI s` booked as the head of the height book at each attempt, so that the
escape's own bound is exactly the height it must beat.

This is `docs/ui-ljfo-clause-table.md` §4.28's "the sub-derivation is
smaller" in the types of the family, and it is the one mechanism the pair
recursion was designed to make available.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_procd
import Meta.Audit

set_option autoImplicit false

namespace LJFO

variable {p : String}

/-! # Part 1 · The `∀p` entry in traversal shape, with escapes -/

/-- **The `∀p` entry with derivation-level escapes** (OPEN, no term built):
`LJF/OFuelPCof.lean`'s `UEntryP` over `interpR`, at an arbitrary record, with
an `EscD` alternative in the conclusion. -/
def UEntryRD (p : String) : Type :=
  ∀ (done : List Neg), Saturated done → ParkedCtxP done →
    ∀ {Γ' K : List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      ∀ (G : Neg) (seen : SeenR) (b : HeightBook seen) {j : JD}
      (d : Inv Γ' [] j G), BookBound seen b (hgtI d) →
      Sum (UpFrom2 (fun e f => Inv (interpR p e [] done none seen :: K) [] .tru
             (interpR p f [] done (some (jGoal j G)) seen)))
          (EscD K seen b)

/-- The entry reduces to the saturated-station statement of
`wip/ui_routeB_r_escd.lean`: take `Γ' := done ++ Δ`. -/
def satA2RD_of_uentryRD (u : UEntryRD p) : SatA2RD p :=
  fun done Δ G seen b hsat hP hΔ _ d hb =>
    u done hsat hP (fun Z hZ => List.mem_append.mp hZ)
      (fun Z hZ => List.mem_append_left _ hZ) hΔ G seen b d hb

/-! # Part 2 · The loop -/

/-- **The recording-site loop.**  Discharge the guard of a parked
implication `Qa ⊃ N` at the station `done`, from the antecedent
sub-derivation `s`, restarting whenever the `∀p` entry escapes for the pair
just recorded — each restart with a strictly smaller derivation of the same
guard sequent — and passing an older pair's escape up unchanged.

The value is exactly the guard conjunct of `parkRowER` / `parkRowAR`: the
`∀p` approximant of `done ⇒ ↑Qa` at the EXTENDED record. -/
def guardLoop (u : UEntryRD p) (done : List Neg)
    (hsat : Saturated done) (hP : ParkedCtxP done) {K : List Neg}
    (hK : PFreeCtx p K) (Qa : Pos) (seen : SeenR) (b : HeightBook seen) :
    ∀ {Γ' : List Neg}, (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' →
      ∀ (s : Inv Γ' [] .tru (.up Qa)), BookBound seen b (hgtI s) →
      Sum (UpFrom2 (fun e f =>
             Inv (interpR p e [] done none ((Qa, done) :: seen) :: K) [] .tru
                 (interpR p f [] done (some (.up Qa)) ((Qa, done) :: seen))))
          (EscD K seen b) := fun {Γ'} hm hm2 s hb =>
  match hu : u done hsat hP hm hm2 hK (.up Qa) ((Qa, done) :: seen)
              (hgtI s, b) (j := .tru) s ⟨Nat.le_refl _, hb⟩ with
  | .inl w => .inl (by rw [jGoal_tru] at w; exact w)
  | .inr (.here gd hlt) =>
      guardLoop u done hsat hP hK Qa seen b
        (Γ' := done ++ K) (fun Z hZ => List.mem_append.mp hZ)
        (fun Z hZ => List.mem_append_left _ hZ) gd
        (bookBound_mono seen b (Nat.le_of_lt hlt) hb)
  | .inr (.there e) => .inr e
  termination_by Γ' _ _ s _ => hgtI s
  decreasing_by exact hlt

end LJFO

/-! ## Pins -/

#axioms_within LJFO.satA2RD_of_uentryRD [propext]
#axioms_within LJFO.guardLoop [propext]
