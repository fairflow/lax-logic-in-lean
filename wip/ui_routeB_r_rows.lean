/-
Route (B), node **N4**, WP12c: **the row layer for `interpR` at a saturated
station**.

`LJF/OFuelPMin.lean` Parts 2–4 for the pair recursion: the aggregate at fuel
`f+1` as an equation, one per goal shape, and one membership lemma per row.
These are what every clause of the saturated traversal reads; they are all
`rfl` against `wip/ui_routeB_r_sound.lean`'s `rAgg`/`aggR_*` and
`List.mem_map_of_mem`, because `stepR`'s station maps are PLAIN maps over
`splits done` (where `interpP`'s are `.attach` maps, so `LJF/OFuelPMin.lean`
needs `rowMem`).

Part 3 adds the four equations a dispatch clause splits on: the two rows with
the loop test open, and the two with it fired.

`LJF/` is untouched; this module is a leaf.
-/
import wip.ui_routeB_r_guard
import Meta.Audit

set_option autoImplicit false

namespace LJFO

variable {p : String} {f : Nat} {done : List Neg} {seen : SeenR}

/-! # Part 1 · The aggregate at fuel `f+1`, by goal shape -/

theorem interpRE_eq (hsat : Saturated done) :
    interpR p (f + 1) [] done none seen
      = nAndAll (eRowsR id p (interpR p f) done seen) :=
  (rAgg (rst := id) hsat none seen).trans (aggR_none _ _ _)

theorem interpRA_imp_eq (hsat : Saturated done) (Q : Pos) (N : Neg) :
    interpR p (f + 1) [] done (some (.imp Q N)) seen
      = nAndAll ((invertPos Q).map (fun b =>
          .imp (.down (interpR p f b done none seen))
               (interpR p f b done (some N) seen))) :=
  (rAgg (rst := id) hsat _ seen).trans (aggR_imp _ _ Q N _)

theorem interpRA_and_eq (hsat : Saturated done) (M N : Neg) :
    interpR p (f + 1) [] done (some (.and M N)) seen
      = nAnd (interpR p f [] done (some M) seen)
             (interpR p f [] done (some N) seen) :=
  (rAgg (rst := id) hsat _ seen).trans (aggR_and _ _ M N _)

theorem interpRA_atomT_eq (hsat : Saturated done) {q : String}
    (hq : atomMem q done = true) :
    interpR p (f + 1) [] done (some (.up (.atom q))) seen = nTop :=
  (rAgg (rst := id) hsat _ seen).trans (aggR_atomT _ hq _)

theorem interpRA_atomF_eq (hsat : Saturated done) {q : String}
    (hq : ¬ atomMem q done = true) :
    interpR p (f + 1) [] done (some (.up (.atom q))) seen
      = nOrAll (atomHead p q ++
          aRowsR id p (interpR p f) done (.up (.atom q)) false seen) :=
  (rAgg (rst := id) hsat _ seen).trans (aggR_atomF _ hq _)

theorem interpRA_fls_eq (hsat : Saturated done) :
    interpR p (f + 1) [] done (some (.up .fls)) seen
      = nOrAll (aRowsR id p (interpR p f) done (.up .fls) false seen) :=
  (rAgg (rst := id) hsat _ seen).trans (aggR_fls _ _ _)

theorem interpRA_or_eq (hsat : Saturated done) (P₁ P₂ : Pos) :
    interpR p (f + 1) [] done (some (.up (.or P₁ P₂))) seen
      = nOrAll ([interpR p f [] done (some (.up P₁)) seen,
                 interpR p f [] done (some (.up P₂)) seen] ++
          aRowsR id p (interpR p f) done (.up (.or P₁ P₂)) false seen) :=
  (rAgg (rst := id) hsat _ seen).trans (aggR_or _ _ P₁ P₂ _)

theorem interpRA_down_eq (hsat : Saturated done) (M : Neg) :
    interpR p (f + 1) [] done (some (.up (.down M))) seen
      = nOrAll ([interpR p f [] done (some M) seen] ++
          aRowsR id p (interpR p f) done (.up (.down M)) false seen) :=
  (rAgg (rst := id) hsat _ seen).trans (aggR_down _ _ M _)

theorem interpRA_circ_eq (hsat : Saturated done) (Q : Pos) :
    interpR p (f + 1) [] done (some (.circ Q)) seen
      = .circ (.down (nOrAll (laxPrefixR (interpR p f) done seen Q ++
          aRowsR id p (interpR p f) done (.circ Q) true seen))) :=
  (rAgg (rst := id) hsat _ seen).trans (aggR_circ _ _ Q _)

/-! # Part 2 · The rows, by membership in `splits done`

`stepR`'s station maps are plain maps, so every row membership is
`List.mem_map_of_mem`. -/

theorem eRow_atomMem {a : String} {rest : List Neg}
    (h : (Neg.up (.atom a), rest) ∈ splits done) :
    pGuard p a nTop (.up (.atom a)) ∈ eRowsR id p (interpR p f) done seen :=
  List.mem_map_of_mem h

theorem eRow_qimpMem {a : String} {N : Neg} {rest : List Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    pGuard p a nTop (.imp (.atom a) (interpR p f [N] rest none seen))
      ∈ eRowsR id p (interpR p f) done seen :=
  List.mem_map_of_mem h

theorem eRow_dykMem {Q' : Pos} {N' N : Neg} {rest : List Neg}
    (h : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    parkRowER id (interpR p f) done (.down (.imp Q' N')) N rest
      [.imp (.down N') N] seen ∈ eRowsR id p (interpR p f) done seen :=
  List.mem_map_of_mem h

theorem eRow_boxMem {Q : Pos} {rest : List Neg}
    (h : (Neg.circ Q, rest) ∈ splits done) :
    Neg.circ (.down (interpR p f [.up Q] rest none seen))
      ∈ eRowsR id p (interpR p f) done seen :=
  List.mem_map_of_mem h

theorem eRow_cimpMem {Q' : Pos} {N : Neg} {rest : List Neg}
    (h : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    parkRowER id (interpR p f) done (.down (.circ Q')) N rest [] seen
      ∈ eRowsR id p (interpR p f) done seen :=
  List.mem_map_of_mem h

theorem eRow_orimpMem {Qa Qb : Pos} {N : Neg} {rest : List Neg}
    (h : (Neg.imp (.or Qa Qb) N, rest) ∈ splits done) :
    parkRowER id (interpR p f) done (.or Qa Qb) N rest [] seen
      ∈ eRowsR id p (interpR p f) done seen :=
  List.mem_map_of_mem h

theorem eRow_shimpMem {Pa : Pos} {N : Neg} {rest : List Neg}
    (h : (Neg.imp (.down (.up Pa)) N, rest) ∈ splits done) :
    parkRowER id (interpR p f) done (.down (.up Pa)) N rest [] seen
      ∈ eRowsR id p (interpR p f) done seen :=
  List.mem_map_of_mem h

theorem eRow_andimpMem {Ma Mb N : Neg} {rest : List Neg}
    (h : (Neg.imp (.down (.and Ma Mb)) N, rest) ∈ splits done) :
    parkRowER id (interpR p f) done (.down (.and Ma Mb)) N rest [] seen
      ∈ eRowsR id p (interpR p f) done seen :=
  List.mem_map_of_mem h

section ARows
variable (goal : Neg) (box : Bool)

theorem aRow_qimpMem {a : String} {N : Neg} {rest : List Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    pGuard p a nBot (nAnd (.up (.atom a))
        (interpR p f [N] rest (some goal) seen))
      ∈ aRowsR id p (interpR p f) done goal box seen :=
  List.mem_map_of_mem h

theorem aRow_dykMem {Q' : Pos} {N' N : Neg} {rest : List Neg}
    (h : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    parkRowAR id (interpR p f) done (.down (.imp Q' N')) N rest goal seen
      ∈ aRowsR id p (interpR p f) done goal box seen :=
  List.mem_map_of_mem h

theorem aRow_cimpMem {Q' : Pos} {N : Neg} {rest : List Neg}
    (h : (Neg.imp (.down (.circ Q')) N, rest) ∈ splits done) :
    parkRowAR id (interpR p f) done (.down (.circ Q')) N rest goal seen
      ∈ aRowsR id p (interpR p f) done goal box seen :=
  List.mem_map_of_mem h

theorem aRow_orimpMem {Qa Qb : Pos} {N : Neg} {rest : List Neg}
    (h : (Neg.imp (.or Qa Qb) N, rest) ∈ splits done) :
    parkRowAR id (interpR p f) done (.or Qa Qb) N rest goal seen
      ∈ aRowsR id p (interpR p f) done goal box seen :=
  List.mem_map_of_mem h

theorem aRow_shimpMem {Pa : Pos} {N : Neg} {rest : List Neg}
    (h : (Neg.imp (.down (.up Pa)) N, rest) ∈ splits done) :
    parkRowAR id (interpR p f) done (.down (.up Pa)) N rest goal seen
      ∈ aRowsR id p (interpR p f) done goal box seen :=
  List.mem_map_of_mem h

theorem aRow_andimpMem {Ma Mb N : Neg} {rest : List Neg}
    (h : (Neg.imp (.down (.and Ma Mb)) N, rest) ∈ splits done) :
    parkRowAR id (interpR p f) done (.down (.and Ma Mb)) N rest goal seen
      ∈ aRowsR id p (interpR p f) done goal box seen :=
  List.mem_map_of_mem h

/-- The opened-box row, present only in a `◯`-goal aggregate. -/
theorem aRow_boxMem {R : Pos} {rest : List Neg}
    (h : (Neg.circ R, rest) ∈ splits done) :
    (if box then
        Neg.imp (.down (interpR p f [.up R] rest none seen))
                (interpR p f [.up R] rest (some goal) seen)
      else nBot)
      ∈ aRowsR id p (interpR p f) done goal box seen :=
  List.mem_map_of_mem h

end ARows

/-! # Part 3 · The four equations a dispatch clause splits on -/

variable (prev : ApproxR) (Qa : Pos) (N : Neg) (rest res : List Neg) (goal : Neg)

/-- The `∃p` row with the loop test OPEN: the guarded conjunct is present,
its guard at the extended record. -/
theorem parkRowER_open (h : ¬ seenMemR seen Qa done = true) :
    parkRowER id prev done Qa N rest res seen
      = nAnd (.imp (.down (prev [] done (some (.up Qa)) ((Qa, done) :: seen)))
                   (prev [N] rest none seen))
             (prev res rest none seen) := by
  rw [parkRowER_record, if_neg h]

/-- The `∃p` row with the loop test FIRED: the guarded conjunct is `⊤`, and
what remains is the residual alone. -/
theorem parkRowER_cut (h : seenMemR seen Qa done = true) :
    parkRowER id prev done Qa N rest res seen
      = nAnd nTop (prev res rest none seen) := by
  rw [parkRowER_record, if_pos h]

/-- The `∀p` row with the loop test OPEN. -/
theorem parkRowAR_open (h : ¬ seenMemR seen Qa done = true) :
    parkRowAR id prev done Qa N rest goal seen
      = nAnd (prev [] done (some (.up Qa)) ((Qa, done) :: seen))
             (prev [N] rest (some goal) seen) := by
  rw [parkRowAR_record, if_neg h]

/-- The `∀p` row with the loop test FIRED: the row is `⊥`, which is why the
traversal must ESCAPE there. -/
theorem parkRowAR_cut (h : seenMemR seen Qa done = true) :
    parkRowAR id prev done Qa N rest goal seen = nBot := by
  rw [parkRowAR_record, if_pos h]

end LJFO

/-! ## Pins -/

#axioms_within LJFO.interpRE_eq [propext]
#axioms_within LJFO.interpRA_imp_eq [propext]
#axioms_within LJFO.interpRA_and_eq [propext]
#axioms_within LJFO.interpRA_atomT_eq [propext]
#axioms_within LJFO.interpRA_atomF_eq [propext]
#axioms_within LJFO.interpRA_fls_eq [propext]
#axioms_within LJFO.interpRA_or_eq [propext]
#axioms_within LJFO.interpRA_down_eq [propext]
#axioms_within LJFO.interpRA_circ_eq [propext]
#axioms_within LJFO.eRow_atomMem [propext, Quot.sound]
#axioms_within LJFO.eRow_qimpMem [propext, Quot.sound]
#axioms_within LJFO.eRow_dykMem [propext, Quot.sound]
#axioms_within LJFO.eRow_boxMem [propext, Quot.sound]
#axioms_within LJFO.eRow_cimpMem [propext, Quot.sound]
#axioms_within LJFO.eRow_orimpMem [propext, Quot.sound]
#axioms_within LJFO.eRow_shimpMem [propext, Quot.sound]
#axioms_within LJFO.eRow_andimpMem [propext, Quot.sound]
#axioms_within LJFO.aRow_qimpMem [propext, Quot.sound]
#axioms_within LJFO.aRow_dykMem [propext, Quot.sound]
#axioms_within LJFO.aRow_cimpMem [propext, Quot.sound]
#axioms_within LJFO.aRow_orimpMem [propext, Quot.sound]
#axioms_within LJFO.aRow_shimpMem [propext, Quot.sound]
#axioms_within LJFO.aRow_andimpMem [propext, Quot.sound]
#axioms_within LJFO.aRow_boxMem [propext, Quot.sound]
#axioms_within LJFO.parkRowER_open []
#axioms_within LJFO.parkRowER_cut []
#axioms_within LJFO.parkRowAR_open []
#axioms_within LJFO.parkRowAR_cut []
