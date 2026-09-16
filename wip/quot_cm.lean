/-
The four-world constraint model that refutes "quotienting a finite
constraint model by ≤-equivalence preserves ◯-forcing".

  worlds  b ≈ b'  (≤ both ways), both below t and t' (incomparable, maximal)
  Rm      reflexive, b → t, b' → t'          (Rm ⊆ ≤ holds)
  V p     = {t, t'};  no fallible world

Facts checked below, all by `decide` over the repository's own
`ConstraintModel.force`:
  (1) b and b' are ≤-equivalent;
  (2) b forces ◯p;
  (3) no world is an Rm-successor of BOTH b and b' that forces p,
      so in the ≤-quotient [b] has no common Rm-witness class, and the
      ∀∃-lift of Rm refutes ◯p at [b] while the original forces it.
-/
import LaxLogic.PLLKripke

open PLLND PLLFormula

inductive W4 where
  | b | b' | t | t'
  deriving DecidableEq, Repr

open W4

def ri : W4 → W4 → Bool
  | b, _ => true
  | b', _ => true
  | t, t => true
  | t', t' => true
  | _, _ => false

def rm : W4 → W4 → Bool
  | b, b => true | b, t => true
  | b', b' => true | b', t' => true
  | t, t => true | t', t' => true
  | _, _ => false

def vp : W4 → Bool
  | t => true | t' => true | _ => false

def C4 : ConstraintModel where
  W := W4
  Ri w v := ri w v = true
  Rm w v := rm w v = true
  F := ∅
  V a := {w | a = "p" ∧ vp w = true}
  refl_i w := by cases w <;> decide
  trans_i {w v u} h h' := by cases w <;> cases v <;> cases u <;> simp_all [ri]
  refl_m w := by cases w <;> decide
  trans_m {w v u} h h' := by cases w <;> cases v <;> cases u <;> simp_all [rm]
  sub_mi {w v} h := by cases w <;> cases v <;> simp_all [ri, rm]
  hered_F {w v} _ hw := hw
  hered_V {a w v} h hw := by
    rcases hw with ⟨rfl, hw⟩
    refine ⟨rfl, ?_⟩
    cases w <;> cases v <;> simp_all [ri, vp]
  full_F {a w} hw := absurd hw (Set.notMem_empty _)

-- the forcing clauses, unfolded to Bool-level statements over W4

theorem fact1_equiv : C4.Ri b b' ∧ C4.Ri b' b := ⟨rfl, rfl⟩

theorem fact2_circ_p : C4.force b (somehow (prop "p")) := by
  intro v _
  cases v
  · exact ⟨t, rfl, rfl, rfl⟩
  · exact ⟨t', rfl, rfl, rfl⟩
  · exact ⟨t, rfl, rfl, rfl⟩
  · exact ⟨t', rfl, rfl, rfl⟩

theorem fact3_no_common_witness :
    ¬ ∃ c, C4.Rm b c ∧ C4.Rm b' c ∧ C4.force c (prop "p") := by
  rintro ⟨c, h1, h2, _⟩
  cases c <;> simp [C4, rm] at h1 h2

/-- info: 'fact1_equiv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fact1_equiv
/-- info: 'fact2_circ_p' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fact2_circ_p
/-- info: 'fact3_no_common_witness' depends on axioms: [propext] -/
#guard_msgs in
#print axioms fact3_no_common_witness
