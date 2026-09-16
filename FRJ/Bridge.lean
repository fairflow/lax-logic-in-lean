/-
# The bridge: an `FRJ(◯)` derivation as a certificate about the ORIGINAL PLL

`FRJ/` carries its own syntax (`Form`) and its own model structure
(`Kripke`), both written to follow Fiorentini–Ferrari.  Everything else in
the repository is built on `PLLFormula` and `PLLND.ConstraintModel`.  This
module connects the two, so that a derivation found by the FRJ(◯) search
is a statement about the development's own judgments rather than about a
private copy of the logic.

Three parts.

* **Syntax.**  `ofPLL`/`toPLL` are mutually inverse (`toPLL_ofPLL`,
  `ofPLL_toPLL`): the two datatypes are isomorphic, constructor for
  constructor.  There is no content here; it is recorded so that the
  eventual merge of the two definitions is a renaming.
* **Semantics.**  `Kripke.toConstraint` forgets what FRJ adds
  (finiteness, antisymmetry, a root, decidability) and keeps what a
  constraint model needs.  `force_toConstraint` says forcing agrees under
  the syntax map, in EVERY world.  So `Kripke` is a subclass of
  `ConstraintModel`, and refutation over the subclass is the stronger
  statement.
* **The certificate.**  `not_derivable_of_provable`: if the FRJ(◯) search
  returns a derivation of `ofPLL φ`, then `φ` has no `LaxND` proof.
  `not_entails_of_provable` and `not_interd_of_provable` are the forms the
  RN(◯,{}) dictionary cells are stated in.

The direction of the isomorphism is deliberate: `PLLFormula` is primary,
`Form` derived.
-/
import FRJ.Sound
import LaxLogic.PLLKripke

namespace FRJ

open PLLND

/-! ## Syntax: the two formula types are isomorphic -/

/-- The original syntax, read into FRJ's. -/
def ofPLL : PLLFormula → Form
  | .prop a     => .atom a
  | .falsePLL   => .bot
  | .and φ ψ    => .and (ofPLL φ) (ofPLL ψ)
  | .or φ ψ     => .or (ofPLL φ) (ofPLL ψ)
  | .ifThen φ ψ => .imp (ofPLL φ) (ofPLL ψ)
  | .somehow φ  => .circ (ofPLL φ)

/-- FRJ's syntax, read back into the original. -/
def toPLL : Form → PLLFormula
  | .atom a  => .prop a
  | .bot     => .falsePLL
  | .and A B => .and (toPLL A) (toPLL B)
  | .or A B  => .or (toPLL A) (toPLL B)
  | .imp A B => .ifThen (toPLL A) (toPLL B)
  | .circ A  => .somehow (toPLL A)

@[simp] theorem toPLL_ofPLL : ∀ φ : PLLFormula, toPLL (ofPLL φ) = φ
  | .prop _     => rfl
  | .falsePLL   => rfl
  | .and φ ψ    => by simp [ofPLL, toPLL, toPLL_ofPLL φ, toPLL_ofPLL ψ]
  | .or φ ψ     => by simp [ofPLL, toPLL, toPLL_ofPLL φ, toPLL_ofPLL ψ]
  | .ifThen φ ψ => by simp [ofPLL, toPLL, toPLL_ofPLL φ, toPLL_ofPLL ψ]
  | .somehow φ  => by simp [ofPLL, toPLL, toPLL_ofPLL φ]

@[simp] theorem ofPLL_toPLL : ∀ A : Form, ofPLL (toPLL A) = A
  | .atom _  => rfl
  | .bot     => rfl
  | .and A B => by simp [ofPLL, toPLL, ofPLL_toPLL A, ofPLL_toPLL B]
  | .or A B  => by simp [ofPLL, toPLL, ofPLL_toPLL A, ofPLL_toPLL B]
  | .imp A B => by simp [ofPLL, toPLL, ofPLL_toPLL A, ofPLL_toPLL B]
  | .circ A  => by simp [ofPLL, toPLL, ofPLL_toPLL A]

/-! ## Semantics: every FRJ model is a constraint model -/

/-- The forgetful map.  A `Kripke` model is a `ConstraintModel` whose
frame happens to be a finite rooted poset with decidable everything. -/
def Kripke.toConstraint (K : Kripke) : ConstraintModel where
  W := K.W
  Ri := K.le
  Rm := K.Rm
  F := fun w => K.Fal w
  V := fun a w => K.V w a
  refl_i := K.le_refl
  trans_i := K.le_trans
  refl_m := K.rm_refl
  trans_m := K.rm_trans
  sub_mi := K.sub_mi
  hered_F := K.fal_mono
  hered_V := fun h hw => K.V_mono h _ hw
  full_F := fun hw => K.fal_V hw _

/-- **Forcing agrees.**  The two definitions of `⊩` are the same relation,
clause for clause, once the syntax is translated. -/
theorem force_toConstraint (K : Kripke) :
    ∀ (φ : PLLFormula) (w : K.W), K.toConstraint.force w φ ↔ K.force w (ofPLL φ)
  | .prop _, _   => Iff.rfl
  | .falsePLL, _ => Iff.rfl
  | .and φ ψ, w  =>
      and_congr (force_toConstraint K φ w) (force_toConstraint K ψ w)
  | .or φ ψ, w   =>
      or_congr (force_toConstraint K φ w) (force_toConstraint K ψ w)
  | .ifThen φ ψ, _w =>
      ⟨fun h b hb ha =>
          (force_toConstraint K ψ b).mp (h b hb ((force_toConstraint K φ b).mpr ha)),
       fun h b hb ha =>
          (force_toConstraint K ψ b).mpr (h b hb ((force_toConstraint K φ b).mp ha))⟩
  | .somehow φ, _w =>
      ⟨fun h b hb =>
          let ⟨c, hc, hf⟩ := h b hb
          ⟨c, hc, (force_toConstraint K φ c).mp hf⟩,
       fun h b hb =>
          let ⟨c, hc, hf⟩ := h b hb
          ⟨c, hc, (force_toConstraint K φ c).mpr hf⟩⟩

/-! ## The certificate

The chain is: `LaxND`-derivable ⟹ valid in every constraint model
(`PLLND.soundness_valid`) ⟹ valid in every `Kripke` model (this bridge)
⟹ not `FRJ`-provable (`FRJ.soundness`). -/

/-- A `LaxND` theorem is valid at the root of every FRJ model. -/
theorem valid_of_derivable {φ : PLLFormula} (p : LaxND [] φ) (K : Kripke) :
    K.valid (ofPLL φ) :=
  (force_toConstraint K φ K.root).mp (soundness_valid p K.toConstraint K.root)

/-- **An FRJ(◯) derivation refutes the original judgment.**  If the search
returns a derivation of `ofPLL φ`, then `φ` is not a theorem of PLL. -/
theorem not_derivable_of_provable {φ : PLLFormula} (h : Provable (ofPLL φ)) :
    ¬ Nonempty (LaxND [] φ) :=
  fun ⟨p⟩ => soundness h (valid_of_derivable p)

/-- **The pinning interface.**  A concrete finite model refuting `ofPLL φ`
at its root refutes the original judgment, with no reference to the search
that found it: this is what makes a discovery re-checkable by the kernel. -/
theorem not_derivable_of_countermodel {φ : PLLFormula} (K : Kripke)
    (h : ¬ K.valid (ofPLL φ)) : ¬ Nonempty (LaxND [] φ) :=
  fun ⟨p⟩ => h (valid_of_derivable p K)

/-- The entailment form, for a dictionary cell. -/
theorem not_entails_of_countermodel {φ ψ : PLLFormula} (K : Kripke)
    (h : ¬ K.valid (ofPLL (.ifThen φ ψ))) : ¬ Nonempty (LaxND [φ] ψ) :=
  fun ⟨p⟩ => not_derivable_of_countermodel K h ⟨.impIntro p⟩

/-- The one-hypothesis form: a derivation of the implication refutes the
entailment.  (`impIntro` is the deduction theorem, on the nose.) -/
theorem not_entails_of_provable {φ ψ : PLLFormula}
    (h : Provable (ofPLL (.ifThen φ ψ))) : ¬ Nonempty (LaxND [φ] ψ) :=
  fun ⟨p⟩ => not_derivable_of_provable h ⟨.impIntro p⟩

/-- The form the RN(◯,{}) dictionary cells are stated in: this is
`¬ PLLND.SemUI.Interd φ ψ`, unfolded so that the bridge need not import
the `SemUI` development. -/
theorem not_interd_of_provable {φ ψ : PLLFormula}
    (h : Provable (ofPLL (.ifThen φ ψ))) :
    ¬ (Nonempty (LaxND [φ] ψ) ∧ Nonempty (LaxND [ψ] φ)) :=
  fun hc => not_entails_of_provable h hc.1

/-- Symmetric form: refuting the converse implication refutes the cell too. -/
theorem not_interd_of_provable' {φ ψ : PLLFormula}
    (h : Provable (ofPLL (.ifThen ψ φ))) :
    ¬ (Nonempty (LaxND [φ] ψ) ∧ Nonempty (LaxND [ψ] φ)) :=
  fun hc => not_entails_of_provable h hc.2

end FRJ
