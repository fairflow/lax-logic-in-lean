/-
# `LaxLogic.QLL.Kit` — what a checker is built from

Fresh names and the proof that they are fresh; the size lemmas that justify the
recursion; the error type; context lookup.  Split out so that `Certify.lean`
does not depend on a second checker.

Everything here was originally written to *prove* a soundness theorem about a
`Prop`-valued family.  That theorem no longer exists — `Certify.lean` returns
the derivation, so soundness is typed — but the lemmas survived unchanged,
because constructing a derivation needs exactly what proving one needed: that
`freshFor`'s choice satisfies the rule's freshness condition, and that a
successful context lookup lands on a *variable* entry.
-/
import LaxLogic.QLL.Deriv
import LaxLogic.QLL.Lc

namespace LaxLogic.QLL

/-! ## Fresh names -/

/-- `n` copies of `"z"`.  Appended on the right, so that at run time each step
extends the (unshared) accumulator in place. -/
def zs : Nat → String
  | 0     => ""
  | n + 1 => zs n ++ "z"

/-- Measured in bytes, not characters: in this toolchain `String.length` and
`String.toList` depend on `Classical.choice`, so any statement mentioning them
does, while `String.utf8ByteSize` depends on no axioms and
`String.utf8ByteSize_append` only on `propext` and `Quot.sound`. -/
theorem zs_byteSize : ∀ n : Nat, (zs n).utf8ByteSize = n
  | 0     => rfl
  | n + 1 => by
      show (zs n ++ "z").utf8ByteSize = n + 1
      rw [String.utf8ByteSize_append, zs_byteSize n]
      rfl

/-- The largest UTF-8 byte size of a name in the list (`0` for `[]`). -/
def maxSize : List String → Nat
  | []      => 0
  | s :: ss => max s.utf8ByteSize (maxSize ss)

theorem byteSize_le_maxSize : ∀ (ss : List String) (s : String), s ∈ ss →
    s.utf8ByteSize ≤ maxSize ss
  | [],      _, h => nomatch h
  | t :: ts, s, h => by
      show s.utf8ByteSize ≤ max t.utf8ByteSize (maxSize ts)
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (byteSize_le_maxSize ts s h') (Nat.le_max_right _ _)

/--
A name not occurring in `ss`: `"z"` repeated one more time than the byte size
of the longest name in `ss`, so it is strictly longer than every one of them.

The length is one more than the *maximum*, not the sum.  An earlier revision
concatenated every name in `ss` onto a `"z"`; since the checker puts each fresh
name into the context before choosing the next, name length then doubled with
every nested binder, and a term with about 25 nested `let`s exhausted memory.
With the maximum, the name chosen at binder depth `d` has at most `d` bytes
more than the longest name of the input.

Crude on purpose.  A counter would need a search to avoid collisions, and the
freshness property is wanted as a *theorem* for soundness, not as a runtime
check.
-/
def freshFor (ss : List String) : String := zs (maxSize ss + 1)

/-- The UTF-8 byte size of `freshFor ss` exceeds that of every name in `ss`. -/
theorem freshFor_byteSize (ss : List String) :
    (freshFor ss).utf8ByteSize = maxSize ss + 1 :=
  zs_byteSize _

/-- `freshFor` does what its name says.  Soundness will need this. -/
theorem freshFor_notMem (ss : List String) : freshFor ss ∉ ss := by
  intro h
  have h1 := byteSize_le_maxSize ss _ h
  rw [freshFor_byteSize ss] at h1
  omega

/-- info: 'LaxLogic.QLL.freshFor_notMem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms freshFor_notMem

/-! ## Size is preserved by opening

The checker recurses on opened bodies, which are not structural subterms of
the binder, so termination is by `Pf.size`.  Opening with a *variable* leaves
the size alone; opening an individual leaves it alone for any term, since
`openI` touches only the embedded `Tm`s. -/

theorem size_openP (k : Nat) (z : String) (p : Pf) :
    (Pf.openP k (.fvar z) p).size = p.size := by
  induction p generalizing k with
  | bvar i => by_cases h : i = k <;> simp [Pf.openP, Pf.size, h]
  | _ => simp_all [Pf.openP, Pf.size]

theorem size_openI (k : Nat) (u : Tm) (p : Pf) :
    (Pf.openI k u p).size = p.size := by
  induction p generalizing k <;> simp_all [Pf.openI, Pf.size]

/-! ## Errors -/

/-- Why a check failed.  Carries enough to locate the fault. -/
inductive Err where
  /-- X de Bruijn index escaped its binder: the term is not locally closed. -/
  | looseIndex (i : Nat)
  /-- X free proof variable with no variable entry in the context. -/
  | unbound (x : String)
  /-- The inferred formula had the wrong shape for the rule the term names. -/
  | expected (shape : String) (got : Form)
  /-- Inferred and required formulas differ. -/
  | mismatch (required got : Form)
  /-- X term that cannot be inferred appeared where no goal was available. -/
  | notInferable (term : String)
  /-- `∃E`'s eigenvariable escaped into the conclusion. -/
  | escapes (a : String) (K : Form)
  /-- `◯E` mixed the two modalities, which Fig. 5 does not permit. -/
  | modalityClash (found required : Q)
  /-- Inference for `∀` produced a body with a loose de Bruijn index, so the
  open/close roundtrip is unavailable.  Cannot arise for well-formed input;
  refused rather than mis-accepted. -/
  | notLocallyClosed (A : Form)
  deriving Repr, DecidableEq

/-- The formula attached to a *variable* entry of the context. -/
def Ctx.lookup? (Γ : Ctx) (x : String) : Option Form :=
  match Γ with
  | []                 => none
  | (.fvar y, A) :: Γ' => if y = x then some A else Ctx.lookup? Γ' x
  | _ :: Γ'            => Ctx.lookup? Γ' x

/-! ## Freshness, and lookup -/

theorem freshFor_notMem_of_mem_append {X Y : List String} {x : String}
    (h : freshFor (X ++ Y) = x) : x ∉ X ∧ x ∉ Y := by
  subst h
  have h := freshFor_notMem (X ++ Y)
  exact ⟨fun hm => h (List.mem_append.mpr (Or.inl hm)),
         fun hm => h (List.mem_append.mpr (Or.inr hm))⟩

theorem freshP_freshFor (Γ : Ctx) (p : Pf) :
    FreshP (freshFor (Ctx.fvP Γ ++ p.fvP)) Γ p :=
  freshFor_notMem_of_mem_append rfl

theorem freshI_freshFor (Γ : Ctx) (p : Pf) (A : Form) :
    FreshI (freshFor (Ctx.fvI Γ ++ p.fvI ++ A.fv)) Γ p A := by
  have h := freshFor_notMem (Ctx.fvI Γ ++ p.fvI ++ A.fv)
  refine ⟨fun hm => h ?_, fun hm => h ?_, fun hm => h ?_⟩
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hm)))
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm)))
  · exact List.mem_append.mpr (Or.inr hm)

/-- The `∃E` case chooses away from the goal as well, so the eigenvariable
condition comes for free. -/
theorem freshI_freshFor4 (Γ : Ctx) (p : Pf) (A K : Form) :
    FreshI (freshFor (Ctx.fvI Γ ++ p.fvI ++ A.fv ++ K.fv)) Γ p A ∧
      freshFor (Ctx.fvI Γ ++ p.fvI ++ A.fv ++ K.fv) ∉ K.fv := by
  have h := freshFor_notMem (Ctx.fvI Γ ++ p.fvI ++ A.fv ++ K.fv)
  refine ⟨⟨fun hm => h ?_, fun hm => h ?_, fun hm => h ?_⟩, fun hm => h ?_⟩
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inl hm)))))
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr hm)))))
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm)))
  · exact List.mem_append.mpr (Or.inr hm)

/-! ## Context lookup -/

/-- `Ctx.lookup?` only ever finds a *variable* entry, which is what `Derivable.var`
requires. -/
theorem lookup_mem {Γ : Ctx} {x : String} {A : Form} :
    Ctx.lookup? Γ x = some A → (Pf.fvar x, A) ∈ Γ := by
  induction Γ with
  | nil => intro h; simp [Ctx.lookup?] at h
  | cons e Γ' ih =>
    obtain ⟨q, B⟩ := e
    match q with
    | .fvar y =>
        intro h
        simp only [Ctx.lookup?] at h
        by_cases hy : y = x
        · subst hy
          simp at h
          subst h
          exact List.Mem.head _
        · rw [if_neg hy] at h
          exact List.Mem.tail _ (ih h)
    | .bvar _ | .star | .pair _ _ | .fst _ | .snd _ | .inl _ | .inr _
    | .caseOr _ _ _ | .lam _ | .app _ _ | .val _ _ | .letQ _ _ _ | .gen _
    | .inst _ _ | .pack _ _ | .caseEx _ _ | .exf _ _ =>
        intro h
        simp only [Ctx.lookup?] at h
        exact List.Mem.tail _ (ih h)

end LaxLogic.QLL
