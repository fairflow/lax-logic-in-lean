/-
# Pinning a discovery: from a derivation to a kernel-checkable countermodel

The search is untrusted by design.  What makes a hit usable is that the
model it builds is finite and concrete, so the refutation can be re-checked
by the kernel without replaying the search: `Tab` is a model as plain
tables, `Tab.toKripke?` turns one into a `Kripke` (returning `none` unless
the frame conditions hold, so the check is part of the data), and
`FRJ.not_derivable_of_countermodel` converts non-validity into
underivability in the ORIGINAL PLL.

The extracted models are bigger than they need to be: a derivation builds a
world per rule application.  `minimise` removes worlds greedily as long as
what remains is still a model refuting the goal, which is what makes the
final `by decide` affordable.
-/
import FRJ.Search.Engine
import FRJ.Bridge

namespace FRJ.Search

/-! ## Models as tables -/

structure Tab where
  n : Nat
  root : Nat
  leT : List (List Bool)
  rmT : List (List Bool)
  falT : List Bool
  atomsT : List (List String)
  deriving Repr

namespace Tab

variable (T : Tab)

def leB (a b : Fin T.n) : Bool := (T.leT.getD a.val []).getD b.val false
def rmB (a b : Fin T.n) : Bool := (T.rmT.getD a.val []).getD b.val false
def falB (a : Fin T.n) : Bool := T.falT.getD a.val false
def atoms (a : Fin T.n) : List String := T.atomsT.getD a.val []

def idx : List (Fin T.n) := (List.range T.n).attach.map (fun x =>
  ⟨x.val, List.mem_range.mp x.property⟩)

theorem mem_idx (a : Fin T.n) : a ∈ T.idx := by
  simp only [idx, List.mem_map, List.mem_attach, true_and, Subtype.exists]
  exact ⟨a.val, List.mem_range.mpr a.isLt, rfl⟩

/-- Every frame condition a `Kripke` needs, as one decidable check.  The
root clause is stated at `Nat` level so that `okB` does not have to know
`root < n`; that is checked separately. -/
def okB : Bool :=
  T.idx.all (fun a => T.leB a a) &&
  T.idx.all (fun a => T.idx.all (fun b => T.idx.all (fun c =>
    !(T.leB a b && T.leB b c) || T.leB a c))) &&
  T.idx.all (fun a => T.idx.all (fun b =>
    !(T.leB a b && T.leB b a) || decide (a = b))) &&
  T.idx.all (fun a => T.rmB a a) &&
  T.idx.all (fun a => T.idx.all (fun b => T.idx.all (fun c =>
    !(T.rmB a b && T.rmB b c) || T.rmB a c))) &&
  T.idx.all (fun a => T.idx.all (fun b => !(T.rmB a b) || T.leB a b)) &&
  T.idx.all (fun a => T.idx.all (fun b =>
    !(T.leB a b && T.falB a) || T.falB b)) &&
  T.idx.all (fun a => T.idx.all (fun b =>
    !(T.leB a b) || (T.atoms a).all (fun p => (T.atoms b).contains p))) &&
  T.idx.all (fun a => (T.leT.getD T.root []).getD a.val false)

/-! ### Reading the conditions back off `okB` -/

theorem all_of_okB {p : Fin T.n → Bool} (h : T.idx.all p = true) (a : Fin T.n) :
    p a = true := List.all_eq_true.mp h a (T.mem_idx a)

theorem okB_le_refl (h : T.okB = true) (a : Fin T.n) : T.leB a a = true := by
  simp only [okB, Bool.and_eq_true] at h
  exact all_of_okB T h.1.1.1.1.1.1.1.1 a

theorem okB_le_trans (h : T.okB = true) {a b c : Fin T.n}
    (h1 : T.leB a b = true) (h2 : T.leB b c = true) : T.leB a c = true := by
  simp only [okB, Bool.and_eq_true] at h
  have := all_of_okB T (all_of_okB T (all_of_okB T h.1.1.1.1.1.1.1.2 a) b) c
  simp [h1, h2] at this; exact this

theorem okB_le_antisymm (h : T.okB = true) {a b : Fin T.n}
    (h1 : T.leB a b = true) (h2 : T.leB b a = true) : a = b := by
  simp only [okB, Bool.and_eq_true] at h
  have := all_of_okB T (all_of_okB T h.1.1.1.1.1.1.2 a) b
  simp [h1, h2] at this; exact this

theorem okB_rm_refl (h : T.okB = true) (a : Fin T.n) : T.rmB a a = true := by
  simp only [okB, Bool.and_eq_true] at h
  exact all_of_okB T h.1.1.1.1.1.2 a

theorem okB_rm_trans (h : T.okB = true) {a b c : Fin T.n}
    (h1 : T.rmB a b = true) (h2 : T.rmB b c = true) : T.rmB a c = true := by
  simp only [okB, Bool.and_eq_true] at h
  have := all_of_okB T (all_of_okB T (all_of_okB T h.1.1.1.1.2 a) b) c
  simp [h1, h2] at this; exact this

theorem okB_rm_sub (h : T.okB = true) {a b : Fin T.n}
    (h1 : T.rmB a b = true) : T.leB a b = true := by
  simp only [okB, Bool.and_eq_true] at h
  have := all_of_okB T (all_of_okB T h.1.1.1.2 a) b
  simp [h1] at this; exact this

theorem okB_fal_mono (h : T.okB = true) {a b : Fin T.n}
    (h1 : T.leB a b = true) (h2 : T.falB a = true) : T.falB b = true := by
  simp only [okB, Bool.and_eq_true] at h
  have := all_of_okB T (all_of_okB T h.1.1.2 a) b
  simp [h1, h2] at this; exact this

theorem okB_atoms_mono (h : T.okB = true) {a b : Fin T.n}
    (h1 : T.leB a b = true) {p : String} (hp : p ∈ T.atoms a) : p ∈ T.atoms b := by
  simp only [okB, Bool.and_eq_true] at h
  have := all_of_okB T (all_of_okB T h.1.2 a) b
  simp [h1] at this
  exact this p hp

theorem okB_root_le (h : T.okB = true) (hr : T.root < T.n) (a : Fin T.n) :
    T.leB ⟨T.root, hr⟩ a = true := by
  simp only [okB, Bool.and_eq_true] at h
  exact all_of_okB T h.2 a

/-! ### The model -/

/-- The `Kripke` model a well-formed table denotes.  `V a p` is
"`p` is labelled at `a`, or `a` is fallible", the shape `FRJ.toKripke`
uses, which is what makes `fal_V` hold. -/
def toKripke (h : T.okB = true) (hr : T.root < T.n) : Kripke where
  W := Fin T.n
  elems := T.idx
  complete := T.mem_idx
  decEq := inferInstance
  le := fun a b => T.leB a b = true
  le_refl := T.okB_le_refl h
  le_trans := fun h1 h2 => T.okB_le_trans h h1 h2
  le_antisymm := fun h1 h2 => T.okB_le_antisymm h h1 h2
  root := ⟨T.root, hr⟩
  root_le := T.okB_root_le h hr
  V := fun a p => p ∈ T.atoms a ∨ T.falB a = true
  V_mono := fun hab p hp => hp.elim
    (fun hm => Or.inl (T.okB_atoms_mono h hab hm))
    (fun hf => Or.inr (T.okB_fal_mono h hab hf))
  Rm := fun a b => T.rmB a b = true
  rm_refl := T.okB_rm_refl h
  rm_trans := fun h1 h2 => T.okB_rm_trans h h1 h2
  sub_mi := fun h1 => T.okB_rm_sub h h1
  Fal := fun a => T.falB a = true
  fal_mono := fun hab hf => T.okB_fal_mono h hab hf
  fal_V := fun hf _ => Or.inr hf
  decLe := fun _ _ => inferInstance
  decV := fun _ _ => inferInstance
  decRm := fun _ _ => inferInstance
  decFal := fun _ => inferInstance

def toKripke? : Option Kripke :=
  if h : T.okB = true ∧ T.root < T.n then some (T.toKripke h.1 h.2) else none

/-- Does the table denote a model that refutes `A` at its root? -/
def refutes (A : Form) : Bool :=
  match T.toKripke? with
  | none => false
  | some K => !(decide (K.force K.root A))

/-- Keep only the listed worlds. -/
def restrict (keep : List Nat) : Tab where
  n := keep.length
  root := keep.findIdx (fun i => i == T.root)
  leT := keep.map (fun a => keep.map (fun b => (T.leT.getD a []).getD b false))
  rmT := keep.map (fun a => keep.map (fun b => (T.rmT.getD a []).getD b false))
  falT := keep.map (fun a => T.falT.getD a false)
  atomsT := keep.map (fun a => T.atomsT.getD a [])

/-- Greedy minimisation: drop worlds while what is left is still a model
refuting `A`.  Dropping the root fails the frame check, so the root is
protected without a special case. -/
def minimise (A : Form) : Tab :=
  let rec go : Nat → List Nat → List Nat
    | 0, keep => keep
    | fuel + 1, keep =>
        match keep.find? (fun i => (T.restrict (keep.filter (fun j => j != i))).refutes A) with
        | none => keep
        | some i => go fuel (keep.filter (fun j => j != i))
  T.restrict (go T.n (List.range T.n))

end Tab

/-! ## Extraction -/

/-- Read a model off any `Kripke`, indexing worlds by position in `elems`
(duplicates removed).  `atomList` is the set of atoms the goal can see;
outside it the valuation is irrelevant to the refutation. -/
def tabOf (K : Kripke) (atomList : List String) : Tab :=
  let ws := K.elems.foldl
    (fun acc w => if acc.any (fun v => decide (v = w)) then acc else acc ++ [w]) []
  let idxOf : K.W → Nat := fun w => ws.findIdx (fun v => decide (v = w))
  { n := ws.length
    root := idxOf K.root
    leT := ws.map (fun a => ws.map (fun b => decide (K.le a b)))
    rmT := ws.map (fun a => ws.map (fun b => decide (K.Rm a b)))
    falT := ws.map (fun a => decide (K.Fal a))
    atomsT := ws.map (fun a => atomList.filter (fun p => decide (K.V a p))) }

/-- The atoms of a formula, for `tabOf`. -/
def atomsOf : Form → List String
  | .atom p => [p]
  | .bot => []
  | .and A B => atomsOf A ++ atomsOf B
  | .or A B => atomsOf A ++ atomsOf B
  | .imp A B => atomsOf A ++ atomsOf B
  | .circ A => atomsOf A

/-- Emit a table as Lean source. -/
def render (T : Tab) (nm : String) : String :=
  let bl := fun (l : List Bool) => "[" ++ String.intercalate ", " (l.map toString) ++ "]"
  let bll := fun (l : List (List Bool)) => "[" ++ String.intercalate ", " (l.map bl) ++ "]"
  let sl := fun (l : List String) => "[" ++ String.intercalate ", " (l.map (fun s => "\"" ++ s ++ "\"")) ++ "]"
  let sll := fun (l : List (List String)) => "[" ++ String.intercalate ", " (l.map sl) ++ "]"
  "def " ++ nm ++ " : FRJ.Search.Tab where\n" ++
  s!"  n := {T.n}\n" ++
  s!"  root := {T.root}\n" ++
  "  leT := " ++ bll T.leT ++ "\n" ++
  "  rmT := " ++ bll T.rmT ++ "\n" ++
  "  falT := " ++ bl T.falT ++ "\n" ++
  "  atomsT := " ++ sll T.atomsT ++ "\n"


end FRJ.Search
