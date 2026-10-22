import tools.Decide
import LaxLogic.PLL.SubTab.Sound

/-!
# Finite-model enumeration for `pllfast` and `refbench` (library, no `main`)

See `tools/SubTab/PllFast.lean` for the race.  Split out 2026-10-15 so that
`refbench` can import the enumeration (two root `main`s in one import
closure is an error).

## The original header of `pllfast`

(Changed 2026-10-22: the proof terms now come from the tableau, through
`PLLND.SubTab.termOf`, and the W-engine is a fallback that no longer runs
alongside the searches; see `tools/SubTab/PllFast.lean`.)

2026-10-15, after a benchmark of `lake exe pll` on closed cells:
the W-engine proves fast, but on some refutable cells its disproof side runs
out of memory, while direct enumeration of small models finds the
countermodel in milliseconds.

A sequent is unprovable exactly when it has a countermodel, so the two
searches are run together:

  * the W-engine (`FRJ.Arity.decideDataByEngine`, verified `checkClosed`), in a
    dedicated thread, exactly as `lake exe pll` runs it;
  * in the main thread, enumeration of finite rooted subframe models
    (W, ≤, S, V) smallest first: a root below a naturally labelled poset, every
    S ⊆ W, every persistent valuation of the atoms of the formula; the formula
    is evaluated on bitmasks.

The first verdict wins.  A model hit is written as a `Tab` with one fallible
top world (`Rm` reaches it exactly from the worlds outside `S`, so `◯φ` holds
at `x` iff `φ` holds at every S-point above `x`) and CONFIRMED by
`Tab.refutes`, the evaluator the kernel certificate runs; an unconfirmed hit
is reported as a tool defect and ignored.  ORDER (2026-10-15, measured on the
benchmark cells): the subframe refutation tableau (`tools/SubTab/Tableau.lean`)
first, for the verdict; then the enumeration, only over the sizes below the
tableau's minimised model (`--maxN`, default 5; `--cap`, default 50,000), to
shrink the certificate; the engine supplies proof terms (and decides alone
if both searches fail).
Output layer, exit codes and flags as `lake exe pll`, plus `--maxN=` and
`--cap=`.
-/

open FRJ FRJ.Search FRJ.Gbu FRJ.Gbu.W PLLND

namespace PllFast

/-! ## Finite rooted models on bitmasks -/

structure BM where
  n : Nat
  up : Array Nat          -- up-set of each world, as a mask (the world included)
  S : Nat                 -- the S-points
  val : List (String × Nat)

def fullM (n : Nat) : Nat := (1 <<< n) - 1

def BM.imp (m : BM) (a b : Nat) : Nat :=
  let bad := a &&& (fullM m.n ^^^ b)       -- worlds where a holds and b fails
  (List.range m.n).foldl (fun acc w =>
    if m.up[w]! &&& bad == 0 then acc ||| (1 <<< w) else acc) 0

def BM.box (m : BM) (a : Nat) : Nat :=
  let bad := m.S &&& (fullM m.n ^^^ a)
  (List.range m.n).foldl (fun acc w =>
    if m.up[w]! &&& bad == 0 then acc ||| (1 <<< w) else acc) 0

def BM.eval (m : BM) : PLLFormula → Nat
  | .prop a => (m.val.lookup a).getD 0
  | .falsePLL => 0
  | .and x y => m.eval x &&& m.eval y
  | .or x y => m.eval x ||| m.eval y
  | .ifThen x y => m.imp (m.eval x) (m.eval y)
  | .somehow x => m.box (m.eval x)

def hasBox : PLLFormula → Bool
  | .prop _ | .falsePLL => false
  | .and x y | .or x y | .ifThen x y => hasBox x || hasBox y
  | .somehow _ => true

def atomsL : PLLFormula → List String
  | .prop a => [a]
  | .falsePLL => []
  | .and x y | .or x y | .ifThen x y => atomsL x ++ atomsL y
  | .somehow x => atomsL x

/-- Naturally labelled posets on `0..m-1` (strict pairs `i < j`), as relations. -/
def posets (m : Nat) : List (List (Nat × Nat)) :=
  let pairs := (List.range m).flatMap fun i => ((List.range m).filter (i < ·)).map (i, ·)
  let all := (List.range (1 <<< pairs.length)).map fun mask =>
    (pairs.zipIdx.filter fun (_, k) => (mask >>> k) &&& 1 == 1).map (·.1)
  all.filter fun rel => rel.all fun (a, b) => rel.all fun (b', c) =>
    b != b' || rel.contains (a, c)

/-- The rooted poset on `n` worlds: world 0 below the poset `rel` on `1..n-1`. -/
def upsOf (n : Nat) (rel : List (Nat × Nat)) : Array Nat :=
  (List.range n).toArray.map fun w =>
    if w == 0 then fullM n
    else rel.foldl (fun acc (a, b) => if a + 1 == w then acc ||| (1 <<< (b + 1)) else acc)
      (1 <<< w)

def upSets (n : Nat) (up : Array Nat) : List Nat :=
  (List.range (1 <<< n)).filter fun U =>
    (List.range n).all fun w => (U >>> w) &&& 1 == 0 || up[w]! &&& U == up[w]!

/-- The table of a hit: worlds `0..n-1` plus a fallible top `n`. -/
def toTab (m : BM) (ats : List String) : Tab :=
  let f := m.n
  let bit (x w : Nat) : Bool := (x >>> w) &&& 1 == 1
  { n := f + 1, root := 0
    leT := (List.range (f + 1)).map fun i => (List.range (f + 1)).map fun j =>
      j == f || (i < f && j < f && bit m.up[i]! j)
    rmT := (List.range (f + 1)).map fun i => (List.range (f + 1)).map fun j =>
      i == j || (j == f && i < f && !bit m.S i)
    falT := (List.range (f + 1)).map (· == f)
    atomsT := (List.range (f + 1)).map fun w =>
      if w == f then ats else ats.filter fun a => bit ((m.val.lookup a).getD 0) w }

/-- The first valuation of `ats` by up-sets from `us` (extending `acc`) under
which `φ` fails at the root; streamed, never materialised (the list version
reached 4.4 GB on a five-atom cell). -/
def findVal (φ : PLLFormula) (n : Nat) (up : Array Nat) (S : Nat) (us : List Nat) :
    List String → List (String × Nat) → Option (List (String × Nat))
  | [], acc => if (BM.eval ⟨n, up, S, acc⟩ φ) &&& 1 == 0 then some acc else none
  | a :: as, acc => us.findSome? fun U => findVal φ n up S us as ((a, U) :: acc)

/-- Search one rooted frame; `none` if no model on it refutes `φ`.  The count
is the number of models the frame carries (all of them when there is no hit). -/
def searchFrame (φ : PLLFormula) (ats : List String) (n : Nat) (up : Array Nat) :
    Option BM × Nat :=
  let Ss := if hasBox φ then List.range (1 <<< n) else [0]
  let us := upSets n up
  let per := us.length ^ ats.length
  let rec go : List Nat → Nat → Option BM × Nat
    | [], c => (none, c)
    | S :: rest, c =>
      match findVal φ n up S us ats [] with
      | some v => (some ⟨n, up, S, v⟩, c + per)
      | none => go rest (c + per)
  go Ss 0

def firstHit (φ : PLLFormula) (maxN : Nat) : Option (Nat × BM) :=
  let ats := (atomsL φ).eraseDups
  (List.range' 1 maxN).findSome? fun n =>
    (posets (n - 1)).findSome? fun rel => ((searchFrame φ ats n (upsOf n rel)).1).map (n, ·)

/-- A model as `SubCM` tables (no fallible world), for the lean-certify
disprover `enum`. -/
def bmToSubCM (m : BM) (ats : List String) : PLLND.SubTab.SubCM :=
  { n := m.n, root := 0
    le := (List.range m.n).map fun i => (List.range m.n).map fun j => (m.up[i]! >>> j) &&& 1 == 1
    S := (List.range m.n).map fun i => (m.S >>> i) &&& 1 == 1
    val := (List.range m.n).map fun i =>
      ats.filter fun a => ((m.val.lookup a).getD 0 >>> i) &&& 1 == 1 }

/-- The first refuting model on at most `maxN` worlds within `cap` models. -/
def firstHitCap (φ : PLLFormula) (maxN cap : Nat) : Option BM :=
  let ats := (atomsL φ).eraseDups
  let frames := (List.range' 1 maxN).flatMap fun n => (posets (n - 1)).map fun rel => (n, upsOf n rel)
  let rec go : List (Nat × Array Nat) → Nat → Option BM
    | [], _ => none
    | (n, up) :: rest, c =>
      if c ≥ cap then none
      else match searchFrame φ ats n up with
        | (some m, _) => some m
        | (none, k) => go rest (c + k)
  go frames 0

end PllFast
