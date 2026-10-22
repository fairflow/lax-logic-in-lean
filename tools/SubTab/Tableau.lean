import tools.SubTab.ModelEnum
import LaxLogic.PLL.SubTab.Sound
import Std.Data.HashMap

/-!
# A goal-directed refutation tableau for subframe semantics (library, no `main`)

2026-10-15, at Matthew's request ("we do need a new refuter based
on subframes").  UNTRUSTED search: every model it returns is confirmed by
`Tab.refutes` (the evaluator of the kernel certificate) before use.

Subframe models: x ⊩ ◯A iff A holds at every S-point above x.  A world
carries signed formulas, T (true there) and F (false there).

* Inside a world (invertible): T(A∧B) gives T A, T B; T(A∨B) branches;
  T(A ↠ B) branches T B | F A and is carried up; T◯A gives T A at an
  S-point; F(A∨B) gives F A, F B; F(A∧B) branches; F(A ↠ B) with A already
  true gives F B (persistence: B true here would make B true wherever A is);
  F◯A at an S-point gives F A (likewise).  T p with F p, or T ⊥, closes.
* New worlds, only on demand: F(A ↠ B) with A not true makes a world above,
  outside S, with T A, F B and all of T; F◯A at a world outside S makes an
  S-point above with F A and all of T.
* Depth-first, with backtracking over the branches of each world; a world is
  open when all its demands have open worlds.

Termination: along a chain T never shrinks, an S-point creates only worlds
whose T grows, and a world outside S creates a world with equal T only as
an S-point; so T grows at least every second step and the depth is at most
twice the number of subformulas.  Completeness: a countermodel guides every
choice (each new world corresponds to a witness in it).  Both are paper
arguments; the confirmation by `Tab.refutes` is what the tool relies on.
-/

open FRJ FRJ.Search PLLND

namespace SubTab

inductive K where
  | atom (s : String) | bot | conj (a b : Nat) | disj (a b : Nat) | imp (a b : Nat) | box (a : Nat)
  deriving BEq, Hashable, Inhabited

structure Tbl where
  nodes : Array K := #[]
  ids : Std.HashMap K Nat := {}

def Tbl.add (t : Tbl) (k : K) : Tbl × Nat :=
  match t.ids[k]? with
  | some i => (t, i)
  | none => ({ nodes := t.nodes.push k, ids := t.ids.insert k t.nodes.size }, t.nodes.size)

/-- Intern the subformulas: equal subformulas get one index. -/
def intern : PLLFormula → Tbl → Tbl × Nat
  | .prop s, t => t.add (.atom s)
  | .falsePLL, t => t.add .bot
  | .and a b, t => let (t, i) := intern a t; let (t, j) := intern b t; t.add (.conj i j)
  | .or a b, t => let (t, i) := intern a t; let (t, j) := intern b t; t.add (.disj i j)
  | .ifThen a b, t => let (t, i) := intern a t; let (t, j) := intern b t; t.add (.imp i j)
  | .somehow a, t => let (t, i) := intern a t; t.add (.box i)

structure Node where
  isS : Bool
  atoms : List String
  kids : List Node
  deriving Inhabited

@[inline] def has (x i : Nat) : Bool := (x >>> i) &&& 1 == 1
def bitsOf (x n : Nat) : List Nat := (List.range n).filter (has x)

section
variable (tb : Array K)

/-- Saturate one world, depth-first over the branches; `k` receives each
saturated (T, F) in turn and decides whether the world is open. -/
partial def sat (isS : Bool) (T F : Nat) : List Nat → List Nat →
    (Nat → Nat → Option Node) → Option Node
  | [], [], k => k T F
  | i :: tt, tf, k =>
    if has T i then sat isS T F tt tf k
    else if has F i then none
    else
      let T := T ||| (1 <<< i)
      match tb[i]! with
      | .atom _ => sat isS T F tt tf k
      | .bot => none
      | .conj a b => sat isS T F (a :: b :: tt) tf k
      | .disj a b => (sat isS T F (a :: tt) tf k).orElse fun _ => sat isS T F (b :: tt) tf k
      | .imp a b =>
          if has T b || has F a then sat isS T F tt tf k
          else (sat isS T F (b :: tt) tf k).orElse fun _ => sat isS T F tt (a :: tf) k
      | .box a => if isS then sat isS T F (a :: tt) tf k else sat isS T F tt tf k
  | [], i :: tf, k =>
    if has F i then sat isS T F [] tf k
    else if has T i then none
    else
      let F := F ||| (1 <<< i)
      match tb[i]! with
      | .atom _ | .bot => sat isS T F [] tf k
      | .conj a b => (sat isS T F [] (a :: tf) k).orElse fun _ => sat isS T F [] (b :: tf) k
      | .disj a b => sat isS T F [] (a :: b :: tf) k
      | .imp a b => if has T a then sat isS T F [] (b :: tf) k else sat isS T F [] tf k
      | .box a => if isS then sat isS T F [] (a :: tf) k else sat isS T F [] tf k

mutual
/-- An open world refuting the given signed formulas, or `none`. -/
partial def world (isS : Bool) (initT initF : List Nat) : Option Node :=
  sat tb isS 0 0 initT initF (finish isS)

/-- A saturated world: finish the late local rules, then serve the demands. -/
partial def finish (isS : Bool) (T F : Nat) : Option Node :=
  let n := tb.size
  let pend := (bitsOf F n).filterMap fun i => match tb[i]! with
    | .imp a b => if has T a && !has F b then some b else none
    | _ => none
  if !pend.isEmpty then sat tb isS T F [] pend (finish isS)
  else
    let tl := bitsOf T n
    let demands := (bitsOf F n).filterMap fun i => match tb[i]! with
      | .imp a b => if has T a then none else some (false, tl ++ [a], [b])
      | .box a => if isS then none else some (true, tl, [a])
      | _ => none
    let ats := tl.filterMap fun i => match tb[i]! with | .atom s => some s | _ => none
    (demands.mapM fun (s, t, f) => world s t f).map fun ks => ⟨isS, ats, ks⟩
end
end

/-- Preorder flattening: each world with its ancestors. -/
partial def flatten (nd : Node) (anc : List Nat) (acc : Array (Bool × List String × List Nat)) :
    Array (Bool × List String × List Nat) :=
  let i := acc.size
  nd.kids.foldl (fun acc k => flatten k (i :: anc) acc) (acc.push (nd.isS, nd.atoms, anc))

/-- The tree as a `Tab`, plus one fallible top world reached by `Rm` from the
worlds outside S. -/
def toTab (nd : Node) (allAtoms : List String) : Tab :=
  let ws := flatten nd [] #[]
  let N := ws.size
  let le (i j : Nat) : Bool := i == j || (ws[j]!.2.2).contains i
  { n := N + 1, root := 0
    leT := (List.range (N + 1)).map fun i => (List.range (N + 1)).map fun j =>
      j == N || (i < N && j < N && le i j)
    rmT := (List.range (N + 1)).map fun i => (List.range (N + 1)).map fun j =>
      i == j || (j == N && i < N && !ws[i]!.1)
    falT := (List.range (N + 1)).map (· == N)
    atomsT := (List.range (N + 1)).map fun w => if w == N then allAtoms else ws[w]!.2.1 }

/-- The tableau's countermodel for `⊬ φ`, as a table (untrusted; confirm it
with `Tab.refutes`).  `none` means the search closed: by the paper argument,
`φ` is provable. -/
def refute (φ : PLLFormula) : Option Tab :=
  let (tbl, root) := intern φ {}
  (world tbl.nodes false [] [root]).map fun nd => toTab nd (PllFast.atomsL φ).eraseDups

/-! ## The certificate-producing search (the producer of the lean-certify engine)

The same search, now returning a certificate either way: a closed tableau
(`PLLND.SubTab.TCert`) when it closes, the open tree when it does not.  Each
rule application wraps the result in the matching constructor, so the
certificate's sequents grow exactly as the checker's do; formulas are named
by value (`formsOf`). -/

/-- The formulas of the table, by index (children come before parents). -/
def formsOf (tb : Array K) : Array PLLFormula :=
  tb.foldl (fun acc k => acc.push (match k with
    | .atom s => .prop s
    | .bot => .falsePLL
    | .conj a b => .and acc[a]! acc[b]!
    | .disj a b => .or acc[a]! acc[b]!
    | .imp a b => .ifThen acc[a]! acc[b]!
    | .box a => .somehow acc[a]!)) #[]

open PLLND.SubTab (TCert SubCM) in
/-- The outcome of the search: a closed tableau or an open tree. -/
inductive Res where
  | closed (c : PLLND.SubTab.TCert)
  | opn (n : Node)
  deriving Inhabited

def Res.wrap (f : PLLND.SubTab.TCert → PLLND.SubTab.TCert) : Res → Res
  | .closed c => .closed (f c)
  | r => r

section
variable (tb : Array K) (fs : Array PLLFormula)

/-- Saturate one world, recording the rules. -/
partial def satC (isS : Bool) (T F : Nat) : List Nat → List Nat → (Nat → Nat → Res) → Res
  | [], [], k => k T F
  | i :: tt, tf, k =>
    if has T i then satC isS T F tt tf k
    else if has F i then .closed (.ax fs[i]!)
    else
      let T := T ||| (1 <<< i)
      match tb[i]! with
      | .atom _ => satC isS T F tt tf k
      | .bot => .closed .bot
      | .conj a b => (satC isS T F (a :: b :: tt) tf k).wrap (.andL fs[a]! fs[b]!)
      | .disj a b =>
          match satC isS T F (a :: tt) tf k with
          | .closed c₁ =>
            match satC isS T F (b :: tt) tf k with
            | .closed c₂ => .closed (.orL fs[a]! fs[b]! c₁ c₂)
            | r => r
          | r => r
      | .imp a b =>
          if has T b || has F a then satC isS T F tt tf k
          else
            match satC isS T F (b :: tt) tf k with
            | .closed c₂ =>
              match satC isS T F tt (a :: tf) k with
              | .closed c₁ => .closed (.impL fs[a]! fs[b]! c₁ c₂)
              | r => r
            | r => r
      | .box a =>
          if isS then (satC isS T F (a :: tt) tf k).wrap (.boxL fs[a]!)
          else satC isS T F tt tf k
  | [], i :: tf, k =>
    if has F i then satC isS T F [] tf k
    else if has T i then .closed (.ax fs[i]!)
    else
      let F := F ||| (1 <<< i)
      match tb[i]! with
      | .atom _ | .bot => satC isS T F [] tf k
      | .conj a b =>
          match satC isS T F [] (a :: tf) k with
          | .closed c₁ =>
            match satC isS T F [] (b :: tf) k with
            | .closed c₂ => .closed (.andR fs[a]! fs[b]! c₁ c₂)
            | r => r
          | r => r
      | .disj a b => (satC isS T F [] (a :: b :: tf) k).wrap (.orR fs[a]! fs[b]!)
      | .imp a b =>
          if has T a then (satC isS T F [] (b :: tf) k).wrap (.impLoc fs[a]! fs[b]!)
          else satC isS T F [] tf k
      | .box a =>
          if isS then (satC isS T F [] (a :: tf) k).wrap (.boxLoc fs[a]!)
          else satC isS T F [] tf k

mutual
/-- A world: closed tableau or open subtree. -/
partial def worldC (isS : Bool) (initT initF : List Nat) : Res :=
  satC tb fs isS 0 0 initT initF (finishC isS)

/-- A saturated world: the late local rule, then the demands. -/
partial def finishC (isS : Bool) (T F : Nat) : Res :=
  let n := tb.size
  let late := (bitsOf F n).findSome? fun i => match tb[i]! with
    | .imp a b => if has T a && !has F b then some (a, b) else none
    | _ => none
  match late with
  | some (a, b) => (satC tb fs isS T F [] [b] (finishC isS)).wrap (.impLoc fs[a]! fs[b]!)
  | none =>
    let tl := bitsOf T n
    let ats := tl.filterMap fun i => match tb[i]! with | .atom s => some s | _ => none
    let demands : List (Bool × List Nat × List Nat × (PLLND.SubTab.TCert → PLLND.SubTab.TCert)) :=
      (bitsOf F n).filterMap fun i => match tb[i]! with
        | .imp a b => if has T a then none else some (false, tl ++ [a], [b], .impR fs[a]! fs[b]!)
        | .box a => if isS then none else some (true, tl, [a], .boxR fs[a]!)
        | _ => none
    serve isS ats demands []

/-- Serve the demands: the first closed one closes the world. -/
partial def serve (isS : Bool) (ats : List String) :
    List (Bool × List Nat × List Nat × (PLLND.SubTab.TCert → PLLND.SubTab.TCert)) →
    List Node → Res
  | [], acc => .opn ⟨isS, ats, acc.reverse⟩
  | (s, t, f, w) :: ds, acc =>
    match worldC s t f with
    | .closed c => .closed (w c)
    | .opn nd => serve isS ats ds (nd :: acc)
end
end

/-- An open tree as tables: the worlds in preorder, ordered by ancestry. -/
def toSubCM (nd : Node) : PLLND.SubTab.SubCM :=
  let ws := flatten nd [] #[]
  let N := ws.size
  { n := N, root := 0
    le := (List.range N).map fun i => (List.range N).map fun j =>
      i == j || (ws[j]!.2.2).contains i
    S := (List.range N).map fun i => ws[i]!.1
    val := (List.range N).map fun i => ws[i]!.2.1 }

/-- **The producer**: a closed tableau for `⊢ φ`, or a finite subframe
countermodel. Untrusted; the certifiers judge. -/
def solve (φ : PLLFormula) : Except PLLND.SubTab.SubCM PLLND.SubTab.TCert :=
  let (tbl, root) := intern φ {}
  match worldC tbl.nodes (formsOf tbl.nodes) false [] [root] with
  | .closed c => .ok c
  | .opn nd => .error (toSubCM nd)

/-! ## Minimisation and source (lean-certify R6 and the splice) -/

/-- Keep only the listed worlds (untrusted; the certifier judges the result). -/
def restrictCM (m : PLLND.SubTab.SubCM) (keep : List Nat) : PLLND.SubTab.SubCM :=
  { n := keep.length, root := keep.findIdx (· == m.root)
    le := keep.map fun a => keep.map fun b => m.leB a b
    S := keep.map m.SB
    val := keep.map fun a => m.val.getD a [] }

/-- Greedy minimisation (R6): drop worlds while the tables still refute `φ`. -/
def minimiseCM (m : PLLND.SubTab.SubCM) (φ : PLLFormula) : PLLND.SubTab.SubCM :=
  let rec go : Nat → List Nat → List Nat
    | 0, keep => keep
    | fuel + 1, keep =>
      match keep.find? (fun i => (restrictCM m (keep.filter (· != i))).refutes φ) with
      | none => keep
      | some i => go fuel (keep.filter (· != i))
  restrictCM m (go m.n (List.range m.n))

/-- A closed tableau as Lean source (expected type `TCert`). -/
def tcertSrc : PLLND.SubTab.TCert → String
  | .bot => ".bot"
  | .ax A => s!"(.ax {PLLTools.srcOfP A})"
  | .andL A B c => s!"(.andL {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c})"
  | .orL A B c₁ c₂ => s!"(.orL {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c₁} {tcertSrc c₂})"
  | .impL A B c₁ c₂ => s!"(.impL {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c₁} {tcertSrc c₂})"
  | .boxL A c => s!"(.boxL {PLLTools.srcOfP A} {tcertSrc c})"
  | .andR A B c₁ c₂ => s!"(.andR {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c₁} {tcertSrc c₂})"
  | .orR A B c => s!"(.orR {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c})"
  | .impLoc A B c => s!"(.impLoc {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c})"
  | .boxLoc A c => s!"(.boxLoc {PLLTools.srcOfP A} {tcertSrc c})"
  | .impR A B c => s!"(.impR {PLLTools.srcOfP A} {PLLTools.srcOfP B} {tcertSrc c})"
  | .boxR A c => s!"(.boxR {PLLTools.srcOfP A} {tcertSrc c})"

/-- Countermodel tables as Lean source (expected type `SubCM`). -/
def subcmSrc (m : PLLND.SubTab.SubCM) : String :=
  s!"\{ n := {m.n}, root := {m.root}, le := {m.le}, S := {m.S}, val := {repr m.val} }"

end SubTab
