import LaxLogic.PLL.Syntax.Formula
import Meta.Audit

/-!
# Concrete syntax of PLL formulas: the parser and the Lean-source printer

The formula parser of `lake exe pll` and of the tools built on it (`pllfast`,
`subtabdecide`, `refbench`), and `srcOfP`, which prints a formula as fully
qualified Lean source.  Moved here from `tools/Decide.lean` on 2026-10-27 (F0
re-implementation plan, step 3), names unchanged, so that the subframe
tableau's decider and its certificate printers need no `tools/` module.

One change in the move: the parser builds `PLLFormula` directly, where it built
FRJ's `Form` and read it back with `FRJ.toPLL`.  The two types are isomorphic
constructor for constructor (`FRJ/Bridge.lean`), so the parsed formula is the
same; the old and new parsers were compared on designed strings, every token
and both error paths, before the old one was removed.

Axioms.  `parseFormula` reaches `Classical.choice` through `String.toList`, in
Lean's core (the UTF-8 decoding lemmas); so do `String.foldl`, `String.foldr`,
the string iterator and `String.Pos.Raw.get`, every way of reading the
characters of a `String` that was tried.  That is why this module is not in the
`SubTab` library, whose declarations are all within `[propext, Quot.sound]`.
`srcOfP` is within `[propext]`.
-/

namespace PLLTools

/-! ## 1. Parsing (the `frjcert` grammar, atoms only — no `q<k>` names) -/

inductive Tok where
  | lp | rp | bot | top | neg | box | conj | disj | imp
  | id (s : String)
  deriving BEq, Repr

def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

partial def tokenize (cs : List Char) : Except String (List Tok) :=
  match cs with
  | [] => .ok []
  | c :: rest =>
    if c == ' ' || c == '\t' then tokenize rest
    else if c == '(' then (tokenize rest).map (.lp :: ·)
    else if c == ')' then (tokenize rest).map (.rp :: ·)
    else if c == '⊥' then (tokenize rest).map (.bot :: ·)
    else if c == '⊤' then (tokenize rest).map (.top :: ·)
    else if c == '¬' || c == '~' then (tokenize rest).map (.neg :: ·)
    else if c == '◯' || c == '#' then (tokenize rest).map (.box :: ·)
    else if c == '∧' || c == '&' then (tokenize rest).map (.conj :: ·)
    else if c == '⊃' || c == '→' then (tokenize rest).map (.imp :: ·)
    else if c == '∨' then (tokenize rest).map (.disj :: ·)
    else if c == '|' then (tokenize rest).map (.disj :: ·)
    else if c == '-' then
      match rest with
      | '>' :: r => (tokenize r).map (.imp :: ·)
      | _ => .error "stray '-'"
    else if isIdChar c then
      let name := String.ofList (c :: rest.takeWhile isIdChar)
      (tokenize (rest.dropWhile isIdChar)).map (.id name :: ·)
    else .error s!"unexpected character '{c}'"

mutual

partial def pImp (ts : List Tok) : Except String (PLLFormula × List Tok) := do
  let (a, ts) ← pDisj ts
  match ts with
  | .imp :: r => let (b, r) ← pImp r; pure (.ifThen a b, r)
  | _ => pure (a, ts)

partial def pDisj (ts : List Tok) : Except String (PLLFormula × List Tok) := do
  let (a, ts) ← pConj ts
  match ts with
  | .disj :: r => let (b, r) ← pDisj r; pure (.or a b, r)
  | _ => pure (a, ts)

partial def pConj (ts : List Tok) : Except String (PLLFormula × List Tok) := do
  let (a, ts) ← pUn ts
  match ts with
  | .conj :: r => let (b, r) ← pConj r; pure (.and a b, r)
  | _ => pure (a, ts)

partial def pUn (ts : List Tok) : Except String (PLLFormula × List Tok) := do
  match ts with
  | .neg :: r => let (a, r) ← pUn r; pure (.ifThen a .falsePLL, r)
  | .box :: r => let (a, r) ← pUn r; pure (.somehow a, r)
  | .bot :: r => pure (.falsePLL, r)
  | .top :: r => pure (.ifThen .falsePLL .falsePLL, r)
  | .id s :: r => pure (.prop s, r)
  | .lp :: r => do
      let (a, r) ← pImp r
      match r with
      | .rp :: r' => pure (a, r')
      | _ => .error "expected ')'"
  | _ => .error "expected a formula"

end

def parseFormula (s : String) : Except String PLLFormula := do
  let ts ← tokenize s.toList
  let (g, r) ← pImp ts
  if r.isEmpty then pure g else .error "trailing tokens after the formula"

/-- A `PLLFormula` as fully qualified Lean source (as
`PLLND.Search.srcOf`, copied here to keep the search engine out of the
decider's import graph). -/
def srcOfP : PLLFormula → String
  | .prop a      => s!"(PLLFormula.prop \"{a}\")"
  | .falsePLL    => "PLLFormula.falsePLL"
  | .and A B     => s!"({srcOfP A}.and {srcOfP B})"
  | .or A B      => s!"({srcOfP A}.or {srcOfP B})"
  | .ifThen A B  => s!"({srcOfP A}.ifThen {srcOfP B})"
  | .somehow A   => s!"({srcOfP A}.somehow)"

/-! ## Axiom pins -/

#axioms_within srcOfP [propext]
#axioms_within parseFormula [propext, Classical.choice, Quot.sound]

end PLLTools
