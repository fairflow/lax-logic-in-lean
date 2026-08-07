import LaxLogic.PLLSearchCmd

/-!
# Erné's ABC applied to RN(◯,{})

Marcel Erné, *Nuclear ranges in implicative semilattices*, Algebra Universalis
83 (2022), art. 18.  For an implicative semilattice `A` and `a ∈ A` he studies
three families of l-ideals (§5), writing `xᵃ` for `x → a`:

    𝔞a = {a → x | x ∈ A}    basic open      (nucleus αₐ = a → ·)
    𝔟a = {x → a | x ∈ A}    boolean         (nucleus βₐ x = (x→a)→a)
    𝔠a = ↑a                 basic closed    (nucleus γₐ = a ∨ ·)

`A = RN(◯,{})`, the closed fragment of PLL, is a bounded Heyting LATTICE
(it has `∨`), but it is **not complete** and **not boolean** — the latter
because `⊬ ◯⊥ ∨ ¬◯⊥`, pinned in `wip/nisFig6.lean`.

## What this file probes

Erné's **Theorem 5.9**: for a Heyting semilattice `A` the following are
equivalent — `A` is a boolean lattice; `𝔟_A` is isotone; `𝔟_A : A → 𝒩A` is an
isomorphism; and several more.  His closing remark: *"It is quite surprising
that isotonicity of the map `𝔟_A` resp. `β_A` is already sufficient (and
necessary) for `A` to be a boolean lattice."*

Contrapositive, for us: since RN(◯,{}) is **not** boolean, `a ↦ 𝔟a` is **not
isotone** on it.  So there must exist `a ≤ b` and a `y` with

    y = (y → a) → a      but      y ≠ (y → b) → b,

i.e. `y ∈ 𝔟a ∖ 𝔟b` with `a ≤ b`.  Theorem 5.9 guarantees a witness exists but
does not name one.  This file names one and checks it.

The candidate is the smallest place the failure of booleanness lives:

    a = ⊥,   b = ◯⊥,   y = ¬◯⊥.

`𝔟⊥` is the set of regular elements (`y = ¬¬y`) — the booleanization, by the
Glivenko–Frink theorem Erné cites.  So the two things to check are that
`¬◯⊥` is regular, and that it is *not* fixed by `β_{◯⊥}`.

PROBE, not a theorem: `#eval` output is not kernel-checked.  Not registered in
`lakefile.toml`; run with `lake env lean wip/erneNuclei.lean`.
-/

open PLLFormula PLLND PLLND.Search

namespace ErneNuclei

/-- `◯⊥`. -/
def oBot : PLLFormula := falsePLL.somehow
/-- `x → a`, Erné's `xᵃ`. -/
def imp (x a : PLLFormula) : PLLFormula := x.ifThen a
/-- `¬x = x → ⊥`. -/
def neg (x : PLLFormula) : PLLFormula := imp x falsePLL
/-- `βₐ x = (x → a) → a`. -/
def beta (a x : PLLFormula) : PLLFormula := imp (imp x a) a

/-- `y = ¬◯⊥`, the candidate witness. -/
def y : PLLFormula := neg oBot

/-- Interderivability, both directions, by certificate-carrying search. -/
def interd (A B : PLLFormula) : String :=
  let f := fun (P Q : PLLFormula) =>
    match settle budgetedConfig [P] Q with
    | .proved _      => "Y"
    | .refuted _ _ _ => "."
    | .unknown       => "?"
  f A B ++ f B A

def report : String :=
  String.intercalate "\n"
    [ "A is not boolean:      ⊢ ◯⊥ ∨ ¬◯⊥                " ++
        (match settle budgetedConfig [] (oBot.or y) with
         | .proved _ => "derivable" | .refuted _ _ _ => "REFUTED" | .unknown => "?")
    , "y regular (y ∈ 𝔟⊥):    ¬◯⊥ ⊣⊢ β_⊥(¬◯⊥) = ¬¬¬◯⊥   " ++ interd y (beta falsePLL y)
    , "y ∈ 𝔟◯⊥ ?             ¬◯⊥ ⊣⊢ β_◯⊥(¬◯⊥)          " ++ interd y (beta oBot y)
    , "  (the two halves separately, ⊢ then ⊣)"
    , "    ¬◯⊥ ⊢ (¬◯⊥→◯⊥)→◯⊥                            " ++
        (match settle budgetedConfig [y] (beta oBot y) with
         | .proved _ => "Y" | .refuted _ _ _ => "." | .unknown => "?")
    , "    (¬◯⊥→◯⊥)→◯⊥ ⊢ ¬◯⊥                            " ++
        (match settle budgetedConfig [beta oBot y] y with
         | .proved _ => "Y" | .refuted _ _ _ => "." | .unknown => "?")
    , "β_◯⊥(¬◯⊥) vs ⊤:        (¬◯⊥→◯⊥)→◯⊥ ⊣⊢ ⊤          " ++ interd (beta oBot y) truePLL ]

/-! ### Where the witness lives

`β_◯⊥(¬◯⊥) = (¬◯⊥→◯⊥)→◯⊥` is closed and `∨`-free, so by Bezhanishvili et al.
Theorem 9.3 (`wip/nisFig6.lean`) it must be interderivable with one of the
eight elements of their Figure 6.  Which one? -/

def fig6 : List (String × PLLFormula) :=
  [ ("⊥",              falsePLL)
  , ("◯⊥",             oBot)
  , ("¬◯⊥",            y)
  , ("¬¬◯⊥",           neg y)
  , ("◯¬◯⊥",           y.somehow)
  , ("¬¬◯⊥⊃◯⊥",        imp (neg y) oBot)
  , ("(¬¬◯⊥⊃◯⊥)⊃◯¬◯⊥", imp (imp (neg y) oBot) y.somehow)
  , ("⊤",              truePLL) ]

def locate : String :=
  let w := beta oBot y
  String.intercalate "\n"
    (fig6.map (fun (nm, e) => "  β_◯⊥(¬◯⊥) ⊣⊢ " ++ nm ++ "  " ++ interd w e))

end ErneNuclei

#eval IO.println ErneNuclei.report
#eval IO.println ErneNuclei.locate
