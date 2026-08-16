/-
# FRJ◯ W2 — the indexed refutation calculus (PCLL-reduced instance)

The judgment `FRJD G b S` : a derivation that SOME world forces
`S.stable` and refutes `S.goal` — one constructor per rule, indexed by
its sequent, side conditions as decidable `= true` fields.  The
architecture is RK(Ξ)'s (CEUR 2214), with FRJ(G)'s irregular zones
replaced by explicit child premises: a `world` node assembles a fresh
root from child derivations (its Kripke successors), a cone
declaration (which children are `Rₘ`-successors) and an optional
fallible leaf — the ∀-obligations of `◯` discharged as decidable side
conditions against the declared cone, exactly the forward move.

Goal-discharge rules at the root: `orR`, `impIn`/`impOut`, `circIn`/
`circOut` — the ⊃∈/⊃∉ and ◯∈/◯∉ pairs of the plan.  `b` is the `Cl`
budget threaded through the side conditions; extraction (W3) never
trusts it.
-/
import FRJO.Seq

namespace FRJO

open PLLFormula

variable (G : Cell) (b : Nat)

/-- The root-assembly side condition for a `world` node: heredity of
the stable zone into every child, the ◯-positive obligations against
the declared cone, and the base-goal discharge.  Decidable by
construction; each conjunct is one FRJ side condition. -/
def worldOK (S : List PLLFormula) (C : PLLFormula)
    (kids : List (Reg G)) (cone : List Bool) (leaf : Bool) : Bool :=
  -- zones in the universe
  S.all (sfPlus G).contains && (sfPlus G).contains C &&
  -- heredity: the stable zone persists into every child
  kids.all (fun k => S.all (fun φ => (clB G b k.stable).contains φ)) &&
  -- the cone: the root's Rm-successors are itself, the declared
  -- children, and the leaf; ◯-POSITIVE obligation: every ◯A ∈ S is
  -- realised — by the leaf (fallible realises anything), or by a
  -- declared cone child forcing A, or by the root itself
  (S.all fun φ => match φ with
    | .somehow A =>
        leaf ||
        (List.zip kids cone).any (fun kc =>
          kc.2 && (clB G b kc.1.stable).contains A) ||
        (clB G b S).contains A
    | _ => true) &&
  -- the goal is NOT forced at the root: base shapes only (compound
  -- goals are discharged by their own rules before the world node)
  !(clB G b S).contains C &&
  -- and if the goal is a box ◯A, refuting it at the root's OWN cone:
  -- the cone (root + declared children + leaf) must MISS A — with a
  -- leaf present this is impossible, so a boxed goal forces leaf=false
  (match C with
    | .somehow A =>
        !leaf && !(clB G b S).contains A &&
        (List.zip kids cone).all (fun kc =>
          !kc.2 || !(clB G b kc.1.stable).contains A)
    | _ => true)

/-- **The calculus.**  `FRJD G b ⟨S, C⟩` derives "some world forces
`S`, refutes `C`". -/
inductive FRJD : Reg G → Type where
  /-- Refute a disjunction: both disjuncts refuted at the same world. -/
  | orR {S A B} : FRJD ⟨S, A⟩ → FRJD ⟨S, B⟩ → FRJD ⟨S, .or A B⟩
  /-- `⊃∈`: the refuting world is this one — the antecedent already
  holds here. -/
  | impIn {S A B} : FRJD ⟨S, B⟩ →
      (clB G b S).contains A = true → FRJD ⟨S, .ifThen A B⟩
  /-- `⊃∉`: the refuting world is strictly above — a child assuming
  `A` and refuting `B`; heredity is the world-node's business, so the
  child's stable zone must extend this world's. -/
  | impOut {S A B S'} : FRJD ⟨S', B⟩ →
      (clB G b S').contains A = true →
      S.all (fun φ => (clB G b S').contains φ) = true →
      FRJD ⟨S, .ifThen A B⟩
  /-- `◯∉`: the ◯-refuting witness is strictly above — a child
  refuting `◯A` (its own cone misses `A`). -/
  | circOut {S A S'} : FRJD ⟨S', .somehow A⟩ →
      S.all (fun φ => (clB G b S').contains φ) = true →
      FRJD ⟨S, .somehow A⟩
  /-- **The world node** — RK(Ξ)'s join.  Assemble a fresh root below
  the child worlds; `cone` declares which children are
  `Rₘ`-successors, `leaf` an optional fallible leaf above the root.
  Discharges base-shaped goals (atoms, `⊥`, and `◯A` refuted at THIS
  root — the `◯∈` case reads the declared cone).  `n = 0`, no leaf:
  the final-world axiom, RK's `⋈₀`. -/
  | world {S C} (kids : List (Reg G)) (cone : List Bool) (leaf : Bool)
      (prems : ∀ K ∈ kids, FRJD K)
      (ok : worldOK G b S C kids cone leaf = true) : FRJD ⟨S, C⟩

/-! ## The size measure (for W3's induction) -/

def FRJD.rank : {S : Reg G} → FRJD G b S → Nat
  | _, .orR d e => max d.rank e.rank
  | _, .impIn d _ => d.rank
  | _, .impOut d _ _ => d.rank + 1
  | _, .circOut d _ => d.rank + 1
  | _, .world (S := _) kids _ _ prems _ =>
      1 + kids.attach.foldl (fun a k => max a ((prems k.1 k.2).rank)) 0

end FRJO
