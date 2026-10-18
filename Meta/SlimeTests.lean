/-
Regression tests for `#slime` (Meta/Slime.lean), 2026-10-17.

Each family below puts one kind of index in a constructor's conclusion.
The expected verdicts were established by `cases` itself, against a
concrete index (`h : H "add"` and the like): where `cases` fails with
"Dependent elimination failed: Failed to solve equation", the index is
slime; where it succeeds, it is not.

| index                         | `cases` vs a concrete index | verdict |
|-------------------------------|-----------------------------|---------|
| `c.head` (projection)         | fails: `"add" = c.1`        | slime   |
| `headOf c`, `def := c.head`   | fails, same equation        | slime   |
| `headAb c`, `abbrev`          | fails, same equation        | slime   |
| `mkCl s`, `def := ⟨s, 0⟩`     | succeeds                    | clean   |
| `⟨s, 0⟩` (constructor)        | succeeds                    | clean   |
| `n + 1`                       | succeeds (offset)           | clean   |
| `double n`, `def := n + n`    | fails: `4 = n.add n`        | slime   |
| `0` (numeral)                 | succeeds                    | clean   |

Before the weak-head-normal-form change, `#slime` reported `mkCl s` and
the numeral `0` as slime.
-/
import Meta.Slime

namespace Audit.SlimeTests

structure Cl where
  head : String
  arity : Nat

def headOf (c : Cl) : String := c.head
abbrev headAb (c : Cl) : String := c.head
def mkCl (s : String) : Cl := ⟨s, 0⟩
def double (n : Nat) : Nat := n + n

inductive HProj : String → Prop where
  | fire (c : Cl) : HProj c.head
inductive HDef : String → Prop where
  | fire (c : Cl) : HDef (headOf c)
inductive HAbb : String → Prop where
  | fire (c : Cl) : HAbb (headAb c)
inductive HMk : Cl → Prop where
  | fire (s : String) : HMk (mkCl s)
inductive HCtor : Cl → Prop where
  | fire (s : String) : HCtor ⟨s, 0⟩
inductive HSucc : Nat → Prop where
  | fire (n : Nat) : HSucc (n + 1)
inductive HDouble : Nat → Prop where
  | fire (n : Nat) : HDouble (double n)
inductive HZero : Nat → Prop where
  | zero : HZero 0

/--
warning: Audit.SlimeTests.HProj — 1 indices, 1 constructors, 1 carrying green slime

  fire
    index 1  c.head
              ↳ computed by  Audit.SlimeTests.Cl.head
-/
#guard_msgs in
#slime HProj

/--
warning: Audit.SlimeTests.HDef — 1 indices, 1 constructors, 1 carrying green slime

  fire
    index 1  headOf c
              ↳ computed by  Audit.SlimeTests.headOf
-/
#guard_msgs in
#slime HDef

/--
warning: Audit.SlimeTests.HAbb — 1 indices, 1 constructors, 1 carrying green slime

  fire
    index 1  headAb c
              ↳ computed by  Audit.SlimeTests.headAb
-/
#guard_msgs in
#slime HAbb

/--
info: Audit.SlimeTests.HMk — 1 indices, 1 constructors, 0 carrying green slime

  clean: fire
-/
#guard_msgs in
#slime HMk

/--
info: Audit.SlimeTests.HCtor — 1 indices, 1 constructors, 0 carrying green slime

  clean: fire
-/
#guard_msgs in
#slime HCtor

/--
info: Audit.SlimeTests.HSucc — 1 indices, 1 constructors, 0 carrying green slime

  clean: fire
-/
#guard_msgs in
#slime HSucc

/--
warning: Audit.SlimeTests.HDouble — 1 indices, 1 constructors, 1 carrying green slime

  fire
    index 1  double n
              ↳ computed by  Audit.SlimeTests.double
-/
#guard_msgs in
#slime HDouble

/--
info: Audit.SlimeTests.HZero — 1 indices, 1 constructors, 0 carrying green slime

  clean: zero
-/
#guard_msgs in
#slime HZero

end Audit.SlimeTests
