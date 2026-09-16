/-
# Conservativity, and why most of it is free

Theorem 1 of Fairtlough–Mendler–Cheng states that the `p : M` construct is a
conservative extension of HOL. In Isabelle/HOL that has real content: Fig. 2
adds a grammar, Fig. 5 adds a natural deduction system, and one must check that
the new rules prove no new theorems of the old language.

**Over Lean the question has a different answer, and Matthew supplied it: the
base logic is Lean's own — higher-order dependent type theory, with `propext`
and `Quot.sound` if wanted, which come for free as with any axiomatic
extension.** Relative to that base, the theory half of this library is
conservative *by construction*: `LaxAll`, `LaxEx`, `val`, `pair`, `meet` and
`image` are ordinary definitions, and every rule the paper gives is an ordinary
theorem proved from them. Nothing was added to the logic, so nothing new can be
derived from it, and the certificate is the axiom pin — every declaration in
`Modality.lean` reports *does not depend on any axioms*, which is stronger than
the baseline Matthew allows.

That also relocates the content of Theorem 1 rather than discarding it. What the
paper proves once, about a system of rules, is here distributed over the rule
lemmas: `laxAll_pair`, `laxAll_image` and the rest each carry their own share,
and soundness of the rules is the fact that they are theorems at all.

## Where it is *not* free

The tactic half is a different matter. `postpone` and `postponing theorem` are
elaborators: they call `addDecl`, and `addDecl` has an `addAsAxiom` fallback
(`Lean/AddDecl.lean`) which fires when the kernel rejects a declaration. When it
fires, the name enters the environment **as an axiom**, and the extension stops
being conservative — silently. This is not hypothetical; it was observed during
development, and `#print axioms dataHole` read `[dataHole]`.

Two guards in `Postpone.lean` now prevent the two routes that were found. This
module supplies the check that the guards worked, as a gate rather than an
assurance: `#obligations_audit` walks the ledger and verifies that every
declaration the mechanism produced is a **theorem** and every obligation is a
**definition**, that none of them is an axiom, that no `sorryAx` survives, and
that no declaration rests on an axiom the mechanism itself introduced.

Run it at the end of any module that uses `postponing theorem`. It fails the
build rather than reporting.
-/

import LaxLogic.Obligation.Ledger

namespace LaxLogic.Obligation

open Lean Elab Command

/-- Every name the mechanism has introduced: the holed theorems and their
obligation constants. An axiom bearing one of these names is the signature of
`addDecl`'s `addAsAxiom` fallback having fired. -/
def ledgerNames (env : Environment) : Array Name := Id.run do
  let mut ns : Array Name := #[]
  for o in owedEntries env do
    ns := ns.push o.decl
    for e in o.obligations do
      ns := ns.push e.name
  return ns

/-- Audit the obligation ledger for conservativity over Lean's own logic.

Checks, for every declaration produced by `postponing theorem`:

* the declaration exists and is a **theorem**, not an axiom;
* each of its obligation constants exists and is a **definition**, not an axiom;
* it does not depend on `sorryAx` — a postponed proof must be genuinely
  complete in the part it claims to have proved;
* it does not depend on any axiom that the mechanism itself introduced, which
  is what `addDecl`'s `addAsAxiom` fallback would produce.

Axioms of the *base* theory are reported but permitted: `propext`,
`Quot.sound` and `Classical.choice` are part of the logic being extended, not
additions to it. The command throws on any violation, so it can be used as a
build gate. -/
elab "#obligations_audit" : command => do
  let env ← getEnv
  let entries := owedEntries env
  let introduced := ledgerNames env
  let mut bad : Array MessageData := #[]
  let mut lines : Array MessageData := #[]
  for o in entries do
    match env.find? o.decl with
    | none =>
        bad := bad.push m!"{o.decl}: recorded in the ledger but absent from the environment"
    | some (.axiomInfo _) =>
        bad := bad.push m!"{o.decl}: present as an AXIOM, not a theorem — \
          `addDecl`'s addAsAxiom fallback has fired and the extension is not \
          conservative"
    | some (.thmInfo _) => pure ()
    | some _ =>
        bad := bad.push m!"{o.decl}: present, but is neither a theorem nor an axiom"
    for e in o.obligations do
      match env.find? e.name with
      | none => bad := bad.push m!"{e.name}: obligation constant is missing"
      | some (.axiomInfo _) =>
          bad := bad.push m!"{e.name}: obligation present as an AXIOM, not a definition"
      | some (.defnInfo _) => pure ()
      | some _ => bad := bad.push m!"{e.name}: obligation is not a definition"
    let ax ← collectAxioms o.decl
    if ax.contains ``sorryAx then
      bad := bad.push m!"{o.decl}: depends on sorryAx — the proved part is not complete"
    for a in ax do
      if introduced.contains a then
        bad := bad.push m!"{o.decl}: rests on `{a}`, an axiom introduced by the \
          mechanism itself"
    lines := lines.push <|
      if ax.isEmpty then m!"  {o.decl} — no axioms"
      else m!"  {o.decl} — {ax.toList}"
  if !bad.isEmpty then
    throwError m!"conservativity audit FAILED:\n{MessageData.joinSep bad.toList "\n"}"
  if entries.isEmpty then
    logInfo "conservativity audit: nothing recorded"
  else
    logInfo m!"conservativity audit passed for {entries.size} declaration(s); \
      base-theory axioms only:\n{MessageData.joinSep lines.toList "\n"}"

end LaxLogic.Obligation
