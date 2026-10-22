# Are the 22 ρ minimal? A test of the accepted-forms rule (2026-10-22)

The question comes from METHOD-F0.md §1 C and invariant 5: is each
ρ-representative of `LaxLogic/RN/Rho.lean` the minimal known member of its
class under the order

    (◯-depth, size), compared lexicographically

where size counts the nodes of the unabbreviated tree (`¬A` is `A ↠ ⊥`, and
`⊤` is `⊥ ↠ ⊥`, of size 3)?  The test is read-only and cheap.  It was
watched failing: with ◯-depth disabled, its self-test reports 6 failures.

**Script:** `scripts/f0_min_forms.py`.

**Known members of a class**, from two sources kept apart:

* **K, kernel-checked.**
  * the RNDB `interd` entries, closed by union-find;
  * equal one-pass `Rewrite.canon` forms.  These rest on the theorem
    `canon_interd`, which is pinned with `Classical.choice`.
* **C, computed only.**  Spike S2's decider verdicts (G4c proof terms and
  FinCM models, not re-checked by the kernel): a formula `X` of S2's test
  set T2 with `[X] ⊢ ρ` and `[ρ] ⊢ X`.

**Limitation.**  These are the *known* members only.  The test enumerates
no formula space (CLAUDE.md rule 9), so a smaller member that the
database has never seen cannot be found this way.  Coverage is uneven:
* ρ0–ρ12 and ρ14 have 16 to 120 known members;
* ρ13 and ρ15–ρ21 have only 2 or 3.

## Result

| | ρ |
|---|---|
| beaten on (◯-depth, size) by a known member | **none** |
| the unique minimum among the known members | ρ0, ρ1, ρ2, ρ3, ρ5, ρ7, ρ8, ρ12 |
| minimal, but tied with another known member | ρ4, ρ6, ρ9, ρ10, ρ11, ρ13, ρ14, ρ15, ρ16, ρ17, ρ18, ρ19, ρ20, ρ21 |

So **every ρ is minimal on (◯-depth, size) among the known members.**  What
differs between the ties is only the tie-break.

**The ties.**  In 13 of the 14 tied classes, the tied members are the same
formula with the disjuncts of some `∨` in the other order.  They are
`canon`'s output, which sorts disjuncts:

    ρ4  = ◯⊥ ∨ ¬◯⊥         tied with   ¬◯⊥ ∨ ◯⊥                 (1, 7)
    ρ15 = (◯¬◯⊥ ↠ ◯⊥ ∨ ¬◯⊥) ∨ ◯¬◯⊥
                            tied with   ◯¬◯⊥ ∨ (◯¬◯⊥ ↠ ◯⊥ ∨ ¬◯⊥)   (2, 19)

One tie is structural, in the class of ρ14, at weight (2, 20):

    ρ14             = ◯¬◯⊥ ∨ ¬¬◯⊥   ↠  ◯⊥ ∨ ¬◯⊥        ◯-scope  8
    a known member  = ◯(¬◯⊥ ∨ ¬¬◯⊥) ↠  ◯⊥ ∨ ¬◯⊥        ◯-scope 15

The second antecedent is `◯ρ6`, which is q12.  So `q12 ↠ ρ4` is
interderivable with `ρ9 ↠ ρ4`, and that equivalence is kernel-checked.

**Matthew's ruling on this tie (2026-10-22).**  The first formula is the
simpler, because the scopes of ◯ are smaller; a normalisation routine
would simplify the `◯(_ ∨ _)` bracket.  This is now a third component of
the weight, **◯-scope**: the sum, over the ◯ nodes, of the size of the
formula under each ◯.

    weight = (◯-depth, size, ◯-scope), compared lexicographically

Re-run with that weight:
* no ρ is beaten by any known member;
* the ρ14 tie goes to ρ14 (8 against 15);
* every remaining tie is a reordering of `∨` only, with equal ◯-scope.

The alternative, ◯-scope before size, would also replace ρ19
(`(◯¬◯⊥ ↠ ◯⊥ ∨ ¬◯⊥) ↠ ◯¬◯⊥`, weight (2, 19, 12)) by the computed member
`(◯¬◯⊥ ↠ ◯⊥ ∨ ¬◯⊥) ↠ ◯⊥ ∨ ¬◯⊥`, which is longer (size 21, ◯-scope 9).
That is why ◯-scope is placed after size.

## Consequence for the tie rule

With ◯-scope in the weight, 13 ties remain, all reorderings of `∨`.  Any
purely syntactic tie-break re-points them.  The order used here
(constructor rank, then children) re-points all 13, each only to reorder
a disjunction.  That would be a change for no gain
(§1 D).  The proposal is therefore that **ties go to the incumbent**, so
that a representative changes only for a strictly smaller member.  The
fixed syntactic order is then needed only for a class with no incumbent.
Under that rule, **all 22 ρ stand as the representatives.**  This proposal
is METHOD-F0.md §8, question 5, and is for Matthew to decide.

The ρ-labels name the classes for now.  They are labels in the historical
order of discovery, not the systematic numbering of METHOD-F0 §1 E,
which is §8 question 6.

## Reproduce

    python3 -I scripts/f0_min_forms.py --selftest
    python3 -I scripts/f0_min_forms.py <rndb-export.jsonl> <f0s2-cells.jsonl>

The export comes from `.lake/build/bin/rndbexport` (on main since #73).
The cells come from `f0s2` (branch `f0-forms-s2`).  Neither file is
committed.
