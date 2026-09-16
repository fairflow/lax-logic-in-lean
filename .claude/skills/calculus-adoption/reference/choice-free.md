# Keeping it choice-free

Target: **`[propext, Quot.sound]`** at worst, and no axioms at all where
attainable. `Classical.choice` blocks extraction, and extraction is the
point.

## Method: bisect, do not guess

```lean
#choice_path myTheorem
```

It gives the shortest chain to `Classical.choice` with each step's module.
Where the names stop being yours, that is the entry point.

This matters because **twice in one campaign the choice was in a tool
rather than in the argument, and the guess was wrong both times.** The
first guess named `simp`; the actual source was Mathlib's
`lt_or_eq_of_le`, which `simp` merely routed through.

## The checklist

* **`Finset` union, erase and image are choice-tainted at the DEFINITION
  level** — `Finset.instUnion`, `Finset.erase`, `Finset.image`,
  `Multiset.ndunion`. Any term that merely *mentions* `s ∪ t` carries
  choice however it is proved; re-deriving the membership lemmas by hand
  does not help. Only `Finset.filter` is clean.
* **The `List` API is axiom-free at definition level** — `List.union`,
  `List.inter`, `List.filter`, `List.map`, `List.flatMap`,
  `List.finRange`, `List.instMembership`; membership lemmas cost
  `[propext]`. **Avoid `List.dedup` and `List.erase`**, both classical;
  filter instead.
* **Three more Mathlib list lemmas carry it**: `List.argmax_mem`,
  `List.le_of_mem_argmax` (though `List.argmax` itself is clean), and
  `List.eq_nil_iff_forall_not_mem`. Replacements live in
  `FRJ/Basic.lean`: `maxOn` with `maxOn_mem`/`le_maxOn`, and
  `eq_nil_of_forall_not_mem`.
* **`Finite` costs choice to eliminate** (`Fintype.ofFinite`). Carry a
  constructive enumeration instead — `elems : List W` with
  `complete : ∀ w, w ∈ elems`, plus `decEq`/`decLe`/`decV`. That is also
  what makes forcing *decidable*, which is worth having for its own sake.
* **Tactics.** `tauto` and `push_neg` are classical, as is
  `Classical.propDecidable`. `simp` can be, indirectly: on an inequality
  goal it may route through Mathlib's ordered-algebra instances and out
  through `lt_or_eq_of_le`. **Prefer `omega` for arithmetic and order
  goals.**
* **Shape predicates as `Bool`**, not `Prop`.
* **`choose` and `Nonempty.some` are choice**, so a construction that must
  yield a derivation has to be `Type`-valued and return one.

## Pin it, do not trust it

Generate pins with `#axiom_pin` and guard them with `#guard_msgs` in an
`Audit.lean` (`templates/Audit.lean`). A pin that is retyped can be
mistyped; a pin that is not guarded is a note, not a check.

## When choice is genuinely in the statement

Say so, and give the constructive form beside it. `Provable G ↔ ¬ IPL G`
needs the classical step from `¬ ∀ K, K.valid G` to `∃ K, ¬ K.valid G`;
`Provable G ↔ ∃ K, ¬ K.valid G` is the same theorem with that step left
to the caller, and it is choice-free. Both are stated, and the pins record
which is which.
