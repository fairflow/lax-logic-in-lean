# What went wrong before

Stated factually, because each cost hours and each is cheap to avoid.

1. **Extending before the base was verified.** A modal extension was
   built thirteen hours *before* the base calculus it extends. Its
   completeness was proved while its soundness was false — twice over, at
   two successive versions of one side condition. Stepping back to the
   base alone produced soundness, completeness and the biconditional in a
   single day. **Extension is a separate campaign with its own Stage 0,
   starting only when the base's fidelity table is complete and its
   theorems pinned.**
2. **Formalising from a paraphrase.** The unsound rule table came from an
   in-repo orientation summary, not the paper. Its central rule
   corresponded to no published calculus. Rule tables come from the
   source.
3. **Transcribing from the figure alone.** The prose carries side
   conditions, and it distinguishes *rules* from *proof-search
   restrictions* — which are not interchangeable, and neither fact is
   visible in the figure.
4. **Bundling part of the conclusion into a definition.** A model
   construction carried `forces_lhs` as an invariant; `forces_lhs` *is*
   the lemma the soundness proof was supposed to establish. That is a
   restructuring of the proof, not the proof. The same test catches a
   certificate format wearing the word "calculus": a tree plus an
   external checker cannot be inducted on, and its soundness lives
   outside the data.
5. **Treating choice as something to report in the pin.** It is a design
   constraint from the first definition. Retrofitting it cost a rewrite
   of the completeness construction — which, to be fair, was the right
   rewrite for other reasons.
6. **Computed indices in constructor return types** (green slime). If a
   constructor concludes `FRJi G (St ++ Lam) Th C`, then a *given*
   derivation can never be re-indexed, and no transport lemma exists to
   fix it — `Ax^I` pins its own zone, so "same members implies same
   derivations" is false. This blocked the `List` conversion outright and
   was resolved by canonicalising contexts, not by weakening the rules.
7. **Blaming the mathematics for a dirty axiom pin.** Twice the
   `Classical.choice` was in a tool, not an argument. Bisect first.
8. **Trusting your own success check.** A generator reported "0 items
   unextracted" while two rows displayed raw LaTeX; the check counted a
   marker string rather than inspecting the cells. Another reported clean
   output because the grep pattern could not match what it was looking
   for. Look at the artefact as its reader would.
9. **Reimplementing a tool that is installed.** Simulating LaTeX's
   counters produced a confidently wrong number, on the strength of which
   a correct record was "corrected". Compiling the document answers the
   question exactly. Guessing costs more than the guess.
