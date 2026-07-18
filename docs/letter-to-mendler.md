# Draft letter to Michael Mendler

*For Matthew to personalise, trim, and send — the openings and closings
especially are placeholders for your own voice.*

---

Dear Michael,

It has been far too long, and I'm writing because I've spent the last
stretch doing something I think you'll want to see: our Propositional
Lax Logic paper now lives, in its entirety, inside a proof assistant —
and the project grew well past the original paper while it was at it.

The repository is `github.com/fairflow/lax-logic-in-lean` (Lean 4 +
Mathlib). The state of it, briefly. Everything in I&C 137 is
mechanised: the Hilbert system, natural deduction, the term calculus
and the cut-free sequent calculus, all proved equivalent; cut
elimination; the disjunction property and ◯-reflection; the constraint
models with their fallible worlds; soundness; the (Γ, Δ, Θ)-triple
completeness proof of our §4; the finite model property; decidability.
Beyond the paper: strong normalisation of the full term reduction — β
together with let-associativity, freely interleaved — by Lindley–Stark
⊤⊤-lifting, which appears to be the first mechanisation of that method
with sums; Craig interpolation by Maehara; and, a small private
satisfaction, the Kleene–Brouwer well-foundedness theorem that defeated
me in LEGO at the LFCS all those years ago — now proved fully
constructively, with literally no axioms at all.

Two findings along the way will interest you as a proof theorist.
First, the published G4-style terminating calculus for PLL (Iemhoff,
in the de Jongh volume / arXiv:2209.08976) is provably incomplete:
there is a machine-checked PLL-derivable sequent it cannot derive, and
neither cut nor contraction is admissible in it — the culprit being
that its ◯-implication rules consume formulas that a derivation can
need twice. A three-rule retention repair restores completeness, cut,
and termination, and the repaired calculus carries the mechanised
decision procedure. I'm preparing a polite note to Rosalie about it.
Second — and this is the part I most want your reaction to — the old
"Belief in Lax Logic" plan has come back to life and turned into a
paper. ◯ read as "is believed": on a Boolean algebra every nucleus is
closed, so classical belief collapses to ◯M ≡ M ∨ a — belief is worth
having only constructively — and there is now a realisability
semantics over our constraint models in which evidence for ◯M is a
*strategy* responding to presented futures, with a completeness
theorem: PLL is exactly complete when the ⊃-clause, like the ◯-clause,
is shown the future — and provably incomplete for anything more rigid.
The countermodels come from a finitisation of our §4 construction in
which your Θ-component does its old work unchanged and Zorn's lemma is
replaced by an iterated appeal to the decision procedure — the
Lindenbaum step literally asks PLL what it is consistent to believe,
formula by formula. The whole chain, completeness theorem included,
audits choice-free.

I should say plainly how it was done, because it is part of the story:
the formalisation and much of the drafting were carried out with a
large language model operating Lean under a strict regime — nothing
asserted beyond its machine-checked status, axiom audits recorded per
theorem, and my job largely to direct, to read statements, and to catch
its errors (there were some). Twice the interesting theorems were found
by the machine failing to prove the statement we first wrote down and
the failure being provable. Whatever one thinks of the tools, the
kernel is indifferent to the provenance of its proofs.

Where to look, in order: `docs/pll-formalisation-ledger.md` is the
statement-level index of everything with its axiom audit;
`docs/belief-paper-draft.md` is the draft of the belief paper (written,
you may notice, in a register that owes a debt to a certain 1997
paper); the three files in `docs/annotated/` walk through the central
proofs with the Lean interleaved. I would particularly value your eye
on the consistency formula's ◯-guard in the finitised §4 — your design
carrying a new proof — and on whether the belief reading convinces you.

[Personal close — yours to write.]

Matt

---

*Notes for Matthew, not part of the letter: (i) the LEGO/LFCS memory is
stated as yours — correct it if the history was otherwise; (ii) the
letter says a note to Iemhoff is "in preparation" — adjust if it has
been sent by the time this goes; (iii) if you would rather soften the
AI paragraph for a first contact, the minimal honest version is the
final sentence alone.*
