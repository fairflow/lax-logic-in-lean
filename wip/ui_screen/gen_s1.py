#!/usr/bin/env python3
"""S1 = [◯(d ⊃ p) ⊃ a, c ⊃ ◯p] ⇒ a : sufficiency of candidate Δ, and where
the ∀p sits relative to the hand candidate a ∨ ◯¬d and the instance bounds."""
import os, re, sys
OUT = sys.argv[1]; os.makedirs(OUT, exist_ok=True)
G_ = ["(◯(d ⊃ p) ⊃ a)", "(c ⊃ ◯p)"]; G = "a"
gamma = "(" + " ∧ ".join(G_) + ")"
def subst(s, chi): return re.sub(r"\bp\b", f"({chi})", s)
def psi(chi): return "((" + " ∧ ".join(subst(x, chi) for x in G_) + ") ⊃ " + subst(G, chi) + ")"
TOP = "(⊥ ⊃ ⊥)"; ND = "(d ⊃ ⊥)"; HAND = f"(a ∨ ◯{ND})"
cells = {
  # sufficiency of candidate p-free Δ
  "sufD_a_or_Ond": f"({gamma} ∧ {HAND}) ⊃ a",
  "sufD_Ond":      f"({gamma} ∧ ◯{ND}) ⊃ a",
  "sufD_Odc":      f"({gamma} ∧ ◯(d ⊃ c)) ⊃ a",
  "sufD_OdObot":   f"({gamma} ∧ ◯(d ⊃ ◯⊥)) ⊃ a",
  "sufD_c":        f"({gamma} ∧ c) ⊃ a",
  # instance bounds versus the hand candidate: ψ_χ ⊢ a ∨ ◯¬d ?
  "bnd_bot":  f"{psi('⊥')} ⊃ {HAND}",
  "bnd_top":  f"{psi(TOP)} ⊃ {HAND}",
  "bnd_c":    f"{psi('c')} ⊃ {HAND}",
  "bnd_Oc":   f"{psi('◯c')} ⊃ {HAND}",
  "bnd_Obot": f"{psi('◯⊥')} ⊃ {HAND}",
  "bnd_a":    f"{psi('a')} ⊃ {HAND}",
  "bnd_nd":   f"{psi(ND)} ⊃ {HAND}",
  # is the conjunction of instance bounds sufficient?
  "sufConj": f"({gamma} ∧ ({psi('⊥')} ∧ {psi(TOP)} ∧ {psi('c')} ∧ {psi('◯c')} ∧ {psi('◯⊥')} ∧ {psi('a')} ∧ {psi(ND)} ∧ {psi('d')})) ⊃ a",
}
for n, f in cells.items():
    with open(f"{OUT}/{n}.tsv", "w") as h: h.write(f"{n}\tscr\t{f}\n")
print(len(cells))
