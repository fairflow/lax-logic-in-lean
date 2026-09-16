#!/usr/bin/env python3
"""Instance screen for the §4.11 candidate family.

For each station Γ (list of PLL formulas as strings), goal G, and each
p-free instance χ, the cell  suf_<S>_<χ> :  (⋀Γ ∧ (⋀Γ[χ] ⊃ G[χ])) ⊃ G
asks whether the χ-instance bound is SUFFICIENT.  If it is, the cell is
instance-closed (∀p = Γ[χ] ⊃ G[χ]).  ctrl_<S> : ⋀Γ ⊃ G must be invalid
(else the cell is trivial).  One TSV per cell, so each oracle run can be
bounded separately.
"""
import os, re, sys

OUT = sys.argv[1]
os.makedirs(OUT, exist_ok=True)

TOP = "(⊥ ⊃ ⊥)"
def neg(x): return f"({x} ⊃ ⊥)"

stations = {
  # name : (Γ, G)
  "S1": (["(◯(d ⊃ p) ⊃ a)", "(c ⊃ ◯p)"], "a"),
  "S2": (["(◯(d ⊃ p) ⊃ a)", "(c ⊃ p)"], "a"),                 # control: expected closed by χ = c
  "S3": (["(◯(d ⊃ p) ⊃ a)", "(◯c ⊃ p)"], "a"),
  "S5": (["(◯(d ⊃ c) ⊃ p)", "(c ⊃ p)"], "((p ⊃ q) ∨ (q ⊃ p))"),
  "S6": (["(◯(d ⊃ p) ⊃ a)", "(c ⊃ ◯p)", "((d ⊃ c) ⊃ e)"], "a"),
  "S7": (["(◯(d ⊃ p) ⊃ a)", "(c ⊃ ◯p)"], "(a ∨ c)"),
  "S8": (["(◯(p ⊃ d) ⊃ a)", "(c ⊃ ◯p)"], "a"),                 # control: p only positive
}

chis = {
  "bot": "⊥", "top": TOP, "a": "a", "c": "c", "d": "d", "q": "q",
  "Obot": "◯⊥", "Oa": "◯a", "Oc": "◯c", "Od": "◯d",
  "nd": neg("d"), "Ond": "◯" + neg("d"), "nc": neg("c"), "nq": neg("q"),
}

def subst(s, chi):
    # p is the eigenvariable; every other atom is a single distinct letter
    return re.sub(r"\bp\b", f"({chi})", s)

def conj(xs):
    return xs[0] if len(xs) == 1 else "(" + " ∧ ".join(xs) + ")"

n = 0
for S, (G_, G) in stations.items():
    gamma = conj(G_)
    with open(f"{OUT}/ctrl_{S}.tsv", "w") as f:
        f.write(f"ctrl_{S}\tscr\t{gamma} ⊃ {G}\n"); n += 1
    for cn, chi in chis.items():
        gam_chi = conj([subst(x, chi) for x in G_])
        g_chi = subst(G, chi)
        psi = f"({gam_chi} ⊃ {g_chi})"
        with open(f"{OUT}/suf_{S}_{cn}.tsv", "w") as f:
            f.write(f"suf_{S}_{cn}\tscr\t({gamma} ∧ {psi}) ⊃ {G}\n"); n += 1
print(f"{n} cells written to {OUT}")
