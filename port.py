import re, pathlib
W = pathlib.Path("/Users/matthew/Lean/Sources/lax-logic-in-lean/.claude/worktrees/agent-ae24d1b90e438b3fa")
src = (W / "LJF/OCore.lean").read_text().split("\n")
eSound = src[2518:2727]   # lines 2519..2727  (body only)
aSound = src[2730:4016]   # lines 2731..4016


def hdr(l):
    return l.startswith("  | ")


def subst(lines):
    out = []
    for l in lines:
        if hdr(l):
            l = "  | f+1, " + l[4:]
        l = l.replace("rw [interp]", "rw [interpF]")
        l = l.replace("interp p ", "interpF p f ")
        l = l.replace("eSound p ", "eSoundF p f ")
        l = l.replace("aSound p ", "aSoundF p f ")
        l = l.replace("fireASound hf", "fireASoundF hf")
        out.append(l)
    return out


e = subst(eSound)
a = subst(aSound)
print("eSound clause headers:", sum(1 for l in e if l.startswith("  | f+1,")))
print("aSound clause headers:", sum(1 for l in a if l.startswith("  | f+1,")))
print("residual 'interp p ':", sum(l.count("interp p ") - l.count("interpF p f ") for l in e + a))

# ---- the 11 atkCimp modal rows in the A-side ----
KEY = "(aSoundF p f [] rest (.up (.down (.circ Q'))))"
n = 0
for i, l in enumerate(a):
    if l.strip() == KEY:
        n += 1
        ind = l[: len(l) - len(l.lstrip())]
        a[i] = ind + "(aSoundF p f [] done (.up (.down (.circ Q'))))"
        assert "splits_sub hXr Z hZ" in a[i - 1], (i, a[i - 1])
        a[i - 1] = a[i - 1].replace("(splits_sub hXr Z hZ)", "hZ")
        nxt = a[i + 1].strip()
        assert nxt.startswith("(aSoundF p f [N] rest ") and nxt.endswith(")"), (i, nxt)
        a[i + 1] = (
            ind
            + "("
            + nxt
            + ".wk (Sub.cons _ (Sub.cons _ (splits_sub hXr))))"
        )
print("atkCimp rows patched:", n)

(W / "e.txt").write_text("\n".join(e))
(W / "a.txt").write_text("\n".join(a))
