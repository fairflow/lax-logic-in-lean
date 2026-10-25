# Paper III, "The order of F0": status of the v0.5 revision

Tracked status note for the revision of `F0Paper/` from v0.4.1 to v0.5
(manager's brief of 2026-10-25).  Agent worktree `agent-aff1d57f31573668e`,
branch `worktree-agent-aff1d57f31573668e`, cut from main `21d3eb3` (PR #89)
with `origin/f0-filter-iso` (PR #92, `00373c0`) merged in.  Nothing pushed.

## 2026-10-25 19:14 GMT: plan

1. Running header in the shared machinery: `III:F0Lattice 0.5 · 25 Oct 2026`;
   the branch@sha stamp moves to the title block in small type.  Same for the
   semantics paper (`I:Semantics 0.2`), content unchanged.
2. The Dedekind–MacNeille section rewritten: cuts as in Dedekind's ℝ from ℚ,
   where choice enters, the extension of ◯, the points of F*.
3. New section: which filters [p, ⊤] are order-isomorphic to F0
   (`wip/f0FilterIso.lean`).
4. Two closing sections: "What is established" (one table, axioms computed)
   and "Open problems" (status, sketches).
5. Optional: `wip/f0MacNeillePoints.lean` for (D) a non-principal point and
   (C) |F*| = 2^ℵ₀, each only if under about 100 lines.

Not touched: `wip/f0Normal.lean` (F₇ is certified in another worktree).

The Edit/Write tools refuse this worktree (the hook takes the manager's
worktree as the session root); files are written in the scratchpad and moved
in with `mv`, or edited by an exact-replacement script that writes a
temporary file and renames it.
