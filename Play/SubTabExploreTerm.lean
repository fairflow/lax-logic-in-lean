/-
# `Play/SubTabExploreTerm.lean`: walk a derivation, and read its proof term

Matthew's file.  Claude prepared it (2026-11-21) from the examples of that
day and does not edit it again.  It is in no library, so no `lake build`
builds it and nothing imports it; open it in VS Code.  (Build
`SubTabExplore` first: `lake build SubTabExplore`.)

**To walk.**  `#walk d` shows the attempt or derivation `d` at a position:
the sequents and moves from the root down to the focus (marked `>`), the
premises of the focus, numbered, and where the open goals are.  Put the
editor's cursor on a line of a walk and read the view under Messages.

    up            to the node the focus is a premise of
    down i        to premise `i` of the focus
    left, right   to the premise before, or after, of the same node
    top           to the root
    goal k        to open goal `k`

**To walk by clicking.**  Under the view of a walk's last line is a second
message, `Motions from here:`.  Click `[apply]` on a motion: it is written
after the last motion, on the same line, the view changes, and the next
motions are offered.  The same motions are in the menu of code actions
(the light bulb, or `⌘.`).  Break the line where you want the view in
between.  `set_option walk.offer false` turns the offer off.

**The proof term.**  `tm d` is the proof term of a derivation `d` of
`⇒ φ`, a `Tm [] φ`, and `nf d` its normal form (`ExploreTerm.lean`).
-/
import LaxLogic.PLL.SubTab.ExploreTerm
open PLLFormula ProofTools PLLND PLLND.SubTab PLLND.SubTab.ExploreTest

set_option apply_move.tryThis false   -- delete this line to get the "Try this" suggestions

-- 1. Build a derivation, then walk it.
def mine : Explore.Der STab (goal ((p ∧ q) ↠ (q ∧ p))) := by
  subtab impR
  subtab andL
  subtab andR
  subtab ax
  subtab ax

#walk mine
  down 0
  down 0
  down 1
  left
  top

-- 2. Stop an attempt, then look at where it stopped.
def stuck : Explore.Att STab true (goal (◯p ↠ p)) := by
  subtab impR
  leave_open

#walk stuck goal 0

-- 3. The proof term of your derivation, and its normal form.
#eval IO.println (report "mine" mine)
#eval IO.println ((tm mine).write 0 false)
#eval IO.println (compare "mine" mine)

-- 4. Walk what the search found.
def searchAtt (φ : PLLFormula) : Explore.Att STab true (goal φ) :=
  match produceScript φ 0 with
  | .pass ls => (Explore.run STab (goal φ) ls).att
  | _ => .goal

#walk (searchAtt chain4) down 0 down 0 down 0 down 0 down 0

-- 5. Walk by clicking.  Put the cursor on the line below.  Under Messages, after
--    the view, are the motions that can be made: click `[apply]` on one.
#walk mine
