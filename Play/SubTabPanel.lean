/-
# `Play/SubTabPanel.lean`: the panel of `#walk`, a trial

Matthew's file.  Claude prepared it (2026-11-21) and does not edit it again.
It is in no library; open it in VS Code.  (Build `SubTabExplore` first:
`lake build SubTabExplore`.)

With `set_option walk.panel true`, `#walk` also draws the attempt as a tree
in the infoview, while the editor's cursor is on the command.  It is under
the messages, headed `Walk: at …`.

    a click on a node     puts the focus there (the highlighted line)
    ▸ and ▾               show and hide the premises of a node; a hidden
                          part says `[closed]` or `[n open]`
    up left right top     the motions, as buttons
    goal k                to open goal `k`
    write into the file   replaces the motions of the `#walk` by the path
                          to the focus; until then nothing is written

The switch is the line `set_option walk.panel true` below: make it `false`,
or delete it, and the panel is gone.  The view and the offer of motions
under Messages are there either way.
-/
import LaxLogic.PLL.SubTab.ExploreTerm
open PLLFormula ProofTools PLLND PLLND.SubTab PLLND.SubTab.ExploreTest

set_option walk.panel true

-- 1. A derivation.  Put the cursor on the next line and look under the messages.
#walk strength

-- 2. An attempt with an open goal, walked to it.
#walk distAtt goal 0

-- 3. What the search found for the chain, 403 moves: most of it is hidden
--    until you open it.
def searchAtt (φ : PLLFormula) : Explore.Att STab true (goal φ) :=
  match produceScript φ 0 with
  | .pass ls => (Explore.run STab (goal φ) ls).att
  | _ => .goal

#walk (searchAtt chain4)
