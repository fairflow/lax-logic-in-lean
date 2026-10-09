import wip.ui_routeB_r_sound
import wip.ui_routeB_r_cells
open LJFO

/-- Where do `interpR` and `interpP` differ?  (true = equal at that fuel) -/
#eval (List.range 7).map (fun f =>
  (f, decide (interpR "p" f [] cell1 (some goal1) [] = interpP "p" f [] cell1 (some goal1)),
      decide (interpR "p" f [] cell1 none [] = interpP "p" f [] cell1 none)))

#eval (List.range 7).map (fun f =>
  (f, decide (interpR "p" f [] cell3 (some goal3) [] = interpP "p" f [] cell3 (some goal3))))
