import wip.ui_routeB_r_def
import wip.ui_routeB_n4q_cells
set_option autoImplicit false
namespace LJFO
theorem k_m10 : ∀ f ∈ [35,36,37],
    interpR "p" f [] m10 (some (.circ (.atom "g"))) []
      = interpR "p" 34 [] m10 (some (.circ (.atom "g"))) [] := by
  decide +kernel
end LJFO
