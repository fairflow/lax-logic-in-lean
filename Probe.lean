import LaxLogic.Obligation.Modular
import LaxLogic.Obligation.Solve
namespace LaxLogic.Obligation.Modular
open LaxLogic.Obligation.Solve

solve_obligations pipeline_meets_clock

#check @pipeline_meets_clock.obligation1_solved
#check @pipeline_meets_clock.obligation2_solved
#check @pipeline_meets_clock.obligation3_solved
#check @pipeline_meets_clock_debt
end LaxLogic.Obligation.Modular
