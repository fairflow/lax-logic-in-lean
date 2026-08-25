/- Executable wrapper for `wip/rho_order.lean` (kept separate so the
module can be imported by `wip/rho_engines.lean`; a root-level `main`
in an imported module blocks any other executable). -/
import wip.rho_order

def main (args : List String) : IO Unit := RhoOrder.main args
