/-
The configuration graph of a space bounded nondeterministic machine, and the
deterministic middle-first search run on it.
-/
import RequestProject.NTM

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS
namespace Sim

variable (M : NTM) (s : ℕ) (x : List Bool)

/-- Vertices of the configuration graph: the configurations of `M`, plus a sink
`none` which is entered from every accepting configuration. -/
abbrev Node : Type := Option (Conf M x.length s)

/-- Edges of the configuration graph.  A single edge query only inspects the
local transition table of `M` at the scanned symbols. -/

def stepB (M : NTM) (x : List Bool) {n s : ℕ} (c c' : Conf M n s) : Bool :=
  (M.δ c.1 x[c.2.1.val]? (c.2.2.1 c.2.2.2)).any fun t =>
    decide (c' = (t.1, t.2.2.1.move c.2.1,
      Function.update c.2.2.1 c.2.2.2 t.2.1, t.2.2.2.move c.2.2.2))

/-- `M` accepts `x` in space `s` if some accepting configuration is reachable
from the initial configuration. -/
