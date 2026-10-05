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

def detStep : Savitch.Cfg (Node M s x) → Savitch.Cfg (Node M s x) :=
  Savitch.step (edge M s x) (nodes M s x)

/-- The initial configuration of the deterministic search machine: it asks
whether the sink is reachable from the initial configuration of `M` within
`2 ^ depth` steps. -/
