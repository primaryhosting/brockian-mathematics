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

theorem reachSet_subset {E : V → V → Prop} {u : V} {m n : ℕ} (h : m ≤ n) :
    reachSet E u m ⊆ reachSet E u n := by
  intro v hv
  exact mem_reachSet.2 (reachLe_mono h (mem_reachSet.1 hv))

/-- If the reachable-set stops growing at step `n`, it never grows again. -/
