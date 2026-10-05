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

theorem card_reachSet_lt {E : V → V → Prop} {u : V} {n : ℕ}
    (h : reachSet E u (n + 1) ≠ reachSet E u n) :
    (reachSet E u n).card < (reachSet E u (n + 1)).card := by
  have hsub : reachSet E u n ⊆ reachSet E u (n + 1) := reachSet_subset (by omega)
  exact Finset.card_lt_card (lt_of_le_of_ne (Finset.le_iff_subset.2 hsub) (Ne.symm h))

