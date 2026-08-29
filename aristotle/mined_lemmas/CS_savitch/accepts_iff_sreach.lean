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

theorem accepts_iff_sreach :
    M.AcceptsIn s x ↔ sreach (edge M s x) (nodes M s x) (depth M s x) (source M s x) none = true := by
  rw [sreach_iff (edge M s x) (nodes M s x) (mem_nodes M s x)]
  constructor
  · intro h
    have h1 := (accepts_iff_reach M s x).1 h
    have h2 := reachLe_card_of_reflTransGen h1
    exact reachLe_mono (le_trans (le_of_eq rfl) (numNodes_le_pow M s x)) h2
  · intro h
    exact (accepts_iff_reach M s x).2 (reachLe_reflTransGen h)

/-- **Correctness of the deterministic simulation.**  The deterministic machine
halts, and its answer is `true` exactly when `M` accepts. -/
