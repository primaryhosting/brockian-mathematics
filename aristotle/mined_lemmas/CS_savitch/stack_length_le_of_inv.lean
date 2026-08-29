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

theorem stack_length_le_of_inv {K : ℕ} {c : Cfg V} (h : Inv K c) : c.stack.length ≤ K := by
  match c with
  | .call k u v st =>
      have h1 := h.1
      show st.length ≤ K
      omega
  | .ret b st => exact h.1
  | .done b => simp [Cfg.stack]

/-- **Space bound.**  Every configuration reachable from the initial
configuration `call K u v []` carries at most `K` stack frames. -/
