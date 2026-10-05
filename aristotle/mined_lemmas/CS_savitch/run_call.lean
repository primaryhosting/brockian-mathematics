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

theorem run_call (E : V → V → Bool) (all : List V) (K : ℕ) (u v : V) :
    ∃ n, (step E all)^[n] (.call K u v []) = .done (sreach E all K u v) := by
  obtain ⟨n, hn⟩ := call_evals E all K u v []
  exact ⟨n + 1, iter_trans (step E all) hn rfl⟩

/-! ### The space bound: the stack never exceeds `K` frames -/

/-- Levels increase by one going down the stack. -/
