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

theorem reachLe_succ_of_step {E : V → V → Prop} {n : ℕ} {u w v : V}
    (h : reachLe E n u w) (hs : E w v) : reachLe E (n + 1) u v :=
  Or.inr ⟨w, h, hs⟩

/-- Composition: a walk of length `≤ m + n` splits as a walk of length `≤ m`
followed by a walk of length `≤ n`. -/
