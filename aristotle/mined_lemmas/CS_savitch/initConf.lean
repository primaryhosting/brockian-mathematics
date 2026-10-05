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

def initConf (M : NTM) (n s : ℕ) : Conf M n s :=
  (M.start, ⟨0, Nat.succ_pos n⟩, fun _ => M.blank, ⟨0, Nat.succ_pos s⟩)

/-- The one-step relation of `M` on input `x`, as a decidable predicate. -/
