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

theorem reachLe_two_pow_succ {E : V → V → Prop} (k : ℕ) (u v : V) :
    reachLe E (2 ^ (k + 1)) u v ↔
      ∃ w, reachLe E (2 ^ k) u w ∧ reachLe E (2 ^ k) w v := by
  have h : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  rw [h, reachLe_add]

