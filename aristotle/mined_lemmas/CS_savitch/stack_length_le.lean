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

theorem stack_length_le (E : V → V → Bool) (all : List V) (K : ℕ) (u v : V) (n : ℕ) :
    ((step E all)^[n] (Cfg.call K u v [])).stack.length ≤ K :=
  stack_length_le_of_inv (inv_iterate E all K _ (inv_init K u v) n)

/-! ### Every frame stores small data -/

/-- Second invariant: every frame on the stack has a recursion level `< K` and a
candidate index pointing into the vertex list. -/
