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

def Inv (K : ℕ) : Cfg V → Prop
  | .call k _ _ st => k + st.length = K ∧ StackChain st ∧ ∀ f ∈ st.head?, f.level = k
  | .ret _ st => st.length ≤ K ∧ StackChain st ∧ ∀ f ∈ st.head?, f.level + st.length = K
  | .done _ => True

omit [DecidableEq V] in
