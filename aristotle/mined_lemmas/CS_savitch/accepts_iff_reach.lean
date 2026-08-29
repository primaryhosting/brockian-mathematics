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

theorem accepts_iff_reach :
    M.AcceptsIn s x ↔
      Relation.ReflTransGen (fun a b => edge M s x a b = true) (source M s x) none :=
  ⟨reach_of_accepts M s x, accepts_of_reach M s x⟩

/-! ### Acceptance is decided by the bounded search -/

