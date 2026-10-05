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

theorem inv2_iterate (E : V → V → Bool) (all : List V) (K : ℕ) (c : Cfg V)
    (h : Inv K c) (h2 : Inv2 K all c) (n : ℕ) : Inv2 K all ((step E all)^[n] c) := by
  induction n generalizing c with
  | zero => simpa using h2
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (inv_step E all K c h) (inv2_step E all K c h h2)

/-- Every frame reachable in a run started at level `K` stores a level `< K` and
an index into the vertex list. -/
