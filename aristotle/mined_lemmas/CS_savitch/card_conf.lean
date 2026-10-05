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

theorem card_conf (M : NTM) (n s : ℕ) :
    Fintype.card (Conf M n s)
      = Fintype.card M.Q * ((n + 1) * (Fintype.card M.Γ ^ (s + 1) * (s + 1))) := by
  simp [Conf, Fintype.card_prod, Fintype.card_fun]

end CS

/-
Bounded reachability in a (finite) directed graph.

This file develops the elementary theory of "reachable in at most `n` steps",
the halving identity that underlies Savitch's algorithm, and the fact that in a
finite graph reachability is the same as reachability in at most `card V` steps.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS

universe u

variable {V : Type u}

/-- `reachLe E n u v` : `v` can be reached from `u` by at most `n` `E`-steps. -/
