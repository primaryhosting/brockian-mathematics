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

@[simp] theorem Frame.idx_mid2 {V : Type u} (k : ℕ) (u v : V) (i : ℕ) (m : V) :
    (Frame.mid2 k u v i m).idx = i := rfl

/-- A configuration of the deterministic search machine. -/
inductive Cfg (V : Type u) where
  | call (k : ℕ) (u v : V) (st : List (Frame V))
  | ret (b : Bool) (st : List (Frame V))
  | done (b : Bool)

/-- The stack held in a configuration. -/
