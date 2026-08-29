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

theorem bits_le (E : V → V → Bool) (all : List V) (K N : ℕ) (u v : V) (n : ℕ) :
    ((step E all)^[n] (Cfg.call K u v [])).bits K N ≤ K * frameWidth K N :=
  Nat.mul_le_mul_right _ (stack_length_le E all K u v n)

end Savitch
end CS

/-
Space bounded nondeterministic Turing machines.

A machine has a finite control, a read-only input tape holding the input word
`x : List Bool` (position `|x|` reads the end marker `none`), and a read/write
work tape.  A machine *running in space `s`* has `s + 1` work cells available;
this is the usual definition of a space bounded computation, where exceeding
the bound is forbidden.
-/
import RequestProject.StackMachine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS

/-- Head movement. -/
inductive Dir where
  | left | stay | right
  deriving DecidableEq

/-- Move a head position inside a tape of `k + 1` cells; the head stays put at
the two ends. -/
