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

theorem frameWidth_le :
    Savitch.frameWidth (depth M s x) (numNodes M s x) ≤ 5 * depth M s x + 1 := by
  have h : Nat.clog 2 (depth M s x) ≤ depth M s x := clog_le_self _
  have h2 : Nat.clog 2 (numNodes M s x) = depth M s x := rfl
  simp only [Savitch.frameWidth, h2]
  omega

end Sim
end CS

/-
The deterministic middle-first search machine used in Savitch's theorem.

This is an explicit *small-step* deterministic machine.  Its memory is a stack
of frames; a single step inspects only the top frame (plus one bit of returned
information) and performs a single push, pop, or top-frame update, together
with at most one query of the edge relation `E`.  The two facts proved here are

* `CS.Savitch.run_call`        : the machine computes `sreach`, i.e. bounded reachability;
* `CS.Savitch.stack_length_le` : the stack never holds more than `K` frames,

which together give the `O(K · framewidth)` space bound of Savitch's algorithm.
-/
import RequestProject.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS
namespace Savitch

universe u

/-- A stack frame.  `mid1 k u v i m` means: we are computing
`sreach (k+1) u v`, are currently trying the `i`-th candidate midpoint `m`,
and are waiting for the result of the recursive call `sreach k u m`.
`mid2` is the same but waiting for the second call `sreach k m v`. -/
inductive Frame (V : Type u) where
  | mid1 (k : ℕ) (u v : V) (i : ℕ) (m : V)
  | mid2 (k : ℕ) (u v : V) (i : ℕ) (m : V)
  deriving DecidableEq

/-- The recursion level a frame is waiting on. -/
