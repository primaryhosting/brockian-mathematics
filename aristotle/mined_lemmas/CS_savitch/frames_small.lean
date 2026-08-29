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

theorem frames_small (E : V → V → Bool) (all : List V) (K : ℕ) (u v : V) (n : ℕ) :
    ∀ f ∈ ((step E all)^[n] (Cfg.call K u v [])).stack,
      f.level < K ∧ f.idx < all.length :=
  inv2_iterate E all K _ (inv_init K u v) (by intro f hf; simp at hf) n

/-! ### The cost model

A frame consists of a recursion level `< K`, three vertices (`u`, `v` and the
current midpoint `m`), a loop index `< N` (where `N` is the number of vertices)
and a one-bit tag distinguishing `mid1` from `mid2`.  Writing all components in
binary, a frame occupies `frameWidth K N` bits. -/

/-- Number of bits occupied by one stack frame. -/
