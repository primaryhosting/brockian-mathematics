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

theorem reachLe_mono {E : V → V → Prop} {m n : ℕ} (h : m ≤ n) {u v : V}
    (huv : reachLe E m u v) : reachLe E n u v := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.le_zero.1 h
      subst hm; exact huv
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hm | hm
      · exact Or.inl (ih (by omega))
      · have : m = n + 1 := le_antisymm h hm
        subst this; exact huv

