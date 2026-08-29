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

theorem reachSet_stable {E : V → V → Prop} {u : V} {n : ℕ}
    (h : reachSet E u (n + 1) = reachSet E u n) (m : ℕ) :
    reachSet E u (n + m) = reachSet E u n := by
  induction m with
  | zero => rfl
  | succ m ih =>
      apply Finset.Subset.antisymm
      · intro v hv
        have hv' : reachLe E (n + m + 1) u v := mem_reachSet.1 hv
        rcases hv' with hh | ⟨w, hw, hwv⟩
        · exact ih ▸ mem_reachSet.2 hh
        · have hwn : w ∈ reachSet E u n := ih ▸ mem_reachSet.2 hw
          have : v ∈ reachSet E u (n + 1) := by
            exact mem_reachSet.2 (reachLe_succ_of_step (mem_reachSet.1 hwn) hwv)
          rwa [h] at this
      · exact reachSet_subset (by omega)

