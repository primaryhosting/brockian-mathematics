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

theorem card_le_card_reachSet {E : V → V → Prop} {u : V} (n : ℕ)
    (h : ∀ m < n, reachSet E u (m + 1) ≠ reachSet E u m) :
    n + 1 ≤ (reachSet E u n).card := by
  induction n with
  | zero =>
      have : u ∈ reachSet E u 0 := mem_reachSet.2 rfl
      exact Finset.card_pos.2 ⟨u, this⟩
  | succ n ih =>
      have h1 : n + 1 ≤ (reachSet E u n).card := ih (fun m hm => h m (by omega))
      have h2 := card_reachSet_lt (h n (by omega))
      omega

/-- In a finite graph, reachability implies reachability in at most `card V` steps. -/
