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

theorem reachLe_reflTransGen {E : V → V → Prop} {n : ℕ} {u v : V}
    (h : reachLe E n u v) : Relation.ReflTransGen E u v := by
  induction n generalizing v with
  | zero => cases h; exact Relation.ReflTransGen.refl
  | succ n ih =>
      rcases h with h | ⟨w, hw, hwv⟩
      · exact ih h
      · exact (ih hw).tail hwv

/-! ### Reachability in a finite graph is bounded reachability -/

section Finite

variable [Fintype V]

open scoped Classical in
/-- The finset of vertices reachable from `u` in at most `n` steps. -/
