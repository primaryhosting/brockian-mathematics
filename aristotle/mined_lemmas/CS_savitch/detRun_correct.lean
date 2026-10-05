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

theorem detRun_correct :
    ∃ (b : Bool) (n : ℕ), (detStep M s x)^[n] (detInit M s x) = Savitch.Cfg.done b ∧
      (b = true ↔ M.AcceptsIn s x) := by
  obtain ⟨n, hn⟩ :=
    Savitch.run_call (edge M s x) (nodes M s x) (depth M s x) (source M s x) none
  exact ⟨_, n, hn, (accepts_iff_sreach M s x).symm⟩

/-! ### The space bound -/

/-- **Space bound.**  At every moment the deterministic machine keeps at most
`depth` frames on its stack. -/
