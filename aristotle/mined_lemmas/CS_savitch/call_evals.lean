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

theorem call_evals (E : V → V → Bool) (all : List V) :
    ∀ (k : ℕ) (u v : V) (st : List (Frame V)),
      ∃ n, (step E all)^[n] (.call k u v st) = .ret (sreach E all k u v) st := by
  intro k
  induction k with
  | zero => exact fun u v st => ⟨1, rfl⟩
  | succ k ih =>
      intro u v st
      obtain ⟨n, hn⟩ :=
        tryFrom_evals E all k u v (fun u' v' st' => ih u' v' st') all.length 0 (by omega) st
      refine ⟨1 + n, ?_⟩
      have h0 : (step E all)^[1] (Cfg.call (k + 1) u v st) = tryFrom all k u v 0 st := rfl
      have := iter_trans (step E all) h0 hn
      rw [this]
      simp [sreach]

/-- Running the machine from the initial configuration produces the answer. -/
