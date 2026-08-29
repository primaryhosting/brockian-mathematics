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

theorem reach_key (b : Node M s x)
    (hb : Relation.ReflTransGen (fun a b => edge M s x a b = true) (source M s x) b) :
    (∀ c, b = some c →
        Relation.ReflTransGen (fun a b => stepB M x a b = true) (initConf M x.length s) c) ∧
      (b = none → M.AcceptsIn s x) := by
  induction hb with
  | refl =>
      constructor
      · intro c hc
        have : c = initConf M x.length s := by
          simpa [source] using hc.symm
        subst this
        exact Relation.ReflTransGen.refl
      · intro h
        simp [source] at h
  | tail hab hbc ih =>
      rename_i b1 b2 _
      constructor
      · intro c hc
        subst hc
        rcases b1 with _ | c1
        · simp [edge] at hbc
        · have hstep : stepB M x c1 c = true := by simpa [edge] using hbc
          exact (ih.1 c1 rfl).tail hstep
      · intro hc
        subst hc
        rcases b1 with _ | c1
        · exact ih.2 rfl
        · have hacc : c1.1 = M.acc := by simpa [edge] using hbc
          exact ⟨c1, ih.1 c1 rfl, hacc⟩

