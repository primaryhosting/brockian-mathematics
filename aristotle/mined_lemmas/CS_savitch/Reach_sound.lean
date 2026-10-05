import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import RequestProject.Savitch.Machine

/-!
# Reduction to single-target reachability

`CS.addSink M` adds one new configuration (the *sink*) to `M`, with an edge from every
accepting configuration of `M` to the sink and no outgoing edge from the sink.  Then `M`
accepts iff the sink is reachable from the start configuration of `addSink M`, so that
deciding acceptance becomes deciding reachability between two *fixed* configurations.
-/

namespace CS

namespace Machine

/-- Add a sink configuration reachable exactly from the accepting configurations. -/

theorem Reach_sound {k : ℕ} {a b : Fin M.N} (h : Reach M k a b = true) : M.Reaches a b := by
  induction k generalizing a b with
  | zero =>
      rw [Reach_zero] at h
      rcases Bool.or_eq_true_iff.1 h with h | h
      · exact (of_decide_eq_true h) ▸ Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single h
  | succ k ih =>
      obtain ⟨m, h1, h2⟩ := (Reach_succ_iff k a b).1 h
      exact (ih h1).trans (ih h2)

/-! ### Walks -/

/-- `W M n a b` : there is a walk of at most `n` steps from `a` to `b`. -/
