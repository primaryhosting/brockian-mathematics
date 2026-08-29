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

theorem W_unsnoc {n : ℕ} {a b : Fin M.N} (h : W M (n + 1) a b = true) :
    W M n a b = true ∨ ∃ c, W M n a c = true ∧ M.step c b = true := by
  induction n generalizing a with
  | zero =>
      rcases (W_succ_iff 0 a b).1 h with rfl | ⟨c, hc, hw⟩
      · exact Or.inl (W_refl 0 a)
      · rw [W_zero] at hw
        have : c = b := of_decide_eq_true hw
        subst this
        exact Or.inr ⟨a, W_refl 0 a, hc⟩
  | succ n ih =>
      rcases (W_succ_iff (n + 1) a b).1 h with rfl | ⟨c, hc, hw⟩
      · exact Or.inl (W_refl _ a)
      · rcases ih hw with hw' | ⟨d, hd1, hd2⟩
        · exact Or.inl ((W_succ_iff n a b).2 (Or.inr ⟨c, hc, hw'⟩))
        · exact Or.inr ⟨d, (W_succ_iff n a d).2 (Or.inr ⟨c, hc, hd1⟩), hd2⟩

