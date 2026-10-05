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

theorem Reach_of_W {k n : ℕ} {a b : Fin M.N} (hn : n ≤ 2 ^ k) (h : W M n a b = true) :
    Reach M k a b = true := by
  induction k generalizing n a b with
  | zero =>
      have h1 : W M 1 a b = true := W_le (by simpa using hn) h
      rcases (W_succ_iff 0 a b).1 h1 with rfl | ⟨c, hc, hw⟩
      · simp [Reach_zero]
      · rw [W_zero] at hw
        have : c = b := of_decide_eq_true hw
        subst this
        simp [Reach_zero, hc]
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      have h' : W M (2 ^ k + 2 ^ k) a b = true := W_le (by omega) h
      obtain ⟨c, h1, h2⟩ := W_split h'
      exact (Reach_succ_iff k a b).2 ⟨c, ih le_rfl h1, ih le_rfl h2⟩

/-! ### Reachable sets and stabilisation -/

/-- The set of configurations reachable from `a` in at most `i` steps. -/
