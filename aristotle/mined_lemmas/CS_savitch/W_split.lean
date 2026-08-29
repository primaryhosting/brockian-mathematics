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

theorem W_split {p q : ℕ} {a b : Fin M.N} (h : W M (p + q) a b = true) :
    ∃ c, W M p a c = true ∧ W M q c b = true := by
  induction p generalizing a with
  | zero => exact ⟨a, W_refl 0 a, by simpa using h⟩
  | succ p ih =>
      have h' : W M ((p + q) + 1) a b = true := by
        have : p + 1 + q = (p + q) + 1 := by omega
        rwa [this] at h
      rcases (W_succ_iff (p + q) a b).1 h' with rfl | ⟨c, hc, hw⟩
      · exact ⟨a, W_refl _ a, W_refl _ a⟩
      · obtain ⟨d, hd1, hd2⟩ := ih hw
        exact ⟨d, (W_succ_iff p a d).2 (Or.inr ⟨c, hc, hd1⟩), hd2⟩

