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

import Mathlib

/-!
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Finset

namespace Brockian.EquidistributionBVReduction

/-- The set of *configurations* of size `N` in the residue class `r` modulo `q`:
pairs `(a, b)` with `a, b < N` and `a + b ≡ r [MOD q]`. -/

lemma mem_config_iff (q r a b : ℕ) (hq : 0 < q) :
    (a + b) % q = r % q ↔ b % q = (r + (q - 1) * a) % q := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have key : (a + b + m * a) % (m + 1) = b % (m + 1) := by
    rw [show a + b + m * a = b + (m + 1) * a by ring]
    exact Nat.add_mul_mod_self_left _ _ _
  constructor
  · intro h
    have h2 : (a + b + m * a) % (m + 1) = (r + m * a) % (m + 1) :=
      Nat.ModEq.add_right (m * a) h
    rwa [key] at h2
  · intro h
    have h2 : (a + b + m * a) % (m + 1) = (r + m * a) % (m + 1) := by rw [key]; exact h
    exact Nat.ModEq.add_right_cancel' (m * a) h2

/-- Counting the elements of `[0, N)` lying in a fixed residue class modulo `q`. -/
