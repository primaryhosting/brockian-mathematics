import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-- A `±1` sequence, indexed by the positive integers. -/

theorem erdos_discrepancy_dilate (f : ℕ → ℤ) (hf : IsPlusMinusOne f) (k : ℕ) (hk : 0 < k) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ 2 ≤ |apSum f (k * d) n| := by
  obtain ⟨d, n, hd, hn, h⟩ := erdos_discrepancy (fun m => f (k * m))
    (fun m hm => hf (k * m) (Nat.one_le_iff_ne_zero.2 (by positivity)))
  refine ⟨d, n, hd, hn, ?_⟩
  have : apSum (fun m => f (k * m)) d n = apSum f (k * d) n := by
    simp only [apSum]
    exact Finset.sum_congr rfl fun i _ => by ring_nf
  rwa [this] at h

end Frontier

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

