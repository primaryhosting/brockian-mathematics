import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- `A` contains an arithmetic progression of length `k`: there are a starting point `a`
and a positive common difference `d` with `a, a + d, …, a + (k-1) d` all in `A`. -/

theorem HasAPOfLength.shift {A : Set ℕ} {k j : ℕ} (h : HasAPOfLength A (j + k)) :
    ∃ a d : ℕ, 0 < d ∧ j ≤ a ∧ ∀ i < k, a + i * d ∈ A := by
  obtain ⟨a, d, hd, ha⟩ := h
  refine ⟨a + j * d, d, hd, ?_, fun i hi ↦ ?_⟩
  · have : j * 1 ≤ j * d := Nat.mul_le_mul_left j hd
    omega
  · have h' := ha (j + i) (by omega)
    have he : a + (j + i) * d = a + j * d + i * d := by ring
    rwa [he] at h'

/-- If a set contains arbitrarily long progressions, then for each `k` it contains *infinitely
many* progressions of length `k`: the set of possible first terms is infinite. -/
