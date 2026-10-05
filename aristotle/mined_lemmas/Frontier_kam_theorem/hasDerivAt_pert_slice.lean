import Mathlib
/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

variable {n : ℕ}

/-- The Euclidean pairing `⟨c, x⟩ = ∑ⱼ cⱼ xⱼ` on `Fin n → ℝ`. -/

lemma hasDerivAt_pert_slice (s : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → ℝ)
    (j : Fin n) (x : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => pert s a (Function.update x j t))
      (-(2 * Real.pi) * ∑ k ∈ s, a k * (k j : ℝ) * Real.sin (2 * Real.pi * dotZR k x)) (x j) := by
  have key : ∀ k ∈ s, HasDerivAt
      (fun t : ℝ => a k * Real.cos (2 * Real.pi * dotZR k (Function.update x j t)))
      (-(2 * Real.pi) * (a k * (k j : ℝ) * Real.sin (2 * Real.pi * dotZR k x))) (x j) := by
    intro k _
    have hinner : HasDerivAt
        (fun t : ℝ => 2 * Real.pi * (dotZR k x + (k j : ℝ) * (t - x j)))
        (2 * Real.pi * (k j : ℝ)) (x j) := by
      have h1 : HasDerivAt (fun t : ℝ => dotZR k x + (k j : ℝ) * (t - x j)) ((k j : ℝ)) (x j) := by
        simpa using (((hasDerivAt_id (x j)).sub_const (x j)).const_mul ((k j : ℝ))).const_add
          (dotZR k x)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h1.const_mul (2 * Real.pi)
    have hcos := (hinner.cos).const_mul (a k)
    have : (fun t : ℝ => a k * Real.cos (2 * Real.pi * dotZR k (Function.update x j t)))
        = fun t : ℝ => a k * Real.cos (2 * Real.pi * (dotZR k x + (k j : ℝ) * (t - x j))) := by
      funext t; rw [dotZR_update]
    rw [this]
    have hx : 2 * Real.pi * (dotZR k x + (k j : ℝ) * (x j - x j)) = 2 * Real.pi * dotZR k x := by
      ring
    convert hcos using 1
    rw [hx]
    ring
  have h := HasDerivAt.sum key
  have hf : (fun t : ℝ => pert s a (Function.update x j t))
      = ∑ k ∈ s, (fun t : ℝ => a k * Real.cos (2 * Real.pi * dotZR k (Function.update x j t))) := by
    funext t
    simp [pert, Finset.sum_apply]
  rw [hf, Finset.mul_sum]
  exact h

