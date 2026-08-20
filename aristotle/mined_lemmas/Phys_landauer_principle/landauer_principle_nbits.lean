import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Statement: Erasing one bit dissipates at least kT ln 2 of heat (Landauer).
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

namespace Phys

/-- The Gibbs (Boltzmann–Shannon) entropy `S = -k ∑ᵢ pᵢ log pᵢ` of a probability
distribution `p` on a finite set of microstates, with Boltzmann constant `k`. -/

theorem landauer_principle_nbits
    (n : ℕ) (k T Q : ℝ) (hT : 0 < T)
    (pInit pFinal : Fin (2 ^ n) → ℝ)
    (hInit : ∀ i, pInit i = ((2 : ℝ) ^ n)⁻¹)
    (i₀ : Fin (2 ^ n)) (hFinal : ∀ i, pFinal i = if i = i₀ then 1 else 0)
    (hSecondLaw : 0 ≤ (gibbsEntropy k pFinal - gibbsEntropy k pInit) + Q / T) :
    (n : ℝ) * (k * T * Real.log 2) ≤ Q := by
  haveI : Nonempty (Fin (2 ^ n)) := ⟨i₀⟩
  have hcard : (Fintype.card (Fin (2 ^ n)) : ℝ) = (2 : ℝ) ^ n := by
    simp
  have hSi : gibbsEntropy k pInit = (n : ℝ) * (k * Real.log 2) := by
    have h := gibbsEntropy_uniform (ι := Fin (2 ^ n)) k pInit (by
      intro i; rw [hInit i, hcard])
    rw [hcard, Real.log_pow] at h
    rw [h]; ring
  have hSf : gibbsEntropy k pFinal = 0 := gibbsEntropy_dirac k i₀ pFinal hFinal
  rw [hSi, hSf] at hSecondLaw
  have hQT : (n : ℝ) * (k * Real.log 2) ≤ Q / T := by linarith
  have h2 := mul_le_mul_of_nonneg_left hQT (le_of_lt hT)
  rw [mul_div_cancel₀ _ (ne_of_gt hT)] at h2
  nlinarith [h2]

end Phys

