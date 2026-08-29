import Mathlib
import RequestProject.Fock
/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
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

set_option grind.warning false

namespace Frontier

open scoped InnerProductSpace

/-- The cyclotron frequency `ω_c = q B / m` of a particle of charge `q` and mass `m`
in a uniform magnetic field of strength `B`. -/

theorem fockInner_definite (p : ℕ →₀ ℂ) (h : fockInner p p = 0) : p = 0 := by
  rw [fockInner_self] at h
  have hsum : (∑ n ∈ p.support, (n ! : ℝ) * Complex.normSq (p n)) = 0 := by exact_mod_cast h
  have hnonneg : ∀ n ∈ p.support, 0 ≤ (n ! : ℝ) * Complex.normSq (p n) := fun n _ =>
    mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  ext n
  by_cases hn : n ∈ p.support
  · have h2 := hzero n hn
    have hns : Complex.normSq (p n) = 0 := by
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (by positivity)
      · exact h3
    simpa using Complex.normSq_eq_zero.mp hns
  · simp [Finsupp.notMem_support_iff.mp hn]

