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

/-
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

theorem log_le_prod_inv (z : ℕ) (hz : 1 ≤ z) :
    Real.log z ≤ ∏ p ∈ (z + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hnorm : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    show |((p:ℝ)⁻¹)| < 1
    rw [abs_of_nonneg (by positivity), inv_lt_one_iff₀]
    right; linarith
  obtain ⟨-, hsum⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := invHom) hnorm ((z + 1).primesBelow)
  have hfilter : ((z + 1).primesBelow).filter Nat.Prime = (z + 1).primesBelow :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primesBelow hp
  rw [hfilter] at hsum
  have hsub : ∀ n ∈ Finset.Icc 1 z, n ∈ Nat.factoredNumbers ((z + 1).primesBelow) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Nat.mem_factoredNumbers]
    refine ⟨by omega, fun p hp => ?_⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hpn : p ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactorsList hp)
    exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩
  have key := sum_le_hasSum (Finset.subtype (· ∈ Nat.factoredNumbers ((z + 1).primesBelow))
    (Finset.Icc 1 z)) (fun i _ => by
      show (0:ℝ) ≤ invHom (i : ℕ)
      exact inv_nonneg.mpr (Nat.cast_nonneg _)) hsum
  rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hsub] at key
  exact (log_le_sum_inv z hz).trans key

