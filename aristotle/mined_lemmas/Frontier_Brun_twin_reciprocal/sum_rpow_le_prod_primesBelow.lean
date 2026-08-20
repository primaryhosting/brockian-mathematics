import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma sum_rpow_le_prod_primesBelow (z : ℕ) {s : ℝ} (hs : 1 < s) :
    ∑ n ∈ Icc 1 z, (n : ℝ) ^ (-s) ≤ ∏ p ∈ Nat.primesBelow (z + 1), (1 - (p : ℝ) ^ (-s))⁻¹ := by
  have hsum : Summable (rpowHom s) := by
    have : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
      rw [Real.summable_nat_rpow]; linarith
    exact this
  have heq := EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hsum (z + 1)
  simp only [rpowHom_apply] at heq
  rw [heq]
  have hmem : ∀ n ∈ Icc 1 z, n ∈ Nat.smoothNumbers (z + 1) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [Nat.mem_smoothNumbers]
    refine ⟨by omega, fun p hp => ?_⟩
    have := Nat.le_of_mem_primeFactorsList hp
    omega
  set T : Finset (Nat.smoothNumbers (z + 1)) := (Icc 1 z).subtype _ with hT
  have h1 : ∑ x ∈ T, (rpowHom s) x = ∑ n ∈ Icc 1 z, (n : ℝ) ^ (-s) := by
    rw [hT, Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hmem]
    rfl
  have hsub : Summable (fun x : Nat.smoothNumbers (z + 1) => (rpowHom s) x) := hsum.subtype _
  have h2 : ∑ x ∈ T, (rpowHom s) x ≤ ∑' m : Nat.smoothNumbers (z + 1), (rpowHom s) m := by
    refine Summable.sum_le_tsum T (fun i _ => ?_) hsub
    rw [rpowHom_apply]
    positivity
  rw [← h1]
  exact h2

/-- `∏_{p ≤ z} (1 - 1/p) ≤ e / log z`. -/
