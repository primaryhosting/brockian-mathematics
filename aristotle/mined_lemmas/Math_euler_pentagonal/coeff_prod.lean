/-
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
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

/-!
Euler's pentagonal number theorem.

We prove that the coefficient of `q^n` in the (truncated) product `∏_{i=1}^{N} (1 - q^i)`
(for any `N ≥ n`, so that the coefficient has already stabilised) equals
`∑_{k ∈ ℤ} (-1)^k [n = k(3k-1)/2]`.

The proof is Franklin's involution on partitions into distinct parts.
-/

namespace Math

open Finset

/-! ### Basic combinatorial gadgets -/

/-- `runLen s t` is the length of the maximal run `t, t-1, t-2, …` of consecutive
elements of `s` ending at `t`. -/

lemma coeff_prod (n N : ℕ) (h : n ≤ N) :
    (PowerSeries.coeff n) (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∑ s ∈ distinctParts n, (-1 : ℤ) ^ s.card := by
  classical
  have hprod : (∏ i ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i))
      = ∑ t ∈ (Finset.Icc 1 N).powerset,
          ((-1 : ℤ) ^ t.card) • ((PowerSeries.X : PowerSeries ℤ) ^ (∑ i ∈ t, i)) := by
    have hrw : ∀ i, (1 - (PowerSeries.X : PowerSeries ℤ) ^ i)
        = (-(PowerSeries.X : PowerSeries ℤ) ^ i) + 1 := by
      intro i; ring
    simp only [hrw]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl ?_
    intro t _
    simp only [Finset.prod_const_one, mul_one]
    rw [Finset.prod_neg, Finset.prod_pow_eq_pow_sum, zsmul_eq_mul]
    push_cast; ring
  rw [hprod, map_sum]
  simp only [map_smul, PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_powerset, mem_distinctParts]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum.symm⟩
    have := hsub h0; simp at this
  · rintro ⟨h0, hsum⟩
    refine ⟨fun a ha => ?_, hsum.symm⟩
    have h1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | hp
      · exact absurd ha h0
      · exact hp
    have h2 : a ≤ n := by
      rw [← hsum]; exact Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) ha
    simp only [Finset.mem_Icc, h1, true_and]
    omega

/-- **Euler's pentagonal number theorem**. For `n ≤ N`, the coefficient of `q^n` in the
product `∏_{i=1}^N (1 - q^i)` equals `∑_{k ∈ ℤ} (-1)^k [n = k(3k-1)/2]`. -/
