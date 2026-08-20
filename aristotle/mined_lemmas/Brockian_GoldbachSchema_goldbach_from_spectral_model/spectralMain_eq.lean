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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat

namespace Brockian.GoldbachSchema

open Finset Complex

/-- The primes below `n`, i.e. the support of the spectral model at level `n`. -/

theorem spectralMain_eq (n : ℕ) (hn : n ≠ 0) :
    spectralMain n = n * goldbachCount n := by
  have hfilter : (primesBelow n ×ˢ primesBelow n).filter (fun pq => n ∣ pq.1 + pq.2)
      = (primesBelow n ×ˢ primesBelow n).filter (fun pq => pq.1 + pq.2 = n) := by
    apply Finset.filter_congr
    intro pq hpq
    simp only [primesBelow, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hpq
    obtain ⟨⟨hp1, hp2⟩, hq1, hq2⟩ := hpq
    constructor
    · rintro ⟨c, hc⟩
      have := hp2.two_le
      have := hq2.two_le
      have hc2 : c < 2 := by nlinarith [hc]
      interval_cases c <;> omega
    · rintro rfl; exact dvd_rfl
  have hsq : ∀ j : ℕ, spectralSum n j ^ 2
      = ∑ pq ∈ primesBelow n ×ˢ primesBelow n, zeta n ^ ((pq.1 + pq.2) * j) := by
    intro j
    rw [sq, spectralSum, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rw [← pow_add]; ring_nf
  rw [spectralMain, Finset.sum_congr rfl (fun j _ => hsq j), Finset.sum_comm,
    Finset.sum_congr rfl (fun pq (_ : pq ∈ primesBelow n ×ˢ primesBelow n) =>
      sum_zeta_pow n hn (pq.1 + pq.2)),
    Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
    hfilter, goldbachCount, mul_comm]

