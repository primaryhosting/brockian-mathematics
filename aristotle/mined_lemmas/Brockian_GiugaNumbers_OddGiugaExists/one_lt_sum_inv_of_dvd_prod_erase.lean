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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite natural number `n > 1` such that
`p ∣ n / p - 1` for every prime `p` dividing `n`. -/

theorem one_lt_sum_inv_of_dvd_prod_erase {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime)
    (hcard : 2 ≤ S.card) (hdvd : ∀ p ∈ S, p ∣ (∏ q ∈ S.erase p, q) - 1) :
    1 < ∑ p ∈ S, (p : ℚ)⁻¹ := by
  classical
  set N : ℕ := ∏ p ∈ S, p with hN
  set T : ℕ := ∑ p ∈ S, ∏ q ∈ S.erase p, q with hT
  have hposq : ∀ p ∈ S, 1 ≤ ∏ q ∈ S.erase p, q := by
    intro p hpS
    refine Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 ?_)
    intro q hq
    exact (hp q (Finset.mem_of_mem_erase hq)).ne_zero
  have hT2 : 2 ≤ T := by
    have h := Finset.card_nsmul_le_sum S (fun p => ∏ q ∈ S.erase p, q) 1 hposq
    simp only [smul_eq_mul, mul_one] at h
    omega
  have hqdvd : ∀ q ∈ S, q ∣ T - 1 := by
    intro q hq
    have hsplit : T = (∏ r ∈ S.erase q, r) + ∑ p ∈ S.erase q, ∏ r ∈ S.erase p, r := by
      rw [hT, ← Finset.add_sum_erase _ _ hq]
    have h1 : q ∣ (∏ r ∈ S.erase q, r) - 1 := hdvd q hq
    have h2 : q ∣ ∑ p ∈ S.erase q, ∏ r ∈ S.erase p, r := by
      refine Finset.dvd_sum ?_
      intro p hpe
      have hpq : p ≠ q := (Finset.mem_erase.1 hpe).1
      exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨fun h => hpq h.symm, hq⟩)
    have hge1 : 1 ≤ ∏ r ∈ S.erase q, r := hposq q hq
    have hrw : T - 1 = ((∏ r ∈ S.erase q, r) - 1) + ∑ p ∈ S.erase q, ∏ r ∈ S.erase p, r := by
      omega
    rw [hrw]
    exact Nat.dvd_add h1 h2
  have hNdvd : N ∣ T - 1 :=
    Finset.prod_primes_dvd _ (fun a ha => (hp a ha).prime) hqdvd
  have hNpos : 0 < N := by
    refine Nat.pos_of_ne_zero ?_
    rw [hN]
    exact Finset.prod_ne_zero_iff.2 (fun q hq => (hp q hq).ne_zero)
  have hNT : N < T := by
    have := Nat.le_of_dvd (by omega) hNdvd
    omega
  have hsum : ∑ p ∈ S, (p : ℚ)⁻¹ = (T : ℚ) / (N : ℚ) := by
    rw [hT, hN]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro p hpS
    have hprod : (∏ q ∈ S, (q : ℚ)) = (p : ℚ) * ∏ q ∈ S.erase p, (q : ℚ) :=
      (Finset.mul_prod_erase _ _ hpS).symm
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hp p hpS).ne_zero
    have hq0 : (∏ q ∈ S.erase p, (q : ℚ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 (fun q hq => ?_)
      exact Nat.cast_ne_zero.2 (hp q (Finset.mem_of_mem_erase hq)).ne_zero
    rw [hprod]
    field_simp
  rw [hsum, lt_div_iff₀ (by exact_mod_cast hNpos)]
  simpa using (Nat.cast_lt (α := ℚ)).2 hNT

/-- The reciprocals of at most eight distinct odd primes sum to less than `1`. -/
