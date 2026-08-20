/-
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

namespace Frontier.Spectral

open Complex Finset Matrix

/-! ## Definitions -/

/-- The `n`-th root of unity `exp (2πI/n)`. -/

theorem cycleVec_sum {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    ∑ m : Fin n, cycleVec n m * zetaN n ^ ((n - (m : ℕ)) * (k : ℕ)) = cycleEig n k := by
  have hn0 : n ≠ 0 := by omega
  have hz0 : zetaN n ≠ 0 := zetaN_ne_zero n
  have hpow : ∀ a : ℕ, zetaN n ^ (n * a) = 1 := by
    intro a
    rw [pow_mul, zetaN_pow_n hn0, one_pow]
  obtain ⟨a0, ha0⟩ : ∃ a : Fin n, (a : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a : Fin n, (a : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a : Fin n, (a : ℕ) = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
  have hsub : ({a0, a1, a2} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ m ∈ (Finset.univ : Finset (Fin n)), m ∉ ({a0, a1, a2} : Finset (Fin n)) →
      cycleVec n m * zetaN n ^ ((n - (m : ℕ)) * (k : ℕ)) = 0 := by
    intro m _ hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, ha0, ha1, ha2] at hm
    obtain ⟨h0, h1, h2⟩ := hm
    simp [cycleVec, h0, h1, h2]
  rw [← Finset.sum_subset hsub hzero,
    Finset.sum_insert (by simp [Finset.mem_insert, Fin.ext_iff, ha0, ha1, ha2]; omega),
    Finset.sum_insert (by simp [Finset.mem_singleton, Fin.ext_iff, ha1, ha2]; omega),
    Finset.sum_singleton]
  have e0 : cycleVec n a0 * zetaN n ^ ((n - (a0 : ℕ)) * (k : ℕ)) = 2 := by
    have hv : cycleVec n a0 = 2 := by simp [cycleVec, ha0]
    rw [hv, ha0, Nat.sub_zero, hpow, mul_one]
  have e1 : cycleVec n a1 * zetaN n ^ ((n - (a1 : ℕ)) * (k : ℕ)) = -(zetaN n ^ (k : ℕ))⁻¹ := by
    have hv : cycleVec n a1 = -1 := by simp [cycleVec, ha1]
    have hmul : (zetaN n ^ ((n - 1) * (k : ℕ))) * (zetaN n ^ (k : ℕ)) = 1 := by
      rw [← pow_add]
      have hexp : (n - 1) * (k : ℕ) + (k : ℕ) = n * (k : ℕ) := by
        have : 1 ≤ n := by omega
        cases' Nat.exists_eq_add_of_le this with c hc
        subst hc
        simp [Nat.add_mul]
        ring
      rw [hexp, hpow]
    have hinv : zetaN n ^ ((n - 1) * (k : ℕ)) = (zetaN n ^ (k : ℕ))⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul
    rw [hv, ha1, hinv]
    ring
  have e2 : cycleVec n a2 * zetaN n ^ ((n - (a2 : ℕ)) * (k : ℕ)) = -(zetaN n ^ (k : ℕ)) := by
    have hv : cycleVec n a2 = -1 := by
      have hne : n - 1 ≠ 0 := by omega
      simp [cycleVec, hne, ha2]
    have hn1 : n - (a2 : ℕ) = 1 := by rw [ha2]; omega
    rw [hv, hn1, one_mul]
    ring
  rw [e0, e1, e2, cycleEig]
  have hcos := zetaN_pow_add_inv hn0 (k : ℕ)
  push_cast at hcos ⊢
  linear_combination -hcos

