/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ### The shift matrices

`U n` is the matrix of the `n`-fold cyclic shift on `Fin 16`; the adjacency matrix of the
cycle graph `C₁₆` is `U 1 + U 15`. -/

/-- The matrix of the `n`-fold cyclic shift of `Fin 16`. -/

theorem dvd_huckelPoly_comp :
    (X ^ 16 - 1 : ℂ[X]) ∣ huckelPoly.comp (X + X ^ 15) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  set I : Ideal ℂ[X] := Ideal.span {(X ^ 16 - 1 : ℂ[X])} with hI
  have hIzero : Ideal.Quotient.mk I (X ^ 16 - 1 : ℂ[X]) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hq : huckelPoly.comp (X + X ^ 15)
      = ∏ k ∈ Finset.range 16, ((X + X ^ 15) - C (lamC k)) := by
    rw [huckelPoly, Polynomial.prod_comp]
    simp [sub_comp]
  rw [hq, map_prod]
  set x : ℂ[X] ⧸ I := Ideal.Quotient.mk I X with hx
  have hx16 : x ^ 16 = 1 := by
    rw [map_sub, map_one, map_pow, sub_eq_zero] at hIzero
    exact hIzero.symm ▸ rfl
  set y : ℕ → ℂ[X] ⧸ I := fun k => Ideal.Quotient.mk I (C (zt ^ k)) with hy
  set y' : ℕ → ℂ[X] ⧸ I := fun k => Ideal.Quotient.mk I (C (zt ^ (16 - k))) with hy'
  have hprod0 : ∏ k ∈ Finset.range 16, (x - y k) = 0 := by
    have hcast : ∀ k : ℕ, x - y k = Ideal.Quotient.mk I (X - C (zt ^ k)) := by
      intro k; rw [hx, hy, map_sub]
    rw [Finset.prod_congr rfl (fun k _ => hcast k), ← map_prod, prod_X_sub_zt]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hstep : ∀ k ∈ Finset.range 16,
      x * (x + x ^ 15 - Ideal.Quotient.mk I (C (lamC k))) = (x - y k) * (x - y' k) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hkle : k ≤ 16 := by omega
    have hc : Ideal.Quotient.mk I (C (lamC k)) = y k + y' k := by
      rw [lamC_eq k hkle, map_add, hy, hy', map_add]
    have hyy : y k * y' k = 1 := by
      rw [hy, hy', ← map_mul, ← map_mul, zt_pow_mul k hkle, map_one, map_one]
    rw [hc]
    linear_combination hx16 - hyy
  calc ∏ k ∈ Finset.range 16, (x + x ^ 15 - Ideal.Quotient.mk I (C (lamC k)))
      = x ^ 16 * ∏ k ∈ Finset.range 16, (x + x ^ 15 - Ideal.Quotient.mk I (C (lamC k))) := by
        rw [hx16, one_mul]
    _ = (∏ _k ∈ Finset.range 16, x) * ∏ k ∈ Finset.range 16,
          (x + x ^ 15 - Ideal.Quotient.mk I (C (lamC k))) := by
        rw [Finset.prod_const, Finset.card_range]
    _ = ∏ k ∈ Finset.range 16, (x * (x + x ^ 15 - Ideal.Quotient.mk I (C (lamC k)))) := by
        rw [Finset.prod_mul_distrib]
    _ = ∏ k ∈ Finset.range 16, ((x - y k) * (x - y' k)) := Finset.prod_congr rfl hstep
    _ = (∏ k ∈ Finset.range 16, (x - y k)) * ∏ k ∈ Finset.range 16, (x - y' k) := by
        rw [Finset.prod_mul_distrib]
    _ = 0 := by rw [hprod0, zero_mul]

/-- `∏_{k=0}^{15} (A - 2cos(2πk/16)) = 0` for the adjacency matrix `A` of `C₁₆`. -/
