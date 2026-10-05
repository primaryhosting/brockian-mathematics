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
noncomputable def U (n : ℕ) : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun i j => if (j : ℕ) = ((i : ℕ) + n) % 16 then 1 else 0

theorem U_mul (m n : ℕ) : U m * U n = U (m + n) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [U, Matrix.of_apply]
  rw [Finset.sum_eq_single (⟨((i : ℕ) + m) % 16, by omega⟩ : Fin 16)]
  · have h : (((i : ℕ) + m) % 16 + n) % 16 = ((i : ℕ) + (m + n)) % 16 := by omega
    simp [h]
  · intro b _ hb
    have h : (b : ℕ) ≠ ((i : ℕ) + m) % 16 := fun h => hb (Fin.ext h)
    simp [h]
  · intro h
    simp at h

theorem U_one_pow (n : ℕ) : (U 1) ^ n = U n := by
  induction n with
  | zero =>
    ext i j
    simp [U, Matrix.one_apply, Nat.mod_eq_of_lt i.isLt, eq_comm, Fin.ext_iff]
  | succ n ih => rw [pow_succ, ih, U_mul, Nat.add_comm]

theorem U_sixteen : U 16 = 1 := by
  ext i j
  have h : ((i : ℕ) + 16) % 16 = (i : ℕ) := by omega
  simp only [U, Matrix.of_apply, h, Matrix.one_apply, Fin.ext_iff]
  by_cases hij : (i : ℕ) = (j : ℕ) <;> simp [hij, eq_comm]

theorem U_mulVec (n : ℕ) (v : Fin 16 → ℂ) (i : Fin 16) :
    (U n *ᵥ v) i = v ⟨((i : ℕ) + n) % 16, by omega⟩ := by
  rw [Matrix.mulVec]
  simp only [dotProduct, U, Matrix.of_apply]
  rw [Finset.sum_eq_single (⟨((i : ℕ) + n) % 16, by omega⟩ : Fin 16)]
  · simp
  · intro b _ hb
    have h : (b : ℕ) ≠ ((i : ℕ) + n) % 16 := fun h => hb (Fin.ext h)
    simp [h]
  · intro h
    simp at h

theorem adj_iff : ∀ i j : Fin 16, (SimpleGraph.cycleGraph 16).Adj i j ↔
    ((j : ℕ) = ((i : ℕ) + 1) % 16 ∨ (j : ℕ) = ((i : ℕ) + 15) % 16) := by decide

/-- The adjacency matrix of the cycle graph `C₁₆` is the sum of the two cyclic shifts. -/
theorem adjMatrix_eq : (SimpleGraph.cycleGraph 16).adjMatrix ℂ = U 1 + U 15 := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply]
  simp only [U, Matrix.add_apply, Matrix.of_apply, adj_iff]
  have hi := i.isLt
  by_cases h1 : (j : ℕ) = ((i : ℕ) + 1) % 16 <;> by_cases h2 : (j : ℕ) = ((i : ℕ) + 15) % 16 <;>
    simp [h1, h2] <;> omega

/-! ### The 16th roots of unity -/

/-- A primitive 16th root of unity. -/
noncomputable def zt : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

theorem zt_prim : IsPrimitiveRoot zt 16 := Complex.isPrimitiveRoot_exp 16 (by norm_num)

theorem zt_pow16 : zt ^ 16 = 1 := zt_prim.pow_eq_one

theorem zt_pow_mul (k : ℕ) (hk : k ≤ 16) : zt ^ k * zt ^ (16 - k) = 1 := by
  rw [← pow_add, Nat.add_sub_cancel' hk, zt_pow16]

theorem zt_pow_eq (k : ℕ) : zt ^ k = Complex.exp ((2 * Real.pi * k / 16 : ℝ) * Complex.I) := by
  rw [zt, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem prod_X_sub_zt : ∏ i ∈ Finset.range 16, (X - C (zt ^ i)) = X ^ 16 - 1 := by
  have h := X_pow_sub_C_eq_prod zt_prim (by norm_num) (one_pow 16)
  simp only [mul_one, map_one] at h
  rw [← h]

/-- The `k`-th Hückel eigenvalue `2·cos(2πk/16)`, viewed as a complex number. -/
noncomputable def lamC (k : ℕ) : ℂ := 2 * Real.cos (2 * Real.pi * k / 16)

theorem lamC_eq (k : ℕ) (hk : k ≤ 16) : lamC k = zt ^ k + zt ^ (16 - k) := by
  have h1 : zt ^ (16 - k) = (zt ^ k)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact zt_pow_mul k hk)
  rw [lamC, h1, zt_pow_eq k, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  push_cast
  ring_nf

/-! ### An annihilating polynomial for the adjacency matrix -/

/-- The polynomial `∏_{k=0}^{15} (X - 2cos(2πk/16))`. -/
noncomputable def huckelPoly : ℂ[X] := ∏ k ∈ Finset.range 16, (X - C (lamC k))

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
theorem aeval_huckelPoly :
    aeval ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) huckelPoly = 0 := by
  have hA : (SimpleGraph.cycleGraph 16).adjMatrix ℂ = aeval (U 1) (X + X ^ 15 : ℂ[X]) := by
    rw [adjMatrix_eq]
    simp [U_one_pow]
  rw [hA, ← Polynomial.aeval_comp]
  obtain ⟨r, hr⟩ := dvd_huckelPoly_comp
  rw [hr, map_mul]
  have h16 : aeval (U 1) (X ^ 16 - 1 : ℂ[X]) = 0 := by
    simp [U_one_pow, U_sixteen]
  rw [h16, zero_mul]

/-! ### The two inclusions -/

theorem spectrum_subset :
    spectrum ℂ ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) ⊆
      {z : ℂ | ∃ k : Fin 16, z = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 16)} := by
  intro w hw
  have hmem : Polynomial.eval w huckelPoly ∈
      spectrum ℂ (aeval ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) huckelPoly) :=
    spectrum.subset_polynomial_aeval _ huckelPoly ⟨w, hw, rfl⟩
  rw [aeval_huckelPoly, spectrum.zero_eq] at hmem
  have hzero : Polynomial.eval w huckelPoly = 0 := hmem
  rw [huckelPoly, Polynomial.eval_prod] at hzero
  simp only [eval_sub, eval_X, eval_C] at hzero
  obtain ⟨k, hk, hk0⟩ := Finset.prod_eq_zero_iff.1 hzero
  simp only [Finset.mem_range] at hk
  refine ⟨⟨k, hk⟩, ?_⟩
  have : w = lamC k := sub_eq_zero.1 hk0
  rw [this, lamC]

theorem spectrum_superset :
    {z : ℂ | ∃ k : Fin 16, z = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 16)} ⊆
      spectrum ℂ ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) := by
  rintro w ⟨k, rfl⟩
  set m : ℂ := zt ^ (k : ℕ) with hm
  have hm16 : m ^ 16 = 1 := by
    rw [hm, ← pow_mul, mul_comm, pow_mul, zt_pow16, one_pow]
  have hmmod : ∀ n : ℕ, m ^ (n % 16) = m ^ n := by
    intro n
    conv_rhs => rw [← Nat.div_add_mod n 16]
    rw [pow_add, pow_mul, hm16, one_pow, one_mul]
  -- the eigenvalue equals `m + m^15`
  have hlam : (2 * Real.cos (2 * Real.pi * (k : ℕ) / 16) : ℂ) = m + m ^ 15 := by
    have h1 : lamC (k : ℕ) = zt ^ (k : ℕ) + zt ^ (16 - (k : ℕ)) :=
      lamC_eq _ (le_of_lt k.isLt)
    have h2 : zt ^ (16 - (k : ℕ)) = m ^ 15 := by
      have hne : zt ^ (k : ℕ) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
      have e1 : zt ^ (k : ℕ) * zt ^ (16 - (k : ℕ)) = 1 := zt_pow_mul _ (le_of_lt k.isLt)
      have e2 : zt ^ (k : ℕ) * m ^ 15 = 1 := by
        rw [hm, ← pow_mul, ← pow_add]
        have : (k : ℕ) + (k : ℕ) * 15 = 16 * (k : ℕ) := by ring
        rw [this, pow_mul, zt_pow16, one_pow]
      exact mul_left_cancel₀ hne (e1.trans e2.symm)
    rw [← lamC, h1, h2]
  -- the eigenvector
  set v : Fin 16 → ℂ := fun j => m ^ (j : ℕ) with hv
  have hvne : v ≠ 0 := by
    intro h
    have h0 : v 0 = 0 := by rw [h]; rfl
    rw [hv] at h0
    simp at h0
  have hAv : (SimpleGraph.cycleGraph 16).adjMatrix ℂ *ᵥ v = (m + m ^ 15) • v := by
    funext i
    rw [adjMatrix_eq, Matrix.add_mulVec]
    simp only [Pi.add_apply, U_mulVec, hv, Pi.smul_apply, smul_eq_mul]
    rw [hmmod, hmmod, pow_add, pow_add]
    ring
  -- hence `m + m^15` is in the spectrum
  rw [spectrum.mem_iff]
  intro hunit
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
  apply hunit
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hvne, ?_⟩
  rw [Matrix.sub_mulVec, hAv, hlam, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_self]

/-- **Hückel theory for the C₁₆ annulene ring.**  The eigenvalues of the adjacency matrix of the
cycle graph `C₁₆` are exactly the numbers `2·cos(2πk/16)` for `k = 0, …, 15`. -/
theorem huckel_C16 :
    spectrum ℂ ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) =
      {z : ℂ | ∃ k : Fin 16, z = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 16)} :=
  Set.Subset.antisymm spectrum_subset spectrum_superset

end Chem

