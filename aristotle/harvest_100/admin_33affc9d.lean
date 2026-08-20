import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to occur at the very beginning of a file,
before any module docstring, hence the header comment above appears just after the import.
-/

open Complex Polynomial Matrix

namespace Chem

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 18)

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 18 := by
  have := Complex.isPrimitiveRoot_exp 18 (by norm_num)
  simpa [zeta] using this

lemma zeta_pow_18 : zeta ^ 18 = 1 := zeta_isPrimitiveRoot.pow_eq_one

lemma zeta_ne_zero : zeta ≠ 0 := Complex.exp_ne_zero _

/-- Powers of an 18-th root of unity only depend on the exponent mod 18. -/
lemma pow_mod_eighteen (x : ℂ) (hx : x ^ 18 = 1) (a : ℕ) : x ^ (a % 18) = x ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 18]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

/-- The eigenvalue attached to index `k`: `2 cos (2πk/18)`. -/
noncomputable def mu (k : Fin 18) : ℂ := ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ)

/-- The (complex) adjacency matrix of the cycle graph `C₁₈`. -/
noncomputable def A : Matrix (Fin 18) (Fin 18) ℂ := (SimpleGraph.cycleGraph 18).adjMatrix ℂ

/-- The matrix of characters, `P i j = ζ ^ (i * j)`; a Vandermonde matrix. -/
noncomputable def P : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.vandermonde (fun i : Fin 18 => zeta ^ (i : ℕ))

lemma P_apply (i j : Fin 18) : P i j = zeta ^ ((i : ℕ) * (j : ℕ)) := by
  simp [P, Matrix.vandermonde, ← pow_mul]

lemma P_det_ne_zero : P.det ≠ 0 := by
  rw [P, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  simp only [Finset.mem_Ioi] at hj
  refine sub_ne_zero_of_ne ?_
  intro h
  exact absurd (Fin.ext (zeta_isPrimitiveRoot.pow_inj j.isLt i.isLt h)) hj.ne'

/-- Shifting the index by `+1` multiplies the power by `x`. -/
lemma pow_succ_fin (x : ℂ) (hx : x ^ 18 = 1) (i : Fin 18) :
    x ^ (((i + 1 : Fin 18)) : ℕ) = x ^ (i : ℕ) * x := by
  have h : ((i + 1 : Fin 18) : ℕ) = ((i : ℕ) + 1) % 18 := by simp [Fin.val_add]
  rw [h, pow_mod_eighteen x hx, pow_succ]

/-- Shifting the index by `-1` multiplies the power by `x ^ 17`. -/
lemma pow_pred_fin (x : ℂ) (hx : x ^ 18 = 1) (i : Fin 18) :
    x ^ (((i - 1 : Fin 18)) : ℕ) = x ^ (i : ℕ) * x ^ 17 := by
  have h : ((i - 1 : Fin 18) : ℕ) = ((i : ℕ) + 17) % 18 := by
    rw [Fin.sub_def]
    norm_num
    omega
  rw [h, pow_mod_eighteen x hx, pow_add]

/-- `ζ^(17k) + ζ^k = 2 cos (2πk/18)`. -/
lemma zeta_pow_add_inv (k : Fin 18) :
    (zeta ^ (k : ℕ)) ^ 17 + zeta ^ (k : ℕ) = mu k := by
  have hz : zeta ^ (k : ℕ) = Complex.exp (((2 * Real.pi * (k : ℕ) / 18 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h18 : (zeta ^ (k : ℕ)) ^ 18 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, zeta_pow_18, one_pow]
  have h17 : (zeta ^ (k : ℕ)) ^ 17 = (zeta ^ (k : ℕ))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h18)
  rw [h17, hz, ← Complex.exp_neg, mu, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

lemma A_mul_P : A * P = P * Matrix.diagonal mu := by
  ext i j
  have hne : (i - 1 : Fin 18) ≠ i + 1 := by
    intro h
    simp [Fin.ext_iff, Fin.sub_def, Fin.add_def] at h
    omega
  have hsum : (A * P) i j = P (i - 1) j + P (i + 1) j := by
    rw [Matrix.mul_apply]
    have hs : ∑ l, A i l * P l j
        = ∑ l ∈ (SimpleGraph.cycleGraph 18).neighborFinset i, P l j := by
      rw [A, SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
      simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
    rw [hs]
    have hnb : (SimpleGraph.cycleGraph 18).neighborFinset i = {i - 1, i + 1} := by
      have := @SimpleGraph.cycleGraph_neighborFinset 16 i
      simpa using this
    rw [hnb, Finset.sum_pair hne]
  rw [hsum, Matrix.mul_apply, Finset.sum_eq_single j]
  · simp only [Matrix.diagonal_apply_eq]
    rw [P_apply, P_apply, P_apply]
    rw [mul_comm (i : ℕ) (j : ℕ), mul_comm ((i - 1 : Fin 18) : ℕ) (j : ℕ),
      mul_comm ((i + 1 : Fin 18) : ℕ) (j : ℕ), pow_mul, pow_mul, pow_mul]
    have hx : (zeta ^ (j : ℕ)) ^ 18 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, zeta_pow_18, one_pow]
    rw [pow_pred_fin _ hx, pow_succ_fin _ hx, ← zeta_pow_add_inv j]
    ring
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ hb]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Hückel theory for C₁₈.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₈` is `∏ k, (X - 2 cos (2πk/18))`, i.e. the adjacency eigenvalues of `C₁₈`
(with multiplicity) are exactly `2 cos (2πk/18)` for `k = 0, …, 17`. -/
theorem huckel_C18 :
    ((SimpleGraph.cycleGraph 18).adjMatrix ℂ).charpoly =
      ∏ k : Fin 18, (X - C ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ)) := by
  have hunit : IsUnit P.det := isUnit_iff_ne_zero.mpr P_det_ne_zero
  let U : (Matrix (Fin 18) (Fin 18) ℂ)ˣ := Matrix.nonsingInvUnit P hunit
  have hUP : (U : Matrix (Fin 18) (Fin 18) ℂ) = P := rfl
  have hUinv : ((U⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) : Matrix (Fin 18) (Fin 18) ℂ) = P⁻¹ := rfl
  have hA : A = (U : Matrix (Fin 18) (Fin 18) ℂ) * Matrix.diagonal mu *
      ((U⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) : Matrix (Fin 18) (Fin 18) ℂ) := by
    rw [hUP, hUinv, ← A_mul_P, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
  calc ((SimpleGraph.cycleGraph 18).adjMatrix ℂ).charpoly = A.charpoly := rfl
    _ = (Matrix.diagonal mu).charpoly := by rw [hA, Matrix.charpoly_units_conj]
    _ = ∏ k : Fin 18, (X - C (mu k)) := Matrix.charpoly_diagonal mu
    _ = _ := rfl

/-- The spectrum of the adjacency matrix of `C₁₈` is exactly the set of Hückel energies
`{2 cos (2πk/18) : k = 0, …, 17}`. -/
theorem huckel_C18_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) =
      Set.range (fun k : Fin 18 => ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ)) := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, huckel_C18,
    Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Set.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by linear_combination -ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [ha]; ring⟩

end Chem

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

