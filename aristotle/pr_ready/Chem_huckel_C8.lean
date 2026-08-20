/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Statement: The adjacency eigenvalues of the cycle graph C_8 are 2·cos(2πk/8) for k=0..7.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C₈` (the Hückel π-system of cyclooctatetraene)
are `2 cos (2πk/8)` for `k = 0, …, 7`.  This is expressed as a complete factorisation of the
characteristic polynomial of the adjacency matrix of `SimpleGraph.cycleGraph 8`.

The proof diagonalises the adjacency matrix by the discrete Fourier matrix built from the
primitive eighth root of unity `ω = (√2/2)(1 + i)`.
-/

open Matrix Complex Polynomial SimpleGraph

namespace Chem

/-- The primitive eighth root of unity `exp (2πi/8) = (√2/2)(1 + i)`. -/
noncomputable def om : ℂ := (Real.sqrt 2 / 2) + (Real.sqrt 2 / 2) * I

lemma om_sq : om ^ 2 = I := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [om]
  apply Complex.ext <;> (simp [pow_two, Complex.add_re, Complex.mul_re]; try nlinarith [h])

lemma om_pow8 : om ^ 8 = 1 := by
  have h : om ^ 8 = (om ^ 2) ^ 4 := by ring
  rw [h, om_sq]; simp [pow_succ, Complex.I_mul_I]

lemma om_shift (n : ℕ) (h : 8 ≤ n) : om ^ n = om ^ (n - 8) := by
  conv_lhs => rw [show n = (n - 8) + 8 by omega]
  rw [pow_add, om_pow8, mul_one]

lemma om_reduce (n r q : ℕ) (h : n = r + 8 * q) : om ^ n = om ^ r := by
  subst h; rw [pow_add, pow_mul, om_pow8, one_pow, mul_one]

lemma om3 : om ^ 3 = I * om := by rw [pow_succ, om_sq]
lemma om4 : om ^ 4 = -1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, om_sq, Complex.I_sq]
lemma om5 : om ^ 5 = -om := by rw [pow_succ, om4]; ring
lemma om6 : om ^ 6 = -I := by rw [show (6 : ℕ) = 2 + 4 from rfl, pow_add, om_sq, om4]; ring
lemma om7 : om ^ 7 = -(I * om) := by
  rw [show (7 : ℕ) = 3 + 4 from rfl, pow_add, om3, om4]; ring

/-- The (unnormalised) discrete Fourier matrix; its columns are the eigenvectors of the
adjacency matrix of the cycle `C₈`. -/
noncomputable def dft : Matrix (Fin 8) (Fin 8) ℂ := fun j k => om ^ (j.val * k.val)

/-- The inverse of `dft`. -/
noncomputable def dftInv : Matrix (Fin 8) (Fin 8) ℂ :=
  fun j k => (1 / 8 : ℂ) * om ^ (7 * (j.val * k.val))

/-- The diagonal matrix of eigenvalues `ω^k + ω^(-k)`. -/
noncomputable def eigDiag : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal fun k : Fin 8 => om ^ k.val + om ^ (7 * k.val)

set_option maxHeartbeats 4000000 in
lemma dft_mul_dftInv : dft * dftInv = 1 := by
  ext j l
  fin_cases j <;> fin_cases l <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_eight, dft, dftInv, Matrix.one_apply] <;>
    ring_nf <;>
    norm_num [om_shift, om_sq, om3, om4, om5, om6, om7] <;>
    try ring

set_option maxHeartbeats 4000000 in
lemma dftInv_mul_dft : dftInv * dft = 1 := by
  ext j l
  fin_cases j <;> fin_cases l <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_eight, dft, dftInv, Matrix.one_apply] <;>
    ring_nf <;>
    norm_num [om_shift, om_sq, om3, om4, om5, om6, om7] <;>
    try ring

set_option maxHeartbeats 4000000 in
lemma adj_mul_dft : ((cycleGraph 8).adjMatrix ℂ) * dft = dft * eigDiag := by
  ext j l
  fin_cases j <;> fin_cases l <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_eight, dft, eigDiag, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply] <;>
    norm_num +decide <;>
    ring_nf <;>
    norm_num [om_shift, om_sq, om3, om4, om5, om6, om7] <;>
    try ring

lemma adj_eq_conj : ((cycleGraph 8).adjMatrix ℂ) = dft * eigDiag * dftInv := by
  rw [← adj_mul_dft, mul_assoc, dft_mul_dftInv, mul_one]

lemma charpoly_adj_complex :
    ((cycleGraph 8).adjMatrix ℂ).charpoly = eigDiag.charpoly := by
  rw [adj_eq_conj, mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, dftInv_mul_dft, mul_one]

/-- The `k`-th eigenvalue `ω^k + ω^(-k)` equals `2 cos (2πk/8)`. -/
lemma eig_entry (k : ℕ) (hk : k < 8) :
    om ^ k + om ^ (7 * k) = ((2 * Real.cos (2 * Real.pi * k / 8) : ℝ) : ℂ) := by
  interval_cases k
  · rw [show (2 * Real.pi * ((0:ℕ):ℝ) / 8 : ℝ) = 0 by push_cast; ring, Real.cos_zero]
    norm_num
  · rw [show (2 * Real.pi * ((1:ℕ):ℝ) / 8 : ℝ) = Real.pi / 4 by push_cast; ring,
      Real.cos_pi_div_four]
    rw [show (7 * 1 : ℕ) = 7 from rfl, om7, pow_one, om]
    push_cast
    apply Complex.ext <;> (simp; try ring)
  · rw [show (2 * Real.pi * ((2:ℕ):ℝ) / 8 : ℝ) = Real.pi / 2 by push_cast; ring,
      Real.cos_pi_div_two]
    rw [show (7 * 2 : ℕ) = 14 from rfl, om_reduce 14 6 1 rfl, om6, om_sq]
    norm_num
  · rw [show (2 * Real.pi * ((3:ℕ):ℝ) / 8 : ℝ) = Real.pi - Real.pi / 4 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
    rw [show (7 * 3 : ℕ) = 21 from rfl, om_reduce 21 5 2 rfl, om5, om3, om]
    push_cast
    apply Complex.ext <;> (simp; try ring)
  · rw [show (2 * Real.pi * ((4:ℕ):ℝ) / 8 : ℝ) = Real.pi by push_cast; ring, Real.cos_pi]
    rw [show (7 * 4 : ℕ) = 28 from rfl, om_reduce 28 4 3 rfl, om4]
    norm_num
  · rw [show (2 * Real.pi * ((5:ℕ):ℝ) / 8 : ℝ) = Real.pi + Real.pi / 4 by push_cast; ring,
      Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_four]
    rw [show (7 * 5 : ℕ) = 35 from rfl, om_reduce 35 3 4 rfl, om5, om3, om]
    push_cast
    apply Complex.ext <;> (simp; try ring)
  · rw [show (2 * Real.pi * ((6:ℕ):ℝ) / 8 : ℝ) = Real.pi + Real.pi / 2 by push_cast; ring,
      Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
    rw [show (7 * 6 : ℕ) = 42 from rfl, om_reduce 42 2 5 rfl, om6, om_sq]
    norm_num
  · rw [show (2 * Real.pi * ((7:ℕ):ℝ) / 8 : ℝ) = 2 * Real.pi - Real.pi / 4 by push_cast; ring,
      Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_four]
    rw [show (7 * 7 : ℕ) = 49 from rfl, om_reduce 49 1 6 rfl, om7, pow_one, om]
    push_cast
    apply Complex.ext <;> (simp; try ring)

/-- Complex form: the characteristic polynomial of the adjacency matrix of `C₈` factors as
`∏_{k=0}^{7} (X - 2 cos (2πk/8))`. -/
theorem huckel_C8_complex :
    ((cycleGraph 8).adjMatrix ℂ).charpoly =
      ∏ k : Fin 8, (X - C ((2 * Real.cos (2 * Real.pi * k.val / 8) : ℝ) : ℂ)) := by
  rw [charpoly_adj_complex, eigDiag, Matrix.charpoly_diagonal]
  exact Finset.prod_congr rfl fun k _ => by rw [eig_entry k.val k.isLt]

lemma adjMatrix_map :
    ((cycleGraph 8).adjMatrix ℝ).map (algebraMap ℝ ℂ) = (cycleGraph 8).adjMatrix ℂ := by
  ext i j
  simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply]
  split <;> simp

/-- **Hückel theory for cyclic C₈ (cyclooctatetraene).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₈` is
`∏_{k=0}^{7} (X - 2 cos (2πk/8))`; equivalently, the adjacency eigenvalues of `C₈` are exactly
`2 cos (2πk/8)` for `k = 0, …, 7`, counted with multiplicity. -/
theorem huckel_C8 :
    ((cycleGraph 8).adjMatrix ℝ).charpoly =
      ∏ k : Fin 8, (X - C (2 * Real.cos (2 * Real.pi * k.val / 8))) := by
  have hinj : Function.Injective (Polynomial.map (algebraMap ℝ ℂ)) :=
    Polynomial.map_injective _ (algebraMap ℝ ℂ).injective
  apply hinj
  rw [← Matrix.charpoly_map, adjMatrix_map, huckel_C8_complex, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun k _ => by
    simp [Polynomial.map_sub]

end Chem


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

