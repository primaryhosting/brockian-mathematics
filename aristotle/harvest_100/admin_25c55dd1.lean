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

/-!
# Hückel theory for the cycle graph `C₁₄`

The adjacency eigenvalues of the cycle graph `C₁₄` (the Hückel eigenvalues, in units of the
resonance integral β, of a cyclic conjugated system with 14 centres such as [14]annulene)
are `2 * cos (2 * π * k / 14)` for `k = 0, …, 13`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier matrix
`Pm j k = ζ ^ (j * k)`, where `ζ = exp (2 * π * I / 14)` is a primitive 14-th root of unity.
-/

namespace Chem

open Complex Matrix SimpleGraph Polynomial

attribute [local instance] Fin.instCommRing

/-- A primitive 14-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 14)

theorem om_prim : IsPrimitiveRoot om 14 := Complex.isPrimitiveRoot_exp 14 (by norm_num)

theorem om_pow_mod (a : ℕ) : om ^ (a % 14) = om ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 14]
  rw [pow_add, pow_mul, om_prim.pow_eq_one, one_pow, one_mul]

theorem om_pow_congr {a b : ℕ} (h : a ≡ b [MOD 14]) : om ^ a = om ^ b := by
  rw [← om_pow_mod a, ← om_pow_mod b, h]

/-- The character `a ↦ om ^ a` of `Fin 14` (viewed as `ℤ/14ℤ`). -/
noncomputable def zeta (a : Fin 14) : ℂ := om ^ a.val

theorem zeta_mul (a b : Fin 14) : zeta (a * b) = om ^ (a.val * b.val) := by
  unfold zeta; exact om_pow_congr (Nat.mod_modEq _ _)

theorem zeta_add (a b : Fin 14) : zeta (a + b) = zeta a * zeta b := by
  unfold zeta; rw [← pow_add]; exact om_pow_congr (Nat.mod_modEq _ _)

theorem zeta_pow (a b : Fin 14) : zeta (a * b) = zeta b ^ a.val := by
  rw [zeta_mul, zeta, ← pow_mul, mul_comm]

theorem zeta_eq_one_iff (a : Fin 14) : zeta a = 1 ↔ a = 0 := by
  constructor
  · intro h
    exact Fin.ext (Nat.eq_zero_of_dvd_of_lt ((om_prim.pow_eq_one_iff_dvd a.val).mp h) a.isLt)
  · rintro rfl; simp [zeta]

theorem zeta_pow_fourteen (a : Fin 14) : zeta a ^ 14 = 1 := by
  rw [zeta, ← pow_mul, mul_comm, pow_mul, om_prim.pow_eq_one, one_pow]

/-- Orthogonality of the characters of `ℤ/14ℤ`. -/
theorem sum_zeta (c : Fin 14) : ∑ k : Fin 14, zeta (k * c) = if c = 0 then 14 else 0 := by
  simp only [zeta_pow]
  rw [Fin.sum_univ_eq_sum_range (fun i => zeta c ^ i) 14]
  by_cases hc : c = 0
  · simp [hc, zeta]
  · rw [if_neg hc, geom_sum_eq (by simpa [zeta_eq_one_iff] using hc), zeta_pow_fourteen]
    simp

theorem zeta_eq_exp (a : Fin 14) :
    zeta a = Complex.exp ((2 * Real.pi * a.val / 14 : ℝ) * Complex.I) := by
  rw [zeta, om, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem zeta_add_zeta_neg (k : Fin 14) :
    zeta k + zeta (-k) = 2 * (Real.cos (2 * Real.pi * k.val / 14) : ℂ) := by
  have h1 : zeta k * zeta (-k) = 1 := by rw [← zeta_add]; simp [zeta]
  have h2 : zeta (-k) = (zeta k)⁻¹ := (DivisionMonoid.inv_eq_of_mul _ _ h1).symm
  rw [h2, zeta_eq_exp, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  push_cast
  ring_nf

/-- The discrete Fourier matrix of order 14. -/
noncomputable def Pm : Matrix (Fin 14) (Fin 14) ℂ := Matrix.of fun j k => zeta (j * k)

/-- The inverse discrete Fourier matrix of order 14. -/
noncomputable def Qm : Matrix (Fin 14) (Fin 14) ℂ :=
  Matrix.of fun j k => (14 : ℂ)⁻¹ * zeta (-(j * k))

/-- The diagonal matrix of Hückel eigenvalues of `C₁₄`. -/
noncomputable def Dm : Matrix (Fin 14) (Fin 14) ℂ :=
  Matrix.diagonal fun k => 2 * (Real.cos (2 * Real.pi * k.val / 14) : ℂ)

theorem Pm_mul_Qm : Pm * Qm = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : Fin 14, Pm i k * Qm k j = (14 : ℂ)⁻¹ * zeta (k * (i - j)) := by
    intro k
    show zeta (i * k) * ((14 : ℂ)⁻¹ * zeta (-(k * j))) = _
    rw [show k * (i - j) = i * k + -(k * j) by ring, zeta_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, sum_zeta]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (by simpa [sub_eq_zero] using hij), Matrix.one_apply_ne hij]
    ring

theorem Qm_mul_Pm : Qm * Pm = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : Fin 14, Qm i k * Pm k j = (14 : ℂ)⁻¹ * zeta (k * (j - i)) := by
    intro k
    show (14 : ℂ)⁻¹ * zeta (-(i * k)) * zeta (k * j) = _
    rw [show k * (j - i) = -(i * k) + k * j by ring, zeta_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, sum_zeta]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (by simpa [sub_eq_zero] using Ne.symm hij), Matrix.one_apply_ne hij]
    ring

theorem sub_one_ne_add_one (i : Fin 14) : i - 1 ≠ i + 1 := by
  intro h
  have h2 : (2 : Fin 14) = 0 := by
    have := sub_eq_iff_eq_add.mp h
    omega
  exact absurd h2 (by decide)

/-- The adjacency matrix of `C₁₄` is diagonalised by the discrete Fourier matrix. -/
theorem adjMatrix_mul_Pm : (SimpleGraph.cycleGraph 14).adjMatrix ℂ * Pm = Pm * Dm := by
  ext i k
  rw [SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one i), Dm, Matrix.mul_diagonal]
  show zeta ((i - 1) * k) + zeta ((i + 1) * k) = zeta (i * k) * _
  rw [show (i - 1) * k = i * k + -k by ring, show (i + 1) * k = i * k + k by ring,
    zeta_add, zeta_add, ← mul_add, add_comm (zeta (-k)), zeta_add_zeta_neg]

/-- The discrete Fourier matrix as a unit of the matrix ring. -/
noncomputable def Pu : (Matrix (Fin 14) (Fin 14) ℂ)ˣ := ⟨Pm, Qm, Pm_mul_Qm, Qm_mul_Pm⟩

/-- **Hückel eigenvalues of the 14-cycle.** The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₄` is `∏ k < 14, (X - 2 cos (2 π k / 14))`; that is, the
adjacency eigenvalues of `C₁₄` are `2 cos (2 π k / 14)` for `k = 0, …, 13`. -/
theorem huckel_C14 :
    ((SimpleGraph.cycleGraph 14).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 14,
        (Polynomial.X - Polynomial.C ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ)) := by
  have hA : (SimpleGraph.cycleGraph 14).adjMatrix ℂ = Pu.val * Dm * (Pu⁻¹).val := by
    show _ = Pm * Dm * Qm
    rw [← adjMatrix_mul_Pm, mul_assoc, Pm_mul_Qm, mul_one]
  rw [hA, Matrix.charpoly_units_conj, Dm, Matrix.charpoly_diagonal,
    Fin.prod_univ_eq_prod_range
      (fun i => (X : ℂ[X]) - C (2 * (Real.cos (2 * Real.pi * i / 14) : ℂ))) 14]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  push_cast
  ring

/-- The spectrum of the adjacency matrix of `C₁₄` is exactly the set of the
14 Hückel eigenvalues `2 cos (2 π k / 14)`, `k = 0, …, 13`. -/
theorem huckel_C14_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 14).adjMatrix ℂ) =
      {mu : ℂ | ∃ k : ℕ, k < 14 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ)} := by
  ext mu
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C14, Polynomial.IsRoot,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_range, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero, Set.mem_setOf_eq]

/-- The explicit Hückel molecular orbitals: the vector `j ↦ exp (2 π i j k / 14)` is an
eigenvector of the adjacency matrix of `C₁₄` with eigenvalue `2 cos (2 π k / 14)`. -/
theorem huckel_C14_eigenvector (k : Fin 14) :
    (SimpleGraph.cycleGraph 14).adjMatrix ℂ *ᵥ (fun j => zeta (j * k)) =
      (2 * (Real.cos (2 * Real.pi * k.val / 14) : ℂ)) • (fun j => zeta (j * k)) := by
  funext i
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one i)]
  rw [show (i - 1) * k = i * k + -k by ring, show (i + 1) * k = i * k + k by ring,
    zeta_add, zeta_add, ← mul_add, add_comm (zeta (-k)), zeta_add_zeta_neg]
  simp [mul_comm]

end Chem

