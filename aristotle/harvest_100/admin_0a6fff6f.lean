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

set_option grind.warning false

namespace Chem

open Complex Polynomial Matrix

/-- The commutative ring structure on `Fin 20 = ZMod 20`, used for index arithmetic. -/
noncomputable instance : CommRing (Fin 20) := inferInstanceAs (CommRing (ZMod 20))

/-- A primitive 20-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)

/-- The character `Fin 20 → ℂ`, `n ↦ w ^ n`. -/
noncomputable def zeta (n : Fin 20) : ℂ := w ^ (n : ℕ)

/-- The adjacency matrix of the cycle graph `C₂₀` (the Hückel matrix of a 20-cycle). -/
noncomputable def A20 : Matrix (Fin 20) (Fin 20) ℂ :=
  (SimpleGraph.cycleGraph 20).adjMatrix ℂ

/-- The list of Hückel eigenvalues `2 cos (2πk/20)`. -/
noncomputable def ev (k : Fin 20) : ℂ := (2 * Real.cos (2 * Real.pi * k / 20) : ℝ)

/-- The (unnormalized) discrete Fourier matrix. -/
noncomputable def P20 : Matrix (Fin 20) (Fin 20) ℂ := fun i k => zeta (i * k)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def Q20 : Matrix (Fin 20) (Fin 20) ℂ := fun k j => (20 : ℂ)⁻¹ * zeta (-(k * j))

lemma w_primitive : IsPrimitiveRoot w 20 := by
  simpa [w] using Complex.isPrimitiveRoot_exp 20 (by norm_num)

lemma w_pow_20 : w ^ (20 : ℕ) = 1 := w_primitive.pow_eq_one

lemma w_pow_mod (n : ℕ) : w ^ (n % 20) = w ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 20]
  rw [pow_add, pow_mul, w_pow_20, one_pow, one_mul]

lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_add (a b : Fin 20) : zeta (a + b) = zeta a * zeta b := by
  simp only [zeta, Fin.val_add]
  rw [w_pow_mod, pow_add]

lemma zeta_ne_zero (a : Fin 20) : zeta a ≠ 0 := by
  simp [zeta, w, Complex.exp_ne_zero]

lemma zeta_neg (a : Fin 20) : zeta (-a) = (zeta a)⁻¹ := by
  have h : zeta (-a) * zeta a = 1 := by rw [← zeta_add]; simp [zeta_zero]
  exact eq_inv_of_mul_eq_one_left h

lemma zeta_mul (k c : Fin 20) : zeta (k * c) = zeta c ^ (k : ℕ) := by
  simp only [zeta, Fin.val_mul, ← pow_mul]
  rw [w_pow_mod, mul_comm]

lemma zeta_eq_one_iff (c : Fin 20) : zeta c = 1 ↔ c = 0 := by
  constructor
  · intro h
    have := (w_primitive.pow_eq_one_iff_dvd (c : ℕ)).1 h
    have hlt : (c : ℕ) < 20 := c.isLt
    have : (c : ℕ) = 0 := by
      rcases this with ⟨m, hm⟩
      omega
    exact Fin.ext this
  · rintro rfl; exact zeta_zero

/-- Orthogonality of characters. -/
lemma zeta_sum (c : Fin 20) : (∑ k : Fin 20, zeta (k * c)) = if c = 0 then 20 else 0 := by
  simp only [zeta_mul]
  rw [Fin.sum_univ_eq_sum_range (fun n => zeta c ^ n) 20]
  by_cases hc : c = 0
  · subst hc
    simp [zeta_zero]
  · have h1 : zeta c ≠ 1 := fun h => hc ((zeta_eq_one_iff c).1 h)
    have h20 : zeta c ^ (20 : ℕ) = 1 := by
      simp only [zeta, ← pow_mul]
      rw [mul_comm, pow_mul, w_pow_20, one_pow]
    rw [geom_sum_eq h1, h20, sub_self, zero_div, if_neg hc]

lemma ev_eq (k : Fin 20) : zeta k + zeta (-k) = ev k := by
  rw [zeta_neg]
  simp only [zeta, w, ev]
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos,
    show (2 * (Real.pi : ℂ) * (k : ℕ) / 20) * Complex.I
        = (k : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 20) by ring,
    show -(2 * (Real.pi : ℂ) * (k : ℕ) / 20) * Complex.I
        = -((k : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 20)) by ring]

lemma sub_one_ne_add_one (i : Fin 20) : i - 1 ≠ i + 1 := by
  intro h
  have h2 : (2 : Fin 20) = 0 := by linear_combination -h
  exact absurd h2 (by decide)

/-- The key computation: the adjacency matrix acts on the Fourier mode `j ↦ ζ(jk)` by the
scalar `2 cos (2πk/20)`. -/
lemma A20_mulVec_fourier (k : Fin 20) :
    A20 *ᵥ (fun j : Fin 20 => zeta (j * k)) = ev k • (fun j : Fin 20 => zeta (j * k)) := by
  funext i
  rw [A20, SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one i)]
  have h1 : (i - 1) * k = i * k + -k := by ring
  have h2 : (i + 1) * k = i * k + k := by ring
  rw [h1, h2, zeta_add, zeta_add, Pi.smul_apply, smul_eq_mul, ← ev_eq]
  ring

lemma A20_mul_P20 : A20 * P20 = P20 * Matrix.diagonal ev := by
  ext i k
  have h : (A20 * P20) i k = (A20 *ᵥ (fun j : Fin 20 => zeta (j * k))) i := by
    rw [Matrix.mul_apply]; rfl
  rw [h, A20_mulVec_fourier, Matrix.mul_diagonal, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

lemma P20_mul_Q20 : P20 * Q20 = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : Fin 20, P20 i k * Q20 k j = (20 : ℂ)⁻¹ * zeta (k * (i - j)) := by
    intro k
    simp only [P20, Q20]
    rw [show k * (i - j) = i * k + -(k * j) by ring, zeta_add]
    ring
  simp only [h, ← Finset.mul_sum, zeta_sum]
  rw [Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; norm_num
  · rw [if_neg (by simpa [sub_eq_zero] using hij), if_neg hij, mul_zero]

lemma Q20_mul_P20 : Q20 * P20 = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : Fin 20, Q20 i k * P20 k j = (20 : ℂ)⁻¹ * zeta (k * (j - i)) := by
    intro k
    simp only [P20, Q20]
    rw [show k * (j - i) = -(i * k) + k * j by ring, zeta_add]
    ring
  simp only [h, ← Finset.mul_sum, zeta_sum]
  rw [Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; norm_num
  · rw [if_neg (by simpa [sub_eq_zero] using (Ne.symm hij)), if_neg hij, mul_zero]

/-- `P20` as a unit of the matrix ring. -/
noncomputable def U20 : (Matrix (Fin 20) (Fin 20) ℂ)ˣ :=
  ⟨P20, Q20, P20_mul_Q20, Q20_mul_P20⟩

lemma A20_conj : A20 = (U20 : Matrix (Fin 20) (Fin 20) ℂ) * Matrix.diagonal ev
    * ((U20⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) := by
  have hP : ((U20 : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) = P20 := rfl
  have hQ : ((U20⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) = Q20 := rfl
  rw [hP, hQ, ← A20_mul_P20, mul_assoc, P20_mul_Q20, mul_one]

/-- **Hückel theory for C₂₀.** The characteristic polynomial of the adjacency matrix of the
cycle graph `C₂₀` is `∏ k < 20, (X - 2 cos (2πk/20))`; i.e. the adjacency eigenvalues of `C₂₀`
are exactly the numbers `2 cos (2πk/20)`, `k = 0, …, 19`. -/
theorem huckel_C20 :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).charpoly =
      ∏ k : Fin 20, (X - C ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ)) := by
  have h : ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) = A20 := rfl
  rw [h, A20_conj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

/-- The spectrum of the adjacency matrix of `C₂₀` is `{2 cos (2πk/20) : k = 0, …, 19}`. -/
theorem huckel_C20_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) =
      {μ : ℂ | ∃ k : Fin 20, μ = ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ)} := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C20]
  simp [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- Explicit eigenvectors: the Fourier mode `j ↦ exp(2πi jk/20)` is an eigenvector of the
adjacency matrix of `C₂₀` with eigenvalue `2 cos (2πk/20)`. -/
theorem huckel_C20_eigenvector (k : Fin 20) :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) *ᵥ (fun j : Fin 20 => zeta (j * k)) =
      ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ) • (fun j : Fin 20 => zeta (j * k)) :=
  A20_mulVec_fourier k

/-- The Fourier modes used in `huckel_C20_eigenvector` are nonzero vectors. -/
theorem huckel_C20_eigenvector_ne_zero (k : Fin 20) :
    (fun j : Fin 20 => zeta (j * k)) ≠ 0 := by
  intro h
  have h0 : zeta ((0 : Fin 20) * k) = 0 := congrFun h 0
  exact zeta_ne_zero _ h0

end Chem

