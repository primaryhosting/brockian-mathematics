import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
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

namespace Chem

open Complex Matrix Polynomial

/-- A primitive ninth root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (9 : ℕ))

theorem om_primitive : IsPrimitiveRoot om 9 := Complex.isPrimitiveRoot_exp 9 (by norm_num)

theorem om_pow_nine : om ^ 9 = 1 := om_primitive.pow_eq_one

theorem om_ne_zero : om ≠ 0 := by
  intro h
  simpa [h] using om_pow_nine

/-- The adjacency matrix of the cycle graph `C₉` (as a complex matrix). -/
noncomputable def A9 : Matrix (Fin 9) (Fin 9) ℂ := (SimpleGraph.cycleGraph 9).adjMatrix ℂ

/-- The Hückel eigenvalues `2 cos (2πk/9)`. -/
noncomputable def lam (k : Fin 9) : ℂ := 2 * (Real.cos (2 * Real.pi * (k : ℕ) / 9) : ℝ)

/-- The discrete Fourier matrix. -/
noncomputable def F9 : Matrix (Fin 9) (Fin 9) ℂ := Matrix.of fun j k => om ^ (j.val * k.val)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def G9 : Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.of fun k j => (9 : ℂ)⁻¹ * (om ^ (k.val * j.val))⁻¹

theorem om_pow_mod (m : ℕ) : om ^ m = om ^ (m % 9) := by
  conv_lhs => rw [← Nat.div_add_mod m 9]
  rw [pow_add, pow_mul, om_pow_nine, one_pow, one_mul]

theorem geom_sum_om (a b : Fin 9) :
    ∑ k : Fin 9, (om ^ a.val * (om ^ b.val)⁻¹) ^ k.val = if a = b then (9 : ℂ) else 0 := by
  have hpow9 : ∀ c : ℕ, (om ^ c) ^ 9 = 1 := by
    intro c; rw [← pow_mul, mul_comm, pow_mul, om_pow_nine, one_pow]
  by_cases h : a = b
  · subst h
    rw [mul_inv_cancel₀ (pow_ne_zero _ om_ne_zero)]
    simp
  · have hne : om ^ a.val * (om ^ b.val)⁻¹ ≠ 1 := by
      intro hc
      rw [mul_inv_eq_one₀ (pow_ne_zero _ om_ne_zero)] at hc
      exact h (Fin.ext (om_primitive.pow_inj a.isLt b.isLt hc))
    have hz9 : (om ^ a.val * (om ^ b.val)⁻¹) ^ 9 = 1 := by
      rw [mul_pow, hpow9, inv_pow, hpow9, inv_one, mul_one]
    rw [if_neg h, Fin.sum_univ_eq_sum_range (fun k => (om ^ a.val * (om ^ b.val)⁻¹) ^ k) 9,
      geom_sum_eq hne, hz9]
    simp

theorem F9_mul_G9 : F9 * G9 = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 9, F9 j k * G9 k j' = (9:ℂ)⁻¹ * (om ^ j.val * (om ^ j'.val)⁻¹) ^ k.val := by
    intro k
    simp only [F9, G9, Matrix.of_apply]
    rw [pow_mul, mul_comm k.val j'.val, pow_mul, mul_pow, ← inv_pow]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, geom_sum_om]
  by_cases h : j = j' <;> simp [h, Matrix.one_apply]

theorem G9_mul_F9 : G9 * F9 = 1 := by
  ext k k'
  rw [Matrix.mul_apply]
  have key : ∀ j : Fin 9, G9 k j * F9 j k' = (9:ℂ)⁻¹ * (om ^ k'.val * (om ^ k.val)⁻¹) ^ j.val := by
    intro j
    simp only [F9, G9, Matrix.of_apply]
    rw [mul_comm k.val j.val, pow_mul, pow_mul, mul_pow, ← inv_pow]
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum, geom_sum_om]
  by_cases h : k = k' <;> simp [h, Matrix.one_apply, eq_comm]

/-- The unit given by the Fourier matrix. -/
noncomputable def U9 : (Matrix (Fin 9) (Fin 9) ℂ)ˣ :=
  ⟨F9, G9, F9_mul_G9, G9_mul_F9⟩

theorem om_pow_add_inv (m : ℕ) :
    om ^ m + (om ^ m)⁻¹ = 2 * (Real.cos (2 * Real.pi * m / 9) : ℝ) := by
  have h : om ^ m = Complex.exp (((2 * Real.pi * m / 9 : ℝ) : ℂ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos, neg_mul]
  ring

theorem cyc_sub_ne_add (i : Fin 9) : (i - 1 : Fin 9) ≠ i + 1 := by
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc i, left_eq_add]
  exact ne_of_beq_false rfl

theorem A9_mul_F9 : A9 * F9 = F9 * Matrix.diagonal lam := by
  ext i k
  have hentry : (A9 * F9) i k
      = om ^ ((i + 1 : Fin 9).val * k.val) + om ^ ((i - 1 : Fin 9).val * k.val) := by
    have h : (A9 * F9) i k = ((SimpleGraph.cycleGraph 9).adjMatrix ℂ *ᵥ fun j => F9 j k) i := by
      rw [Matrix.mul_apply]; rfl
    rw [h, SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
      Finset.sum_pair (cyc_sub_ne_add i)]
    simp [F9]
    ring
  set x : ℂ := om ^ k.val with hxdef
  have hxne : x ≠ 0 := pow_ne_zero _ om_ne_zero
  have hx9 : x ^ 9 = 1 := by rw [hxdef, ← pow_mul, mul_comm, pow_mul, om_pow_nine, one_pow]
  have hxmod : ∀ m : ℕ, x ^ (m % 9) = x ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m 9]
    rw [pow_add, pow_mul, hx9, one_pow, one_mul]
  have hconv : ∀ j : Fin 9, om ^ (j.val * k.val) = x ^ j.val := by
    intro j; rw [hxdef, mul_comm, pow_mul]
  have hx8 : x ^ 8 = x⁻¹ := by
    field_simp
    exact hx9
  rw [hentry, hconv, hconv, Matrix.mul_apply, Fin.val_add, Fin.val_sub]
  have e1 : (i.val + (1 : Fin 9).val) % 9 = (i.val + 1) % 9 := by norm_num
  rw [e1, hxmod, show (9 - (1 : Fin 9).val + i.val) = (i.val + 8) by simp; omega, hxmod,
    pow_add, pow_add, hx8, pow_one]
  have hRHS : ∑ j : Fin 9, F9 i j * Matrix.diagonal lam j k = x ^ i.val * lam k := by
    rw [Finset.sum_eq_single k]
    · simp [F9, Matrix.diagonal_apply_eq, hconv i]
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ hb]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [hRHS, lam, ← om_pow_add_inv k.val]
  ring

theorem A9_eq : A9 = F9 * Matrix.diagonal lam * G9 := by
  have h : A9 * F9 * G9 = F9 * Matrix.diagonal lam * G9 := by rw [A9_mul_F9]
  rwa [Matrix.mul_assoc, F9_mul_G9, Matrix.mul_one] at h

/-- The characteristic polynomial of the adjacency matrix of the cycle graph `C₉`
factors as `∏ k, (X - 2 cos (2πk/9))`. -/
theorem huckel_C9_charpoly :
    ((SimpleGraph.cycleGraph 9).adjMatrix ℂ).charpoly =
      ∏ k : Fin 9, (X - C (2 * (Real.cos (2 * Real.pi * (k : ℕ) / 9) : ℝ) : ℂ)) := by
  have h := Matrix.charpoly_units_conj U9 (Matrix.diagonal lam)
  have hU : ((U9 : (Matrix (Fin 9) (Fin 9) ℂ)ˣ) : Matrix (Fin 9) (Fin 9) ℂ) = F9 := rfl
  have hUinv : ((U9⁻¹ : (Matrix (Fin 9) (Fin 9) ℂ)ˣ) : Matrix (Fin 9) (Fin 9) ℂ) = G9 := rfl
  rw [hU, hUinv] at h
  show A9.charpoly = _
  rw [A9_eq, h, Matrix.charpoly_diagonal]
  rfl

/-- **Hückel theory for `C₉`**: a complex number `μ` is an eigenvalue of the adjacency matrix
of the cycle graph `C₉` if and only if `μ = 2 cos (2πk/9)` for some `k = 0, …, 8`. -/
theorem huckel_C9 (mu : ℂ) :
    (∃ v : Fin 9 → ℂ, v ≠ 0 ∧ ((SimpleGraph.cycleGraph 9).adjMatrix ℂ).mulVec v = mu • v) ↔
      ∃ k : Fin 9, mu = 2 * (Real.cos (2 * Real.pi * (k : ℕ) / 9) : ℝ) := by
  have hscal : ∀ v : Fin 9 → ℂ, (Matrix.scalar (Fin 9) mu).mulVec v = mu • v := by
    intro v
    ext i
    simp [Matrix.mulVec, Matrix.scalar_apply, Matrix.diagonal, dotProduct]
  have key : ∀ v : Fin 9 → ℂ,
      A9.mulVec v = mu • v ↔ (Matrix.scalar (Fin 9) mu - A9).mulVec v = 0 := by
    intro v
    rw [Matrix.sub_mulVec, sub_eq_zero, hscal v]
    exact eq_comm
  rw [show ((SimpleGraph.cycleGraph 9).adjMatrix ℂ) = A9 from rfl,
    exists_congr (fun v : Fin 9 → ℂ => and_congr_right (fun _ => key v)),
    Matrix.exists_mulVec_eq_zero_iff, ← Matrix.eval_charpoly,
    show A9.charpoly = _ from huckel_C9_charpoly, Polynomial.eval_prod]
  simp [Finset.prod_eq_zero_iff, sub_eq_zero]

end Chem

