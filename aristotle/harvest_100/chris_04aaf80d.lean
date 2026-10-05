/-
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
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

namespace Riemann
namespace BaezDuarte

/-- **Gram nonnegativity (general form).**  In any real inner product space `V`, for any
finite family of vectors `v : Fin n → V` and any real coefficients `c : Fin n → ℝ`, the
Gram quadratic form `∑ i, ∑ j, c i * c j * ⟪v i, v j⟫` is nonnegative, since it equals the
squared norm of `∑ i, c i • v i`. -/
theorem gram_sum_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (v : Fin n → V) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * inner ℝ (v i) (v j) := by
  have key : ∑ i, ∑ j, c i * c j * inner ℝ (v i) (v j)
      = inner ℝ (∑ i, c i • v i) (∑ j, c j • v j) := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
  rw [key]
  exact real_inner_self_nonneg

/-- **Gram nonnegativity, 3 × 3 case.**  If `p q r s t u` are the entries of the Gram matrix
`[[p, q, r], [q, s, t], [r, t, u]]` of three vectors `v₀ v₁ v₂` of a real inner product space
(so the matrix is positive semidefinite), then the associated quadratic form is nonnegative. -/
theorem gram_nonneg_three {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v₀ v₁ v₂ : V) (p q r s t u : ℝ)
    (hp : p = inner ℝ v₀ v₀) (hq : q = inner ℝ v₀ v₁) (hr : r = inner ℝ v₀ v₂)
    (hs : s = inner ℝ v₁ v₁) (ht : t = inner ℝ v₁ v₂) (hu : u = inner ℝ v₂ v₂)
    (a b c : ℝ) :
    0 ≤ a ^ 2 * p + b ^ 2 * s + c ^ 2 * u + 2 * a * b * q + 2 * a * c * r + 2 * b * c * t := by
  have h := gram_sum_nonneg ![v₀, v₁, v₂] ![a, b, c]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h
  rw [hp, hq, hr, hs, ht, hu]
  simp only [real_inner_comm v₁ v₀, real_inner_comm v₂ v₀, real_inner_comm v₂ v₁] at h ⊢
  linarith [h]

/-- **Gram / distance nonnegativity, clean self-contained case.**
For all real `a` and `b`, `0 ≤ a^2 - 2*a*b + b^2`; this is the Gram (squared distance)
nonnegativity `0 ≤ (a - b)^2` underlying the Baez-Duarte / Nyman-Beurling distance,
which is a sum of such squares. -/
theorem gram_nonneg : ∀ a b : ℝ, 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
  intro a b
  nlinarith [sq_nonneg (a - b)]

end BaezDuarte
end Riemann

