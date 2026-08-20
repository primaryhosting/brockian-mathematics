/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the required header is
-- repeated verbatim as the module docstring immediately below the import.)

import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
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

namespace QI

open Matrix ComplexOrder

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]

/-! ## Definitions -/

/-- The **Knill–Laflamme conditions** for a code with orthogonal projector `P` and a set of
error operators `E i`: `P (E i)ᴴ (E j) P = c i j • P` for some matrix of scalars `c`. -/

lemma exists_smul_of_sum_outer {κ : Type*} [Fintype κ] (M : κ → Matrix d d ℂ)
    (ψ : d → ℂ) (hψ : ψ ≠ 0)
    (h : ∑ k, M k * vecMulVec ψ (star ψ) * (M k)ᴴ = vecMulVec ψ (star ψ)) (k : κ) :
    ∃ t : ℂ, M k *ᵥ ψ = t • ψ := by
  have hnψ : star ψ ⬝ᵥ ψ ≠ 0 := fun h0 => hψ (dotProduct_star_self_eq_zero.mp h0)
  refine ⟨(star ψ ⬝ᵥ (M k *ᵥ ψ)) / (star ψ ⬝ᵥ ψ), ?_⟩
  set t : ℂ := (star ψ ⬝ᵥ (M k *ᵥ ψ)) / (star ψ ⬝ᵥ ψ) with ht
  set w0 : d → ℂ := M k *ᵥ ψ - t • ψ with hw0def
  have hw0ψ : star ψ ⬝ᵥ w0 = 0 := by
    rw [hw0def, dotProduct_sub, dotProduct_smul, smul_eq_mul, ht]
    field_simp
    ring
  have hψw0 : star w0 ⬝ᵥ ψ = 0 := by
    rw [star_dotProduct, hw0ψ]; simp
  have key : ∀ l, star w0 ⬝ᵥ (M l *ᵥ ψ) = 0 := by
    have h1 : star w0 ⬝ᵥ ((∑ l, M l * vecMulVec ψ (star ψ) * (M l)ᴴ) *ᵥ w0)
        = star w0 ⬝ᵥ (vecMulVec ψ (star ψ) *ᵥ w0) := by rw [h]
    rw [Matrix.sum_mulVec, dotProduct_sum, outer_quadratic, hψw0] at h1
    simp only [conj_mul_outer, outer_quadratic, mul_zero] at h1
    have h2 : star (fun l => star w0 ⬝ᵥ (M l *ᵥ ψ)) ⬝ᵥ (fun l => star w0 ⬝ᵥ (M l *ᵥ ψ)) = 0 := by
      simpa [dotProduct] using h1
    exact fun l => congrFun (dotProduct_star_self_eq_zero.mp h2) l
  have hw00 : star w0 ⬝ᵥ w0 = 0 := by
    rw [hw0def, dotProduct_sub, dotProduct_smul, key k, hψw0, smul_zero, sub_zero]
  have h3 := dotProduct_star_self_eq_zero.mp hw00
  rw [hw0def] at h3
  exact sub_eq_zero.mp h3

omit [DecidableEq d] in
/-- An operator acting as a scalar on every vector of the code acts as a fixed scalar on the
whole code. -/
