import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
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

namespace Chem

open Matrix Complex

/-- Adjacency matrix of the cycle graph `C₅` (the Hückel matrix of the cyclopentadienyl
π-system in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

theorem C5adj_hasEigenvector (k : ℕ) :
    ∃ v : Fin 5 → ℂ, v ≠ 0 ∧
      C5adj *ᵥ v = (2 * (Real.cos (2 * Real.pi * k / 5) : ℂ)) • v := by
  set θ : ℝ := 2 * Real.pi * k / 5 with hθ
  set z : ℂ := Complex.exp (θ * I) with hzdef
  have hzne : z ≠ 0 := Complex.exp_ne_zero _
  have hz5 : z ^ 5 = 1 := by
    rw [hzdef, ← Complex.exp_nat_mul,
      show ((5 : ℕ) : ℂ) * ((θ : ℂ) * I) = ((k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by
        push_cast [hθ]; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  have hz4 : z ^ 4 = Complex.exp (-((θ : ℂ) * I)) := by
    have h1 : z ^ 4 * z = 1 := by rw [← pow_succ]; exact hz5
    have h2 : Complex.exp (-((θ : ℂ) * I)) * z = 1 := by
      rw [hzdef, ← Complex.exp_add]; simp
    exact mul_right_cancel₀ hzne (h1.trans h2.symm)
  have hc : (2 * (Real.cos θ : ℂ)) = z + z ^ 4 := by
    rw [hz4, hzdef, Complex.ofReal_cos, Complex.two_cos, neg_mul]
  rw [hc]
  refine ⟨![1, z, z ^ 2, z ^ 3, z ^ 4], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · ext i
    fin_cases i
    · simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    · simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      linear_combination -hz5
    · simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      linear_combination -z * hz5
    · simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      linear_combination -z ^ 2 * hz5
    · simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      linear_combination (-1 - z ^ 3) * hz5

/-- The characteristic polynomial of `C₅`:
`det (A - μ) = -(μ⁵ - 5μ³ + 5μ - 2)`. -/
