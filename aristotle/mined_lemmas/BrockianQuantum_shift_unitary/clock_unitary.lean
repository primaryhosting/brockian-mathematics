import Mathlib
/-!
# Stabilizer formalism: qudit generalized-Pauli unitarity + qubit Pauli anticommutation.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. All TRUE.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** (generalized Pauli X). -/

theorem clock_unitary : clock d * (clock d)ᴴ = 1 := by
  have hconj : ∀ z : ℂ, (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * z / d)
      = -(2 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) z / d) := by
    intro z
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      Complex.conj_natCast]
    ring
  ext i l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, clock, Matrix.one_apply,
    RCLike.star_def, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · by_cases h : i = l
    · subst h
      simp only [if_true]
      -- `exp z * conj (exp z) = exp z * exp (-z) = 1` since the exponent is purely imaginary.
      rw [← Complex.exp_conj, hconj, Complex.conj_natCast, Complex.exp_neg,
        mul_inv_cancel₀ (Complex.exp_ne_zero _)]
    · simp [h, Ne.symm h]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- **Qubit Pauli anticommutation** (base case of the stabilizer group): `X Z = − Z X` for the
2×2 Pauli matrices `X = [[0,1],[1,0]]`, `Z = [[1,0],[0,-1]]`. -/
