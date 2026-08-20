/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The banner above is repeated as a module docstring below; Lean does not allow a
-- `/-! ... -/` module docstring to precede the `import` line.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ComplexConjugate

namespace QI

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- A family of vectors `u k : A → ℂ` (`k : ι`) is orthonormal for the standard
Hermitian inner product on `ℂ^A`. -/

theorem sum_mul_conj_of_orthonormal {r : ℕ} {v : Fin r → B → ℂ} (hv : IsOrthonormalFamily v)
    (a d : Fin r → ℂ) :
    ∑ b, (∑ k, a k * v k b) * (∑ l, d l * conj (v l b)) = ∑ k, a k * d k := by
  have hv' := hv.conj_right
  have expand : ∀ b : B, (∑ k, a k * v k b) * (∑ l, d l * conj (v l b))
      = ∑ k, ∑ l, (a k * d l) * (v k b * conj (v l b)) := by
    intro b
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => expand b, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have hk : ∀ l : Fin r, (∑ b, (a k * d l) * (v k b * conj (v l b)))
      = (a k * d l) * (if k = l then 1 else 0) := by
    intro l
    rw [← Finset.mul_sum, hv' k l]
  simp only [hk]
  simp

omit [DecidableEq B] in
/-- The reduced density matrix acts on `x` through the Schmidt vectors. -/
