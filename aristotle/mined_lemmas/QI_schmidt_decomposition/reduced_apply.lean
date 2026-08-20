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

theorem reduced_apply {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) (x : A → ℂ) (i : A) :
    ∑ i', reduced psi i i' * x i' = ∑ k, ((s k : ℂ) ^ 2 * ∑ i', conj (u k i') * x i') * u k i := by
  obtain ⟨hs, hu, hv, hrec⟩ := h
  set c : Fin r → ℂ := fun l => ∑ i', conj (u l i') * x i' with hc
  have step1 : ∑ i', reduced psi i i' * x i'
      = ∑ b, psi i b * ∑ i', conj (psi i' b) * x i' := by
    simp only [reduced, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i' _ => by ring
  have step2 : ∀ b, ∑ i', conj (psi i' b) * x i'
      = ∑ l, ((s l : ℂ) * c l) * conj (v l b) := by
    intro b
    have : ∀ i' : A, conj (psi i' b) * x i'
        = ∑ l, ((s l : ℂ) * conj (v l b)) * (conj (u l i') * x i') := by
      intro i'
      rw [hrec i' b]
      simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.mul_sum]
    simp only [hc]
    ring
  have step3 : ∀ b, psi i b = ∑ k, ((s k : ℂ) * u k i) * v k b := by
    intro b
    rw [hrec i b]
  rw [step1]
  simp only [step2, step3]
  rw [sum_mul_conj_of_orthonormal hv (fun k => (s k : ℂ) * u k i) (fun l => (s l : ℂ) * c l)]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq B] in
/-- Each Schmidt vector `u l` is an eigenvector of the reduced density matrix with
eigenvalue `(s l)^2`. -/
