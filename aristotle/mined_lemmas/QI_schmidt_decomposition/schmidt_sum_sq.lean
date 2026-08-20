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

theorem schmidt_sum_sq {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) :
    ∑ k, (s k) ^ 2 = ∑ i, ∑ j, Complex.normSq (psi i j) := by
  obtain ⟨hs, hu, hv, hrec⟩ := h
  have hu' : ∀ k l, ∑ i, conj (u k i) * u l i = if k = l then 1 else 0 := hu
  have inner : ∀ i, ∑ j, psi i j * conj (psi i j)
      = ∑ k, ((s k : ℂ) * u k i) * ((s k : ℂ) * conj (u k i)) := by
    intro i
    have h1 : ∀ j, psi i j = ∑ k, ((s k : ℂ) * u k i) * v k j := fun j => hrec i j
    have h2 : ∀ j, conj (psi i j) = ∑ l, ((s l : ℂ) * conj (u l i)) * conj (v l j) := by
      intro j
      rw [hrec i j, map_sum]
      exact Finset.sum_congr rfl fun l _ => by
        simp only [map_mul, Complex.conj_ofReal]
    calc ∑ j, psi i j * conj (psi i j)
        = ∑ j, (∑ k, ((s k : ℂ) * u k i) * v k j)
            * (∑ l, ((s l : ℂ) * conj (u l i)) * conj (v l j)) :=
          Finset.sum_congr rfl fun j _ => by rw [h2 j, h1 j]
      _ = ∑ k, ((s k : ℂ) * u k i) * ((s k : ℂ) * conj (u k i)) :=
          sum_mul_conj_of_orthonormal hv _ _
  have key : ∑ i, ∑ j, psi i j * conj (psi i j) = ∑ k, ((s k : ℂ)) ^ 2 := by
    simp only [inner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : ∑ i, ((s k : ℂ) * u k i) * ((s k : ℂ) * conj (u k i))
        = (s k : ℂ) ^ 2 * ∑ i, conj (u k i) * u k i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, hu' k k]
    simp
  have hR : ((∑ i, ∑ j, Complex.normSq (psi i j) : ℝ) : ℂ) = ((∑ k, (s k) ^ 2 : ℝ) : ℂ) := by
    calc ((∑ i, ∑ j, Complex.normSq (psi i j) : ℝ) : ℂ)
        = ∑ i, ∑ j, psi i j * conj (psi i j) := by
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.ofReal_sum]
          exact Finset.sum_congr rfl fun j _ => by
            rw [Complex.normSq_eq_conj_mul_self]; ring
      _ = ∑ k, ((s k : ℂ)) ^ 2 := key
      _ = ((∑ k, (s k) ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
          exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  exact_mod_cast hR.symm

omit [DecidableEq B] in
/-- The Schmidt rank (the number of terms in a Schmidt decomposition) is unique. -/
