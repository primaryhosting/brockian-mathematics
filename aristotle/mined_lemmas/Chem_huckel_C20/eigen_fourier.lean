import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

lemma eigen_fourier (x : ZMod 20 → ℂ) (μ : ℂ) (hx : C20 *ᵥ x = μ • x) (m : ℕ) (hm : m ≤ 20) :
    ((2 * Real.cos (2 * Real.pi * m / 20) : ℝ) : ℂ) * (∑ j, evec m j * x j)
      = μ * ∑ j, evec m j * x j := by
  have e1 : ∑ j : ZMod 20, evec m (j + 1) * x j = ∑ j : ZMod 20, evec m j * x (j - 1) :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod 20)) _ _ (fun j => by simp)
  have e2 : ∑ j : ZMod 20, evec m (j - 1) * x j = ∑ j : ZMod 20, evec m j * x (j + 1) :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod 20)) _ _ (fun j => by simp)
  have hshift1 : ∑ j : ZMod 20, evec m j * x (j - 1) = w ^ m * ∑ j, evec m j * x j := by
    rw [← e1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [evec_succ, mul_assoc]
  have hshift2 : ∑ j : ZMod 20, evec m j * x (j + 1) = w ^ (20 - m) * ∑ j, evec m j * x j := by
    rw [← e2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [evec_pred m hm, mul_assoc]
  have hmain : ∑ j : ZMod 20, evec m j * (μ * x j)
      = ((2 * Real.cos (2 * Real.pi * m / 20) : ℝ) : ℂ) * ∑ j, evec m j * x j := by
    have : ∀ j : ZMod 20, evec m j * (μ * x j) = evec m j * (x (j - 1) + x (j + 1)) := by
      intro j
      have := congrFun hx j
      rw [mulVec_C20] at this
      rw [this]
      simp [Pi.smul_apply]
    calc ∑ j : ZMod 20, evec m j * (μ * x j)
        = ∑ j : ZMod 20, (evec m j * x (j - 1) + evec m j * x (j + 1)) :=
          Finset.sum_congr rfl fun j _ => by rw [this j, mul_add]
      _ = ((2 * Real.cos (2 * Real.pi * m / 20) : ℝ) : ℂ) * ∑ j, evec m j * x j := by
          rw [Finset.sum_add_distrib, hshift1, hshift2, ← add_mul, w_pow_add_cos m hm]
  rw [← hmain, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Hückel theory for C₂₀.** The eigenvalues of the adjacency matrix of the cycle graph
`C₂₀` are exactly the numbers `2 cos (2πk/20)`, `k = 0, …, 19`. -/
