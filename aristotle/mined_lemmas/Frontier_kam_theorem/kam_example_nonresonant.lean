/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Real Finset RealInnerProductSpace

namespace Frontier

/-- One factor of phase space, `ℝⁿ`.  It is used both for the action variables `p`
and for the angle variables `q`; the angles are understood modulo the lattice `2π ℤⁿ`. -/
abbrev Phase (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The Fourier mode `k ∈ ℤⁿ`, viewed as a vector of `ℝⁿ`. -/

lemma kam_example_nonresonant :
    ∀ k ∈ ({![1, -1]} : Finset (Fin 2 → ℤ)),
      ⟪mode k, (WithLp.toLp 2 ![(1 : ℝ), Real.sqrt 2] : Phase 2)⟫ ≠ 0 := by
  intro k hk
  simp only [Finset.mem_singleton] at hk
  subst hk
  simp [mode, PiLp.inner_apply, Fin.sum_univ_two]
  intro h
  have h2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  nlinarith [Real.sqrt_nonneg 2]

/-- ... and the corresponding perturbation is not the zero function. -/
