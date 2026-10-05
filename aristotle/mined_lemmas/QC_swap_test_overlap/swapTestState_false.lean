/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open ComplexConjugate

namespace QC

variable {n : Type*} [Fintype n]

/-- The overlap `⟨ψ|φ⟩` of two state vectors indexed by `n`. -/

theorem swapTestState_false (psi phi : n → ℂ) (i j : n) :
    swapTestState psi phi (false, i, j) = (psi i * phi j + phi i * psi j) / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    simp
  simp only [swapTestState, hadamardAncilla, cswap, initState, if_true, if_false,
    Bool.false_eq_true]
  field_simp
  ring_nf
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 by rw [sq]; exact h2]

/-- **SWAP test.** For normalized states `ψ` and `φ`, the SWAP test accepts with
probability `(1 + |⟨ψ|φ⟩|²) / 2`. -/
