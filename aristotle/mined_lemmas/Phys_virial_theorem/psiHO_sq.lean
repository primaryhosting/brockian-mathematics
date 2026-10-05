import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Phys

open Complex MeasureTheory Filter Topology

/-- The expectation value `⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/

theorem psiHO_sq (x : ℝ) : psiHO x ^ 2 = (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [psiHO, mul_pow, ← Real.rpow_natCast (Real.pi ^ (-(1 : ℝ) / 4)) 2, ← Real.rpow_mul hpi.le,
    ← Real.exp_nat_mul]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hpi.le]
  norm_num
  left
  ring

/-- The ground state is normalized: `∫ ψ² = 1`. -/
