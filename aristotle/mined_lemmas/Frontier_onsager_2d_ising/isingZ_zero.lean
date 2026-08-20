/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Real

namespace Frontier

/-- A Boolean spin variable read as a real number `±1`. -/

lemma isingZ_zero (n : ℕ) : isingZ n 0 = 2 ^ ((n + 1) * (n + 1)) := by
  unfold isingZ
  simp only [zero_mul, Real.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_univ]
  rw [Fintype.card_fun]
  simp [ZMod.card]

/-- Base case of Onsager's solution: at `K = 0` the exact finite-volume free energy per site
of the 2D Ising model agrees with Onsager's formula. -/
