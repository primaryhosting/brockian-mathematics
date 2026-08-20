/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Real

/-- The adjacency matrix of the cycle graph `C₅`, on vertex set `Fin 5` with the
cyclic (mod 5) neighbour relation. In Hückel theory (with `α = 0`, `β = 1`) this is the
Hückel matrix of the cyclic π-system of `C₅`. -/

lemma C5adj_pow_mulVec {μ : ℝ} {v : Fin 5 → ℝ} (h : C5adj *ᵥ v = μ • v) :
    ∀ n : ℕ, (C5adj ^ n) *ᵥ v = (μ ^ n) • v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]

/-- Every eigenvalue `μ` of the `C₅` adjacency matrix satisfies `(μ - 2)(μ² + μ - 1) = 0`. -/
