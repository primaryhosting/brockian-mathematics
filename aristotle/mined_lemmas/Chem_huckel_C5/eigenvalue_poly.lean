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

lemma eigenvalue_poly {μ : ℝ} {v : Fin 5 → ℝ} (hv : v ≠ 0) (h : C5adj *ᵥ v = μ • v) :
    (μ - 2) * (μ ^ 2 + μ - 1) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (funext fun i => hc i)
  have key := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M *ᵥ v) C5adj_min_poly
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    C5adj_pow_mulVec h, h] at key
  have hki := congrFun key i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hki
  have : (μ ^ 3 - μ ^ 2 - 3 * μ + 2) * v i = 0 := by linear_combination hki
  have hpoly : μ ^ 3 - μ ^ 2 - 3 * μ + 2 = 0 := by
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hi
  nlinarith [hpoly]

/-- `2` is an eigenvalue of the `C₅` adjacency matrix (the all-ones eigenvector). -/
