/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalizes Gromov's nonsqueezing phenomenon for **linear** symplectomorphisms
of `ℝ^(2n+2)`: a linear symplectic image of a ball of radius `r` that fits inside the
symplectic cylinder of radius `R` forces `r ≤ R`.  An affine version and a sharpness
statement are also proved.
-/

open scoped BigOperators
open Matrix

namespace Math2

/-- Bessel-type inequality for a pair of orthogonal vectors of equal length. -/

lemma bessel_pair {ι : Type*} [Fintype ι] (u v w : ι → ℝ)
    (huv : u ⬝ᵥ v = 0) (hlen : u ⬝ᵥ u = v ⬝ᵥ v) (hpos : 0 < v ⬝ᵥ v) :
    (u ⬝ᵥ w) ^ 2 + (v ⬝ᵥ w) ^ 2 ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
  set A : ℝ := v ⬝ᵥ v with hA
  set W : ℝ := u ⬝ᵥ w with hW
  set C : ℝ := v ⬝ᵥ w with hC
  have key : ∀ i : ι, (A * w i - W * u i - C * v i) ^ 2 =
      A ^ 2 * (w i * w i) + W ^ 2 * (u i * u i) + C ^ 2 * (v i * v i)
        - 2 * A * W * (u i * w i) - 2 * A * C * (v i * w i)
        + 2 * W * C * (u i * v i) := by
    intro i; ring
  have hexp : (0 : ℝ) ≤ A ^ 2 * (w ⬝ᵥ w) - A * W ^ 2 - A * C ^ 2 := by
    have h0 : (0 : ℝ) ≤ ∑ i, (A * w i - W * u i - C * v i) ^ 2 := by positivity
    have h1 : ∑ i, (A * w i - W * u i - C * v i) ^ 2 =
        A ^ 2 * (w ⬝ᵥ w) + W ^ 2 * (u ⬝ᵥ u) + C ^ 2 * (v ⬝ᵥ v)
          - 2 * A * W * (u ⬝ᵥ w) - 2 * A * C * (v ⬝ᵥ w) + 2 * W * C * (u ⬝ᵥ v) := by
      simp only [key, dotProduct, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [h1, huv, hlen, ← hA, ← hW, ← hC] at h0
    linarith [h0]
  nlinarith [hexp, hpos]

section JLemmas

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The canonical symplectic form is alternating: `⟪v, J v⟫ = 0`. -/
