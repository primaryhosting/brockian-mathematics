/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₈`, i.e. the Hückel matrix of
cyclooctatetraene in units where `α = 0` and `β = 1`. -/

lemma gk_congr (k : ℕ) {a b : ℤ} (h : a % 8 = b % 8) : gk k a = gk k b := by
  have hab : a = b + 8 * ((a - b) / 8) := by omega
  rw [hab, gk_period]

/-- The candidate eigenvector for the eigenvalue `2 cos (2πk/8)`. -/
