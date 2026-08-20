/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1` over `ℚ`. -/

lemma two_le_planeGenus {n : ℕ} (hn : 4 ≤ n) : 2 ≤ planeGenus n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h1 : k + 4 - 1 = k + 3 := by omega
  have h2 : k + 4 - 2 = k + 2 := by omega
  have h : (k + 4 - 1) * (k + 4 - 2) = (k + 3) * (k + 2) := by rw [h1, h2]
  have h6 : 6 ≤ (k + 3) * (k + 2) := by nlinarith
  simp only [planeGenus, h]
  omega

/-- Faltings' theorem for the Fermat curves: the statement that the affine Fermat curve of
degree `n ≥ 4` (a curve of genus `(n-1)(n-2)/2 ≥ 2`) has only finitely many rational points. -/
