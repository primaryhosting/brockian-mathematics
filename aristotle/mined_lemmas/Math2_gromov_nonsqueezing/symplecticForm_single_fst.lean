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
-/

open scoped BigOperators

namespace Math2

/-- The standard symplectic form on `ℝ^{2n}`, with coordinates indexed by
`Fin n × Fin 2` (the pair `(i, 0)`, `(i, 1)` being the `i`-th conjugate pair). -/

lemma symplecticForm_single_fst {n : ℕ} (w : Fin (n + 1) × Fin 2 → ℝ) :
    symplecticForm (Pi.single ((0 : Fin (n + 1)), (0 : Fin 2)) (1 : ℝ)) w = w (0, 1) := by
  rw [symplecticForm]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp
  · intro b _ hb
    simp [Prod.ext_iff, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

