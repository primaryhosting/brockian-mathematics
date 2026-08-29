import Mathlib
/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators RealInnerProductSpace

namespace Math2

/-- The standard symplectic vector space `ℝ^{2n}`, with coordinates indexed by
`Fin n × Fin 2`: the pair `(i, 0), (i, 1)` is the `i`-th conjugate coordinate pair. -/
abbrev SympSpace (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin 2)

/-- The standard symplectic form on `ℝ^{2n}`. -/

lemma Jmap_neg {n : ℕ} (u : SympSpace n) : Jmap (-u) = -Jmap u := by
  ext p
  obtain ⟨i, a⟩ := p
  fin_cases a <;> simp [Jmap]

