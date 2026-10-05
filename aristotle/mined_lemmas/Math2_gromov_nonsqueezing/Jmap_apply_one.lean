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

@[simp] lemma Jmap_apply_one {n : ℕ} (u : SympSpace n) (i : Fin n) :
    Jmap u (i, 1) = u (i, 0) := rfl

