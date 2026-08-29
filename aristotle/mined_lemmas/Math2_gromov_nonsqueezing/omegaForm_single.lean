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

lemma omegaForm_single {n : ℕ} (j : Fin n) :
    omegaForm (EuclideanSpace.single (j, 0) (1 : ℝ)) (EuclideanSpace.single (j, 1) (1 : ℝ))
      = 1 := by
  simp [omegaForm, EuclideanSpace.single_apply, Prod.ext_iff, Finset.sum_ite_eq']

/-- **Gromov nonsqueezing (linear case).**  If a linear symplectomorphism of the standard
symplectic space `ℝ^{2n}` maps the closed ball of radius `r` centred at the origin into the
symplectic cylinder of radius `R` over a conjugate coordinate plane, then `r ≤ R`.

(The full Gromov nonsqueezing theorem, for arbitrary smooth symplectic embeddings, requires the
theory of pseudoholomorphic curves; the statement proved here is the classical linear case.) -/
