/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The banner above is repeated as a module docstring below; Lean does not allow a
-- `/-! ... -/` module docstring to precede the `import` line.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ComplexConjugate

namespace QI

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- A family of vectors `u k : A → ℂ` (`k : ι`) is orthonormal for the standard
Hermitian inner product on `ℂ^A`. -/

theorem schmidt_rank_unique {r r' : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} {s' : Fin r' → ℝ} {u' : Fin r' → A → ℂ} {v' : Fin r' → B → ℂ}
    (h : IsSchmidtDecomposition psi s u v) (h' : IsSchmidtDecomposition psi s' u' v') :
    r = r' := by
  have hc := congrArg Multiset.card (schmidt_unique h h')
  simpa using hc

/-- **Schmidt decomposition.** Every bipartite pure state (given by its amplitudes
`psi i j` in a product basis) admits a Schmidt decomposition
`psi i j = ∑ k, s k * u k i * v k j` with positive Schmidt coefficients `s k` and
orthonormal families `u`, `v`; moreover the Schmidt coefficients are unique: any two
Schmidt decompositions of the same state have the same multiset of coefficients (in
particular the same number of terms, the Schmidt rank). -/
