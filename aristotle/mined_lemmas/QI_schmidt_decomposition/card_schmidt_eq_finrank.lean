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

theorem card_schmidt_eq_finrank {r : ℕ} {psi : A → B → ℂ} {s : Fin r → ℝ} {u : Fin r → A → ℂ}
    {v : Fin r → B → ℂ} (h : IsSchmidtDecomposition psi s u v) {t : ℝ} (ht : 0 < t) :
    Fintype.card {k : Fin r // s k = t}
      = Module.finrank ℂ (eigSp (reduced psi) ((t : ℂ) ^ 2)) := by
  rw [← span_schmidt_eq_eigSp h ht, finrank_span_eq_card (schmidt_linearIndependent h t)]

omit [DecidableEq B] in
