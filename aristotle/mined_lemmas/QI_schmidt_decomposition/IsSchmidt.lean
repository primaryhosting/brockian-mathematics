/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open scoped ComplexConjugate

variable {m n : ℕ}

/-- The amplitude matrix of a bipartite pure state, i.e. its coordinates in the product basis. -/

def IsSchmidt {r : ℕ} (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (lam : Fin r → ℝ)
    (e : Fin r → EuclideanSpace ℂ (Fin m)) (f : Fin r → EuclideanSpace ℂ (Fin n)) : Prop :=
  (∀ i, 0 < lam i) ∧ Orthonormal ℂ e ∧ Orthonormal ℂ f ∧
    ∀ p : Fin m × Fin n, ψ p = ∑ i, (lam i : ℂ) * e i p.1 * f i p.2

/-- The `s²`-eigenspace of the reduced density matrix of `ψ`. -/
