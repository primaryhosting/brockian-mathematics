/-
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Finite-dimensional Stinespring dilation theorem: every completely positive
trace-preserving (CPTP) linear map on matrix algebras can be realised by
adjoining an ancilla in a fixed pure state, applying a unitary on the enlarged
system, and tracing out the environment.

The main result is `QI.stinespring`. Along the way we prove Choi's theorem
(`QI.choi_posSemidef`), the Kraus decomposition of a completely positive map
(`QI.exists_kraus`), the completeness relation for the Kraus operators of a
trace-preserving map (`QI.kraus_sum_eq_one`), and the extension of an isometry
to a unitary (`QI.exists_unitary_extension`).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace QI

variable {A B : Type*}

/-- The partial trace of a matrix on a bipartite system `B ⊗ E` over the second
(environment) factor. -/

lemma id_isCompletelyPositive [Fintype A] [DecidableEq A] :
    IsCompletelyPositive (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ) := by
  intro k ρ hρ
  have h : ampliate (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ) (Fin k) ρ = ρ := by
    ext p q; rfl
  rw [h]
  exact hρ

/-- The identity channel is trace preserving. -/
