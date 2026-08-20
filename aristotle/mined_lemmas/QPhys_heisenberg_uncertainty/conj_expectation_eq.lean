import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open ComplexConjugate

local notation "⟪" x ", " y "⟫" => inner ℂ x y

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- For a symmetric operator `A`, the expectation value `⟪ψ, A ψ⟫` is real. -/

lemma conj_expectation_eq (A : H →ₗ[ℂ] H)
    (hA : ∀ u v : H, ⟪A u, v⟫ = ⟪u, A v⟫) (psi : H) :
    conj ⟪psi, A psi⟫ = ⟪psi, A psi⟫ := by
  rw [inner_conj_symm, hA]

/-- The commutator expectation, expressed through the "centred" vectors. -/
