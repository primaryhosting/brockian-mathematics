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

lemma inner_sub_inner_eq (A B : H →ₗ[ℂ] H)
    (hA : ∀ u v : H, ⟪A u, v⟫ = ⟪u, A v⟫) (hB : ∀ u v : H, ⟪B u, v⟫ = ⟪u, B v⟫)
    (psi : H) :
    ⟪A psi - ⟪psi, A psi⟫ • psi, B psi - ⟪psi, B psi⟫ • psi⟫
      - ⟪B psi - ⟪psi, B psi⟫ • psi, A psi - ⟪psi, A psi⟫ • psi⟫
      = ⟪psi, A (B psi) - B (A psi)⟫ := by
  have ha : conj ⟪psi, A psi⟫ = ⟪psi, A psi⟫ := conj_expectation_eq A hA psi
  have hb : conj ⟪psi, B psi⟫ = ⟪psi, B psi⟫ := conj_expectation_eq B hB psi
  have hAp : ⟪A psi, psi⟫ = ⟪psi, A psi⟫ := by rw [← inner_conj_symm, ha]
  have hBp : ⟪B psi, psi⟫ = ⟪psi, B psi⟫ := by rw [← inner_conj_symm, hb]
  have h1 : ⟪psi, A (B psi)⟫ = ⟪A psi, B psi⟫ := by rw [hA]
  have h2 : ⟪psi, B (A psi)⟫ = ⟪B psi, A psi⟫ := by rw [hB]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    h1, h2, ha, hb, hAp, hBp]
  ring

/--
**Heisenberg uncertainty principle** (Robertson form, specialised to the canonical
commutation relation).

Let `X` and `P` be symmetric (formally self-adjoint) operators on a complex inner
product space, and let `psi` be a normalized state satisfying the canonical
commutation relation `X P psi - P X psi = (i ℏ) psi`.  Then the product of the
standard deviations of `X` and `P` in the state `psi` is at least `ℏ / 2`.

The proof is the classical one: the commutator expectation equals twice the
imaginary part of `⟪Δx ψ, Δp ψ⟫`, which is bounded by its modulus, which in turn
is bounded by `‖Δx ψ‖ ‖Δp ψ‖` by Cauchy–Schwarz (`norm_inner_le_norm`).
-/
