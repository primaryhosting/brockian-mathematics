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

namespace QPhys

open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value `⟨T⟩_ψ = ⟪ψ, T ψ⟫` of an observable `T` in the state `ψ`. -/

lemma inner_centred (X P : H →ₗ[ℂ] H) (psi : H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hnorm : ‖psi‖ = 1) :
    ⟪X psi - expect X psi • psi, P psi - expect P psi • psi⟫_ℂ
      = ⟪X psi, P psi⟫_ℂ - expect X psi * expect P psi := by
  have hself : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  have hxa : ⟪X psi, psi⟫_ℂ = expect X psi := by
    rw [hX]; rfl
  have hpb : ⟪psi, P psi⟫_ℂ = expect P psi := rfl
  have ha : conj (expect X psi) = expect X psi := conj_expect X psi hX
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, hself, hxa, hpb, ha]
  ring

/-- **Heisenberg uncertainty principle.**  If `X` and `P` are symmetric operators on a complex
inner product space satisfying the canonical commutation relation `[X, P] ψ = i ℏ ψ` at a
normalized state `ψ`, then the product of the uncertainties of `X` and `P` in the state `ψ`
is at least `ℏ / 2`. -/
