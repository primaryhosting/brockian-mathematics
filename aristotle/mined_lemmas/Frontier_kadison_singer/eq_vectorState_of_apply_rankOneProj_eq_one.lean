/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace Frontier
namespace KadisonSinger

/-! ## The setting

Let `H` be a complex Hilbert space with a distinguished orthonormal (Hilbert) basis `e : ι → H`.
The *diagonal* subalgebra `𝒟` (an atomic MASA in `B(H)`, isomorphic to `ℓ^∞(ι)`) consists of the
bounded operators that are diagonalised by the basis.  The Kadison–Singer problem asks whether
every pure state of `𝒟` extends *uniquely* to a state of `B(H)`; this was answered
affirmatively by Marcus, Spielman and Srivastava.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The rank-one orthogonal projection onto the line spanned by a unit vector `u`, i.e. `u u*`. -/

theorem eq_vectorState_of_apply_rankOneProj_eq_one {psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hpsi : IsState psi) {u : H} (hu : ‖u‖ = 1)
    (h1 : psi (rankOneProj u) = 1) (A : H →L[ℂ] H) : psi A = ⟪u, A u⟫_ℂ := by
  set P := rankOneProj u with hP
  set q : H →L[ℂ] H := 1 - P with hq
  have hstarP : star P = P := star_rankOneProj u
  have hPP : P * P = P := rankOneProj_mul_self u hu
  have hstarq : star q = q := by rw [hq, star_sub, star_one, hstarP]
  have hqq : star q * q = q := by
    have hexp : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    rw [hstarq, hq, hexp, hPP]
    abel
  have hpq : psi (star q * q) = 0 := by
    rw [hqq, hq, map_sub, hpsi.map_one, h1, sub_self]
  -- decomposition `A = P A P + q A + P A q`
  have hdecomp : A = P * A * P + q * A + P * A * q := by
    rw [hq, sub_mul, mul_sub, one_mul, mul_one]
    abel
  have e1 : psi (P * A * P) = ⟪u, A u⟫_ℂ := by
    rw [hP, rankOneProj_mul_mul, map_smul, h1, smul_eq_mul, mul_one]
  have e2 : psi (q * A) = 0 := by
    have := apply_star_mul_eq_zero_left hpsi.nonneg hpq A
    rwa [hstarq] at this
  have e3 : psi (P * A * q) = 0 := by
    have := apply_star_mul_eq_zero_right hpsi.nonneg hpq (star (P * A))
    rwa [star_star] at this
  calc psi A = psi (P * A * P + q * A + P * A * q) := by rw [← hdecomp]
    _ = ⟪u, A u⟫_ℂ := by rw [map_add, map_add, e1, e2, e3, add_zero, add_zero]

/-! ## The vector state really is a state (non-vacuity of the hypotheses) -/

/-- The vector state `A ↦ ⟪u, A u⟫` as a linear functional. -/
