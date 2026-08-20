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

lemma apply_star_mul_eq_zero_right {psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hpos : ∀ A : H →L[ℂ] H, 0 ≤ A → 0 ≤ psi A) {q : H →L[ℂ] H}
    (hq : psi (star q * q) = 0) (X : H →L[ℂ] H) : psi (star X * q) = 0 := by
  set f : (H →L[ℂ] H) →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ psi hpos with hf
  have hfa : ∀ A, f A = psi A := fun _ => rfl
  have hnorm : ‖f.toPreGNS q‖ = 0 := by
    rw [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS, hfa, hq]
    simp
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS X) (f.toPreGNS q)
  rw [hnorm, mul_zero] at h1
  have h2 : ⟪f.toPreGNS X, f.toPreGNS q⟫_ℂ = 0 := by
    simpa using norm_le_zero_iff.mp h1
  rw [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    PositiveLinearMap.ofPreGNS_toPreGNS, hfa] at h2
  exact h2

/-! ## The atomic case: a state concentrated on a unit vector is the vector state -/

/-- If a state `psi` of `B(H)` takes the value `1` on the rank-one projection onto a unit
vector `u`, then `psi` is the vector state `A ↦ ⟪u, A u⟫`. -/
