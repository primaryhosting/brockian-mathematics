/- (header comment; Lean requires `import` to be the first command, so the header
   below is a plain block comment rather than a module docstring)
/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

namespace QPhys

open scoped ComplexInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Expectation value of a (symmetric) operator `A` in the state `psi`. -/

theorem heisenberg_uncertainty {X P : H →ₗ[ℂ] H}
    (hX : ∀ u v : H, inner ℂ (X u) v = inner ℂ u (X v))
    (hP : ∀ u v : H, inner ℂ (P u) v = inner ℂ u (P v))
    {hbar : ℝ} (hbar_nonneg : 0 ≤ hbar) {psi : H} (hpsi : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = (Complex.I * (hbar : ℂ)) • psi) :
    spread X psi * spread P psi ≥ hbar / 2 := by
  set a : ℝ := expect X psi with ha
  set b : ℝ := expect P psi with hb
  set u : H := X psi - (a : ℂ) • psi with hu
  set v : H := P psi - (b : ℂ) • psi with hv
  -- the commutator pairing
  have hkey : inner ℂ u v - inner ℂ v u = Complex.I * (hbar : ℂ) := by
    rw [hu, hv, inner_comm_shift hX hP psi a b, hcomm, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hpsi]
    simp
  have hconj : inner ℂ v u = (starRingEnd ℂ) (inner ℂ u v) := (inner_conj_symm v u).symm
  have habs : hbar = ‖inner ℂ u v - inner ℂ v u‖ := by
    rw [hkey]
    simp [abs_of_nonneg hbar_nonneg]
  have h2 : ‖inner ℂ u v - inner ℂ v u‖ ≤ 2 * ‖inner ℂ u v‖ := by
    calc ‖inner ℂ u v - inner ℂ v u‖ ≤ ‖inner ℂ u v‖ + ‖inner ℂ v u‖ := norm_sub_le _ _
      _ = 2 * ‖inner ℂ u v‖ := by rw [hconj, RCLike.norm_conj]; ring
  have h3 : ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have : hbar ≤ 2 * (‖u‖ * ‖v‖) := by
    calc hbar = ‖inner ℂ u v - inner ℂ v u‖ := habs
      _ ≤ 2 * ‖inner ℂ u v‖ := h2
      _ ≤ 2 * (‖u‖ * ‖v‖) := by linarith
  simp only [spread, ge_iff_le, ← ha, ← hb, ← hu, ← hv]
  linarith

end QPhys

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

