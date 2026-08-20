/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace Phys

/-! ## The pure ring algebra behind Kato's construction -/

/-- The algebraic heart of the adiabatic theorem.  In a ring, let `p` be an idempotent,
`k` an element annihilating `p` on both sides (think of `k = H - E` with `p` the spectral
projection of the eigenvalue `E`), `d` the derivative of `p` (so that `d = d*p + p*d`), and `b`
a two-sided inverse of `k + p`.  Then the explicitly constructed element
`b*(1-p)*d*p - p*d*(1-p)*b` has commutator with `k` equal to `d`. -/

lemma isUnit_gappedOp
    (hP_idem : ∀ s, P s * P s = P s)
    (hEig : ∀ s, Ham s * P s = (Ev s : ℂ) • P s)
    (hComm : ∀ s, Ham s * P s = P s * Ham s)
    (hgap_pos : 0 < gap)
    (hgap : ∀ s, ∀ v : 𝓗, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖) (s : ℝ) :
    IsUnit (gappedOp Ham P Ev s) := by
  have key : ∀ v : 𝓗, gappedOp Ham P Ev s v = 0 → v = 0 := by
    intro v hv
    have happ : Ham s v - (Ev s : ℂ) • v + P s v = 0 := by
      simpa [gappedOp, shiftedHam] using hv
    have hPv : P s v = 0 := by
      have h0 := congrArg (fun w => P s w) happ
      simp only [map_add, map_sub, map_smul, map_zero] at h0
      have h1 : P s (Ham s v) = (Ev s : ℂ) • P s v := by
        have := congrArg (fun (A : 𝓗 →L[ℂ] 𝓗) => A v) ((hComm s).symm.trans (hEig s))
        simpa using this
      have h2 : P s (P s v) = P s v := by
        have := congrArg (fun (A : 𝓗 →L[ℂ] 𝓗) => A v) (hP_idem s)
        simpa using this
      rw [h1, h2] at h0
      simpa using h0
    have h3 : Ham s v - (Ev s : ℂ) • v = 0 := by rw [hPv, add_zero] at happ; exact happ
    have hgv := hgap s v hPv
    rw [h3] at hgv
    simp at hgv
    have hle : ‖v‖ ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [hgv]
    simpa using le_antisymm hle (norm_nonneg v)
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinj : Function.Injective ((gappedOp Ham P Ev s) : 𝓗 →ₗ[ℂ] 𝓗) := by
    intro x y hxy
    have h0 : gappedOp Ham P Ev s (x - y) = 0 := by simpa [map_sub, sub_eq_zero] using hxy
    exact sub_eq_zero.mp (key _ h0)
  exact ⟨hinj, (LinearMap.injective_iff_surjective).1 hinj⟩

omit [FiniteDimensional ℂ 𝓗] in
