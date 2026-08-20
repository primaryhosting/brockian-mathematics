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

lemma contDiff_reducedResolvent
    (hP_idem : ∀ s, P s * P s = P s)
    (hEig : ∀ s, Ham s * P s = (Ev s : ℂ) • P s)
    (hComm : ∀ s, Ham s * P s = P s * Ham s)
    (hgap_pos : 0 < gap)
    (hgap : ∀ s, ∀ v : 𝓗, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖)
    (hHam : ContDiff ℝ 1 Ham) (hEv : ContDiff ℝ 1 Ev) (hP : ContDiff ℝ 1 P) :
    ContDiff ℝ 1 (reducedResolvent Ham P Ev) := by
  have hM : ContDiff ℝ 1 (gappedOp Ham P Ev) := contDiff_gappedOp Ham P Ev hHam hEv hP
  rw [contDiff_iff_contDiffAt]
  intro s
  obtain ⟨u, hu⟩ := isUnit_gappedOp Ham P Ev gap hP_idem hEig hComm hgap_pos hgap s
  have h1 : ContDiffAt ℝ 1 (Ring.inverse : (𝓗 →L[ℂ] 𝓗) → (𝓗 →L[ℂ] 𝓗)) (gappedOp Ham P Ev s) := by
    rw [← hu]; exact contDiffAt_ringInverse ℝ u
  exact h1.comp s hM.contDiffAt

