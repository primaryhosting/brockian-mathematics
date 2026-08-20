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

lemma commutator_katoObs
    (hP_idem : ∀ s, P s * P s = P s)
    (hEig : ∀ s, Ham s * P s = (Ev s : ℂ) • P s)
    (hComm : ∀ s, Ham s * P s = P s * Ham s)
    (hgap_pos : 0 < gap)
    (hgap : ∀ s, ∀ v : 𝓗, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖)
    (hP : ContDiff ℝ 1 P) (s : ℝ) :
    Ham s * katoObs Ham P Ev s - katoObs Ham P Ev s * Ham s
      = -Complex.I • deriv P s := by
  have hkp : shiftedHam Ham Ev s * P s = 0 := by
    rw [shiftedHam, sub_mul, hEig s, smul_mul_assoc, one_mul, sub_self]
  have hpk : P s * shiftedHam Ham Ev s = 0 := by
    rw [shiftedHam, mul_sub, ← hComm s, hEig s, mul_smul_comm, mul_one, sub_self]
  have hunit := isUnit_gappedOp Ham P Ev gap hP_idem hEig hComm hgap_pos hgap s
  have hb1 : reducedResolvent Ham P Ev s * (shiftedHam Ham Ev s + P s) = 1 := by
    rw [reducedResolvent]
    exact Ring.inverse_mul_cancel _ hunit
  have hb2 : (shiftedHam Ham Ev s + P s) * reducedResolvent Ham P Ev s = 1 := by
    rw [reducedResolvent]
    exact Ring.mul_inverse_cancel _ hunit
  have hd := deriv_proj_eq P hP_idem hP s
  have key := kato_commutator (hP_idem s) hkp hpk hd hb1 hb2
  have hHam_eq : Ham s = shiftedHam Ham Ev s + (Ev s : ℂ) • (1 : 𝓗 →L[ℂ] 𝓗) := by
    rw [shiftedHam, sub_add_cancel]
  rw [katoObs]
  set y : 𝓗 →L[ℂ] 𝓗 :=
    reducedResolvent Ham P Ev s * (1 - P s) * deriv P s * P s
      - P s * deriv P s * (1 - P s) * reducedResolvent Ham P Ev s with hy
  have hcomm : Ham s * (-Complex.I • y) - (-Complex.I • y) * Ham s
      = -Complex.I • (shiftedHam Ham Ev s * y - y * shiftedHam Ham Ev s) := by
    rw [hHam_eq]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, one_mul,
      mul_one]
    module
  rw [hcomm, key]

/-- Derivative of the expectation value `⟪ψ, A ψ⟫` along a solution of the Schrödinger
equation `i ε ψ' = H ψ`. -/
