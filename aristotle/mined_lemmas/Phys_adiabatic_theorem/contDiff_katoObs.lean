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

lemma contDiff_katoObs
    (hP_idem : ∀ s, P s * P s = P s)
    (hEig : ∀ s, Ham s * P s = (Ev s : ℂ) • P s)
    (hComm : ∀ s, Ham s * P s = P s * Ham s)
    (hgap_pos : 0 < gap)
    (hgap : ∀ s, ∀ v : 𝓗, P s v = 0 → gap * ‖v‖ ≤ ‖Ham s v - (Ev s : ℂ) • v‖)
    (hHam : ContDiff ℝ 1 Ham) (hEv : ContDiff ℝ 1 Ev) (hP : ContDiff ℝ 2 P) :
    ContDiff ℝ 1 (katoObs Ham P Ev) := by
  have hP1 : ContDiff ℝ 1 P := hP.of_le (by norm_num)
  have hB : ContDiff ℝ 1 (reducedResolvent Ham P Ev) :=
    contDiff_reducedResolvent Ham P Ev gap hP_idem hEig hComm hgap_pos hgap hHam hEv hP1
  have h : ContDiff ℝ (1 + 1 : ℕ) P := by exact_mod_cast hP
  have hdP : ContDiff ℝ 1 (deriv P) := ((contDiff_succ_iff_deriv (n := (1 : ℕ))).1 h).2.2
  have hQ : ContDiff ℝ 1 (fun s => (1 : 𝓗 →L[ℂ] 𝓗) - P s) := contDiff_const.sub hP1
  exact ContDiff.const_smul _
    (((hB.mul hQ).mul hdP).mul hP1 |>.sub (((hP1.mul hdP).mul hQ).mul hB))

omit [FiniteDimensional ℂ 𝓗] in
/-- `P' = P' P + P P'`, obtained by differentiating `P² = P`. -/
