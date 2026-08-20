import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
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

namespace QC

/-- A pure qubit state: a unit vector in `ℂ²`. -/

noncomputable def blochRaw (v : QubitState) : Sphere2 :=
  ⟨![2 * ((starRingEnd ℂ) (v.1 0) * v.1 1).re,
     2 * ((starRingEnd ℂ) (v.1 0) * v.1 1).im,
     ‖v.1 0‖ ^ 2 - ‖v.1 1‖ ^ 2], by
    obtain ⟨v, hv⟩ := v
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    simp only [Complex.sq_norm] at hv ⊢
    simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply, Complex.conj_re,
      Complex.conj_im] at hv ⊢
    nlinarith [hv, sq_nonneg ((v 0).re), sq_nonneg ((v 0).im), sq_nonneg ((v 1).re),
      sq_nonneg ((v 1).im)]⟩

