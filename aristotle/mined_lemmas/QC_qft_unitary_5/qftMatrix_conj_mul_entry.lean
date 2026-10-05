/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

namespace QC

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix:
its `(j, k)` entry is `exp (2 π i j k / N) / √N`. -/

lemma qftMatrix_conj_mul_entry (N : ℕ) (hN : 0 < N) (j l k : Fin N) :
    (starRingEnd ℂ) (qftMatrix N k j) * qftMatrix N k l
      = (Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) - (j : ℕ)) / N)) ^ (k : ℕ) / (N : ℂ) := by
  have hsq : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  simp only [qftMatrix, map_div₀, ← Complex.exp_conj, Complex.conj_ofReal]
  rw [div_mul_div_comm, hsq]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, map_natCast]
  ring

/-- For distinct indices the relevant geometric sum of roots of unity vanishes. -/
