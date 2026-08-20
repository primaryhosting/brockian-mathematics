/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The `N`-dimensional quantum Fourier transform matrix:
`(QFT_N)_{j,k} = exp(2πi·j·k/N) / √N`. -/

lemma zeta_ne_one (N : ℕ) (hN : 0 < N) (d : ℤ) (hd : ¬ ((N : ℤ) ∣ d)) : zeta N d ≠ 1 := by
  intro h
  rw [zeta, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hd' : (d : ℂ) = (n : ℂ) * (N : ℂ) := by
    field_simp at hn
    linear_combination hn
  have : d = n * (N : ℤ) := by exact_mod_cast hd'
  exact hd ⟨n, by rw [this]; ring⟩

/-- Geometric sum of a nontrivial `N`-th root of unity vanishes. -/
