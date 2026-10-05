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

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex

/-- A pure qubit state: a unit vector in `ℂ²`. -/

theorem bloch_phase_invariant {v w : Qubit} (h : v ≈ w) : bloch v = bloch w := by
  obtain ⟨c, hc, h1, h2⟩ := h
  have hcn : normSq c = 1 := by
    rw [Complex.normSq_eq_norm_sq, hc]; norm_num
  have hcn' : c.re ^ 2 + c.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, sq] using hcn
  simp only [bloch, Subtype.mk.injEq, Prod.mk.injEq, h1, h2]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply] <;> nlinarith [hcn']

/-- The Bloch map descended to states modulo global phase. -/
