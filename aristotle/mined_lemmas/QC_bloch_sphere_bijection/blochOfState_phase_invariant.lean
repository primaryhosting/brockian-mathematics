/-
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is written as a plain block comment rather than a module
-- docstring `/-! ... -/` because Lean 4 requires all `import` commands to come
-- before any command, and a module docstring counts as a command.)
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

set_option grind.warning false

namespace QC

open Complex

/-- A (normalized) pure qubit state vector: a unit vector of `ℂ²`. -/

theorem blochOfState_phase_invariant {p q : QubitState} (h : PhaseRel p q) :
    blochOfState p = blochOfState q := by
  obtain ⟨u, hu, h1, h2⟩ := h
  have hconj : (starRingEnd ℂ) u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, hu]
    norm_num
  have key : (starRingEnd ℂ) q.1.1 * q.1.2 = (starRingEnd ℂ) p.1.1 * p.1.2 := by
    rw [h1, h2, map_mul]
    calc (starRingEnd ℂ) u * (starRingEnd ℂ) p.1.1 * (u * p.1.2)
        = ((starRingEnd ℂ) u * u) * ((starRingEnd ℂ) p.1.1 * p.1.2) := by ring
      _ = (starRingEnd ℂ) p.1.1 * p.1.2 := by rw [hconj, one_mul]
  have hn1 : normSq q.1.1 = normSq p.1.1 := by rw [h1, map_mul, hu, one_mul]
  have hn2 : normSq q.1.2 = normSq p.1.2 := by rw [h2, map_mul, hu, one_mul]
  apply Subtype.ext
  show blochVec p = blochVec q
  simp only [blochVec]
  rw [key, hn1, hn2]

/-- The Bloch map from pure qubit states modulo phase to the 2-sphere. -/
