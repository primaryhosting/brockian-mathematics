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

/-
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring below.)
import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex

/-- A (normalised) pure qubit state vector: a unit vector `(a, b)` in `ℂ²`,
representing `a|0⟩ + b|1⟩`. -/

lemma blochRaw_wd {v w : Qubit} (h : phaseRel v w) : blochRaw v = blochRaw w := by
  obtain ⟨z, hz, h1, h2⟩ := h
  have hz1 : normSq z = 1 := Real.sqrt_eq_one.mp hz
  have key : (starRingEnd ℂ) (w : ℂ × ℂ).1 * (w : ℂ × ℂ).2
      = (starRingEnd ℂ) (v : ℂ × ℂ).1 * (v : ℂ × ℂ).2 := by
    rw [h1, h2, map_mul]
    have hc : (starRingEnd ℂ) z * z = (normSq z : ℂ) := normSq_eq_conj_mul_self.symm
    calc (starRingEnd ℂ) z * (starRingEnd ℂ) (v : ℂ × ℂ).1 * (z * (v : ℂ × ℂ).2)
        = ((starRingEnd ℂ) z * z) * ((starRingEnd ℂ) (v : ℂ × ℂ).1 * (v : ℂ × ℂ).2) := by ring
      _ = _ := by rw [hc, hz1]; simp
  have k1 : normSq (w : ℂ × ℂ).1 = normSq (v : ℂ × ℂ).1 := by rw [h1, map_mul, hz1, one_mul]
  have k2 : normSq (w : ℂ × ℂ).2 = normSq (v : ℂ × ℂ).2 := by rw [h2, map_mul, hz1, one_mul]
  apply Subtype.ext
  simp only [blochRaw, blochVec, key, k1, k2]

/-- The Bloch map: pure qubit states modulo global phase → `S²`. -/
