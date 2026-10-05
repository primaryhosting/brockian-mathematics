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

theorem phaseRel_equivalence : Equivalence PhaseRel := by
  constructor
  · intro p
    exact ⟨1, by simp, by simp, by simp⟩
  · rintro p q ⟨u, hu, h1, h2⟩
    have hu0 : u ≠ 0 := by
      intro h; rw [h] at hu; simp at hu
    refine ⟨u⁻¹, ?_, ?_, ?_⟩
    · rw [map_inv₀, hu]; simp
    · rw [h1]; field_simp
    · rw [h2]; field_simp
  · rintro p q r ⟨u, hu, h1, h2⟩ ⟨v, hv, k1, k2⟩
    refine ⟨v * u, ?_, ?_, ?_⟩
    · rw [map_mul, hu, hv]; ring
    · rw [k1, h1]; ring
    · rw [k2, h2]; ring

instance phaseSetoid : Setoid QubitState := ⟨PhaseRel, phaseRel_equivalence⟩

/-- The space of pure qubit states modulo global phase (i.e. `ℂP¹`). -/
