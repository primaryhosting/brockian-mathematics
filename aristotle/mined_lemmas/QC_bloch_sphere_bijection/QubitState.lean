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

def QubitState : Type := {v : Fin 2 → ℂ // ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 = 1}

/-- Two qubit states are identified when they differ by a global phase. -/
instance qubitSetoid : Setoid QubitState where
  r v w := ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ i, w.1 i = z * v.1 i
  iseqv := by
    constructor
    · intro v; exact ⟨1, by simp, by simp⟩
    · rintro v w ⟨z, hz, h⟩
      refine ⟨z⁻¹, ?_, ?_⟩
      · simp [hz]
      · intro i
        have hz0 : z ≠ 0 := by
          intro h0; rw [h0] at hz; simp at hz
        rw [h i, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
    · rintro u v w ⟨z, hz, h⟩ ⟨y, hy, h'⟩
      refine ⟨y * z, by simp [hy, hz], ?_⟩
      intro i
      rw [h' i, h i]; ring

/-- Pure qubit states modulo global phase. -/
