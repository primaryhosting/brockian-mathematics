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

@[ext] theorem ext {v w : Qubit} (h1 : v.fst = w.fst) (h2 : v.snd = w.snd) : v = w := by
  cases v; cases w
  simp only [Subtype.mk.injEq, Prod.ext_iff]
  exact ⟨h1, h2⟩

/-- Two qubit states are equivalent when they differ by a global phase. -/
instance setoid : Setoid Qubit where
  r v w := ∃ c : ℂ, ‖c‖ = 1 ∧ w.fst = c * v.fst ∧ w.snd = c * v.snd
  iseqv := by
    refine ⟨fun v => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro v w ⟨c, hc, h1, h2⟩
      have hc0 : c ≠ 0 := by
        intro h; rw [h] at hc; simp at hc
      exact ⟨c⁻¹, by simp [hc], by rw [h1]; field_simp, by rw [h2]; field_simp⟩
    · rintro u v w ⟨c, hc, h1, h2⟩ ⟨d, hd, h3, h4⟩
      exact ⟨d * c, by simp [hd, hc], by rw [h3, h1]; ring, by rw [h4, h2]; ring⟩

end Qubit

/-- Pure qubit states modulo global phase. -/
