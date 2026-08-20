/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain comment and is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Real

/-- The (unnormalized-constant times) `n`-th stationary state of the infinite square
well of width `L`: `ψ n x = c * sin (n π x / L)`. -/

theorem energy_levels_strictMono (hbar m L : ℝ) (hbar0 : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L) :
    StrictMono (fun n : ℕ => E hbar m L n) := by
  have hb : (0:ℝ) < hbar ^ 2 := by positivity
  intro a b hab
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have ha : (0:ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hsq : (a : ℝ) ^ 2 < (b : ℝ) ^ 2 := by nlinarith
  have hden : (0:ℝ) < 2 * m * L ^ 2 := by positivity
  have hpi : (0:ℝ) < π ^ 2 := by positivity
  have hnum : (a : ℝ) ^ 2 * π ^ 2 * hbar ^ 2 < (b : ℝ) ^ 2 * π ^ 2 * hbar ^ 2 :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hsq hpi) hb
  simp only [E]
  gcongr

end QPhys

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

