import Mathlib

/-!
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)


lemma sum_e : ∑ a : ZMod 5, e a = 0 := by
  have hgeom : ∑ i ∈ Finset.range 5, ω ^ i = 0 :=
    omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  have : ∑ a : ZMod 5, e a = ∑ i ∈ Finset.range 5, ω ^ i := by
    rw [Finset.sum_range fun i => ω ^ i]
    rfl
  rw [this, hgeom]

