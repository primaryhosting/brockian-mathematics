import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## The Boolean cube as an `𝔽₂`-vector space -/

/-- `n`-bit strings, viewed as the elementary abelian 2-group `(ℤ/2)ⁿ`;
addition is bitwise XOR. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2


lemma hadamard_simonState {n : ℕ} (s x0 y : V n) (hs : s ≠ 0) :
    hadamard (simonState s x0) y =
      (Real.sqrt (2 ^ n))⁻¹ * ((Real.sqrt 2)⁻¹ * (sgn (dotp x0 y) + sgn (dotp (x0 + s) y))) := by
  have hne : x0 ≠ x0 + s := fun h => hs (left_eq_add.mp h)
  have hterm : ∀ x : V n, sgn (dotp x y) * simonState s x0 x
      = if x ∈ ({x0, x0 + s} : Finset (V n)) then sgn (dotp x y) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
        else 0 := by
    intro x
    unfold simonState
    split_ifs <;> simp
  unfold hadamard
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]
  push_cast
  ring

/-- **Destructive interference.** Any measurement outcome `y` that is *not* orthogonal to the
hidden shift `s` has amplitude zero. -/
