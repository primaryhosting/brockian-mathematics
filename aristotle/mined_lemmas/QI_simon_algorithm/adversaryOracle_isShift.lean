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


lemma adversaryOracle_isShift {n : ℕ} (Q : Finset (V n)) (s : V n) (i0 : Fin n)
    (hi0 : s i0 = 1) (hQ : ∀ a ∈ Q, a + s ∉ Q) : IsShift (adversaryOracle Q s i0) s := by
  intro x y
  constructor
  · intro hxy
    rcases adversaryOracle_mem_pair Q s i0 x with hx | hx <;>
      rcases adversaryOracle_mem_pair Q s i0 y with hy | hy <;> rw [hx, hy] at hxy
    · exact Or.inl hxy.symm
    · right
      rw [hxy, add_add_cancel_cube]
    · right
      exact hxy.symm
    · left
      exact (add_right_cancel hxy).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (adversaryOracle_shift Q s i0 hi0 hQ x).symm

/-- **The classical lower bound.** Any deterministic classical algorithm solving Simon's
problem on `n` bits must make at least `2^(n/2)` queries. -/
