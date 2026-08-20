/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Bit strings and phases -/

/-- The computational basis of `n` qubits is indexed by bit strings `Fin n → ZMod 2`. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The `𝔽₂`-valued inner product of two bit strings. -/

lemma dotB_update_right {n : ℕ} (b x : Bits n) (i : Fin n) (v : ZMod 2) :
    dotB b (Function.update x i v) = dotB b x + b i * (v + x i) := by
  have key : ∀ k : Fin n, b k * (Function.update x i v) k
      = b k * x k + (if k = i then b i * (v + x i) else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self, if_true, mul_add]
      linear_combination (-(b k * x k)) * zmod2_two_eq_zero
    · simp [hk]
  simp only [dotB, key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i]
  simp

