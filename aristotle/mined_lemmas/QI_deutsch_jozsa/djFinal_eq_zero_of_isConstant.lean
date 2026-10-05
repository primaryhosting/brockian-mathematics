import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
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

variable {n : ℕ}

/-- The computational basis of `n` qubits, indexed by bit strings `Fin n → Bool`. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- The all-zeros bit string. -/

theorem djFinal_eq_zero_of_isConstant {f : Bits n → Bool} (hconst : IsConstant f)
    {y : Bits n} (hy : y ≠ zeros n) : djFinal f y = 0 := by
  have hval : ∀ x : Bits n, (if f x then (-1 : ℂ) else 1)
      = (if f (zeros n) then (-1 : ℂ) else 1) := by
    intro x
    rw [hconst x (zeros n)]
  rw [djFinal_apply]
  simp only [hval]
  rw [← Finset.sum_mul, sum_phaseSign_eq_zero hy]
  ring

/--
**Deutsch–Jozsa.**  Prepare `|0…0⟩`, apply `H^{⊗n}`, make a *single* query to the phase oracle
of `f`, and apply `H^{⊗n}` again.

* If `f` is constant, the amplitude of the all-zeros outcome has modulus `1` and every other
  amplitude vanishes, so measuring the register returns `0…0` with probability `1`.
* If `f` is balanced, the amplitude of the all-zeros outcome is `0`, so the outcome `0…0`
  never occurs.

Hence one query suffices to decide constant versus balanced.
-/
