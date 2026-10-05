import Mathlib
/-!
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` to be the very first command in a file, so the
-- required header comment appears immediately after the single `import Mathlib` line.

namespace NumberTheory

/-- **Euler's theorem** (unit form): if `a : ZMod n` is a unit, then
`a ^ Nat.totient n = 1`. -/
theorem euler_totient {n : ℕ} (a : ZMod n) (ha : IsUnit a) :
    a ^ Nat.totient n = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have h : u ^ Nat.totient n = 1 := ZMod.pow_totient u
  calc ((u : ZMod n)) ^ Nat.totient n = ((u ^ Nat.totient n : (ZMod n)ˣ) : ZMod n) := by
        push_cast; ring
    _ = 1 := by rw [h]; rfl

/-- **Euler's theorem** (congruence form): if `a` and `n` are coprime natural numbers,
then `a ^ Nat.totient n ≡ 1 [MOD n]`. -/
theorem euler_totient_modEq {a n : ℕ} (h : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

end NumberTheory

#print axioms NumberTheory.euler_totient
#print axioms NumberTheory.euler_totient_modEq

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

