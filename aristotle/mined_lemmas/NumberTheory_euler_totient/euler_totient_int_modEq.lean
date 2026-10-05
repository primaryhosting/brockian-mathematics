import Mathlib

/-!
# Euler Totient
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.euler_totient
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

namespace NumberTheory

/-- **Euler's theorem**, unit form: for any unit `a` of `ZMod n`,
`a ^ Nat.totient n = 1`. -/

theorem euler_totient_int_modEq {a : ℤ} {n : ℕ} (h : IsCoprime a (n : ℤ)) :
    a ^ Nat.totient n ≡ 1 [ZMOD (n : ℤ)] := by
  have hu : IsUnit ((a : ZMod n)) := by
    obtain ⟨p, q, hpq⟩ := h
    refine IsUnit.of_mul_eq_one ((p : ZMod n)) ?_
    have hc := congrArg (fun z : ℤ => (z : ZMod n)) hpq
    push_cast at hc
    simpa [ZMod.natCast_self, mul_comm] using hc
  have hpow := euler_totient (a := (a : ZMod n)) hu
  have hcast : ((a ^ Nat.totient n : ℤ) : ZMod n) = ((1 : ℤ) : ZMod n) := by
    push_cast
    simpa using hpow
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp hcast

end NumberTheory

