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

namespace OddZumkeller

/-- A positive natural number `n` is a *Zumkeller number* if its set of divisors can be split
into two parts having the same sum. -/

lemma three_le_of_mem_primeFactors_odd {n p : ℕ} (hodd : Odd n) (hp : p ∈ n.primeFactors) :
    3 ≤ p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hne : p ≠ 2 := by
    rintro rfl
    have h1 : n % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have := hpp.two_le
  omega

/-- **Main structural result.** An odd Zumkeller number has at least three distinct prime
factors. -/
