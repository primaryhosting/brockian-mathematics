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

/-
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian
namespace ZumkellerNumbers

/-- A positive natural number `n` is a *Zumkeller number* if the set of its divisors can be
split into two parts having the same sum. -/

theorem infinite_odd_zumkeller : {n : ℕ | Odd n ∧ Zumkeller n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 945 * 11 ^ k) ?_ ?_
  · intro a b hab
    have h11 : (11 : ℕ) ^ a = 11 ^ b := by
      have := hab
      simp only at this
      omega
    exact Nat.pow_right_injective (by norm_num) h11
  · intro k
    have hodd : Odd ((11 : ℕ) ^ k) := Odd.pow (by decide)
    have hcop : Nat.Coprime 945 (11 ^ k) := Nat.Coprime.pow_right k (by decide)
    obtain ⟨h1, _, h3⟩ := OddZumkellerFrom3Structure hodd hcop
    exact ⟨h1, h3⟩

end ZumkellerNumbers
end Brockian

