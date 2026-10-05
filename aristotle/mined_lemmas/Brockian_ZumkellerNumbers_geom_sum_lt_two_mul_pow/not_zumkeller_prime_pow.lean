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

namespace Brockian.ZumkellerNumbers


theorem not_zumkeller_prime_pow (p k : ℕ) (hp : p.Prime) : ¬ Zumkeller (p ^ k) := by
  rintro ⟨S, hS, hsum⟩
  have hN0 : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hNmem : p ^ k ∈ (p ^ k).divisors := Nat.mem_divisors_self _ hN0
  have hlt := sum_divisors_prime_pow_lt p k hp
  by_cases hNS : p ^ k ∈ S
  · have hle : p ^ k ≤ ∑ d ∈ S, d :=
      Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) hNS
    omega
  · have hsub : S ⊆ (p ^ k).divisors.erase (p ^ k) := Finset.subset_erase.2 ⟨hS, hNS⟩
    have h1 : ∑ d ∈ S, d ≤ ∑ d ∈ (p ^ k).divisors.erase (p ^ k), d :=
      Finset.sum_le_sum_of_subset hsub
    have h2 : p ^ k + ∑ d ∈ (p ^ k).divisors.erase (p ^ k), d = ∑ d ∈ (p ^ k).divisors, d :=
      Finset.add_sum_erase _ (fun d => d) hNmem
    omega

end Brockian.ZumkellerNumbers

