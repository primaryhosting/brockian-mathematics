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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Finset

/-- `IsFortunate n m` says that `m` is the *fortunate number* attached to the primorial `n#`:
it is the least integer `m > 1` such that `n# + m` is prime. -/

theorem not_dvd_of_prime_le {n m q : ℕ} (hm1 : 1 < m) (hp : Nat.Prime (primorial n + m))
    (hq : Nat.Prime q) (hqn : q ≤ n) : ¬ q ∣ m := by
  intro hdvdm
  have hdvdN : q ∣ primorial n :=
    Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hq⟩)
  have hdvd : q ∣ primorial n + m := Nat.dvd_add hdvdN hdvdm
  have hle' : q ≤ m := Nat.le_of_dvd (by omega) hdvdm
  have hpos : 0 < primorial n := primorial_pos n
  rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd with h | h
  · exact hq.one_lt.ne' h
  · omega

/-- **Key unconditional step.** If `m > 1`, `n# + m` is prime and `m ≤ n ^ 2`, then `m` is prime.

Indeed, a composite `m` would have a prime factor `q` with `q ^ 2 ≤ m ≤ n ^ 2`, hence `q ≤ n`,
so `q` divides the primorial `n#` as well as `m`, hence divides the prime `n# + m`, which is
impossible since `1 < q < n# + m`. -/
