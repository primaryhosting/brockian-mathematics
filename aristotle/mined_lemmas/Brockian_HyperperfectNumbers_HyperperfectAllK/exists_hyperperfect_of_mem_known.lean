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

import Mathlib

/-!
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `Hyperperfect k n` says that `n` is a *`k`-hyperperfect number*, i.e. `n > 1` and
`n = 1 + k * (σ(n) - n - 1)`, where `σ(n) = ∑ d ∣ n, d`.

The defining equation is written in the subtraction-free form
`(k + 1) * n + k = k * σ(n) + 1`, which over the integers is equivalent to
`n = 1 + k * (σ n - n - 1)`. -/

theorem exists_hyperperfect_of_mem_known (k : ℕ)
    (hk : k ∈ ({1, 2, 3, 6, 11, 12, 18, 30} : Finset ℕ)) :
    ∃ n : ℕ, Hyperperfect k n := by
  fin_cases hk
  · exact ⟨6, hyperperfect_one_six⟩
  · exact ⟨21, hyperperfect_two_21⟩
  · exact ⟨325, hyperperfect_three_325⟩
  · exact ⟨301, hyperperfect_six_301⟩
  · exact ⟨10693, hyperperfect_eleven_10693⟩
  · exact ⟨2041, hyperperfect_twelve_2041⟩
  · exact ⟨1909, hyperperfect_eighteen_1909⟩
  · exact ⟨3901, hyperperfect_thirty_3901⟩

end Brockian.HyperperfectNumbers

