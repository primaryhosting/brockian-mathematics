/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
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

set_option grind.warning false

namespace Math2

open Finset Filter Asymptotics

/-- The number of points of `𝔽₃ⁿ`, where `𝔽₃ⁿ` is modelled as `Fin n → ZMod 3`. -/

lemma exists_bound_le_pow (ε : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, cornersTheoremBound ε ≤ 3 ^ n := by
  refine ⟨cornersTheoremBound ε, fun n hn => ?_⟩
  calc cornersTheoremBound ε ≤ n := hn
    _ ≤ 3 ^ n := Nat.le_of_lt (Nat.lt_pow_self (by norm_num))

/-- **Cap set theorem** (density form).  For every `ε > 0`, once `n` is large enough, every
3AP-free subset (cap set) of `𝔽₃ⁿ` has size at most `ε · 3ⁿ`. -/
