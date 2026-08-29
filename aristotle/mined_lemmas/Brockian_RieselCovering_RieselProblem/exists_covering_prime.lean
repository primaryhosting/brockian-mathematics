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

/- (Lean requires `import` to be the first command, so this required header is
   given as a plain block comment; it is repeated as a module docstring below.)

# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RieselCovering

/-- Riesel's candidate constant `k = 509203`. -/

theorem exists_covering_prime (n : ℕ) :
    ∃ p ∈ coveringPrimes, p ∣ k * 2 ^ n - 1 ∧ 3 ≤ p ∧ p ≤ 241 := by
  have hr : n % 24 < 24 := Nat.mod_lt _ (by norm_num)
  refine ⟨pick (n % 24), pick_mem _ hr, ?_, pick_bounds _ hr⟩
  have hle : 1 ≤ k * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by simp [k])
  rw [← Nat.modEq_iff_dvd' hle]
  calc (1 : ℕ) ≡ k * 2 ^ (n % 24) [MOD pick (n % 24)] := (pick_value _ hr).symm
    _ ≡ k * 2 ^ n [MOD pick (n % 24)] :=
        Nat.ModEq.mul_left k (pow_two_period (pick_period _ hr) n).symm

/-- **The Riesel problem, covering-set half.** `k = 509203` is a Riesel number:
`509203 * 2 ^ n - 1` is never prime.  (The statement is proved for every `n : ℕ`,
in particular for all `n ≥ 1`.) -/
