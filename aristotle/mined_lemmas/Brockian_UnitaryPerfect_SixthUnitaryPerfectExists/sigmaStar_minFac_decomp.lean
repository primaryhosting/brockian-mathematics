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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to come first in a file, so the
required header comment is placed immediately after the single `import Mathlib` line.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- `d` is a *unitary divisor* of `n` when `d ∣ n` and `d` is coprime to `n / d`. -/

lemma sigmaStar_minFac_decomp {m : ℕ} (hm : 1 < m) :
    ∃ a k : ℕ, 0 < a ∧ k ≠ 0 ∧ m = m.minFac ^ a * k ∧ ¬ m.minFac ∣ k ∧ k ∣ m ∧
      sigmaStar m = (1 + m.minFac ^ a) * sigmaStar k := by
  have hm0 : m ≠ 0 := by omega
  have hp : (m.minFac).Prime := Nat.minFac_prime (by omega)
  have hpos : 0 < m.factorization m.minFac :=
    hp.factorization_pos_of_dvd hm0 (Nat.minFac_dvd m)
  refine ⟨m.factorization m.minFac, ordCompl[m.minFac] m, hpos,
    (Nat.ordCompl_pos m.minFac hm0).ne', (Nat.ordProj_mul_ordCompl_eq_self m m.minFac).symm,
    Nat.not_dvd_ordCompl hp hm0, Nat.ordCompl_dvd m m.minFac, ?_⟩
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self m m.minFac]
  exact sigmaStar_prime_pow_mul hp hpos (Nat.ordCompl_pos m.minFac hm0).ne'
    (Nat.not_dvd_ordCompl hp hm0)

/-- The sum of unitary divisors of an odd number bigger than one is even. -/
