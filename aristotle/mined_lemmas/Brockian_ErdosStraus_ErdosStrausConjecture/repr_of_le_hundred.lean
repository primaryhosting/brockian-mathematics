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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `ErdosStrausRepr n` says that `4/n` is a sum of three positive unit fractions. -/

theorem repr_of_le_hundred {n : ℕ} (hn : 2 ≤ n) (hn' : n ≤ 100) : ErdosStrausRepr n := by
  have hn1 : n ≠ 1 := by omega
  have hp : (n.minFac).Prime := Nat.minFac_prime hn1
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hle : n.minFac ≤ 100 := le_trans (Nat.minFac_le (by omega)) hn'
  have hrep : ErdosStrausRepr n.minFac := by
    by_cases hm : n.minFac % 12 = 1
    · rcases prime_mod_twelve_eq_one_le_hundred hp hm hle with h | h | h | h | h <;> rw [h]
      · exact repr_thirteen
      · exact repr_thirtyseven
      · exact repr_sixtyone
      · exact repr_seventythree
      · exact repr_ninetyseven
    · exact repr_of_prime_of_mod_twelve_ne_one hp hm
  exact hrep.of_dvd hp.pos (by omega) hdvd

end Brockian.ErdosStraus

