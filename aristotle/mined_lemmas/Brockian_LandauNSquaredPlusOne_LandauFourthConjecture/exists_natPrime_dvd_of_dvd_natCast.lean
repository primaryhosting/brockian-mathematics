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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

open Zsqrtd

/-- A *Landau prime* is a prime natural number of the form `n ^ 2 + 1`. -/

lemma exists_natPrime_dvd_of_dvd_natCast {x : GaussianInt} (hx : Prime x) {m : ℕ} (hm : m ≠ 0)
    (hdvd : x ∣ (m : GaussianInt)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ m ∧ x ∣ (p : GaussianInt) := by
  have hprod : ((m : GaussianInt)) =
      (m.primeFactorsList.map (fun p : ℕ => (p : GaussianInt))).prod := by
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList hm]
  rw [hprod] at hdvd
  obtain ⟨a, ha, hxa⟩ := hx.dvd_prod_iff.1 hdvd
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, Nat.dvd_of_mem_primeFactorsList hp, hxa⟩

/-- If `n + i` is a Gaussian prime, then `n ^ 2 + 1` is a rational prime. -/
