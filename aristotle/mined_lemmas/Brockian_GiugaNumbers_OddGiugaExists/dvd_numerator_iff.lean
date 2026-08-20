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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite number `n > 1` such that `p ∣ n / p - 1` for every
prime `p` dividing `n`. -/

lemma dvd_numerator_iff {p : ℕ} (hp : p ∈ S) :
    (p : ℤ) ∣ ((∑ q ∈ S, ∏ r ∈ S.erase q, (r : ℤ)) - 1) ↔
      (p : ℤ) ∣ ((∏ r ∈ S.erase p, (r : ℤ)) - 1) := by
  classical
  have key : (∑ q ∈ S, ∏ r ∈ S.erase q, (r : ℤ)) - 1
      = ((∏ r ∈ S.erase p, (r : ℤ)) - 1) + ∑ q ∈ S.erase p, ∏ r ∈ S.erase q, (r : ℤ) := by
    rw [← Finset.add_sum_erase S _ hp]; ring
  have hdvd : (p : ℤ) ∣ ∑ q ∈ S.erase p, ∏ r ∈ S.erase q, (r : ℤ) := by
    refine Finset.dvd_sum fun q hq => ?_
    have hne : q ≠ p := (Finset.mem_erase.mp hq).1
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm hne, hp⟩)
  rw [key]
  refine ⟨fun h => ?_, fun h => h.add hdvd⟩
  simpa using dvd_sub h hdvd

/-- Divisibility of Giuga's numerator by the whole product. -/
