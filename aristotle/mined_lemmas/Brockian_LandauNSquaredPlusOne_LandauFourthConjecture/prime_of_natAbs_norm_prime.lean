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

lemma prime_of_natAbs_norm_prime {x : GaussianInt} (h : Nat.Prime x.norm.natAbs) : Prime x := by
  rw [← irreducible_iff_prime]
  refine ⟨fun hu => h.ne_one (norm_eq_one_iff.2 hu), ?_⟩
  intro a b hab
  have hn : x.norm.natAbs = a.norm.natAbs * b.norm.natAbs := by
    rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
  rw [hn] at h
  rcases Nat.prime_mul_iff.1 h with ⟨_, hb⟩ | ⟨_, ha⟩
  · exact Or.inr (norm_eq_one_iff.1 hb)
  · exact Or.inl (norm_eq_one_iff.1 ha)

/-- If `n ^ 2 + 1` is prime, then `n + i` is a Gaussian prime. -/
