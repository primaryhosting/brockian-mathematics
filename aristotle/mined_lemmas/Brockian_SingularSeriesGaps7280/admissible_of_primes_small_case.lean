import Mathlib

/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* when, for every prime `p`, the
reductions of the elements of `H` modulo `p` omit at least one residue class.
This is exactly the condition under which the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` is non-zero, i.e. the Hardy–Littlewood
prime `k`-tuples conjecture predicts infinitely many translates of `H` consisting
entirely of primes. -/

theorem admissible_of_primes_small_case {H : Finset ℤ} {p : ℕ} (hp : p.Prime)
    (hple : p ≤ H.card)
    (hH : ∀ h ∈ H, ∃ q : ℕ, q.Prime ∧ (q : ℤ) = h ∧ (H.card : ℤ) < h) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  refine ⟨0, ?_⟩
  intro h hh hzero
  obtain ⟨q, hq, hqh, hlt⟩ := hH h hh
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hzero
  subst hqh
  have hdvd : p ∣ q := by exact_mod_cast hzero
  have hpq : p = q := ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
  have : (H.card : ℤ) < (p : ℤ) := by rw [hpq]; exact hlt
  have : (H.card : ℤ) < (H.card : ℤ) := lt_of_lt_of_le this (by exact_mod_cast hple)
  exact absurd this (lt_irrefl _)

/-- Large primes never obstruct a set with fewer elements than the modulus:
by cardinality, some residue class is missed. -/
