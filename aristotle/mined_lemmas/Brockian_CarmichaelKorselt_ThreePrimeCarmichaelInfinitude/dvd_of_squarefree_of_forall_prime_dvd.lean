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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` such that `a ^ (n - 1) ≡ 1 [MOD n]` for every
`a` coprime to `n` (i.e. a Fermat pseudoprime to every admissible base). -/

theorem dvd_of_squarefree_of_forall_prime_dvd {n m : ℕ} (hsq : Squarefree n)
    (h : ∀ p ∈ n.primeFactors, p ∣ m) : n ∣ m := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  rcases eq_or_ne m 0 with rfl | hm
  · exact dvd_zero n
  rw [← Nat.factorization_le_iff_dvd hn0 hm]
  intro p
  rcases Nat.eq_zero_or_pos (n.factorization p) with hp | hp
  · simp [hp]
  · have hmem : p ∈ n.primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr hp.ne'
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hmem
    calc n.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hsq
      _ ≤ m.factorization p := hprime.factorization_pos_of_dvd hm (h p hmem)

/-- **Korselt's criterion** (sufficiency): a squarefree composite `n > 1` all of whose prime
factors `p` satisfy `(p - 1) ∣ (n - 1)` is a Carmichael number. -/
