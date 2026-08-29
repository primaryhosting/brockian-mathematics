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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` whose sums of prime
factors, counted with multiplicity, agree; the name comes from the pair `(714, 715)`.
Whether there are infinitely many such pairs is an open problem (Erdős); the file below
develops the basic theory of the function `sopfr`, proves a number of unconditional
structural results about Ruth–Aaron pairs, and gives the infinitude statement as a
conditional reduction from the unboundedness hypothesis.
-/

namespace Brockian
namespace RuthAaronPairs

/-! ## The sum-of-prime-factors function `sopfr` -/

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(OEIS A001414).  By convention `sopfr 0 = sopfr 1 = 0`. -/

theorem no_semiprime_ruthAaronPair {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hprod : p * q + 1 = r * s) (hsum : p + q = r + s) : False := by
  have hprod' : (p : ℤ) * q + 1 = r * s := by exact_mod_cast hprod
  have hsum' : (p : ℤ) + q = r + s := by exact_mod_cast hsum
  -- The key identity `(r - p) * (r - q) = -1`.
  have key : ((r : ℤ) - p) * ((r : ℤ) - q) = -1 := by
    linear_combination hprod' - (r : ℤ) * hsum'
  have hcases : ((r : ℤ) - p = 1 ∧ (r : ℤ) - q = -1) ∨ ((r : ℤ) - p = -1 ∧ (r : ℤ) - q = 1) := by
    have h1 : ((r : ℤ) - p) ∣ 1 := ⟨-((r : ℤ) - q), by linarith [key]⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one h1) with h | h
    · exact Or.inl ⟨h, by rw [h] at key; linarith⟩
    · exact Or.inr ⟨h, by rw [h] at key; linarith⟩
  rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hp1 : p + 1 = r := by omega
    have hq1 : q = r + 1 := by omega
    subst hq1; subst hp1
    exact no_three_consecutive_primes hp hr hq
  · have hp1 : p = r + 1 := by omega
    have hq1 : q + 1 = r := by omega
    subst hp1; subst hq1
    exact no_three_consecutive_primes hq hr hp

/-- Restatement of `no_semiprime_ruthAaronPair` for Ruth–Aaron pairs: if `n = p * q` and
`n + 1 = r * s` with `p, q, r, s` prime, then `(n, n+1)` is not a Ruth–Aaron pair. -/
