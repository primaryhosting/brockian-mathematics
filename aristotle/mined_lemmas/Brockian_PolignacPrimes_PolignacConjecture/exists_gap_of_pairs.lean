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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to come before any module docstring, so the header
-- above appears both at the very top of the file (as a plain comment) and here, after the
-- import, as the module docstring.

namespace Brockian.PolignacPrimes

/-- `GapOccursInfinitelyOften n` says that there are infinitely many pairs of *consecutive*
primes whose difference is exactly `n`: for every bound `N` there is a prime `p > N` such that
`p + n` is prime and no integer strictly between `p` and `p + n` is prime. -/

theorem exists_gap_of_pairs (n : ℕ) (hn : 0 < n) (h : PairsOccurInfinitelyOften n) :
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ GapOccursInfinitelyOften m := by
  classical
  by_contra hcon
  push_neg at hcon
  have key : ∀ m : ℕ, ∃ N : ℕ, ∀ p : ℕ, N < p → 0 < m → m ≤ n →
      ¬ (p.Prime ∧ (p + m).Prime ∧ ∀ q : ℕ, p < q → q < p + m → ¬ q.Prime) := by
    intro m
    by_cases hm : 0 < m ∧ m ≤ n
    · have hnot := hcon m hm.1 hm.2
      rw [GapOccursInfinitelyOften, not_forall] at hnot
      obtain ⟨N, hN⟩ := hnot
      refine ⟨N, ?_⟩
      intro p hp _ _ hA
      exact hN ⟨p, hp, hA.1, hA.2.1, hA.2.2⟩
    · exact ⟨0, fun p _ h1 h2 _ => hm ⟨h1, h2⟩⟩
  choose f hf using key
  obtain ⟨p, hpB, hp, hpn⟩ := h ((Finset.range (n + 1)).sup f)
  have hex : ∃ j, 1 ≤ j ∧ (p + j).Prime := ⟨n, hn, hpn⟩
  obtain ⟨hm1, hmp⟩ := Nat.find_spec hex
  have hmn : Nat.find hex ≤ n := Nat.find_le ⟨hn, hpn⟩
  have hfm : f (Nat.find hex) ≤ (Finset.range (n + 1)).sup f :=
    Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hmn))
  refine hf (Nat.find hex) p (by omega) hm1 hmn ⟨hp, hmp, ?_⟩
  intro q hq1 hq2 hqprime
  refine Nat.find_min hex (show q - p < Nat.find hex by omega) ⟨by omega, ?_⟩
  rw [show p + (q - p) = q by omega]
  exact hqprime

end Brockian.PolignacPrimes

