import Mathlib

/-!
# Local constellation counts for `k`-tuples

For a tuple `H : Fin k → ℤ` (a candidate *prime constellation* / admissible tuple)
and a prime `p`, the **local count** `localCount p H` is the number of distinct
residue classes modulo `p` occupied by the entries of `H`.  The tuple is
**admissible** when `localCount p H < p` for every prime `p`, i.e. no prime
completely covered by the tuple obstructs the tuple from being a prime
constellation infinitely often.

The main results here reduce admissibility to a finite check:

* `Brockian.ConstellationLocalCountK2` : for `k = 2` admissibility is exactly the
  condition at `p = 2`;
* `Brockian.ConstellationLocalCountK3` : for `k = 3` admissibility is exactly the
  conjunction of the conditions at `p = 2` and `p = 3`.
-/

namespace Brockian

open Finset

/-- The number of distinct residue classes modulo `p` occupied by the entries of
the tuple `H`. -/

theorem ConstellationLocalCountK2 (H : Fin 2 → ℤ) :
    Admissible H ↔ localCount 2 H < 2 := by
  rw [admissible_iff_forall_le]
  constructor
  · intro h
    exact h 2 Nat.prime_two le_rfl
  · intro h p hp hp2
    have hp2' : 2 ≤ p := hp.two_le
    interval_cases p
    · exact h

/-- **Local constellation count, `k = 3`.**  A triple of integers is admissible iff
it misses a residue class modulo `2` and a residue class modulo `3`; no other prime
imposes a condition. -/
