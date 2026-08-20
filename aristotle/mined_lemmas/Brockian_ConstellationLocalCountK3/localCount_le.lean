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

theorem localCount_le (p : ℕ) {k : ℕ} (H : Fin k → ℤ) : localCount p H ≤ k := by
  refine le_trans (Finset.card_image_le) ?_
  simp [Finset.card_univ]

/-- Primes larger than the length of the tuple never obstruct admissibility. -/
