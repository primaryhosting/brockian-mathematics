/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Statement: A k-uniform intersecting family on [n] (n≥2k) has size ≤ C(n−1,k−1) (Erdős–Ko–Rado).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Statement: A k-uniform intersecting family on [n] (n≥2k) has size ≤ C(n−1,k−1) (Erdős–Ko–Rado).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Math2

/-- The embedding of `[n] = {0, ..., n-1}` into `Fin n` (for `n > 0`). -/

private lemma emb_injOn {n : ℕ} (hn : 0 < n) :
    Set.InjOn (emb n hn) (Finset.range n) := by
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have := congrArg (Fin.val) hab
  rwa [emb_apply_of_lt hn ha, emb_apply_of_lt hn hb] at this

/-- **Erdős–Ko–Rado theorem**: a `k`-uniform intersecting family of subsets of
`[n] = {0, 1, ..., n-1}` with `n ≥ 2k` has at most `(n-1).choose (k-1)` members. -/
