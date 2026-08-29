/-
/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- A finite set of integers `H` is *admissible* if for every prime `p` the reductions of the
elements of `H` modulo `p` omit at least one residue class.  Equivalently, the singular series
`𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}` of the Hardy–Littlewood prime `k`-tuple conjecture
is nonzero. -/

private lemma primeCount_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((Finset.Ico a c).filter Nat.Prime).card
      = ((Finset.Ico a b).filter Nat.Prime).card
        + ((Finset.Ico b c).filter Nat.Prime).card := by
  rw [← Finset.Ico_union_Ico_eq_Ico hab hbc, Finset.filter_union,
    Finset.card_union_of_disjoint]
  exact (Finset.Ico_disjoint_Ico_consecutive a b c).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
