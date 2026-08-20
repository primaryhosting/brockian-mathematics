/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of non-negative integers `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture) if for every prime `p` the elements of `H`
do not cover all residue classes modulo `p`.  Equivalently, the local factor of the
singular series `𝔖(H)` attached to `H` is non-zero at every prime. -/

def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, h % p ≠ r

/-- Large primes never obstruct admissibility: if `p` exceeds the size of `H`, then the
residues of `H` modulo `p` cannot exhaust the `p` residue classes.

The counting step is `Finset.card_le_card_of_injOn`-style reasoning packaged as
`Finset.card_image_le` together with `Finset.exists_mem_notMem_of_card_lt_card`. -/
