/-
# Singular Series Gaps 14501460 — Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps14501460.lean`.  The target theorem there is
stated in plain core Lean (its file has to start with a fixed header comment, which forbids
`import`s).  Here the same mathematical content is formalized in the idiomatic Mathlib way,
with tuples as `Finset ℤ`, primality as `Nat.Prime`, and residues in `ZMod p`.
-/

import Mathlib

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) when, for every prime `p`, the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/

theorem singularSeriesGaps14501460_mathlib :
    (∃ H : Finset ℤ, H ⊆ Finset.Icc (1450 : ℤ) 1460 ∧ IsAdmissible H ∧ H.card = 4) ∧
    (∀ H : Finset ℤ, H ⊆ Finset.Icc (1450 : ℤ) 1460 → IsAdmissible H → H.card ≤ 4) :=
  ⟨⟨gapSet, gapSet_subset, gapSet_isAdmissible, gapSet_card⟩, card_le_four_of_isAdmissible⟩

end Brockian

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-! ## Basic notions

Everything below is developed from first principles (no external library is imported, so
that this file can start with the header comment above).
-/

/-- `IsPrime p` says that `p` is a prime natural number. -/
