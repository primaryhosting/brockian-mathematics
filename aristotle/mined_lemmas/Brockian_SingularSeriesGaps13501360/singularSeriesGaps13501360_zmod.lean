import Mathlib

/-!
# Singular Series Gaps 13501360 — `ZMod`/Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps13501360.lean`.  The target file there is stated
with elementary `Int` arithmetic (it must begin with a fixed header comment, which precludes an
`import` line); here the same mathematics is recorded in the idiomatic Mathlib language of
`Finset ℤ` and `ZMod p`.
-/

namespace Brockian

/-- A finite set of integers misses a residue class modulo `p`. -/

theorem singularSeriesGaps13501360_zmod :
    ∀ h ∈ Finset.Icc (1350 : ℤ) 1360, (AdmissibleZMod {0, h} ↔ Even h) := by
  intro h _
  refine ⟨fun hadm => ?_, admissibleZMod_pair_of_even⟩
  rcases Int.even_or_odd h with he | ho
  · exact he
  · exact absurd hadm (not_admissibleZMod_pair_of_odd ho)

end Brockian

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The usual notion of a prime natural number: `2 ≤ p` and the only divisors of `p` are `1`
and `p`. -/
