/-
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any doc comment `/-!`, so the header above is a
-- plain block comment; the identical text is repeated as the module docstring below.)

import Mathlib

/-!
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- The intersection `⋂_{i ∈ t} A i`, realised as a `Finset` by carving it out of the
ambient finite set `U`.  For a nonempty `t` with all `A i ⊆ U` this is the genuine
intersection (see `Math.iInterOn_eq_inf'`). -/

lemma alternating_sum_nonempty_powerset {T : Finset ι} (hT : T.Nonempty) :
    ∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ (t.card + 1) = 1 := by
  have h0 : ∑ t ∈ T.powerset, (-1 : ℤ) ^ t.card = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hT
  have hsplit :
      ∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ t.card
        + ∑ t ∈ T.powerset with ¬ t.Nonempty, (-1 : ℤ) ^ t.card
        = ∑ t ∈ T.powerset, (-1 : ℤ) ^ t.card :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hempty : ∑ t ∈ T.powerset with ¬ t.Nonempty, (-1 : ℤ) ^ t.card = 1 := by
    simp [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq']
  have hne : ∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ t.card = -1 := by
    rw [h0, hempty] at hsplit; linarith
  calc ∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ (t.card + 1)
      = - ∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ t.card := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun t _ => by ring
    _ = 1 := by rw [hne]; ring

/-- **Inclusion–exclusion principle.**
The cardinality of a finite union `⋃_{i ∈ s} A i` equals the alternating sum
`∑_{∅ ≠ t ⊆ s} (-1)^(|t|+1) |⋂_{i ∈ t} A i|`. -/
