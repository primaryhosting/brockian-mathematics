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
def iInterOn (U : Finset α) (t : Finset ι) (A : ι → Finset α) : Finset α :=
  U.filter fun x => ∀ i ∈ t, x ∈ A i

omit [DecidableEq ι] in
lemma mem_iInterOn {U : Finset α} {t : Finset ι} {A : ι → Finset α} {x : α} :
    x ∈ iInterOn U t A ↔ x ∈ U ∧ ∀ i ∈ t, x ∈ A i := by
  simp [iInterOn]

omit [DecidableEq ι] in
/-- For a nonempty `t ⊆ s`, the set `iInterOn (s.biUnion A) t A` really is the
intersection `⋂_{i ∈ t} A i` (as computed by `Finset.inf'`). -/
lemma iInterOn_eq_inf' {s : Finset ι} {t : Finset ι} (hts : t ⊆ s) (ht : t.Nonempty)
    (A : ι → Finset α) : iInterOn (s.biUnion A) t A = t.inf' ht A := by
  ext x
  simp only [mem_iInterOn, Finset.mem_inf', Finset.mem_biUnion]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨i, hi⟩ := ht
  exact ⟨i, hts hi, h i hi⟩

/-- Auxiliary alternating sum: for a nonempty finset `T`, the alternating sum
`∑_{∅ ≠ t ⊆ T} (-1)^(|t|+1)` equals `1`. -/
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
theorem inclusion_exclusion (s : Finset ι) (A : ι → Finset α) :
    ((s.biUnion A).card : ℤ) =
      ∑ t ∈ s.powerset with t.Nonempty,
        (-1 : ℤ) ^ (t.card + 1) * ((iInterOn (s.biUnion A) t A).card : ℤ) := by
  classical
  set U := s.biUnion A with hU
  -- Expand each cardinality as a sum of indicators over `U` and swap the two sums.
  have hcard : ∀ t : Finset ι, ((iInterOn U t A).card : ℤ)
      = ∑ x ∈ U, if (∀ i ∈ t, x ∈ A i) then (1 : ℤ) else 0 := by
    intro t
    rw [iInterOn, Finset.card_filter]
    push_cast
    rfl
  have hswap :
      ∑ t ∈ s.powerset with t.Nonempty,
        (-1 : ℤ) ^ (t.card + 1) * ((iInterOn U t A).card : ℤ)
        = ∑ x ∈ U, ∑ t ∈ s.powerset with t.Nonempty,
            (if (∀ i ∈ t, x ∈ A i) then (-1 : ℤ) ^ (t.card + 1) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hcard t, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by split <;> ring
  rw [hswap]
  -- The inner sum is `1` for every `x` in the union.
  have hinner : ∀ x ∈ U, (∑ t ∈ s.powerset with t.Nonempty,
      (if (∀ i ∈ t, x ∈ A i) then (-1 : ℤ) ^ (t.card + 1) else 0)) = 1 := by
    intro x hx
    set T := s.filter fun i => x ∈ A i with hT
    have hTne : T.Nonempty := by
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 (hU ▸ hx)
      exact ⟨i, by simp [hT, hi, hxi]⟩
    have hfilter :
        ((s.powerset.filter fun t => t.Nonempty).filter fun t => ∀ i ∈ t, x ∈ A i)
          = T.powerset.filter fun t => t.Nonempty := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_powerset, hT]
      constructor
      · rintro ⟨⟨hts, hne⟩, hmem⟩
        exact ⟨fun i hi => Finset.mem_filter.2 ⟨hts hi, hmem i hi⟩, hne⟩
      · rintro ⟨hsub, hne⟩
        refine ⟨⟨fun i hi => (Finset.mem_filter.1 (hsub hi)).1, hne⟩,
          fun i hi => (Finset.mem_filter.1 (hsub hi)).2⟩
    rw [← Finset.sum_filter, hfilter]
    exact alternating_sum_nonempty_powerset hTne
  rw [Finset.sum_congr rfl hinner]
  simp

end Math

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

