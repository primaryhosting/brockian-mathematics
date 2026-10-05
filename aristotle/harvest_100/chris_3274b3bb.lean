import Mathlib

/-!
# Inclusion Exclusion
Category: Pure Mathematics
Target: Math.inclusion_exclusion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

open Finset

/-- The alternating sum `∑ (-1)^(#t+1)` over the *nonempty* subsets `t` of a nonempty
finite set `T` equals `1`. -/
lemma alternating_sum_nonempty_powerset {ι : Type*} [DecidableEq ι]
    {T : Finset ι} (hT : T.Nonempty) :
    ∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ (#t + 1) = 1 := by
  have hsplit :
      (∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ #t) +
        (∑ t ∈ T.powerset with ¬ t.Nonempty, (-1 : ℤ) ^ #t) =
      ∑ t ∈ T.powerset, (-1 : ℤ) ^ #t := sum_filter_add_sum_filter_not _ _ _
  have hzero : ∑ t ∈ T.powerset, (-1 : ℤ) ^ #t = 0 :=
    sum_powerset_neg_one_pow_card_of_nonempty hT
  have hempty : (∑ t ∈ T.powerset with ¬ t.Nonempty, (-1 : ℤ) ^ #t) = 1 := by
    have : (T.powerset.filter fun t => ¬ t.Nonempty) = {(∅ : Finset ι)} := by
      ext t
      simp only [mem_filter, mem_powerset, Finset.not_nonempty_iff_eq_empty, mem_singleton]
      constructor
      · rintro ⟨-, rfl⟩
        rfl
      · rintro rfl
        exact ⟨Finset.empty_subset _, rfl⟩
    rw [this]
    simp
  have hpos : (∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ #t) = -1 := by
    linarith
  calc ∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ (#t + 1)
      = ∑ t ∈ T.powerset with t.Nonempty, -((-1 : ℤ) ^ #t) := by
        refine sum_congr rfl fun t _ => ?_
        ring
    _ = -(∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ #t) := by
        rw [sum_neg_distrib]
    _ = 1 := by rw [hpos]; ring

/-- **Inclusion–exclusion principle**.

For a finite index set `s` and finite sets `A i`, the cardinality of the union `⋃ i ∈ s, A i`
equals `∑ (-1)^(|t|+1) * |⋂ i ∈ t, A i|`, the sum ranging over the nonempty subsets `t ⊆ s`.

The intersection `⋂ i ∈ t, A i` (for `t` a nonempty subset of `s`) is expressed here as the set
of elements of the union that lie in `A i` for every `i ∈ t`. -/
theorem inclusion_exclusion {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (A : ι → Finset α) :
    (#(s.biUnion A) : ℤ) =
      ∑ t ∈ s.powerset with t.Nonempty,
        (-1 : ℤ) ^ (#t + 1) *
          #((s.biUnion A).filter fun a => ∀ i ∈ t, a ∈ A i) := by
  have hcard : ∀ t : Finset ι,
      (#((s.biUnion A).filter fun a => ∀ i ∈ t, a ∈ A i) : ℤ) =
        ∑ a ∈ s.biUnion A, if ∀ i ∈ t, a ∈ A i then (1 : ℤ) else 0 := by
    intro t
    rw [sum_ite, sum_const, sum_const]
    simp
  calc (#(s.biUnion A) : ℤ)
      = ∑ a ∈ s.biUnion A, (1 : ℤ) := by simp
    _ = ∑ a ∈ s.biUnion A,
          ∑ t ∈ s.powerset with t.Nonempty,
            (-1 : ℤ) ^ (#t + 1) * (if ∀ i ∈ t, a ∈ A i then (1 : ℤ) else 0) := by
        refine sum_congr rfl fun a ha => ?_
        classical
        set T : Finset ι := s.filter fun i => a ∈ A i with hTdef
        have hTne : T.Nonempty := by
          simp only [Finset.mem_biUnion] at ha
          obtain ⟨i, hi, hai⟩ := ha
          exact ⟨i, by simp [hTdef, hi, hai]⟩
        have hfil :
            ((s.powerset.filter fun t => t.Nonempty).filter
              fun t => ∀ i ∈ t, a ∈ A i) = T.powerset.filter fun t => t.Nonempty := by
          ext t
          simp only [mem_filter, mem_powerset, hTdef, Finset.subset_iff, Finset.mem_filter]
          constructor
          · rintro ⟨⟨hts, htne⟩, hmem⟩
            exact ⟨fun {i} hi => ⟨hts hi, hmem i hi⟩, htne⟩
          · rintro ⟨hts, htne⟩
            exact ⟨⟨fun {i} hi => (hts hi).1, htne⟩, fun i hi => (hts hi).2⟩
        symm
        calc ∑ t ∈ s.powerset with t.Nonempty,
              (-1 : ℤ) ^ (#t + 1) * (if ∀ i ∈ t, a ∈ A i then (1 : ℤ) else 0)
            = ∑ t ∈ s.powerset with t.Nonempty,
                (if ∀ i ∈ t, a ∈ A i then (-1 : ℤ) ^ (#t + 1) else 0) := by
              refine sum_congr rfl fun t _ => ?_
              split <;> ring
          _ = ∑ t ∈ (s.powerset.filter fun t => t.Nonempty).filter
                (fun t => ∀ i ∈ t, a ∈ A i), (-1 : ℤ) ^ (#t + 1) := (sum_filter _ _).symm
          _ = ∑ t ∈ T.powerset with t.Nonempty, (-1 : ℤ) ^ (#t + 1) := by rw [hfil]
          _ = 1 := alternating_sum_nonempty_powerset hTne
    _ = ∑ t ∈ s.powerset with t.Nonempty,
          ∑ a ∈ s.biUnion A,
            (-1 : ℤ) ^ (#t + 1) * (if ∀ i ∈ t, a ∈ A i then (1 : ℤ) else 0) := by
        rw [sum_comm]
    _ = ∑ t ∈ s.powerset with t.Nonempty,
          (-1 : ℤ) ^ (#t + 1) *
            #((s.biUnion A).filter fun a => ∀ i ∈ t, a ∈ A i) := by
        refine sum_congr rfl fun t _ => ?_
        rw [hcard t, mul_sum]

end Math

