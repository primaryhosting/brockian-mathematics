import Mathlib

/-!
# Euler's pentagonal number theorem (recurrence form)

The main result `euler_pentagonal` states that for `n > 0`,
`∑ k (-1)^k p(n - g k) = 0` where `g k = k (3k-1)/2` runs over the generalized pentagonal
numbers and `p` is the partition function.

The proof has three parts.

* Part A (generating functions): using Mathlib's machinery for partition generating functions,
  `(∑ p(n) Xⁿ) * (∑ E(n) Xⁿ) = 1`, where `E(n)` is the signed count of partitions of `n` into
  distinct parts, the sign being the parity of the number of parts.
* Part B (Franklin's involution): `E(n) = (-1)^k` if `2n = k(3k-1)` for some integer `k`, and
  `E(n) = 0` otherwise.
* Part C: assembling the two.
-/

namespace Brockian.MsEulerPentagonal

open Finset

noncomputable section PartA

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- The partition function. -/

theorem Edist_eq_Efin (n : ℕ) : Edist n = Efin n := by
  simp only [Edist, Efin]
  refine Finset.sum_bij (fun p hp => p.parts.toFinset) ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_DP]
    have hp' := List.mem_filter.mp hp
    have hnodup := hp'.2
    constructor
    · intro h0
      have := Multiset.mem_toFinset.mp h0
      have h0' : (0 : ℕ) ∈ p.parts := Multiset.mem_toFinset.mp h0
      have := p.2 h0'
      contradiction
    · have hnodup' : p.parts.Nodup := by simpa using hp'.2
      simp [Multiset.toFinset]
      have : p.parts.sum = n := Nat.Partition.parts_sum p
      rw [Multiset.dedup_eq_self.mpr hnodup', this]
  · -- Injectivity
    intro a₁ ha₁ a₂ ha₂ h
    have ha₁' := List.mem_filter.mp ha₁
    have ha₂' := List.mem_filter.mp ha₂
    have hnodup₁ : a₁.parts.Nodup := by simpa using ha₁'.2
    have hnodup₂ : a₂.parts.Nodup := by simpa using ha₂'.2
    have h' : a₁.parts.dedup = a₂.parts.dedup := by simpa [Multiset.toFinset] using h
    have heq : a₁.parts = a₂.parts := by
      rwa [Multiset.dedup_eq_self.mpr hnodup₁, Multiset.dedup_eq_self.mpr hnodup₂] at h'
    exact Nat.Partition.ext heq

  · -- Surjectivity
    intro b hb
    rw [mem_DP] at hb
    have hpos : ∀ x ∈ b, 0 < x := fun x hx => Nat.pos_of_ne_zero (fun h0 => hb.1 (h0 ▸ hx))
    have sum_eq := hb.2
    -- Construct a partition from the finset b
    have sum_eq' : b.val.sum = n := by simp [sum_eq]
    let p : Nat.Partition n := ⟨b.val, (@fun x hx => hpos x (by simpa using hx)), sum_eq'⟩
    use p
    refine ⟨?_, ?_⟩
    · -- p ∈ Nat.Partition.distincts n
      apply Finset.mem_filter.mpr
      refine ⟨by simp, ?_⟩
      exact b.nodup
    · -- p.parts.toFinset = b
      simp [Multiset.toFinset]
      congr 1
      exact Multiset.dedup_eq_self.mpr b.nodup

  · -- Cardinality
    intro a ha
    have ha' := List.mem_filter.mp ha
    have hnodup : a.parts.Nodup := by simpa using ha'.2
    simp only [Multiset.toFinset]
    have : a.parts.dedup = a.parts := Multiset.dedup_eq_self.mpr hnodup
    simp [this]

/-- The largest part (`0` for the empty partition). -/
