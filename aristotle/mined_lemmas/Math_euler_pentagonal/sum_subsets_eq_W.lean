import Mathlib

/-!
# Franklin's involution

Combinatorial core of Euler's pentagonal number theorem: the signed count of partitions of
`n` into distinct parts (sign `(-1)^(number of parts)`) is `0` unless `n` is a generalized
pentagonal number.

Partitions into distinct parts are encoded as finite sets of positive naturals.
-/

namespace EulerPentagonal

open Finset

/-- The largest element of `s` (junk value `0` for `s = ∅`). -/

lemma sum_subsets_eq_W (d : ℕ) (t : Finset ℕ) (ht : Finset.range d ⊆ t) :
    ∑ u ∈ t.powerset.filter (fun u => ∑ i ∈ u, (i + 1) = d), (-1 : ℤ) ^ u.card = W d := by
  have hpos : ∀ s : Finset ℕ, s ∈ DP d → ∀ x ∈ s, 1 ≤ x := by
    intro s hs x hx
    have h0 := (mem_DP.mp hs).1
    rcases Nat.eq_zero_or_pos x with rfl | h
    · exact absurd hx h0
    · exact h
  rw [W]
  refine Finset.sum_nbij' (fun u => u.image (· + 1)) (fun s => s.image (· - 1)) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter, Finset.mem_powerset] at hu
    refine mem_DP.mpr ⟨by simp, ?_⟩
    rw [Finset.sum_image (fun x _ y _ h => by omega)]
    exact hu.2
  · intro s hs
    obtain ⟨h0, hsum⟩ := mem_DP.mp hs
    have hp := hpos s hs
    have hle : ∀ x ∈ s, x ≤ d := by
      intro x hx
      have h1 : x ≤ ∑ i ∈ s, i := by
        simpa using Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
      omega
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ht (Finset.mem_range.mpr (by have := hp x hx; have := hle x hx; omega))
    · rw [Finset.sum_image (fun x hx y hy h => by
        have := hp x (Finset.mem_coe.mp hx); have := hp y (Finset.mem_coe.mp hy); omega)]
      rw [← hsum]
      exact Finset.sum_congr rfl (fun x hx => by have := hp x hx; omega)
  · intro u _
    show Finset.image (fun x => x - 1) (Finset.image (fun x => x + 1) u) = u
    rw [Finset.image_image]
    simp only [Function.comp_def, Nat.add_sub_cancel, Finset.image_id']
  · intro s hs
    have hp := hpos s hs
    show Finset.image (fun x => x + 1) (Finset.image (fun x => x - 1) s) = s
    rw [Finset.image_image]
    ext y
    simp only [Finset.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hp x hx
      rwa [show x - 1 + 1 = x by omega]
    · intro hy
      exact ⟨y, hy, by have := hp y hy; omega⟩
  · intro u _
    rw [Finset.card_image_of_injective _ (fun x y h => by omega)]

/-- The infinite product `∏_{i≥1} (1 - X^i)` is the generating function of the signed count of
partitions into distinct parts. -/
