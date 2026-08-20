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

theorem sum_exc_eq (n : ℕ) :
    ∑ s ∈ (DP n).filter IsExc, (-1 : ℤ) ^ s.card
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), if pentN k = n then (-1 : ℤ) ^ k.natAbs else 0 := by
  have hset : (DP n).filter IsExc
      = ((Finset.Icc (-(n : ℤ)) (n : ℤ)).filter (fun k => pentN k = n)).image excSet := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨hs, hexc⟩
      obtain ⟨h0, hsum⟩ := mem_DP.mp hs
      obtain ⟨k, rfl⟩ := exc_classification h0 hexc
      have hpk : pentN k = n := by rw [← sum_excSet k, hsum]
      have hb := pentN_le k
      rw [hpk] at hb
      exact ⟨k, ⟨⟨by omega, by omega⟩, hpk⟩, rfl⟩
    · rintro ⟨k, ⟨-, hpk⟩, rfl⟩
      exact ⟨mem_DP.mpr ⟨zero_notMem_excSet k, by rw [sum_excSet k, hpk]⟩, isExc_excSet k⟩
  rw [hset, Finset.sum_image ?inj, Finset.sum_filter]
  case inj =>
    intro x hx y hy _
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact pentN_injective (by rw [hx.2, hy.2])
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [card_excSet]

