/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma sum_Icc_int_split (n : ℕ) (f : ℤ → ℤ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f k
      = f 0 + ((∑ c ∈ Finset.Icc 1 n, f (c : ℤ)) + ∑ c ∈ Finset.Icc 1 n, f (-(c : ℤ))) := by
  have hpos : Set.InjOn (fun c : ℕ => (c : ℤ)) ↑(Finset.Icc 1 n) := by
    intro a _ b _ hab
    exact Nat.cast_injective (by simpa using hab)
  have hneg : Set.InjOn (fun c : ℕ => -(c : ℤ)) ↑(Finset.Icc 1 n) := by
    intro a _ b _ hab
    have : (a : ℤ) = (b : ℤ) := by simpa using neg_injective hab
    exact_mod_cast this
  have hdisj : Disjoint ((Finset.Icc 1 n).image (fun c : ℕ => (c : ℤ)))
      ((Finset.Icc 1 n).image (fun c : ℕ => -(c : ℤ))) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_image, Finset.mem_Icc] at hk1 hk2
    obtain ⟨a, ⟨ha1, _⟩, rfl⟩ := hk1
    obtain ⟨b, ⟨hb1, _⟩, hb⟩ := hk2
    omega
  have h0 : (0 : ℤ) ∉ ((Finset.Icc 1 n).image (fun c : ℕ => (c : ℤ))) ∪
      ((Finset.Icc 1 n).image (fun c : ℕ => -(c : ℤ))) := by
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, not_or]
    constructor <;> rintro ⟨c, ⟨hc1, _⟩, hc⟩ <;> omega
  have hset : Finset.Icc (-(n : ℤ)) (n : ℤ) = insert 0
      (((Finset.Icc 1 n).image (fun c : ℕ => (c : ℤ))) ∪
        ((Finset.Icc 1 n).image (fun c : ℕ => -(c : ℤ)))) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro hk
      rcases lt_trichotomy k 0 with h | h | h
      · exact Or.inr (Or.inr ⟨(-k).toNat, ⟨by omega, by omega⟩, by omega⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k.toNat, ⟨by omega, by omega⟩, by omega⟩)
    · rintro (rfl | ⟨c, ⟨hc1, hc2⟩, rfl⟩ | ⟨c, ⟨hc1, hc2⟩, rfl⟩) <;> omega
  rw [hset, Finset.sum_insert h0, Finset.sum_union hdisj, Finset.sum_image hpos,
    Finset.sum_image hneg]

/-- **Euler's pentagonal number theorem**.

For every `n ≤ N`, the coefficient of `X ^ n` in the partition generating function
`∏_{k=1}^{N} (1 - X ^ k)` (which is the coefficient of `X ^ n` in the infinite product
`∏_{k ≥ 1} (1 - X ^ k)`, since larger factors do not contribute to this coefficient) equals
`∑_{k ∈ ℤ} (-1) ^ k` over the integers `k` with `k (3k - 1) / 2 = n`, i.e. it is `(-1) ^ k` if
`n` is the generalized pentagonal number `k (3k - 1) / 2` and `0` otherwise. -/
