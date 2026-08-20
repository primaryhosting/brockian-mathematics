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

lemma coeff_tsum_geom {m : ℕ} (hm : m ≠ 0) (d : ℕ) :
    (coeff d) (∑' j : ℕ, (1 : ℤ) • (X : ℤ⟦X⟧) ^ (m * (j + 1)))
      = if (m ∣ d ∧ d ≠ 0) then 1 else 0 := by
  have hs := Nat.Partition.summable_genFun_term' (R := ℤ) (fun _ _ => (1 : ℤ)) hm
  rw [hs.map_tsum _ (WithPiTopology.continuous_coeff ℤ d)]
  have hterm : ∀ j : ℕ, (coeff d) ((1 : ℤ) • (X : ℤ⟦X⟧) ^ (m * (j + 1)))
      = if d = m * (j + 1) then (1 : ℤ) else 0 := by
    intro j
    rw [coeff_smul, coeff_X_pow]
    simp
  simp_rw [hterm]
  by_cases h : m ∣ d ∧ d ≠ 0
  · obtain ⟨c, hc⟩ := h.1
    have hc0 : c ≠ 0 := by rintro rfl; exact h.2 (by omega)
    rw [if_pos h, tsum_eq_single (c - 1) ?_]
    · rw [if_pos (by rw [show c - 1 + 1 = c from by omega]; exact hc)]
    · intro b hb
      rw [if_neg (by
        intro hcon
        apply hb
        have h2 : m * c = m * (b + 1) := by omega
        have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h2
        omega)]
  · rw [if_neg h]
    have hz : ∀ j : ℕ, (if d = m * (j + 1) then (1 : ℤ) else 0) = 0 := by
      intro j
      rw [if_neg]
      rintro rfl
      exact h ⟨⟨j + 1, rfl⟩, Nat.mul_ne_zero hm (by omega)⟩
    simp_rw [hz]
    exact tsum_zero

/-- The `m`-th factor of the partition generating function is inverse to `1 - X^m`. -/
