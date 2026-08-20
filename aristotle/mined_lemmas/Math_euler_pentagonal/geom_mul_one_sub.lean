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

lemma geom_mul_one_sub {m : ℕ} (hm : m ≠ 0) :
    (1 + ∑' j : ℕ, (1 : ℤ) • (X : ℤ⟦X⟧) ^ (m * (j + 1))) * (1 - X ^ m) = 1 := by
  have hc : ∀ d : ℕ, (coeff d) (1 + ∑' j : ℕ, (1 : ℤ) • (X : ℤ⟦X⟧) ^ (m * (j + 1)))
      = if m ∣ d then 1 else 0 := by
    intro d
    rw [map_add, coeff_tsum_geom hm, coeff_one]
    by_cases hd : d = 0
    · subst hd
      simp
    · simp [hd]
  ext d
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one]
  simp only [hc]
  by_cases hd : d = 0
  · subst hd
    rw [if_pos (dvd_zero m), if_neg (by omega), if_pos rfl]
    ring
  · rw [if_neg hd]
    by_cases hdvd : m ∣ d
    · have hmd : m ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdvd
      rw [if_pos hdvd, if_pos hmd, if_pos (Nat.dvd_sub hdvd dvd_rfl)]
      ring
    · rw [if_neg hdvd]
      by_cases hle : m ≤ d
      · rw [if_pos hle, if_neg (fun hcon => hdvd (by
          have := Nat.dvd_add hcon (dvd_refl m)
          rwa [Nat.sub_add_cancel hle] at this))]
        ring
      · rw [if_neg hle]
        ring

/-- The generating function of the partition function. -/
