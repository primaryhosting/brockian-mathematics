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

lemma isExc_excSet (k : ℤ) : IsExc (excSet k) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hj : 1 ≤ k.natAbs := by omega
    rw [excSet, if_neg (by omega), if_pos hk]
    set j := k.natAbs with hjdef
    have hmn : mn (Finset.Icc (j + 1) (2 * j)) = j + 1 := mn_Icc (by omega)
    have hmx : mx (Finset.Icc (j + 1) (2 * j)) = 2 * j := mx_Icc (by omega)
    have hsl : sl (Finset.Icc (j + 1) (2 * j)) = j := by
      refine sl_eq ?_ ?_
      · rw [hmx]; simp only [Finset.mem_Icc, not_and, not_le]; intro h; omega
      · intro i hi
        rw [hmx]
        simp only [Finset.mem_Icc]
        omega
    rw [IsExc, if_neg (by rw [hmn, hsl]; omega), hmx, hsl]
  · subst hk
    simpa only [excSet, lt_irrefl, if_false] using isExc_empty
  · have hj : 1 ≤ k.natAbs := by omega
    rw [excSet, if_pos hk]
    set j := k.natAbs with hjdef
    have hmn : mn (Finset.Icc j (2 * j - 1)) = j := mn_Icc (by omega)
    have hmx : mx (Finset.Icc j (2 * j - 1)) = 2 * j - 1 := mx_Icc (by omega)
    have hsl : sl (Finset.Icc j (2 * j - 1)) = j := by
      refine sl_eq ?_ ?_
      · rw [hmx]; simp only [Finset.mem_Icc, not_and, not_le]; intro h; omega
      · intro i hi
        rw [hmx]
        simp only [Finset.mem_Icc]
        omega
    rw [IsExc, if_pos (by rw [hmn, hsl]), hmx, hmn]

/-! ### The signed count of partitions into distinct parts -/

noncomputable instance : DecidablePred IsExc := fun s => by unfold IsExc; infer_instance

