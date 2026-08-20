import Mathlib
namespace Brockian.MsVanDerWaerden

open Combinatorics Finset

/-- The set of "moving" coordinates of a combinatorial line. -/

private lemma sum_coords_le {k : ℕ} {ι : Type} [Fintype ι] (v : ι → Fin k) :
    ∑ i, ((v i : ℕ)) ≤ Fintype.card ι * k := by
  calc ∑ i, ((v i : ℕ)) ≤ ∑ _i : ι, k := by
         apply Finset.sum_le_sum
         intro i _
         exact Nat.le_of_lt (Fin.is_lt (v i))
       _ = Fintype.card ι * k := by simp

/-- Van der Waerden's theorem: for any k and any r-coloring of the naturals, some monochromatic
    arithmetic progression of length k exists within a bounded window.

    (The hypotheses `0 < k` and `0 < r` are kept as stated, although the proof does not
    need them.) -/
