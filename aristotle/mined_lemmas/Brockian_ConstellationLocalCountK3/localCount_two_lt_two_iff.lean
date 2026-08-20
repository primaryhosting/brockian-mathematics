import Mathlib

/-!
# Local constellation counts for `k`-tuples

For a tuple `H : Fin k → ℤ` (a candidate *prime constellation* / admissible tuple)
and a prime `p`, the **local count** `localCount p H` is the number of distinct
residue classes modulo `p` occupied by the entries of `H`.  The tuple is
**admissible** when `localCount p H < p` for every prime `p`, i.e. no prime
completely covered by the tuple obstructs the tuple from being a prime
constellation infinitely often.

The main results here reduce admissibility to a finite check:

* `Brockian.ConstellationLocalCountK2` : for `k = 2` admissibility is exactly the
  condition at `p = 2`;
* `Brockian.ConstellationLocalCountK3` : for `k = 3` admissibility is exactly the
  conjunction of the conditions at `p = 2` and `p = 3`.
-/

namespace Brockian

open Finset

/-- The number of distinct residue classes modulo `p` occupied by the entries of
the tuple `H`. -/

theorem localCount_two_lt_two_iff (H : Fin 3 → ℤ) :
    localCount 2 H < 2 ↔ ∀ i j, ((H i : ZMod 2)) = ((H j : ZMod 2)) := by
  constructor
  · intro h i j
    by_contra hne
    have hsub : ({(H i : ZMod 2), (H j : ZMod 2)} : Finset (ZMod 2)) ⊆
        Finset.image (fun i => ((H i : ZMod 2))) Finset.univ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton] at hcard
    rw [localCount] at h
    omega
  · intro h
    have : Finset.image (fun i => ((H i : ZMod 2))) Finset.univ
        = {((H 0 : ZMod 2))} := by
      apply Finset.eq_singleton_iff_unique_mem.2
      refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ 0), ?_⟩
      rintro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact h i 0
    simp [localCount, this]

/-- The triple `(0, 2, 6)` is admissible. -/
