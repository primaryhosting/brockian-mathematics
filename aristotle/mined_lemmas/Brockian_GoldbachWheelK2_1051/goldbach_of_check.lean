import Mathlib
import RequestProject.GoldbachWheelK2_1051

/-!
# Bridge: the import-free primality predicate agrees with `Nat.Prime`

`RequestProject/GoldbachWheelK2_1051.lean` is import-free (so that the required header comment
is the first thing in the file) and therefore uses its own definition `Brockian.IsPrime`.
Here we check that this predicate is literally `Nat.Prime`, and restate the main theorem
in Mathlib's vocabulary.
-/

namespace Brockian


theorem goldbach_of_check {n : Nat} (hn : 2 ≤ n) (hle : n ≤ 1051) (h : goldbachCheck n = true) :
    ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = 2 * n := by
  rw [goldbachCheck, List.any_eq_true] at h
  obtain ⟨p, hp, hpc⟩ := h
  rw [Bool.and_eq_true] at hpc
  have hp200 : p ≤ 200 := by
    rw [List.mem_range'] at hp
    omega
  have hP : IsPrime p := isPrimeSmall_correct (by omega) hpc.1
  have hQ : IsPrime (2 * n - p) := isPrimeSmall_correct (by omega) hpc.2
  have hq2 : 2 ≤ 2 * n - p := hQ.1
  exact ⟨p, 2 * n - p, hP, hQ, by omega⟩

