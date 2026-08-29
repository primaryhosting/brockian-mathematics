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


theorem isPrimeSmall_correct {n : Nat} (hn : n ≤ 2102) (h : isPrimeSmall n = true) :
    IsPrime n := by
  rw [isPrimeSmall, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hall⟩ := h
  have key : ∀ d : Nat, 2 ≤ d → d ≤ 45 → d ∣ n → d = n := by
    intro d hd2 hd45 hdvd
    have hmem : d ∈ List.range' 2 44 := List.mem_range'.mpr ⟨d - 2, by omega, by omega⟩
    have hc := List.all_eq_true.mp hall d hmem
    simp only [bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true] at hc
    obtain ⟨k, hk⟩ := hdvd
    have hmod : n % d = 0 := by rw [hk]; exact Nat.mul_mod_right d k
    rcases hc with hc | hc
    · exact absurd hmod hc
    · omega
  refine ⟨h2, fun m hm => ?_⟩
  obtain ⟨e, he⟩ := hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at he; omega
  have he0 : e ≠ 0 := by rintro rfl; simp at he; omega
  rcases Nat.lt_or_ge m 2 with hlt | hm2
  · exact Or.inl (by omega)
  refine Or.inr ?_
  rcases Nat.lt_or_ge m 46 with hs | hbig
  · exact key m hm2 (by omega) ⟨e, he⟩
  · rcases Nat.lt_or_ge e 2 with he1 | he2
    · have hE : e = 1 := by omega
      subst hE
      omega
    · rcases Nat.lt_or_ge e 46 with hle45 | hbg
      · have hen : e = n := key e he2 (by omega) ⟨m, by rw [he]; exact Nat.mul_comm m e⟩
        subst hen
        have : 2 * e ≤ m * e := Nat.mul_le_mul_right e hm2
        omega
      · have h1 : 46 * 46 ≤ m * e := Nat.mul_le_mul hbig hbg
        rw [← he] at h1
        omega

/-- A successful search yields an honest Goldbach decomposition. -/
