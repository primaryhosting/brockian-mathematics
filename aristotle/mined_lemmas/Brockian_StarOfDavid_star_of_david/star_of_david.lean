import Mathlib
namespace Brockian.StarOfDavid

/-- `(a+b).choose a * a! * b! = (a+b)!`. -/

theorem star_of_david (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Nat.gcd (Nat.gcd (Nat.choose (n - 1) (k - 1)) (Nat.choose n (k + 1))) (Nat.choose (n + 1) k)
      = Nat.gcd (Nat.gcd (Nat.choose (n - 1) k) (Nat.choose n (k - 1))) (Nat.choose (n + 1) (k + 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases eq_or_lt_of_le hkn with heq | hlt
  · subst heq
    simp [Nat.choose_succ_self]
  · obtain ⟨r, rfl⟩ : ∃ r, n = j + r + 2 := ⟨n - j - 2, by omega⟩
    have e1 : j + r + 2 - 1 = j + r + 1 := by omega
    have e2 : j + 1 - 1 = j := by omega
    have e3 : j + r + 2 + 1 = j + r + 3 := by omega
    rw [e1, e2, e3]
    show Nat.gcd (Nat.gcd ((j + r + 1).choose j) ((j + r + 2).choose (j + 2)))
        ((j + r + 3).choose (j + 1))
      = Nat.gcd (Nat.gcd ((j + r + 1).choose (j + 1)) ((j + r + 2).choose j))
        ((j + r + 3).choose (j + 2))
    -- Pascal relations
    have hZ : (j + r + 2).choose (j + 1) = (j + r + 1).choose j + (j + r + 1).choose (j + 1) :=
      Nat.choose_succ_succ (j + r + 1) j
    have hC' : (j + r + 3).choose (j + 2)
        = (j + r + 1).choose j + (j + r + 1).choose (j + 1) + (j + r + 2).choose (j + 2) := by
      rw [← hZ]; exact Nat.choose_succ_succ (j + r + 2) (j + 1)
    have hCC : (j + r + 3).choose (j + 1)
        = (j + r + 2).choose j + (j + r + 1).choose j + (j + r + 1).choose (j + 1) := by
      have h : (j + r + 3).choose (j + 1) = (j + r + 2).choose j + (j + r + 2).choose (j + 1) :=
        Nat.choose_succ_succ (j + r + 2) j
      omega
    exact star_abstract (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne'
      (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne'
      (Nat.choose_pos (by omega)).ne' (Nat.choose_pos (by omega)).ne'
      (choose_prod_identity j r) hC' hCC

end Brockian.StarOfDavid

