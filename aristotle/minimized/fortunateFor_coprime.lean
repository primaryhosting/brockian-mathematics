import Mathlib

def FortunateFor (P m : ℕ) : Prop :=
  1 < m ∧ (P + m).Prime ∧ ∀ k : ℕ, 1 < k → k < m → ¬ (P + k).Prime

theorem fortunateFor_coprime {P m : ℕ} (hP : 0 < P) (h : FortunateFor P m) :
    Nat.Coprime m P := by
  obtain ⟨hm, hp, -⟩ := h
  have hd : Nat.gcd m P ∣ P + m :=
    Nat.dvd_add (Nat.gcd_dvd_right m P) (Nat.gcd_dvd_left m P)
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h2
  · exact h1
  · have hle : Nat.gcd m P ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left m P)
    omega
