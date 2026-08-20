import Mathlib
namespace C5.BS6

def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card

theorem nu_lt_of_prime (p : ℕ) (hp : p.Prime) :
    nu ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p < p := by
  rcases lt_or_ge p 12 with h | h
  · have h2 := hp.two_le
    interval_cases p <;> simp_all (decide := true)
  · calc nu ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ) p
        ≤ ({0,2,6,8,12,18,20,26,30,32,36} : Finset ℕ).card := Finset.card_image_le
      _ = 11 := by decide
      _ < p := by omega
