import Mathlib
namespace Brockian.TwoSquaresUnique

/-- If `p` is prime and `p = a^2 + b^2`, then `a > 0`. -/

private lemma coprime_of_prime_sq_add_sq {p a b : ℕ} (hp : p.Prime) (h : p = a ^ 2 + b ^ 2) :
    Nat.Coprime a b := by
  by_contra hng
  set g := Nat.gcd a b with hgdef
  have ha_pos : 0 < a := pos_of_prime_sq_add_sq hp h
  have hg_pos : 0 < g := Nat.pos_of_ne_zero (fun hz => by
    have := Nat.eq_zero_of_gcd_eq_zero_left (hgdef ▸ hz)
    omega)
  have hg_gt_one : 1 < g :=
    Nat.lt_of_le_of_ne hg_pos (Ne.symm (fun hg1 => hng (by rw [hgdef] at hg1; exact hg1)))
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have hg2 : g ^ 2 ∣ p := by
    rw [h]
    exact Nat.dvd_add (pow_dvd_pow_of_dvd hga 2) (pow_dvd_pow_of_dvd hgb 2)
  have hg2_eq : g ^ 2 = p :=
    (hp.eq_one_or_self_of_dvd (g ^ 2) hg2).resolve_left (by nlinarith)
  rw [← hg2_eq] at hp
  have hdvd : g ∣ g ^ 2 := ⟨g, by ring⟩
  rcases hp.eq_one_or_self_of_dvd g hdvd with h1 | h2
  · linarith
  · nlinarith

/-- If `P^2 = X^2 + Y^2` and `P ∣ Y`, then `Y = 0` or `X = 0`. -/
