import Mathlib

/-!
# Frobenius's theorem

For a finite group `G` and any `n`, `gcd (n, |G|)` divides the number of solutions of `xⁿ = 1`.

The proof is organised as follows.

* `sol G n` is the number of solutions of `x ^ n = 1`, `solEq n y` the number of solutions of
  `x ^ n = y`.
* `solEq_prime_pow_dvd`: if `y` has order `p ^ k` with `k ≥ 1`, then `p ^ a` divides the number
  of solutions of `x ^ (p ^ a) = y`.  (Each solution generates a cyclic group of order `p ^ (a+k)`
  containing `y`, and each such cyclic subgroup contains exactly `p ^ a` solutions.)
* Consequently `sol G (p ^ (a+1)) ≡ sol G (p ^ a) [MOD p ^ a]`, so all the numbers
  `sol G (p ^ b)` for `b ≥ a` are congruent mod `p ^ a`.
* `sol_mul_eq_sum`: writing `n = p ^ α * u` with `p ∤ u`, decomposing an element into its
  `p`-part and `p'`-part gives `sol G n = ∑_{w ^ u = 1} sol (centralizer w) (p ^ α)`.
* `pPart_dvd_sol_pPart` (the key theorem): the number of `p`-elements of `G` is divisible by the
  order of a Sylow `p`-subgroup.  This follows by induction on `|G|` from the previous identity
  applied to `n = |G|`, grouping the sum into conjugacy classes.
* Everything is then assembled.
-/

namespace Brockian.MsFrobeniusGroup

open scoped Classical
open Finset

universe u

variable {G : Type u} [Group G]

/-- The number of solutions of `x ^ n = 1` in `G`. -/

lemma sol_modEq_le [Fintype G] {p a b : ℕ} (hp : p.Prime) (hab : a ≤ b) :
    sol G (p ^ b) ≡ sol G (p ^ a) [MOD p ^ a] := by
  have step : ∀ n, sol G (p ^ (n + 1)) ≡ sol G (p ^ n) [MOD p ^ n] := fun n => sol_modEq_succ hp
  suffices h : ∀ m, a ≤ m → sol G (p ^ m) ≡ sol G (p ^ a) [MOD p ^ a] by exact h b hab
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have h2 := Nat.ModEq.of_dvd (pow_dvd_pow p hn) (step n)
    exact h2.trans ih

/-- Chinese remainder exponents used for the primary decomposition. -/
