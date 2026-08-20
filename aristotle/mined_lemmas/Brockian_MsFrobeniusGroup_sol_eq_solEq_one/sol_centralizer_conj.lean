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

lemma sol_centralizer_conj [Finite G] (g w : G) (n : ℕ) :
    sol ↥(Subgroup.centralizer ({g * w * g⁻¹} : Set G)) n
      = sol ↥(Subgroup.centralizer ({w} : Set G)) n := by
  -- Conjugation by `g` gives an isomorphism between the centralizers.
  let ι : Subgroup.centralizer {w} ≃* Subgroup.centralizer {g * w * g⁻¹} := by
    refine {
      toFun := fun ⟨h, hh⟩ => ⟨g * h * g⁻¹, ?_⟩
      invFun := fun ⟨h, hh⟩ => ⟨g⁻¹ * h * g, ?_⟩
      left_inv := fun ⟨h, _⟩ => ?_
      right_inv := fun ⟨h, _⟩ => ?_
      map_mul' := fun _ _ => ?_ }
    · show g * h * g⁻¹ ∈ Subgroup.centralizer {g * w * g⁻¹}
      simp [Subgroup.mem_centralizer_iff] at hh ⊢
      exact hh
    · simp [Subgroup.mem_centralizer_iff] at hh ⊢
      calc w * (g⁻¹ * h * g) = g⁻¹ * (g * w * g⁻¹) * (h * g) := by simp [mul_assoc]
        _ = g⁻¹ * ((g * w * g⁻¹) * h) * g := by simp [mul_assoc]
        _ = g⁻¹ * (h * (g * w * g⁻¹)) * g := by rw [hh]
        _ = (g⁻¹ * h * g) * w := by simp [mul_assoc]
    · simp [mul_assoc]
    · simp [mul_assoc]
    · simp [mul_assoc]
  exact sol_congr ι.symm n

/-- In a commutative group, if `p` does not divide `m` then `p` does not divide the number of
solutions of `x ^ m = 1`. -/
