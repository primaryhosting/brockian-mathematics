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

lemma solEq_prime_pow_dvd [Finite G] {p a k : ℕ} (hp : p.Prime) {y : G}
    (hk : 0 < k) (hy : orderOf y = p ^ k) : p ^ a ∣ solEq (p ^ a) y := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : DecidableEq (Subgroup G) := inferInstance
  rw [solEq_eq_card_filter]
  let S := univ.filter (fun x : G => x ^ (p ^ a) = y)
  -- For x ∈ S, we have x ^ (p^a) = y, so by orderOf_of_pow_eq, orderOf x = p^(a+k)
  have hx_order : ∀ x ∈ S, orderOf x = p ^ (a + k) := by
    intro x hx
    simp [S] at hx
    exact orderOf_of_pow_eq hp hk hy hx
  -- Partition S by zpowers
  let f : G → Subgroup G := fun x => Subgroup.zpowers x
  have h_card := Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := S.image f)
  have h_maps : Set.MapsTo f ↑S ↑(S.image f) := by
    intro x hx
    exact Finset.mem_image_of_mem f hx
  rw [h_card h_maps]
  apply Finset.dvd_sum
  intro C hC
  rw [Finset.mem_image] at hC
  obtain ⟨x₀, hx₀S, rfl⟩ := hC
  have hx₀S' : x₀ ^ (p ^ a) = y := by simpa [S] using hx₀S
  have h_card_fiber := card_fiber_zpowers (p := p) (a := a) (k := k) hp hk hy hx₀S'
  simp [S] at hx₀S
  have h_eq : {a ∈ S | f a = f x₀} = (univ.filter (fun x : G => x ^ (p ^ a) = y ∧ Subgroup.zpowers x = Subgroup.zpowers x₀)) := by
    simp [S, f, Finset.filter_filter]
  rw [h_eq]
  convert h_card_fiber.symm.dvd using 1
  congr 1
  ext x
  simp

/-- Fibering the solutions of `x ^ (a * b) = 1` over the `a`-th power map. -/
