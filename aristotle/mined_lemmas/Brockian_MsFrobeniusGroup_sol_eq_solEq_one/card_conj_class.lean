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

lemma card_conj_class [Fintype G] (w : G) :
    (univ.filter (fun x : G => IsConj w x)).card = (Subgroup.centralizer ({w} : Set G)).index := by
  have h : (univ.filter (fun x : G => IsConj w x)) = {g * w * g⁻¹ | g : G} := by
    ext x
    simp [IsConj, SemiconjBy]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      calc (c : G) * w * (c : G)⁻¹ = (x * c) * (c : G)⁻¹ := by rw [hc]
        _ = x * (c * (c : G)⁻¹) := by group
        _ = x := by simp
    · rintro ⟨g, hg⟩
      use ⟨g, g⁻¹, by simp, by simp⟩
      simp [← hg]
  simp
  rw [Subgroup.index_eq_card]
  simp_rw [Nat.card_eq_fintype_card]
  have hequiv : (image (fun x => x * w * x⁻¹) univ) ≃ (G ⧸ Subgroup.centralizer {w}) := by
    -- Define the function from G to the conjugacy class
    let f : G → ↥(image (fun x => x * w * x⁻¹) univ) := fun g => ⟨g * w * g⁻¹, Finset.mem_image_of_mem _ (Finset.mem_univ g)⟩
    -- Show that f respects the quotient relation
    have hf : ∀ g1 g2 : G, g1⁻¹ * g2 ∈ Subgroup.centralizer {w} → f g1 = f g2 := by
      intro g1 g2 hg2
      simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff] at hg2
      simp [f]
      have hg2w : (g1⁻¹ * g2) * w = w * (g1⁻¹ * g2) := (hg2 w rfl).symm
      have : g1 * w * g1⁻¹ = g2 * w * g2⁻¹ := by
        calc g1 * w * g1⁻¹ = g1 * w * g1⁻¹ * (g1⁻¹ * g2) * (g1⁻¹ * g2)⁻¹ := by group
          _ = g1 * (w * (g1⁻¹ * g2)) * (g1⁻¹ * g2)⁻¹ * g1⁻¹ := by group
          _ = g1 * ((g1⁻¹ * g2) * w) * (g1⁻¹ * g2)⁻¹ * g1⁻¹ := by rw [hg2w]
          _ = g2 * w * g2⁻¹ := by group
      simp [this]
    -- Lift f to a map from the quotient using Quotient.lift
    let g : G ⧸ Subgroup.centralizer {w} → ↥(image (fun x => x * w * x⁻¹) univ) :=
      Quotient.lift f (fun g1 g2 hg => by
        have : g1⁻¹ * g2 ∈ Subgroup.centralizer {w} := by
          exact QuotientGroup.leftRel_apply.mp hg
        exact hf g1 g2 this)
    have hg_inj : Function.Injective g := by
      intro q1 q2 heq
      obtain ⟨g1, rfl⟩ := Quotient.exists_rep q1
      obtain ⟨g2, rfl⟩ := Quotient.exists_rep q2
      -- heq : g ⟦g1⟧ = g ⟦g2⟧ where g = Quotient.lift f hf
      have heq' : g1 * w * g1⁻¹ = g2 * w * g2⁻¹ := by
        exact congrArg Subtype.val heq
      have hmem : g1⁻¹ * g2 ∈ Subgroup.centralizer {w} := by
        have hg2w : (g1⁻¹ * g2) * w = w * (g1⁻¹ * g2) := by
          calc (g1⁻¹ * g2) * w = g1⁻¹ * (g2 * w) := by group
            _ = g1⁻¹ * (g2 * w * g2⁻¹ * g2) := by group
            _ = g1⁻¹ * (g1 * w * g1⁻¹ * g2) := by rw [heq']
            _ = w * (g1⁻¹ * g2) := by group
        simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff]
        intro h hh
        rw [hh]
        exact hg2w.symm
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr hmem)
    have hg_surj : Function.Surjective g := by
      intro ⟨x, hx⟩
      obtain ⟨g0, hg0⟩ := Finset.mem_image.mp hx
      refine ⟨Quotient.mk'' g0, ?_⟩
      change (Quotient.lift f _ (Quotient.mk'' g0)) = ⟨x, hx⟩
      rw [Quotient.lift_mk]
      exact Subtype.ext hg0.2
    exact (Equiv.ofBijective g ⟨hg_inj, hg_surj⟩).symm
  rw [← Fintype.card_coe]
  exact Fintype.card_congr hequiv

/-- Grouping a conjugation invariant sum into conjugacy classes. -/
