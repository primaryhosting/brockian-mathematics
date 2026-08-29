import RequestProject.CapExpand

/-!
# The Ellenberg–Gijswijt bound

Combining the slice-rank bound with the polynomial expansion gives
`|A| ≤ 3 · #{exponent vectors of degree ≤ 2n/3}` for every 3AP-free `A ⊆ 𝔽₃ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- In `𝔽₃ⁿ`, a 3AP-free set contains no nontrivial triple summing to zero. -/

theorem indicator_slices (x y z : Fin n → ZMod 3) :
    (if x + y + z = 0 then (1 : ZMod 3) else 0)
      = (∑ a ∈ lowExp n, mon n a x * S₁ n a y z)
        + (∑ a ∈ lowExp n, mon n a y * S₂ n a x z)
        + (∑ a ∈ lowExp n, mon n a z * S₃ n a x y) := by
  classical
  set F : Idx n → ZMod 3 :=
    fun g => cprod n g * mon n (e₁ n g) x * mon n (e₂ n g) y * mon n (e₃ n g) z with hF
  rw [indicator_expand x y z]
  -- split the total sum into the three groups
  have hsplit : ∑ g : Idx n, F g
      = (∑ g ∈ P₁ n, F g) + (∑ g ∈ P₂ n, F g) + (∑ g ∈ P₃ n, F g) := by
    have hd12 : Disjoint (P₁ n) (P₂ n) := by
      simp only [P₁, P₂, Finset.disjoint_filter]
      intro g _ h1 h2
      exact h2.1 h1
    have hd3 : Disjoint (P₁ n ∪ P₂ n) (P₃ n) := by
      rw [Finset.disjoint_union_left]
      constructor
      · simp only [P₁, P₃, Finset.disjoint_filter]
        intro g _ h1 h2
        exact h2.1 h1
      · simp only [P₂, P₃, Finset.disjoint_filter]
        intro g _ h1 h2
        exact h2.2.1 h1.2
    have hsub : P₁ n ∪ P₂ n ∪ P₃ n ⊆ univ := Finset.subset_univ _
    have hzero : ∀ g ∈ (univ : Finset (Idx n)), g ∉ P₁ n ∪ P₂ n ∪ P₃ n → F g = 0 := by
      intro g _ hg
      simp only [Finset.mem_union, P₁, P₂, P₃, Finset.mem_filter, Finset.mem_univ,
        true_and, not_or, not_and] at hg
      obtain ⟨⟨h1, h2⟩, h3⟩ := hg
      have hc : cprod n g = 0 := by
        by_contra hc
        have hle := deg_le_of_cprod_ne_zero g hc
        have hD : 3 * D0 n + 2 ≥ 2 * n := by
          have := Nat.lt_succ_of_le (Nat.le_refl (D0 n))
          unfold D0
          omega
        have hb2 := h2 h1
        have hb3 := (h3 h1) hb2
        unfold D0 at hD hb2 hb3 h1 hle
        omega
      rw [hF]
      simp [hc]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_union hd3, Finset.sum_union hd12]
  rw [hsplit]
  congr 1
  congr 1
  · -- first group
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun g => e₁ n g) (t := lowExp n) (fun g hg => by
        simp only [lowExp, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [P₁] using hg) F]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [S₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    have : e₁ n g = a := (Finset.mem_filter.mp hg).2
    rw [hF]
    simp only
    rw [this]
    ring
  · -- second group
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun g => e₂ n g) (t := lowExp n) (fun g hg => by
        simp only [lowExp, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [P₂] using (Finset.mem_filter.mp hg).2.2) F]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [S₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    have : e₂ n g = a := (Finset.mem_filter.mp hg).2
    rw [hF]
    simp only
    rw [this]
    ring
  · -- third group
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun g => e₃ n g) (t := lowExp n) (fun g hg => by
        simp only [lowExp, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [P₃] using (Finset.mem_filter.mp hg).2.2.2) F]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [S₃, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    have : e₃ n g = a := (Finset.mem_filter.mp hg).2
    rw [hF]
    simp only
    rw [this]
    ring

end CapSetAux

/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.CapCount

/-!
# Cap Set

The cap-set theorem: subsets of `𝔽₃ⁿ` with no three-term arithmetic progression have
size `o(3ⁿ)` (Croot–Lev–Pach / Ellenberg–Gijswijt).

Main results: `Math2.cap_set` and `Math2.capSetMax_isLittleO`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- The exponential decay of the Ellenberg–Gijswijt bound relative to `3ⁿ`. -/
