/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import RequestProject.CauchySelfContained

/-!
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Cauchy's theorem**: if a prime `p` divides the order of a finite group `G`,
then `G` contains an element of order `p`.

The proof is self-contained (it does not invoke Mathlib's `exists_prime_orderOf_dvd_card`):
see `Math.cauchy_of_dvd_card`, which argues by strong induction on the order of the group. -/

lemma center_eq_top_of_no_proper_subgroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ Nat.card G)
    (hmin : ∀ H : Subgroup G, H ≠ ⊤ → ¬ p ∣ Nat.card H) :
    Subgroup.center G = ⊤ := by
  classical
  by_contra hne
  refine hmin _ hne ?_
  have hclass := Group.nat_card_center_add_sum_card_noncenter_eq_card G
  have hfin : (ConjClasses.noncenter G).Finite := Set.toFinite _
  have hsum : p ∣ ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.dvd_sum ?_
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective x
    have hgc : g ∉ Subgroup.center G := fun hg => (ConjClasses.mk_bijOn G).mapsTo hg hx
    have hnetop : Subgroup.centralizer ({g} : Set G) ≠ ⊤ := fun h =>
      hgc (Subgroup.centralizer_eq_top_iff_subset.mp h rfl)
    have h2 : p ∣ Nat.card (ConjClasses.mk g).carrier * Nat.card (Subgroup.centralizer {g}) := by
      rw [card_conjClass_mul_card_centralizer g]; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
    · exact h
    · exact absurd h (hmin _ hnetop)
  have heq : Nat.card (Subgroup.center G)
      = Nat.card G - ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier := by omega
  rw [heq]
  exact Nat.dvd_sub hdvd hsum

/-- The abelian case of Cauchy's theorem, assuming the result for all smaller groups. -/
