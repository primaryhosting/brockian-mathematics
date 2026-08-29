/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
A proof of Cauchy's theorem: if a prime `p` divides the order of a finite group `G`,
then `G` has an element of order `p`.

The argument here is the classical one, by strong induction on `|G|`:

* if some proper subgroup `H < G` has order divisible by `p`, apply the induction hypothesis
  to `H`;
* otherwise the class equation forces `p ∣ |Z(G)|`, so `Z(G)` is not proper, i.e. `G` is
  abelian.  Picking `x ≠ 1` and setting `H = ⟨x⟩`, either `H = G` (and then `p ∣ orderOf x`),
  or `H` is proper and `p ∣ [G : H] = |G ⧸ H| < |G|`, so the induction hypothesis produces an
  element of order `p` in the quotient, which lifts to an element of `G` whose order is
  divisible by `p`.
-/

namespace Math

namespace CauchyProof

/-- From an element whose order is divisible by the prime `p` one extracts an element of
order exactly `p`. -/

theorem notMem_center_of_mem_noncenter {G : Type*} [Group G] {g : G}
    (hg : ConjClasses.mk g ∈ ConjClasses.noncenter G) : g ∉ Subgroup.center G := by
  intro hc
  rw [ConjClasses.mem_noncenter] at hg
  refine hg.not_subsingleton ?_
  intro a ha b hb
  rw [ConjClasses.carrier_eq_preimage_mk] at ha hb
  simp only [Set.mem_preimage, Set.mem_singleton_iff, ConjClasses.mk_eq_mk_iff_isConj] at ha hb
  have hcs : g ∈ Set.center G := Set.mem_center_iff.mpr hc
  have haux : ∀ c : G, IsConj c g → c = g := fun _ hcg => hcg.eq_of_right_mem_center hcs
  rw [haux a ha, haux b hb]

/-- Key consequence of the class equation: if no proper subgroup of the finite group `G` has
order divisible by the prime `p`, but `p ∣ |G|`, then `p` divides the order of the centre. -/
