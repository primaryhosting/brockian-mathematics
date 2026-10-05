import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

/-! ## Basic notions -/

/-- A finite set of naturals is *relatively large* when it is nonempty and its cardinality
is at least its least element. -/

theorem goodSet_mem {r : ℕ} (U : Ultrafilter ℕ) (D : ℕ → Finset ℕ → Fin r) (k : ℕ)
    (hU : (U : Filter ℕ) ≤ cofinite)
    (hD : ∀ i s, D (i + 1) s = ulim U (fun x => D i (insert x s))) (T : Finset ℕ) :
    goodSet D k T ∈ U := by
  have h1 : {x | ∀ y ∈ T, y < x} ∈ U := by
    apply hU
    rw [Filter.mem_cofinite]
    refine Set.Finite.subset (Set.finite_Iic (T.sup id)) ?_
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact le_trans hxy (Finset.le_sup (f := id) hy)
  have h2 : (⋂ s ∈ T.powerset,
      {x | ∀ i, i + s.card + 1 = k → D i (insert x s) = D (i + 1) s}) ∈ U := by
    refine (Filter.biInter_finset_mem _).2 ?_
    intro s _
    by_cases hcard : s.card + 1 ≤ k
    · refine Filter.mem_of_superset (ulim_spec U (fun x => D (k - s.card - 1) (insert x s))) ?_
      intro x hx i hi
      have hik : i = k - s.card - 1 := by omega
      subst hik
      rw [hD _ s]
      exact hx
    · exact Filter.univ_mem' (fun _ _ hi => absurd hi (by omega))
  filter_upwards [h1, h2] with x hx1 hx2
  refine ⟨hx1, ?_⟩
  intro s hsT i hi
  exact (Set.mem_iInter₂.1 hx2 s (Finset.mem_powerset.2 hsT)) i hi

/-- The finite set built after `n` steps of the greedy construction. -/
