import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

/-- The homogeneous space `X = G / Γ` for `G = ℝ²` and the lattice `Γ = ℤ²`, i.e. the
two-dimensional torus. -/
abbrev Torus2 : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The projection `G = ℝ² → X = ℝ²/ℤ²`. -/

lemma dense_lineAddLattice (v : ℝ × ℝ) (hv1 : v.1 ≠ 0) (hirr : Irrational (v.2 / v.1)) :
    Dense ((lineAddLattice v : AddSubgroup (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
  set S : AddSubgroup (ℝ × ℝ) := lineAddLattice v with hS
  set C : AddSubgroup (ℝ × ℝ) := S.topologicalClosure with hC
  have hCclosed : IsClosed (C : Set (ℝ × ℝ)) := AddSubgroup.isClosed_topologicalClosure S
  have hSC : S ≤ C := AddSubgroup.le_topologicalClosure S
  have he1 : ((1 : ℝ), (0 : ℝ)) ∈ C :=
    hSC (le_sup_right (a := (LinearMap.toSpanSingleton ℝ (ℝ × ℝ) v).toAddMonoidHom.range)
      (AddSubgroup.subset_closure (by simp)))
  have he2 : ((0 : ℝ), (1 : ℝ)) ∈ C :=
    hSC (le_sup_right (a := (LinearMap.toSpanSingleton ℝ (ℝ × ℝ) v).toAddMonoidHom.range)
      (AddSubgroup.subset_closure (by simp)))
  have hline : ∀ t : ℝ, (t • v) ∈ C := fun t =>
    hSC (le_sup_left (b := AddSubgroup.closure {((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))}) ⟨t, rfl⟩)
  have hkey : ∀ s : ℝ, ((0 : ℝ), s) ∈ C := by
    have hcont : Continuous (AddMonoidHom.inr ℝ ℝ) := continuous_const.prodMk continuous_id
    set K : AddSubgroup ℝ := C.comap (AddMonoidHom.inr ℝ ℝ) with hK
    have hKclosed : IsClosed (K : Set ℝ) := hCclosed.preimage hcont
    have h1 : (1 : ℝ) ∈ K := he2
    have halpha : v.2 / v.1 ∈ K := by
      have hx : ((0 : ℝ), v.2 / v.1) = (1 / v.1) • v - ((1 : ℝ), (0 : ℝ)) := by
        have hv : (1 / v.1) • v = ((1 : ℝ), v.2 / v.1) := by
          ext <;> simp [Prod.smul_def, smul_eq_mul] <;> field_simp
        rw [hv]
        ext <;> simp
      show ((0 : ℝ), v.2 / v.1) ∈ C
      rw [hx]
      exact sub_mem (hline _) he1
    have hsub : AddSubgroup.closure {v.2 / v.1, (1 : ℝ)} ≤ K :=
      (AddSubgroup.closure_le K).mpr (Set.pair_subset_iff.mpr ⟨halpha, h1⟩)
    have hdense : Dense ((AddSubgroup.closure {v.2 / v.1, (1 : ℝ)} : AddSubgroup ℝ) : Set ℝ) :=
      dense_addSubgroupClosure_pair_iff.mpr (by simpa using hirr)
    have huniv : (Set.univ : Set ℝ) ⊆ (K : Set ℝ) := by
      rw [← hdense.closure_eq]
      exact hKclosed.closure_subset_iff.mpr hsub
    exact fun s => huniv (Set.mem_univ s)
  have hCtop : C = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    rintro ⟨x, y⟩
    have h1 : (x / v.1) * v.1 = x := by field_simp
    have h2 : (x / v.1) * v.2 + (y - x * (v.2 / v.1)) = y := by field_simp; ring
    have hdecomp : ((x, y) : ℝ × ℝ) = (x / v.1) • v + ((0 : ℝ), y - x * (v.2 / v.1)) := by
      simp [Prod.smul_def, smul_eq_mul, h1, h2]
    rw [hdecomp]
    exact add_mem (hline _) (hkey _)
  have hclosure : closure (S : Set (ℝ × ℝ)) = Set.univ := by
    rw [← AddSubgroup.topologicalClosure_coe, ← hC, hCtop]
    simp
  exact dense_iff_closure_eq.mpr hclosure

/-- The projection `ℝ² → ℝ²/ℤ²` maps dense sets to dense sets. -/
