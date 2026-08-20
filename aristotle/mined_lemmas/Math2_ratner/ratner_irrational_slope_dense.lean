import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

open scoped Pointwise Topology

namespace Math2

/-! ## Closures of coset-orbits are cosets -/

variable {Q : Type*} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]

/-- The closure of the orbit `S * x` of a subgroup `S` is the coset `S̄ * x`
of the topological closure of `S`. -/
@[to_additive closure_addCoset_eq /-- The closure of the orbit `S + x` of an additive subgroup `S`
is the coset `S̄ + x` of the topological closure of `S`. -/]

theorem ratner_irrational_slope_dense {a : ℝ} (ha : Irrational a) (x : Torus2) :
    Dense (Set.range fun t : ℝ => (((t : ℝ) : AddCircle (1 : ℝ)),
      ((t * a : ℝ) : AddCircle (1 : ℝ))) + x) := by
  set g : ℝ → Torus2 :=
    fun t => (((t : ℝ) : AddCircle (1 : ℝ)), ((t * a : ℝ) : AddCircle (1 : ℝ))) with hg
  have hg0 : g 0 = 0 := by simp [hg]
  have hgadd : ∀ s t : ℝ, g (s + t) = g s + g t := by
    intro s t; simp [hg, add_mul]
  let S : AddSubgroup Torus2 :=
    { carrier := Set.range g
      zero_mem' := ⟨0, hg0⟩
      add_mem' := by rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩; exact ⟨s + t, hgadd s t⟩
      neg_mem' := by
        rintro _ ⟨t, rfl⟩
        refine ⟨-t, ?_⟩
        have h : g (-t) + g t = 0 := by rw [← hgadd]; simp [hg0]
        exact (neg_eq_of_add_eq_zero_left h).symm }
  have hScoe : (S : Set Torus2) = Set.range g := rfl
  set H := S.topologicalClosure with hH
  have hHcoe : (H : Set Torus2) = closure (Set.range g) := by
    rw [hH, AddSubgroup.topologicalClosure_coe, hScoe]
  -- at integer times the flow visits the vertical circle at the points `n • a`
  have hzmul : ∀ n : ℤ, ((0 : AddCircle (1 : ℝ)), (n • ((a : ℝ) : AddCircle (1 : ℝ)))) ∈ S := by
    intro n
    refine ⟨(n : ℝ), ?_⟩
    have h1 : ((n : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      exact_mod_cast (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (n : ℝ))).2 ⟨n, by ring⟩
    have h2 : (((n : ℝ) * a : ℝ) : AddCircle (1 : ℝ)) = n • ((a : ℝ) : AddCircle (1 : ℝ)) := by
      rw [← zsmul_eq_mul]
      exact QuotientAddGroup.mk_zsmul _ a n
    simp [hg, h1, h2]
  -- by irrationality these points are dense, so the whole vertical circle lies in `H`
  have hvert : ∀ c : AddCircle (1 : ℝ), ((0 : AddCircle (1 : ℝ)), c) ∈ H := by
    have hcont : Continuous fun c : AddCircle (1 : ℝ) => ((0 : AddCircle (1 : ℝ)), c) := by fun_prop
    have hclosed : IsClosed ((fun c : AddCircle (1 : ℝ) => ((0 : AddCircle (1 : ℝ)), c)) ⁻¹'
        (H : Set Torus2)) := (S.isClosed_topologicalClosure).preimage hcont
    have hdr : DenseRange (fun n : ℤ => n • ((a : ℝ) : AddCircle (1 : ℝ))) :=
      AddCircle.denseRange_zsmul_coe_iff.2 (by simpa using ha)
    intro c
    have hsub : (Set.univ : Set (AddCircle (1 : ℝ))) ⊆
        (fun c : AddCircle (1 : ℝ) => ((0 : AddCircle (1 : ℝ)), c)) ⁻¹' (H : Set Torus2) := by
      rw [← hdr.closure_eq]
      refine hclosed.closure_subset_iff.2 ?_
      rintro _ ⟨n, rfl⟩
      exact AddSubgroup.le_topologicalClosure S (hzmul n)
    exact hsub (Set.mem_univ c)
  -- hence `H` is everything
  have hall : ∀ y : Torus2, y ∈ H := by
    rintro ⟨p, q⟩
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective (α := ℝ) p
    have h1 : g t ∈ H := AddSubgroup.le_topologicalClosure S ⟨t, rfl⟩
    have h2 : ((0 : AddCircle (1 : ℝ)), q - ((t * a : ℝ) : AddCircle (1 : ℝ))) ∈ H := hvert _
    have h3 := H.add_mem h1 h2
    simpa [hg, Prod.ext_iff] using h3
  have hdense : Dense (Set.range g) := by
    rw [dense_iff_closure_eq, ← hHcoe]
    exact Set.eq_univ_of_forall hall
  have himg : (Set.range fun t : ℝ => g t + x) = (fun y => y + x) '' Set.range g := by
    rw [← Set.range_comp]; rfl
  rw [himg]
  exact dense_image_add_right hdense x

end Math2

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

