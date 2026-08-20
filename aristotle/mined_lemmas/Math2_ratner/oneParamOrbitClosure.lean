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

theorem oneParamOrbitClosure (f : ℝ → Q) (hfc : Continuous f)
    (hfm : ∀ s t : ℝ, f (s + t) = f s * f t) (x : Q) :
    ∃ H : Subgroup Q,
      IsClosed (H : Set Q) ∧
      IsConnected (H : Set Q) ∧
      (∀ t : ℝ, f t ∈ H) ∧
      closure (Set.range fun t : ℝ => f t * x) = (fun g => g * x) '' (H : Set Q) := by
  have hf0 : f 0 = 1 := by
    have h : f 0 * f 0 = f 0 * 1 := by rw [mul_one, ← hfm, add_zero]
    exact mul_left_cancel h
  let S : Subgroup Q :=
    { carrier := Set.range f
      one_mem' := ⟨0, hf0⟩
      mul_mem' := by
        rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
        exact ⟨s + t, hfm s t⟩
      inv_mem' := by
        rintro _ ⟨t, rfl⟩
        refine ⟨-t, ?_⟩
        have h : f (-t) * f t = 1 := by rw [← hfm]; simp [hf0]
        exact eq_inv_of_mul_eq_one_left h }
  have hScoe : (S : Set Q) = Set.range f := rfl
  refine ⟨S.topologicalClosure, S.isClosed_topologicalClosure, ?_, ?_, ?_⟩
  · rw [Subgroup.topologicalClosure_coe, hScoe]
    exact (isConnected_range hfc).closure
  · intro t
    exact Subgroup.le_topologicalClosure S ⟨t, rfl⟩
  · have himg : (Set.range fun t : ℝ => f t * x) = (fun g => g * x) '' (S : Set Q) := by
      rw [hScoe, ← Set.range_comp]
      rfl
    rw [himg, closure_coset_eq]

/-! ## Ratner's orbit closure theorem, homogeneous (abelian / normal) case -/

/-- **Ratner's orbit closure theorem** in the setting of a quotient of a topological group by a
normal subgroup (this covers in particular all unipotent flows on quotients of abelian Lie groups
by lattices, e.g. linear flows on tori, where every element is unipotent).

If `u : ℝ → G` is a continuous one-parameter subgroup of a topological group `G` and `N` is a
normal subgroup, then for every point `x` of `G ⧸ N` the closure of the orbit
`{u(t) · x : t ∈ ℝ}` is *homogeneous*: it is the translate `H · x` of a closed connected subgroup
`H ≤ G ⧸ N` which contains the whole one-parameter subgroup. In particular the flow is minimal on
its orbit closure. -/
@[to_additive ratner_add]
