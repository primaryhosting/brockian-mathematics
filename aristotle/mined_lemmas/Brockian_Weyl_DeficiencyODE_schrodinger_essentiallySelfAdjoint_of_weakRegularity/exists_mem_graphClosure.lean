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

/-
Essential self-adjointness via the basic criterion on deficiency subspaces.

This file develops, for an unbounded (partially defined) operator on a complex Hilbert
space, the classical criterion of von Neumann/Weyl:

  a densely defined symmetric operator `T` is essentially self-adjoint as soon as the two
  deficiency subspaces `ker (T† - i)` and `ker (T† + i)` are trivial.

Along the way we show that under this hypothesis the closure of `T` coincides with the
adjoint `T†`.
-/
import Mathlib

namespace Brockian.Weyl

open LinearPMap Complex
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- An unbounded operator on a Hilbert space is *essentially self-adjoint* if its closure is
self-adjoint. -/

theorem exists_mem_graphClosure (hd : Dense (T.domain : Set H)) (hs : T.IsFormalAdjoint T)
    (h₂ : deficiency T (-I)) (z : H) :
    ∃ p ∈ T.graph.topologicalClosure, p.2 - I • p.1 = z := by
  classical
  set M := T.graph.topologicalClosure with hM
  haveI : CompleteSpace M := (Submodule.isClosed_topologicalClosure T.graph).completeSpace_coe
  -- the map `φ`
  let φ : M →L[ℂ] H :=
    { toFun := fun p => (p : H × H).2 - I • (p : H × H).1
      map_add' := by intro a b; simp [smul_add]; abel
      map_smul' := by
        intro c a
        simp [smul_sub, smul_smul, mul_comm]
      cont := by
        apply Continuous.sub
        · exact continuous_snd.comp continuous_subtype_val
        · exact (continuous_const_smul I).comp (continuous_fst.comp continuous_subtype_val) }
  have hanti : AntilipschitzWith 1 φ := by
    refine AntilipschitzWith.of_le_mul_dist ?_
    intro a b
    have : dist a b = ‖(a : H × H) - b‖ := by
      rw [Subtype.dist_eq, dist_eq_norm]
    rw [this, dist_eq_norm]
    have hab : ((a : H × H) - b) ∈ M := M.sub_mem a.2 b.2
    have := norm_le_norm_sub_I_smul hs hab
    have hφ : φ a - φ b = ((a : H × H) - b).2 - I • ((a : H × H) - b).1 := by
      simp only [φ, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_sub,
        Prod.snd_sub, smul_sub]
      abel
    rw [hφ]
    simpa using this
  have hclosed : IsClosed (Set.range φ) := hanti.isClosed_range φ.uniformContinuous
  set R : Submodule ℂ H := LinearMap.range (φ : M →ₗ[ℂ] H) with hR
  have hRcoe : (R : Set H) = Set.range φ := by
    ext x; simp [hR, LinearMap.mem_range]
  have hRclosed : IsClosed (R : Set H) := by rw [hRcoe]; exact hclosed
  haveI : CompleteSpace R := hRclosed.completeSpace_coe
  have hRtop : R = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    rw [Submodule.eq_bot_iff]
    intro w hw
    -- `w` is orthogonal to the range, hence in the deficiency space at `-I`
    have hw' : ∀ x : T.domain, ⟪(-I) • w, (x : H)⟫ = ⟪w, T x⟫ := by
      intro x
      have hmem : ((x : H), T x) ∈ M := by
        apply Submodule.le_topologicalClosure
        exact T.mem_graph x
      have hmemR : (T x - I • (x : H)) ∈ R := ⟨⟨((x : H), T x), hmem⟩, rfl⟩
      have hzero : ⟪(T x - I • (x : H)), w⟫ = (0 : ℂ) := hw _ hmemR
      have h1 : ⟪T x, w⟫ = ⟪I • (x : H), w⟫ := by
        rw [inner_sub_left, sub_eq_zero] at hzero; exact hzero
      calc ⟪(-I) • w, (x : H)⟫ = I * ⟪w, (x : H)⟫ := by
            rw [inner_smul_left]; congr 1; simp
        _ = conj (⟪I • (x : H), w⟫) := by
            rw [inner_smul_left, map_mul]
            congr 1
            · simp
            · rw [inner_conj_symm]
        _ = conj ⟪T x, w⟫ := by rw [h1]
        _ = ⟪w, T x⟫ := inner_conj_symm _ _
    have hwd : w ∈ T†.domain := mem_adjoint_domain_of_exists _ ⟨(-I) • w, hw'⟩
    exact h₂ ⟨w, hwd⟩ (adjoint_apply_eq hd ⟨w, hwd⟩ hw')
  have : z ∈ R := by rw [hRtop]; trivial
  rw [hR, LinearMap.mem_range] at this
  obtain ⟨p, hp⟩ := this
  exact ⟨(p : H × H), p.2, hp⟩

/-- Under the two deficiency conditions, the graph of the adjoint is contained in the closure of
the graph. -/
