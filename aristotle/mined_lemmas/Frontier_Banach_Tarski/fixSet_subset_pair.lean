import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
-/

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

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


lemma fixSet_subset_pair (M : SO3) (hM : M.1 ≠ 1) : ∃ a : E, fixSet M ⊆ {a, -a} := by
  by_cases hemp : (fixSet M) = ∅
  · exact ⟨0, by rw [hemp]; exact Set.empty_subset _⟩
  · obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hemp
    refine ⟨u, ?_⟩
    intro v hv
    rw [mem_fixSet_iff] at hu hv
    by_contra hcon
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
    have h1 : v.ofLp ≠ u.ofLp := by
      intro h
      exact hcon.1 (by ext i; exact congrFun h i)
    have h2 : v.ofLp ≠ -u.ofLp := by
      intro h
      refine hcon.2 ?_
      ext i
      have := congrFun h i
      simpa using this
    exact hM (eq_one_of_two_fixed M hu.1 hv.1 hu.2 hv.2 h1 h2)

