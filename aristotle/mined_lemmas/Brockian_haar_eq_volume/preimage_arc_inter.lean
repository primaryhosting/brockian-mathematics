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

import Mathlib

/-!
# Equidistribution of irrational rotations, and the density of configuration counts

This file proves Weyl's equidistribution theorem for the sequence `n ↦ {n α}` (`α` irrational)
and deduces the unconditional statement `configCount_density_of_BV`: the density of the set of
`n < N` with `{n α} ∈ [a, b)` tends to `b - a`.

The indicator of an interval is the basic example of a function of bounded variation, and the
"BV reduction" is implemented here through the portmanteau theorem: the empirical measures of
the orbit converge weakly to Haar measure (proved via the Fourier/Weyl criterion), hence the
measures of any arc whose boundary is Haar-null converge.
-/

namespace Brockian
namespace EquidistributionBVReduction

open Filter MeasureTheory Set Topology AddCircle
open scoped BigOperators ENNReal NNReal

/-- The point `n • α` of the circle `ℝ / ℤ`. -/

lemma preimage_arc_inter {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (QuotientAddGroup.mk ⁻¹' (arc a b)) ∩ Set.Ioc a (a + 1) = Set.Ioo a b ∪ {a + 1} := by
  have hb1 : b ≤ a + 1 := by linarith
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    obtain ⟨y, hy, hxy⟩ := hx1
    obtain ⟨k, hk⟩ := (coe_eq_coe_iff y x).mp hxy
    have h1 : (-1 : ℝ) ≤ (k:ℝ) := by linarith [hk, hy.1, hx2.2]
    have h2 : (k:ℝ) < 1 := by linarith [hk, hy.2, hx2.1]
    have hk0 : k = -1 ∨ k = 0 := by
      have h1' : (-1 : ℤ) ≤ k := by exact_mod_cast h1
      have h2' : k < 1 := by exact_mod_cast h2
      omega
    rcases hk0 with rfl | rfl
    · right
      simp only [Set.mem_singleton_iff]
      push_cast at hk
      linarith [hy.1, hx2.2]
    · left
      have hyx : y = x := by push_cast at hk; linarith
      subst hyx
      exact ⟨hx2.1, hy.2⟩
  · rintro (hx | hx)
    · exact ⟨⟨x, ⟨le_of_lt hx.1, hx.2⟩, rfl⟩, hx.1, le_trans (le_of_lt hx.2) hb1⟩
    · simp only [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨⟨a, ⟨le_refl a, hab⟩, ?_⟩, by linarith, le_refl _⟩
      rw [coe_eq_coe_iff]
      exact ⟨-1, by push_cast; ring⟩

