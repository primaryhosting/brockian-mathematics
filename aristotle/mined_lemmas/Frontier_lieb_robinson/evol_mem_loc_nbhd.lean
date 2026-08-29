/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The `r`-neighbourhood of a set of sites `X` inside a metric space of sites. -/

theorem evol_mem_loc_nbhd (hloc : LocalStructure loc)
    (Z : ℕ → Set Site) (u v : ℕ → A)
    (hu : ∀ k, u k ∈ loc (Z k)) (hv : ∀ k, v k ∈ loc (Z k))
    (huv : ∀ k, u k * v k = 1)
    (hdiam : ∀ k, ∀ z ∈ Z k, ∀ w ∈ Z k, dist z w ≤ 1)
    {X : Set Site} {a : A} (ha : a ∈ loc X) (n : ℕ) :
    evol u v n a ∈ loc (nbhd (n : ℝ) X) := by
  induction n with
  | zero =>
      have h : a ∈ loc (nbhd ((0 : ℕ) : ℝ) X) := by
        simpa using hloc.mono (subset_nbhd (le_rfl : (0:ℝ) ≤ 0) X) ha
      simpa [evol] using h
  | succ k ih =>
      have hcast : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      by_cases hdisj : Disjoint (nbhd (k : ℝ) X) (Z k)
      · -- the gate acts trivially on the current support
        have hcomm : u k * evol u v k a = evol u v k a * u k :=
          hloc.commute (Z k) (nbhd (k : ℝ) X) hdisj.symm (u k) (hu k) _ ih
        have : evol u v (k + 1) a = evol u v k a := by
          show u k * evol u v k a * v k = evol u v k a
          rw [hcomm, mul_assoc, huv k, mul_one]
        rw [this]
        refine hloc.mono ?_ ih
        intro z hz
        obtain ⟨x, hx, hzx⟩ := hz
        exact ⟨x, hx, by push_cast; linarith⟩
      · -- the gate region meets the current support: the support grows by one
        rw [Set.not_disjoint_iff] at hdisj
        obtain ⟨p, hp1, hp2⟩ := hdisj
        have hsub : nbhd (k : ℝ) X ∪ Z k ⊆ nbhd ((k : ℝ) + 1) X :=
          nbhd_union_subset hp2 hp1 (hdiam k)
        have hmem : evol u v (k + 1) a ∈ loc (nbhd (k : ℝ) X ∪ Z k) := by
          show u k * evol u v k a * v k ∈ _
          refine hloc.mul_mem _ _ (hloc.mul_mem _ _ ?_ _ ?_) _ ?_
          · exact hloc.mono Set.subset_union_right (hu k)
          · exact hloc.mono Set.subset_union_left ih
          · exact hloc.mono Set.subset_union_right (hv k)
        have := hloc.mono hsub hmem
        rwa [hcast] at this

/-- The evolution is norm non-increasing when the gates are contractions. -/
