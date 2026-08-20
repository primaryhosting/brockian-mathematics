/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory Metric Set Filter Function
open scoped ENNReal Topology

/-! ## The Yang–Mills energy

A Yang–Mills field on a manifold `X` is modelled here by its curvature `F : X → V`, a field with
values in a normed space `V` (in the geometric situation, `V` is the space of `𝔤`-valued
two-forms).  Its Yang–Mills energy over a region `s` is `∫_s ‖F‖²`. -/

section Energy

variable {X : Type*} [MeasurableSpace X] {V : Type*} [NormedAddCommGroup V]

/-- The Yang–Mills energy `∫_s ‖F‖²` of a curvature field `F` over the region `s`. -/

theorem bubbleSet_finite {mu : Measure X} {F : ℕ → X → V} {eps Etot : ℝ≥0∞}
    (hEtot : Etot ≠ ∞) (heps : eps ≠ 0)
    (hbdd : ∀ n, energyOn mu (F n) Set.univ ≤ Etot) :
    (bubbleSet mu F eps).Finite := by
  classical
  set e : ℝ≥0∞ := min eps 1 with he
  have he0 : e ≠ 0 := by
    have : (0 : ℝ≥0∞) < e := lt_min (pos_iff_ne_zero.2 heps) one_pos
    exact this.ne'
  have hetop : e ≠ ∞ := ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Etot / e < (N : ℝ≥0∞) :=
    ENNReal.exists_nat_gt (ENNReal.div_ne_top hEtot he0)
  have hNe : Etot < (N : ℝ≥0∞) * e :=
    (ENNReal.div_lt_iff (Or.inl he0) (Or.inl hetop)).1 hN
  have hsub : (bubbleSet mu F eps) ⊆ bubbleSet mu F e :=
    bubbleSet_mono (min_le_left _ _)
  obtain ⟨S, hSsub, hScard⟩ := (hinf.mono hsub).exists_subset_card_eq N
  have hcard := finset_card_mul_le_of_subset_bubbleSet hbdd S hSsub
  rw [hScard] at hcard
  exact absurd hcard (not_le.2 hNe)

end Bubble

/-! ## The main theorem -/

/-- Four-dimensional Euclidean space, the base manifold of the model Yang–Mills problem. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- **Uhlenbeck bubbling.**

Let `F n` be a sequence of Yang–Mills curvature fields on `ℝ⁴` with uniformly bounded
Yang–Mills energy `Etot < ∞`, and let `eps > 0` be an energy threshold (in the geometric theory,
the `ε`-regularity threshold).  Then:

* the bubbling set — the set of points at which the energy persistently concentrates at scale
  `eps` on all small balls — is **finite**;
* it satisfies the **quantization bound** `#{bubbles} · eps ≤ Etot`, so at most `Etot / eps`
  bubbles can form;
* away from the bubbling set, the fields are **frequently subcritical** on some fixed ball, i.e.
  the hypothesis of `ε`-regularity is available there along a subsequence.

This is the combinatorial core of Uhlenbeck's compactness theorem: modulo `ε`-regularity, the
only obstruction to compactness is the loss of at most `Etot / eps` quanta of energy at finitely
many points. -/
