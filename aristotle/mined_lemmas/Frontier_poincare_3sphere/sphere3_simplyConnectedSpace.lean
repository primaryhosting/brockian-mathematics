import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(Lean requires `import` to be the very first command of a file, before any module-level doc
comment, so the required header block is placed immediately after `import Mathlib`.)

## Contents

* `Frontier.IsClosed3Manifold` : a closed (compact, boundaryless, second countable, Hausdorff)
  topological 3-manifold.
* `Frontier.IsSimplyConnectedClosed3Manifold` : the hypothesis class of the Poincaré conjecture.
* `Frontier.PoincareConjecture3` : the formal statement of the Poincaré conjecture in dimension 3
  (Perelman): every simply connected closed 3-manifold is homeomorphic to `S³`.
* `Frontier.poincare_3sphere` : the Lean-checked *reduction*: the conjecture is equivalent to the
  a priori weaker statement that every simply connected closed 3-manifold admits a continuous
  bijection onto `S³`.  The nontrivial direction is closed by the Mathlib lemma
  `Continuous.homeoOfEquivCompactToT2` (a continuous bijection from a compact space to a Hausdorff
  space is a homeomorphism).
* Supporting results: the hypothesis class is invariant under homeomorphism
  (`Frontier.IsSimplyConnectedClosed3Manifold.homeomorph`) and is realized by `S³` itself
  (`Frontier.sphere3_isClosed3Manifold`), so the statement is not vacuous.

The base case of the conjecture — that `S³` really is a simply connected closed 3-manifold, and
that the conjecture holds for every space homeomorphic to it — is proved in
`RequestProject/Sphere3SimplyConnected.lean`.
-/

universe u v

namespace Frontier

open Metric

/-- The model space `ℝ³` for 3-manifolds. -/
abbrev EuclideanThree : Type := EuclideanSpace ℝ (Fin 3)

/-- The 3-sphere, as the unit sphere of `ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- A *closed 3-manifold*: a compact, Hausdorff, second countable topological space which is
locally homeomorphic to `ℝ³` (a boundaryless topological 3-manifold, i.e. charted over `ℝ³`). -/
structure IsClosed3Manifold (M : Type u) [TopologicalSpace M] : Prop where
  t2Space : T2Space M
  compactSpace : CompactSpace M
  secondCountableTopology : SecondCountableTopology M
  chartedSpace : Nonempty (ChartedSpace EuclideanThree M)

/-- The hypothesis class of the Poincaré conjecture: a simply connected closed 3-manifold. -/
structure IsSimplyConnectedClosed3Manifold (M : Type u) [TopologicalSpace M] : Prop
    extends IsClosed3Manifold M where
  simplyConnectedSpace : SimplyConnectedSpace M

/-- **The Poincaré conjecture in dimension three** (Perelman): every simply connected closed
3-manifold is homeomorphic to the 3-sphere. -/

theorem sphere3_simplyConnectedSpace : SimplyConnectedSpace (sphere (0 : E4) 1) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  constructor
  · rw [← isPathConnected_iff_pathConnectedSpace]
    refine isPathConnected_sphere ?_ 0 zero_le_one
    have hr : Module.rank ℝ E4 = 4 := by
      simp [rank_eq_card_basis (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis]
    rw [hr]
    norm_num
  · intro x γ
    set f : ℝ → E4 := fun u => ((γ.extend u : sphere (0:E4) 1) : E4) with hf
    have hfnorm : ∀ u, ‖f u‖ = 1 := by
      intro u
      simp [hf]
    have hfU : UniformContinuous f := by
      have h1 : UniformContinuous (fun s : unitInterval => ((γ s : sphere (0:E4) 1) : E4)) :=
        CompactSpace.uniformContinuous_of_continuous (by fun_prop)
      have h2 : LipschitzWith 1 (Set.projIcc (0:ℝ) 1 zero_le_one) :=
        LipschitzWith.projIcc zero_le_one
      exact h1.comp h2.uniformContinuous
    obtain ⟨K, Q, hQlip, hQ0, hQ1, hQd⟩ :=
      exists_lipschitz_approx f hfU (fun u => (hfnorm u).le) (ε := 3/8) (by norm_num)
    have hQlb : ∀ t ∈ Icc (0:ℝ) 1, 5/8 ≤ ‖Q t‖ := by
      intro t ht
      have h1 := hQd t ht
      have h2 := hfnorm t
      have ha : ‖f t‖ - ‖Q t‖ ≤ ‖f t - Q t‖ := norm_sub_norm_le _ _
      rw [norm_sub_rev] at ha
      linarith
    have hQub : ∀ t ∈ Icc (0:ℝ) 1, ‖Q t‖ ≤ 2 := by
      intro t ht
      have h1 := hQd t ht
      have h2 := hfnorm t
      have hb : ‖Q t‖ ≤ ‖f t‖ + ‖Q t - f t‖ := by
        have := norm_add_le (f t) (Q t - f t)
        simpa using this
      linarith
    have hQne : ∀ t : unitInterval, Q (t : ℝ) ≠ 0 := by
      intro t h
      have hlb := hQlb (t:ℝ) ⟨t.2.1, t.2.2⟩
      rw [h] at hlb
      simp at hlb
      linarith
    have hcont : Continuous fun t : unitInterval => nrmz (Q (t:ℝ)) := by
      have hc : Continuous fun t : unitInterval => Q (t:ℝ) :=
        hQlip.continuous.comp continuous_subtype_val
      have hinv : Continuous fun t : unitInterval => (‖Q (t:ℝ)‖)⁻¹ :=
        (continuous_norm.comp hc).inv₀ (fun t => norm_ne_zero_iff.mpr (hQne t))
      exact hinv.smul hc
    have hQ0x : Q 0 = (x : E4) := by rw [hQ0, hf]; simp
    have hQ1x : Q 1 = (x : E4) := by rw [hQ1, hf]; simp
    have hxn : ‖(x : E4)‖ = 1 := by simp
    have hnrmzx : nrmz (x : E4) = (x : E4) := by rw [nrmz, hxn]; simp
    let g : Path x x :=
      { toFun := fun t => ⟨nrmz (Q (t:ℝ)), nrmz_mem_sphere (hQne t)⟩
        continuous_toFun := hcont.subtype_mk _
        source' := by
          apply Subtype.ext
          simp only [Set.Icc.coe_zero, hQ0x, hnrmzx]
        target' := by
          apply Subtype.ext
          simp only [Set.Icc.coe_one, hQ1x, hnrmzx] }
    have hne : ∀ s t : unitInterval, (1 - (s:ℝ)) • f (t:ℝ) + (s:ℝ) • Q (t:ℝ) ≠ 0 := by
      intro s t h
      have hd : ‖((1 - (s:ℝ)) • f (t:ℝ) + (s:ℝ) • Q (t:ℝ)) - f (t:ℝ)‖ ≤ 3/8 := by
        have hrw : ((1 - (s:ℝ)) • f (t:ℝ) + (s:ℝ) • Q (t:ℝ)) - f (t:ℝ)
            = (s:ℝ) • (Q (t:ℝ) - f (t:ℝ)) := by module
        rw [hrw, norm_smul, Real.norm_eq_abs, abs_of_nonneg s.2.1]
        have h1 := hQd (t:ℝ) ⟨t.2.1, t.2.2⟩
        nlinarith [s.2.2, norm_nonneg (Q (t:ℝ) - f (t:ℝ))]
      rw [h, zero_sub, norm_neg, hfnorm] at hd
      linarith
    have hcH : Continuous fun st : unitInterval × unitInterval =>
        nrmz ((1 - (st.1:ℝ)) • f (st.2:ℝ) + (st.1:ℝ) • Q (st.2:ℝ)) := by
      have hfc : Continuous f := hfU.continuous
      have hQc : Continuous Q := hQlip.continuous
      have hbase : Continuous fun st : unitInterval × unitInterval =>
          (1 - (st.1:ℝ)) • f (st.2:ℝ) + (st.1:ℝ) • Q (st.2:ℝ) := by fun_prop
      have hinv : Continuous fun st : unitInterval × unitInterval =>
          ‖(1 - (st.1:ℝ)) • f (st.2:ℝ) + (st.1:ℝ) • Q (st.2:ℝ)‖⁻¹ :=
        hbase.norm.inv₀ (fun st => norm_ne_zero_iff.mpr (hne st.1 st.2))
      exact hinv.smul hbase
    have hhom : γ.Homotopic g := by
      refine ⟨{ toFun := fun st => ⟨nrmz ((1 - (st.1:ℝ)) • f (st.2:ℝ) + (st.1:ℝ) • Q (st.2:ℝ)),
                  nrmz_mem_sphere (hne st.1 st.2)⟩
                continuous_toFun := hcH.subtype_mk _
                map_zero_left := ?_
                map_one_left := ?_
                prop' := ?_ }⟩
      · intro t
        apply Subtype.ext
        have hz : ((0 : unitInterval) : ℝ) = 0 := rfl
        simp only [hz, sub_zero, one_smul, zero_smul, add_zero]
        have : nrmz (f (t:ℝ)) = f (t:ℝ) := by rw [nrmz, hfnorm]; simp
        rw [this, hf]
        simp
      · intro t
        apply Subtype.ext
        have ho : ((1 : unitInterval) : ℝ) = 1 := rfl
        simp only [ho, sub_self, one_smul, zero_smul, zero_add]
        rfl
      · intro s y hy
        apply Subtype.ext
        show nrmz ((1 - (s:ℝ)) • f (y:ℝ) + (s:ℝ) • Q (y:ℝ)) = ((γ y : sphere (0:E4) 1) : E4)
        have hyv : (y : ℝ) = 0 ∨ (y : ℝ) = 1 := by
          rcases hy with h | h
          · left; rw [h]; rfl
          · right; rw [Set.mem_singleton_iff.mp h]; rfl
        have hfy : f (y:ℝ) = (x : E4) ∧ Q (y:ℝ) = (x : E4) := by
          rcases hyv with h | h
          · rw [h, hQ0x]
            exact ⟨by rw [hf]; simp, rfl⟩
          · rw [h, hQ1x]
            exact ⟨by rw [hf]; simp, rfl⟩
        rw [hfy.1, hfy.2]
        have hcomb : (1 - (s:ℝ)) • (x : E4) + (s:ℝ) • (x : E4) = (x : E4) := by module
        rw [hcomb, hnrmzx]
        rcases hyv with h | h
        · have : y = 0 := Subtype.ext h
          rw [this]
          simp
        · have : y = 1 := Subtype.ext h
          rw [this]
          simp
    obtain ⟨p, hpnorm, hpne⟩ :=
      exists_sphere_point_not_mem_image hQlip (fun t ht => by linarith [hQlb t ht]) hQub
    have hpS : p ∈ sphere (0:E4) 1 := by simp [mem_sphere_iff_norm, hpnorm]
    have hgp : ∀ t : unitInterval, g t ≠ ⟨p, hpS⟩ := by
      intro t h
      exact hpne (t:ℝ) ⟨t.2.1, t.2.2⟩ (congrArg Subtype.val h)
    exact hhom.trans (nullhomotopic_of_avoids_point g hgp)

/-- The 3-sphere is a simply connected closed 3-manifold: the hypothesis class of the Poincaré
conjecture is nonempty. -/
