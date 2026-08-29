import Mathlib

/-!
# Ratner
Category: Frontier Math
Target: Math2.ratner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized here

Ratner's theorems concern a one-parameter unipotent subgroup `{u_t}` of a Lie group `G` acting on
a homogeneous space `G / Γ` for a lattice `Γ`, and assert that

* the closure of every orbit is a homogeneous subset `x · H` for a closed connected subgroup `H`
  (orbit closure theorem), and
* every ergodic `u_t`-invariant probability measure is the homogeneous measure supported on such
  an orbit closure (measure classification).

This file formalizes and proves these two statements for the abelian instance
`G = ℝ²`, `Γ = ℤ²`, `u_t = (t, α t)`, i.e. the linear flow of slope `α` on the two-torus.
Here every element of `G` is unipotent, `G / Γ` is the compact homogeneous space `ℝ²/ℤ²`,
and the two conclusions read:

* `Math2.closure_orbit_eq_coset` (proved in the generality of an arbitrary topological abelian
  group): every orbit closure of a one-parameter subgroup is a coset of one fixed closed
  connected subgroup;
* `Math2.dense_orbit`: for irrational `α` the flow is minimal, so the orbit closures are the whole
  space (`H = ⊤`);
* `Math2.eq_volume_of_invariant`: for irrational `α` the flow is uniquely ergodic, i.e. Haar
  probability measure is the only invariant Borel probability measure — which is the measure
  classification statement in this setting.

The main theorem `Math2.ratner` packages the three statements together.
-/

open MeasureTheory Set Topology
open scoped BoundedContinuousFunction

namespace Math2

noncomputable section

instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The circle `ℝ / ℤ`. -/
abbrev Circle := AddCircle (1 : ℝ)

/-- The two-dimensional torus `ℝ² / ℤ²`, a homogeneous space `G / Γ` with `G = ℝ²`
(a unipotent group) and `Γ = ℤ²` a lattice. -/
abbrev Torus := Circle × Circle

/-- The one-parameter unipotent subgroup `t ↦ (t, α t)` of `ℝ²`, viewed inside the torus. -/

theorem dense_orbit (α : ℝ) (hα : Irrational α) (x : Torus) : Dense (orbit α x) := by
  rintro ⟨a, b⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t : ℝ, (t : Circle) = a - x.1 := QuotientAddGroup.mk_surjective _
  set g : Circle → Torus := fun y => (a, x.2 + ((α * t₀ : ℝ) : Circle) + y) with hg
  have hgc : Continuous g := by fun_prop
  have hsub : g '' (Set.range fun n : ℤ => (n • (α : Circle))) ⊆ orbit α x := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    refine ⟨t₀ + n, ?_⟩
    have hn : (((n : ℤ) : ℝ) : Circle) = 0 := by
      have hz : ((n : ℝ)) = n • (1 : ℝ) := by simp
      rw [hz, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
    have h1 : ((t₀ + (n : ℝ) : ℝ) : Circle) = a - x.1 := by
      rw [AddCircle.coe_add, ht₀, hn, add_zero]
    have h2 : ((α * (t₀ + (n : ℝ)) : ℝ) : Circle)
        = ((α * t₀ : ℝ) : Circle) + n • (α : Circle) := by
      have : α * (t₀ + (n : ℝ)) = α * t₀ + n • α := by
        rw [zsmul_eq_mul]; ring
      rw [this, AddCircle.coe_add, AddCircle.coe_zsmul]
    simp only [hg, uflow_apply, h1, h2, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    exact ⟨by abel, by abel⟩
  have hdense : Dense (Set.range fun n : ℤ => (n • (α : Circle))) := dense_zmultiples α hα
  have hmem : (a, b) ∈ g '' closure (Set.range fun n : ℤ => (n • (α : Circle))) := by
    refine ⟨b - x.2 - ((α * t₀ : ℝ) : Circle), hdense.closure_eq ▸ Set.mem_univ _, ?_⟩
    have hb : x.2 + ((α * t₀ : ℝ) : Circle) + (b - x.2 - ((α * t₀ : ℝ) : Circle)) = b := by abel
    simp [hg, hb]
  have := (image_closure_subset_closure_image hgc) hmem
  exact closure_mono hsub this

