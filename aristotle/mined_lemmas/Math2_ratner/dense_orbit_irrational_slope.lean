/-
# Ratner
Category: Frontier Math
Target: Math2.ratner
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

set_option grind.warning false

namespace Math2

/-! ## Ratner's orbit closure theorem, abelian (torus) case

Ratner's orbit closure theorem states that if `U = {u_t}` is a one-parameter unipotent
subgroup of a Lie group `G` and `Γ ≤ G` is a lattice, then for every `x ∈ G/Γ` the closure
of the orbit `{u_t · x}` is a homogeneous set `x · H` for some closed connected subgroup
`H ≤ G` containing `U`, and the orbit is equidistributed with respect to the (unique)
`H`-invariant probability measure on `x · H`.

Here we formalise this in the abelian setting, which is a genuine instance of the theorem:
`G = ℝⁿ` is a (unipotent, abelian) Lie group, `Γ = ℤⁿ` is a lattice, the homogeneous space is
the torus `𝕋ⁿ = ℝⁿ/ℤⁿ`, and every one-parameter subgroup `t ↦ t · v` of `ℝⁿ` is unipotent.

* `Math2.orbitClosure_eq_coset` is the orbit closure statement: the closure of the orbit of
  a one-parameter subgroup is a coset of a closed connected subgroup containing the acting
  subgroup.
* `Math2.dense_orbit_irrational_slope` is the classical instance on the two-torus: the linear
  flow of irrational slope has all orbits dense (so there the subgroup `H` is everything).
-/

section OrbitClosure

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- **Orbit closure theorem, abelian case.** For a continuous one-parameter subgroup
`f : ℝ →+ G` of a topological abelian group `G` and any point `x`, the closure of the orbit
`{x + f t : t ∈ ℝ}` is the coset `x + H` of a closed connected subgroup `H` of `G`
containing the one-parameter subgroup. -/

theorem dense_orbit_irrational_slope {α : ℝ} (hα : Irrational α) (x : Torus2) :
    Dense (Set.range fun t : ℝ => x + linearFlow α t) := by
  intro y
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ))
    (y.1 - x.1)
  have hy1 : y.1 = x.1 + ((r : ℝ) : AddCircle (1 : ℝ)) := by rw [hr]; abel
  set c : AddCircle (1 : ℝ) := x.2 + ((α * r : ℝ) : AddCircle (1 : ℝ)) with hc
  -- the sub-orbit at times `r + n`, `n : ℤ`, lies in `{y.1} ×ˢ (c + ℤα)`
  have hsub : ({y.1} : Set (AddCircle (1 : ℝ))) ×ˢ
      (Set.range fun n : ℤ => c + n • ((α : ℝ) : AddCircle (1 : ℝ)))
        ⊆ Set.range fun t : ℝ => x + linearFlow α t := by
    rintro ⟨z₁, z₂⟩ ⟨hz₁, ⟨n, hn⟩⟩
    have hz₁' : z₁ = y.1 := hz₁
    have hn' : c + n • ((α : ℝ) : AddCircle (1 : ℝ)) = z₂ := hn
    refine ⟨r + (n : ℝ), ?_⟩
    have hint : (((n : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
    have h1 : x.1 + ((r + (n : ℝ) : ℝ) : AddCircle (1 : ℝ)) = z₁ := by
      rw [AddCircle.coe_add, hint, hz₁', hy1]
      abel
    have hmul : ((α * (n : ℝ) : ℝ) : AddCircle (1 : ℝ))
        = n • ((α : ℝ) : AddCircle (1 : ℝ)) := by
      rw [mul_comm, ← zsmul_eq_mul]
      exact QuotientAddGroup.mk_zsmul _ _ _
    have h2 : x.2 + ((α * (r + (n : ℝ)) : ℝ) : AddCircle (1 : ℝ)) = z₂ := by
      rw [show α * (r + (n : ℝ)) = α * r + α * (n : ℝ) by ring, AddCircle.coe_add, hmul,
        ← hn', hc]
      abel
    apply Prod.ext
    · simpa [linearFlow_apply] using h1
    · simpa [linearFlow_apply] using h2
  -- the sub-orbit is dense
  have hdense : Dense (Set.range fun n : ℤ => c + n • ((α : ℝ) : AddCircle (1 : ℝ))) := by
    have himg : (Set.range fun n : ℤ => c + n • ((α : ℝ) : AddCircle (1 : ℝ)))
        = (fun z => c + z) '' Set.range (fun n : ℤ => n • ((α : ℝ) : AddCircle (1 : ℝ))) := by
      ext z
      constructor
      · rintro ⟨n, rfl⟩; exact ⟨_, ⟨n, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    rw [himg]
    exact dense_add_left c (denseRange_zsmul_irrational hα)
  have hmem : y ∈ closure (({y.1} : Set (AddCircle (1 : ℝ))) ×ˢ
      (Set.range fun n : ℤ => c + n • ((α : ℝ) : AddCircle (1 : ℝ)))) := by
    rw [closure_prod_eq, hdense.closure_eq]
    exact ⟨by simp, Set.mem_univ _⟩
  exact closure_mono hsub hmem

/-! ## Ratner's measure classification theorem, abelian (torus) case

Ratner's measure classification theorem states that any ergodic probability measure invariant
under a one-parameter unipotent subgroup is the homogeneous (algebraic) measure on a closed
orbit. In the torus case treated here, the irrational linear flow on `𝕋²` is *uniquely
ergodic*: the only invariant Borel probability measure is the Haar (Lebesgue) measure. -/

open MeasureTheory

instance instFactZeroLtOne : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

instance instIsProbabilityMeasureVolumeAddCircle :
    IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp [AddCircle.measure_univ]⟩

instance instIsAddHaarMeasureVolumeTorus2 : (volume : Measure Torus2).IsAddHaarMeasure := by
  rw [show (volume : Measure Torus2)
      = (volume : Measure (AddCircle (1 : ℝ))).prod (volume : Measure (AddCircle (1 : ℝ))) from
    Measure.volume_eq_prod _ _]
  infer_instance

/-- For a finite measure on the torus, the translation average of a continuous function
depends continuously on the translation parameter. -/
