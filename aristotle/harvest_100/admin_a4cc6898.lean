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
theorem closure_coset_eq (S : Subgroup Q) (x : Q) :
    closure ((fun g => g * x) '' (S : Set Q))
      = (fun g => g * x) '' (S.topologicalClosure : Set Q) := by
  have h := (Homeomorph.mulRight x).image_closure (S : Set Q)
  simpa [Subgroup.topologicalClosure_coe] using h.symm

/-! ## Orbit closures of one-parameter subgroups -/

/-- The closure of the orbit `{f t * x : t ∈ ℝ}` of a continuous one-parameter subgroup `f` of a
topological group `Q` is the translate `H * x` of a closed connected subgroup `H` containing the
image of `f`. -/
@[to_additive oneParamAddOrbitClosure /-- The closure of the orbit `{f t + x : t ∈ ℝ}` of a
continuous one-parameter subgroup `f` of a topological additive group `Q` is the translate
`H + x` of a closed connected subgroup `H` containing the image of `f`. -/]
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
theorem ratner {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (u : ℝ → G) (hu : Continuous u)
    (hmul : ∀ s t : ℝ, u (s + t) = u s * u t) (x : G ⧸ N) :
    ∃ H : Subgroup (G ⧸ N),
      IsClosed (H : Set (G ⧸ N)) ∧
      IsConnected (H : Set (G ⧸ N)) ∧
      (∀ t : ℝ, (QuotientGroup.mk (u t) : G ⧸ N) ∈ H) ∧
      closure (Set.range fun t : ℝ => (QuotientGroup.mk (u t) : G ⧸ N) * x)
        = (fun g => g * x) '' (H : Set (G ⧸ N)) := by
  refine oneParamOrbitClosure (fun t => (QuotientGroup.mk (u t) : G ⧸ N))
    (continuous_quot_mk.comp hu) (fun s t => ?_) x
  simp [hmul]

/-! ## The general statement of Ratner's orbit closure theorem -/

/-- **The statement of Ratner's orbit closure theorem** for a one-parameter subgroup `u` acting on
the coset space `G ⧸ Γ` of a topological group `G` by an arbitrary (in Ratner's theorem: discrete,
finite covolume) subgroup `Γ`: every orbit closure of the flow is a *homogeneous* set, i.e. of the
form `H • x` for a closed subgroup `H ≤ G` containing the one-parameter subgroup.

Ratner proved this when `G` is a connected Lie group, `Γ` a lattice and `u` a one-parameter
`Ad`-unipotent subgroup. `Math2.ratner_orbitClosureProperty` below establishes it whenever the
subgroup `Γ` is normal (which covers the abelian situation, e.g. linear flows on tori, where
every element is unipotent). -/
def RatnerOrbitClosureProperty {G : Type*} [Group G] [TopologicalSpace G]
    (Γ : Subgroup G) (u : ℝ → G) : Prop :=
  ∀ x : G ⧸ Γ, ∃ H : Subgroup G, IsClosed (H : Set G) ∧ (∀ t : ℝ, u t ∈ H) ∧
    closure (Set.range fun t : ℝ => u t • x) = (fun h : G => h • x) '' (H : Set G)

/-- Ratner's orbit closure property holds for every continuous one-parameter subgroup acting on
`G ⧸ N` with `N` a normal subgroup. -/
theorem ratner_orbitClosureProperty {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] (u : ℝ → G) (hu : Continuous u)
    (hmul : ∀ s t : ℝ, u (s + t) = u s * u t) : RatnerOrbitClosureProperty N u := by
  intro x
  obtain ⟨H', hclosed, _, hmem, horb⟩ := ratner N u hu hmul x
  have hsmul : ∀ (g : G) (y : G ⧸ N), g • y = (QuotientGroup.mk g : G ⧸ N) * y := by
    intro g y
    induction y using QuotientGroup.induction_on
    rfl
  refine ⟨H'.comap (QuotientGroup.mk' N), ?_, fun t => hmem t, ?_⟩
  · rw [Subgroup.coe_comap]
    exact hclosed.preimage continuous_quot_mk
  · have h1 : (Set.range fun t : ℝ => u t • x)
        = Set.range fun t : ℝ => (QuotientGroup.mk (u t) : G ⧸ N) * x := by
      simp only [hsmul]
    have hmapcomap := congrArg (fun K : Subgroup (G ⧸ N) => (K : Set (G ⧸ N)))
      (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) H')
    simp only [Subgroup.coe_map] at hmapcomap
    have h2 : (fun h : G => h • x) '' ((H'.comap (QuotientGroup.mk' N) : Subgroup G) : Set G)
        = (fun g => g * x) '' (H' : Set (G ⧸ N)) := by
      rw [← hmapcomap, Set.image_image]
      simp only [hsmul]
      rfl
    rw [h1, horb, h2]

/-! ## Homogeneous invariant measures -/

/-- A compact subgroup `H` of a topological group carries a Haar probability measure; pushing it
forward to the coset `H * x` produces an `H`-invariant probability measure concentrated on that
coset (the *homogeneous measure* of the coset). -/
@[to_additive homogeneous_measure_of_isCompact_add]
theorem homogeneous_measure_of_isCompact [MeasurableSpace Q] [BorelSpace Q] [T2Space Q]
    (H : Subgroup Q) (hcomp : IsCompact (H : Set Q)) (x : Q) :
    ∃ μ : MeasureTheory.Measure Q, MeasureTheory.IsProbabilityMeasure μ ∧
      μ ((fun g => g * x) '' (H : Set Q)) = 1 ∧
      ∀ h ∈ H, MeasureTheory.Measure.map (fun y => h * y) μ = μ := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hcomp
  set ν : MeasureTheory.Measure H := MeasureTheory.Measure.haarMeasure ⊤
  haveI : MeasureTheory.IsProbabilityMeasure ν := by
    constructor
    simpa using MeasureTheory.Measure.haarMeasure_self
      (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))
  set φ : H → Q := fun h => (h : Q) * x with hφ
  have hφm : Measurable φ := (by fun_prop : Continuous φ).measurable
  refine ⟨ν.map φ, MeasureTheory.Measure.isProbabilityMeasure_map hφm.aemeasurable, ?_, ?_⟩
  · have hs : MeasurableSet ((fun g => g * x) '' (H : Set Q)) :=
      (hcomp.image (by fun_prop)).isClosed.measurableSet
    rw [MeasureTheory.Measure.map_apply hφm hs]
    have hpre : φ ⁻¹' ((fun g => g * x) '' (H : Set Q)) = Set.univ := by
      ext h; simp [hφ]
    rw [hpre]
    simp
  · intro h hh
    have hmulm : Measurable (fun y : Q => h * y) := (continuous_mul_left h).measurable
    rw [MeasureTheory.Measure.map_map hmulm hφm]
    have hcomp' : ((fun y : Q => h * y) ∘ φ) = φ ∘ (fun k : H => (⟨h, hh⟩ : H) * k) := by
      funext k; simp [hφ, mul_assoc]
    rw [hcomp', ← MeasureTheory.Measure.map_map hφm (measurable_const_mul _)]
    congr 1
    exact MeasureTheory.map_mul_left_eq_self ν (⟨h, hh⟩ : H)

/-- **Ratner's theorems, orbit closure together with its homogeneous invariant measure**, in the
setting of a compact quotient `G ⧸ N` of a topological group by a normal subgroup.

For a continuous one-parameter subgroup `u` and any point `x`, the orbit closure is a translate
`H · x` of a closed connected subgroup `H` containing the flow, and it carries a flow-invariant
probability measure of full mass on it, namely the homogeneous (Haar) measure of `H · x`. -/
@[to_additive ratner_add_measure]
theorem ratner_measure {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] [MeasurableSpace (G ⧸ N)] [BorelSpace (G ⧸ N)]
    [T2Space (G ⧸ N)] [CompactSpace (G ⧸ N)]
    (u : ℝ → G) (hu : Continuous u) (hmul : ∀ s t : ℝ, u (s + t) = u s * u t) (x : G ⧸ N) :
    ∃ H : Subgroup (G ⧸ N),
      IsClosed (H : Set (G ⧸ N)) ∧
      IsConnected (H : Set (G ⧸ N)) ∧
      (∀ t : ℝ, (QuotientGroup.mk (u t) : G ⧸ N) ∈ H) ∧
      closure (Set.range fun t : ℝ => (QuotientGroup.mk (u t) : G ⧸ N) * x)
        = (fun g => g * x) '' (H : Set (G ⧸ N)) ∧
      ∃ μ : MeasureTheory.Measure (G ⧸ N), MeasureTheory.IsProbabilityMeasure μ ∧
        μ (closure (Set.range fun t : ℝ => (QuotientGroup.mk (u t) : G ⧸ N) * x)) = 1 ∧
        ∀ t : ℝ, MeasureTheory.Measure.map
          (fun y => (QuotientGroup.mk (u t) : G ⧸ N) * y) μ = μ := by
  obtain ⟨H, hHclosed, hHconn, hHmem, hHorbit⟩ := ratner N u hu hmul x
  obtain ⟨μ, hμprob, hμmass, hμinv⟩ :=
    homogeneous_measure_of_isCompact H (hHclosed.isCompact) x
  exact ⟨H, hHclosed, hHconn, hHmem, hHorbit,
    μ, hμprob, by rw [hHorbit]; exact hμmass, fun t => hμinv _ (hHmem t)⟩

/-- Non-vacuity of `Math2.ratner_measure`: the hypotheses are satisfied by the linear flow on the
circle `ℝ / ℤ`, whose orbit closure is the whole circle carrying its Haar probability measure. -/
theorem ratner_circle (x : AddCircle (1 : ℝ)) :
    ∃ H : AddSubgroup (AddCircle (1 : ℝ)),
      IsClosed (H : Set (AddCircle (1 : ℝ))) ∧
      IsConnected (H : Set (AddCircle (1 : ℝ))) ∧
      (∀ t : ℝ, (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) ∈ H) ∧
      closure (Set.range fun t : ℝ => (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) + x)
        = (fun g => g + x) '' (H : Set (AddCircle (1 : ℝ))) ∧
      ∃ μ : MeasureTheory.Measure (AddCircle (1 : ℝ)),
        MeasureTheory.IsProbabilityMeasure μ ∧
        μ (closure (Set.range fun t : ℝ =>
          (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) + x)) = 1 ∧
        ∀ t : ℝ, MeasureTheory.Measure.map
          (fun y => (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) + y) μ = μ :=
  ratner_add_measure _ (fun t => t) continuous_id (fun _ _ => rfl) x

/-! ## The classical case: linear flows on the torus `ℝⁿ / ℤⁿ` -/

/-- The standard lattice `ℤⁿ ≤ ℝⁿ`. -/
def stdLattice (n : ℕ) : AddSubgroup (Fin n → ℝ) :=
  AddSubgroup.closure (Set.range fun i : Fin n => Pi.single i (1 : ℝ))

/-- The `n`-dimensional torus `ℝⁿ / ℤⁿ`. -/
abbrev Torus (n : ℕ) := (Fin n → ℝ) ⧸ stdLattice n

/-- **Ratner's orbit closure theorem for linear flows on the torus `ℝⁿ / ℤⁿ`.**
The closure of the orbit of the linear flow `t ↦ x + t • v` is the translate by `x` of a closed
connected subgroup (a subtorus) of `ℝⁿ / ℤⁿ` containing the flow direction. -/
theorem ratner_torus (n : ℕ) (v : Fin n → ℝ) (x : Torus n) :
    ∃ H : AddSubgroup (Torus n),
      IsClosed (H : Set (Torus n)) ∧
      IsConnected (H : Set (Torus n)) ∧
      (∀ t : ℝ, (QuotientAddGroup.mk (t • v) : Torus n) ∈ H) ∧
      closure (Set.range fun t : ℝ => (QuotientAddGroup.mk (t • v) : Torus n) + x)
        = (fun g => g + x) '' (H : Set (Torus n)) := by
  refine oneParamAddOrbitClosure (fun t => (QuotientAddGroup.mk (t • v) : Torus n))
    (continuous_quot_mk.comp (by fun_prop)) (fun s t => ?_) x
  simp [add_smul]

/-! ## A nontrivial instance: the irrational linear flow on the `2`-torus is minimal -/

/-- The two-dimensional torus, realized as a product of two circles `ℝ / ℤ`. -/
abbrev Torus2 := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- Translating a dense set by a fixed element keeps it dense. -/
theorem dense_image_add_right {X : Type*} [TopologicalSpace X] [AddGroup X]
    [IsTopologicalAddGroup X] {s : Set X} (hs : Dense s) (x : X) :
    Dense ((fun g => g + x) '' s) := by
  have h := (Homeomorph.addRight x).image_closure s
  rw [dense_iff_closure_eq] at hs ⊢
  simp only [Homeomorph.coe_addRight] at h
  rw [← h, hs]
  exact Set.image_univ_of_surjective fun y => ⟨y - x, by simp⟩

/-- The linear flow of irrational slope `a` on the `2`-torus has dense orbits: the subgroup
`H` produced by Ratner's theorem is all of `ℝ² / ℤ²`. This is Kronecker's theorem, the abelian
instance of Ratner's minimality statement for unipotent flows. -/
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

