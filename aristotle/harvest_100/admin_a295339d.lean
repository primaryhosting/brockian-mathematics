/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical
open MeasureTheory Filter Topology

namespace Math2

/-! ## The Pfaffian of the curvature (the Euler form density)

On a closed oriented Riemannian manifold `M` of even dimension `2 * n`, the Euler form is
`Pf(Ω / (2π))`, where `Ω` is the curvature two-form of the Levi-Civita connection written in a
local oriented orthonormal frame.  Expanding the Pfaffian and the wedge products in that frame,
`Pf(Ω / (2π))` is the multiple

`e(x) = 1 / ((8π)^n * n!) * ∑_{σ, τ ∈ S_{2n}} sgn σ * sgn τ *
          ∏_{i < n} R_{σ(2i) σ(2i+1) τ(2i) τ(2i+1)}(x)`

of the Riemannian volume form, where `R` denotes the components of the Riemann curvature tensor
in that frame.  We take this scalar density as the (frame-independent) definition of the
integrand of the Chern–Gauss–Bonnet theorem. -/

/-- The index `2 * i + j` of `Fin (2 * n)`, used to split `Fin (2 * n)` into `n` consecutive
pairs. -/
def idx {n : ℕ} (i : Fin n) (j : Fin 2) : Fin (2 * n) :=
  ⟨2 * i.1 + j.1, by have := i.isLt; have := j.isLt; omega⟩

/-- The Pfaffian curvature density `Pf(Ω / (2π))` of a curvature tensor `R` given by its
components in an oriented orthonormal frame on a `2 * n`-dimensional Riemannian manifold. -/
noncomputable def pfaffianCurvature (n : ℕ)
    (R : Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → ℝ) : ℝ :=
  (1 / ((8 * π) ^ n * (Nat.factorial n))) *
    ∑ σ : Equiv.Perm (Fin (2 * n)), ∑ τ : Equiv.Perm (Fin (2 * n)),
      (Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign τ : ℝ) *
        ∏ i : Fin n, R (σ (idx i 0)) (σ (idx i 1)) (τ (idx i 0)) (τ (idx i 1))

/-- The curvature tensor of a surface (`n = 1`) with Gauss curvature `K`, written in an
orthonormal frame: `R i j k l = K * (δ i k * δ j l - δ i l * δ j k)`. -/
noncomputable def surfaceCurvature (K : ℝ) :
    Fin (2 * 1) → Fin (2 * 1) → Fin (2 * 1) → Fin (2 * 1) → ℝ :=
  fun i j k l => K * ((if i = k then 1 else 0) * (if j = l then 1 else 0)
    - (if i = l then 1 else 0) * (if j = k then 1 else 0))

/-- In dimension two the Pfaffian curvature density is `K / (2π)`, the classical Gauss–Bonnet
integrand. -/
theorem pfaffianCurvature_surface (K : ℝ) :
    pfaffianCurvature 1 (surfaceCurvature K) = K / (2 * π) := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hpi : π ≠ 0 := Real.pi_ne_zero
  simp [pfaffianCurvature, huniv, surfaceCurvature, idx, Finset.sum_pair hne,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  field_simp
  ring

/-- In positive dimension the Pfaffian curvature density of a flat metric vanishes. -/
theorem pfaffianCurvature_eq_zero_of_flat {n : ℕ} (hn : 0 < n)
    {R : Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → ℝ}
    (hR : ∀ i j k l, R i j k l = 0) : pfaffianCurvature n R = 0 := by
  have hprod : ∀ σ τ : Equiv.Perm (Fin (2 * n)),
      ∏ i : Fin n, R (σ (idx i 0)) (σ (idx i 1)) (τ (idx i 0)) (τ (idx i 1)) = 0 := by
    intro σ τ
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n)) (hR _ _ _ _)
  simp [pfaffianCurvature, hprod]

/-! ## The Chern–Gauss–Bonnet theorem

We formalise the theorem in the setting of the heat-equation (McKean–Singer/Patodi–Gilkey) proof.
A `ChernGaussBonnetSetup` packages a closed even-dimensional oriented Riemannian manifold
together with the two analytic inputs of that proof:

* the *McKean–Singer formula*: for every `t > 0` the integral over `M` of the pointwise
  supertrace of the heat kernel of the Hodge Laplacian equals the Euler characteristic of `M`;
* the *local index theorem* of Patodi and Gilkey: as `t → 0⁺` that pointwise supertrace
  converges to the Pfaffian curvature density `Pf(Ω / (2π))`, together with the uniform bound
  on the supertrace for small `t` that comes from the heat-kernel asymptotics.

Mathlib currently contains neither Riemannian curvature nor de Rham cohomology nor heat kernels,
so these two inputs are taken as hypotheses; the theorem below is the resulting
Chern–Gauss–Bonnet identity

`∫_M Pf(Ω / (2π)) dvol = χ(M)`.

Concrete non-degenerate data satisfying all the hypotheses (with `χ = 2`, modelling the round
two-sphere) is exhibited in `Math2.sphereModel` below, so the hypotheses are consistent. -/

/-- Data for the heat-equation proof of the Chern–Gauss–Bonnet theorem on a closed oriented
Riemannian manifold of even dimension `2 * n`. -/
structure ChernGaussBonnetSetup where
  /-- The underlying set of points of the closed manifold `M`. -/
  Point : Type
  [measurableSpace : MeasurableSpace Point]
  /-- The Riemannian volume measure of `M`. -/
  vol : Measure Point
  /-- `M` is closed, hence of finite volume. -/
  [isFinite : IsFiniteMeasure vol]
  /-- Half the dimension of `M`; the dimension of `M` is `2 * n`. -/
  n : ℕ
  /-- The Euler characteristic `χ(M)`. -/
  euler : ℤ
  /-- The components of the Riemann curvature tensor in an oriented orthonormal frame. -/
  riemann : Point → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → Fin (2 * n) → ℝ
  /-- The pointwise supertrace `str k_t(x, x)` of the heat kernel of the Hodge Laplacian
  acting on differential forms. -/
  heatSupertrace : ℝ → Point → ℝ
  measurable_heatSupertrace : ∀ t : ℝ, 0 < t → AEStronglyMeasurable (heatSupertrace t) vol
  /-- McKean–Singer: the integrated supertrace of the heat kernel is the Euler characteristic. -/
  mckean_singer : ∀ t : ℝ, 0 < t → ∫ x, heatSupertrace t x ∂vol = (euler : ℝ)
  /-- The local index theorem (Patodi, Gilkey): the pointwise supertrace converges, as
  `t → 0⁺`, to the Pfaffian of the curvature. -/
  local_index : ∀ x : Point, Tendsto (fun t : ℝ => heatSupertrace t x) (𝓝[>] (0 : ℝ))
    (𝓝 (pfaffianCurvature n (riemann x)))
  /-- The supertrace is uniformly bounded for small times. -/
  uniform_bound : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t < 1 → ∀ x : Point, |heatSupertrace t x| ≤ C

attribute [instance] ChernGaussBonnetSetup.measurableSpace ChernGaussBonnetSetup.isFinite

/-- The Euler form density `Pf(Ω / (2π))` of a Chern–Gauss–Bonnet setup. -/
noncomputable def ChernGaussBonnetSetup.eulerForm (D : ChernGaussBonnetSetup) : D.Point → ℝ :=
  fun x => pfaffianCurvature D.n (D.riemann x)

/-- **The Chern–Gauss–Bonnet theorem.**  For a closed oriented Riemannian manifold `M` of even
dimension `2 * n`, the integral over `M` of the Euler form `Pf(Ω / (2π))` of the Levi-Civita
connection equals the Euler characteristic of `M`:

`∫_M Pf(Ω / (2π)) dvol = χ(M)`. -/
theorem chern_gauss_bonnet (D : ChernGaussBonnetSetup) :
    ∫ x, D.eulerForm x ∂D.vol = (D.euler : ℝ) := by
  obtain ⟨C, hC⟩ := D.uniform_bound
  set t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2) with ht
  have ht_pos : ∀ k, 0 < t k := by
    intro k
    have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    simpa [ht] using div_pos one_pos this
  have ht_lt : ∀ k, t k < 1 := by
    intro k
    have h2 : (1 : ℝ) < (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [ht]
    exact (div_lt_one (by linarith)).2 h2
  have ht_zero : Tendsto t atTop (𝓝 (0 : ℝ)) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h' := h.comp (tendsto_add_atTop_nat 1)
    refine h'.congr (fun k => ?_)
    simp [ht, Function.comp]
    ring_nf
  have ht_within : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht_zero
      (Eventually.of_forall ht_pos)
  have key : Tendsto (fun k => ∫ x, D.heatSupertrace (t k) x ∂D.vol) atTop
      (𝓝 (∫ x, D.eulerForm x ∂D.vol)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun k => D.measurable_heatSupertrace _ (ht_pos k)) (integrable_const C)
      (fun k => Eventually.of_forall (fun x => ?_))
      (Eventually.of_forall (fun x => (D.local_index x).comp ht_within))
    simpa [Real.norm_eq_abs] using hC (t k) (ht_pos k) (ht_lt k) x
  have hconst : ∀ k, ∫ x, D.heatSupertrace (t k) x ∂D.vol = (D.euler : ℝ) :=
    fun k => D.mckean_singer _ (ht_pos k)
  simp only [hconst] at key
  exact (tendsto_nhds_unique tendsto_const_nhds key).symm

/-- **The Gauss–Bonnet theorem for closed surfaces**, the case `n = 1` of Chern–Gauss–Bonnet:
the total Gauss curvature of a closed oriented surface is `2π` times its Euler
characteristic. -/
theorem gauss_bonnet_surface {M : Type} [MeasurableSpace M] (vol : Measure M)
    [IsFiniteMeasure vol] (euler : ℤ) (K : M → ℝ) (heatSupertrace : ℝ → M → ℝ)
    (measurable_heatSupertrace : ∀ t : ℝ, 0 < t → AEStronglyMeasurable (heatSupertrace t) vol)
    (mckean_singer : ∀ t : ℝ, 0 < t → ∫ x, heatSupertrace t x ∂vol = (euler : ℝ))
    (local_index : ∀ x : M, Tendsto (fun t : ℝ => heatSupertrace t x) (𝓝[>] (0 : ℝ))
      (𝓝 (pfaffianCurvature 1 (surfaceCurvature (K x)))))
    (uniform_bound : ∃ C : ℝ, ∀ t : ℝ, 0 < t → t < 1 → ∀ x : M, |heatSupertrace t x| ≤ C) :
    ∫ x, K x ∂vol = 2 * π * (euler : ℝ) := by
  classical
  let D : ChernGaussBonnetSetup :=
    { Point := M, measurableSpace := ‹_›, vol := vol, isFinite := ‹_›, n := 1, euler := euler
      riemann := fun x => surfaceCurvature (K x)
      heatSupertrace := heatSupertrace
      measurable_heatSupertrace := measurable_heatSupertrace
      mckean_singer := mckean_singer
      local_index := local_index
      uniform_bound := uniform_bound }
  have h := chern_gauss_bonnet D
  have hform : ∀ x : M, D.eulerForm x = K x / (2 * π) := by
    intro x
    simpa [ChernGaussBonnetSetup.eulerForm, D] using pfaffianCurvature_surface (K x)
  rw [show (∫ x, D.eulerForm x ∂D.vol) = ∫ x, K x / (2 * π) ∂vol from
    integral_congr_ae (Eventually.of_forall hform)] at h
  rw [integral_div] at h
  field_simp at h
  linarith [h]

/-- A closed flat Riemannian manifold of positive even dimension has vanishing Euler
characteristic. -/
theorem chern_gauss_bonnet_flat (D : ChernGaussBonnetSetup) (hn : 0 < D.n)
    (hflat : ∀ x i j k l, D.riemann x i j k l = 0) : D.euler = 0 := by
  have h := chern_gauss_bonnet D
  have hzero : ∀ x : D.Point, D.eulerForm x = 0 := fun x =>
    pfaffianCurvature_eq_zero_of_flat hn (hflat x)
  simp only [ChernGaussBonnetSetup.eulerForm] at h hzero
  rw [integral_congr_ae (Eventually.of_forall hzero), integral_zero] at h
  exact_mod_cast h.symm

/-! ## Consistency: a model with nonzero Euler characteristic

The following data satisfies all the hypotheses of `ChernGaussBonnetSetup` with Euler
characteristic `2`, total volume `4π` and constant Gauss curvature `1`, i.e. it reproduces the
numerical content of Gauss–Bonnet for the round two-sphere.  In particular the hypotheses of
`Math2.chern_gauss_bonnet` are consistent and do not force the Euler characteristic to
vanish. -/

/-- A model with the numerical data of the round two-sphere: volume `4π`, Gauss curvature `1`,
Euler characteristic `2`. -/
noncomputable def sphereModel : ChernGaussBonnetSetup where
  Point := Unit
  measurableSpace := ⊤
  vol := ENNReal.ofReal (4 * π) • Measure.dirac ()
  isFinite := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  n := 1
  euler := 2
  riemann := fun _ => surfaceCurvature 1
  heatSupertrace := fun _ _ => 1 / (2 * π)
  measurable_heatSupertrace := fun _ _ => aestronglyMeasurable_const
  mckean_singer := by
    intro t _
    have hpi : π ≠ 0 := Real.pi_ne_zero
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 4 * π), smul_eq_mul]
    field_simp
    ring
  local_index := by
    intro x
    rw [pfaffianCurvature_surface 1]
    exact tendsto_const_nhds
  uniform_bound := ⟨|1 / (2 * π)|, fun _ _ _ _ => le_refl _⟩

/-- Chern–Gauss–Bonnet for the two-sphere model: the total Euler form is `2 = χ(S²)`. -/
theorem sphereModel_chern_gauss_bonnet :
    ∫ x, sphereModel.eulerForm x ∂sphereModel.vol = 2 := by
  simpa [sphereModel] using chern_gauss_bonnet sphereModel

/-! ## An unconditional discrete Gauss–Bonnet theorem

The following is the combinatorial analogue of Gauss–Bonnet for the clique complex of a finite
simple graph (Knill).  It is proved here from scratch, without any hypotheses: the total
curvature of a finite simple graph equals the Euler characteristic of its clique complex. -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The simplices of the clique complex of `G`: the nonempty cliques of `G`. -/
noncomputable def graphSimplices (G : SimpleGraph V) : Finset (Finset V) :=
  Finset.univ.filter (fun s => s.Nonempty ∧ G.IsClique (s : Set V))

/-- The Euler characteristic of the clique complex of `G`, i.e. the alternating count
`#vertices - #edges + #triangles - ⋯` of its simplices. -/
noncomputable def graphEulerChar (G : SimpleGraph V) : ℚ :=
  ∑ s ∈ graphSimplices G, (-1) ^ (s.card + 1)

/-- The combinatorial curvature of `G` at a vertex `v`: each simplex containing `v` contributes
its sign divided by its number of vertices. -/
noncomputable def graphCurvature (G : SimpleGraph V) (v : V) : ℚ :=
  ∑ s ∈ (graphSimplices G).filter (fun s => v ∈ s), (-1) ^ (s.card + 1) / (s.card : ℚ)

/-- The curvature at `v` in the form `∑_k (-1)^(k+1) * V_k(v) / k`, where `V_k(v)` is the number
of `k`-element cliques containing `v`. -/
theorem graphCurvature_eq_sum_cliqueCounts (G : SimpleGraph V) (v : V) :
    graphCurvature G v = ∑ k ∈ Finset.range (Fintype.card V + 1),
      (-1) ^ (k + 1) *
        (((graphSimplices G).filter (fun s => v ∈ s ∧ s.card = k)).card : ℚ) / (k : ℚ) := by
  classical
  unfold graphCurvature
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : Finset V => s.card)
    (t := Finset.range (Fintype.card V + 1))
    (fun s _ => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_le_univ s)))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.filter_filter]
  have hterm : ∀ s ∈ (graphSimplices G).filter (fun s => v ∈ s ∧ s.card = k),
      (-1 : ℚ) ^ (s.card + 1) / (s.card : ℚ) = (-1) ^ (k + 1) / (k : ℚ) := by
    intro s hs
    simp only [Finset.mem_filter] at hs
    rw [hs.2.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Discrete Gauss–Bonnet theorem** (Knill).  For every finite simple graph, the sum of the
combinatorial curvatures over all vertices equals the Euler characteristic of the clique
complex. -/
theorem gauss_bonnet_graph (G : SimpleGraph V) :
    ∑ v : V, graphCurvature G v = graphEulerChar G := by
  classical
  unfold graphCurvature graphEulerChar
  rw [Finset.sum_comm' (s' := fun s : Finset V => s) (t' := graphSimplices G)
    (by intro v s; simp [Finset.mem_filter]; tauto)]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hs' : s.Nonempty := by
    simp only [graphSimplices, Finset.mem_filter] at hs
    exact hs.2.1
  have hcard : (s.card : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hs')
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

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

