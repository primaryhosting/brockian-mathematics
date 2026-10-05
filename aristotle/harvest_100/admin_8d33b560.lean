import Mathlib

/-!
# Gauss–Bonnet (the `n = 1` case of Chern–Gauss–Bonnet) for the 2-torus

This file contains a *smooth* instance of the Chern–Gauss–Bonnet theorem, complementing the
combinatorial theorem `Math2.chern_gauss_bonnet` in `RequestProject.Main`.

For a closed oriented surface `M` the Chern–Gauss–Bonnet theorem reads
`∫_M K dA = 2π χ(M)`.  We prove this for the closed even-dimensional manifold
`T² = ℝ²/ℤ²` equipped with an *arbitrary* conformal metric `e^{2u}(dx² + dy²)`, where `u` is
any doubly periodic potential with enough regularity.  For such a metric the Gauss curvature
is `K = -e^{-2u} Δu` and the area density is `e^{2u}`, so the total curvature is `-∫∫ Δu`,
which vanishes by periodicity — in agreement with `χ(T²) = 0`.
-/

namespace Math2.Torus

open MeasureTheory

/-- Partial derivative in the first variable. -/
noncomputable def px (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y => deriv (fun s => u s y) x

/-- Partial derivative in the second variable. -/
noncomputable def py (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y => deriv (fun t => u x t) y

/-- The Gauss curvature of the conformal metric `e^{2u}(dx² + dy²)` on the plane,
`K = -e^{-2u} (u_xx + u_yy)`. -/
noncomputable def gaussCurvature (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  -Real.exp (-(2 * u x y)) * (px (px u) x y + py (py u) x y)

/-- The area density of the conformal metric `e^{2u}(dx² + dy²)`, i.e. `dA = e^{2u} dx dy`. -/
noncomputable def areaDensity (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := Real.exp (2 * u x y)

/-- The Euler characteristic of the closed surface `T² = ℝ²/ℤ²`, which is `0`. -/
def torusEulerChar : ℤ := 0

/-- Regularity and periodicity assumptions on the conformal potential `u`: it is `ℤ²`-periodic
(hence defines a metric on the torus `T² = ℝ²/ℤ²`) and has continuous second partial
derivatives.  Every smooth doubly periodic function satisfies these. -/
structure IsPotential (u : ℝ → ℝ → ℝ) : Prop where
  /-- Periodicity in the first variable. -/
  periodic_fst : ∀ x y, u (x + 1) y = u x y
  /-- Periodicity in the second variable. -/
  periodic_snd : ∀ x y, u x (y + 1) = u x y
  /-- Differentiability in the first variable. -/
  diff_fst : ∀ y, Differentiable ℝ fun s => u s y
  /-- Differentiability in the second variable. -/
  diff_snd : ∀ x, Differentiable ℝ fun t => u x t
  /-- Twice differentiability in the first variable. -/
  diff_fst_fst : ∀ y, Differentiable ℝ fun s => px u s y
  /-- Twice differentiability in the second variable. -/
  diff_snd_snd : ∀ x, Differentiable ℝ fun t => py u x t
  /-- Joint continuity of `u_xx`. -/
  cont_fst_fst : Continuous fun p : ℝ × ℝ => px (px u) p.1 p.2
  /-- Joint continuity of `u_yy`. -/
  cont_snd_snd : Continuous fun p : ℝ × ℝ => py (py u) p.1 p.2

variable {u : ℝ → ℝ → ℝ}

lemma IsPotential.px_periodic (hu : IsPotential u) (x y : ℝ) : px u (x + 1) y = px u x y := by
  have h : (fun s => u (s + 1) y) = fun s => u s y := funext fun s => hu.periodic_fst s y
  have := deriv_comp_add_const (fun s => u s y) 1 x
  rw [h] at this
  exact this.symm

lemma IsPotential.py_periodic (hu : IsPotential u) (x y : ℝ) : py u x (y + 1) = py u x y := by
  have h : (fun t => u x (t + 1)) = fun t => u x t := funext fun t => hu.periodic_snd x t
  have := deriv_comp_add_const (fun t => u x t) 1 y
  rw [h] at this
  exact this.symm

lemma IsPotential.integral_pyy (hu : IsPotential u) (x : ℝ) :
    ∫ y in (0 : ℝ)..1, py (py u) x y = 0 := by
  have hcont : Continuous fun t => py (py u) x t :=
    hu.cont_snd_snd.comp (continuous_const.prodMk continuous_id)
  have hFTC : ∫ y in (0 : ℝ)..1, deriv (fun t => py u x t) y = py u x 1 - py u x 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun t _ => (hu.diff_snd_snd x) t)
      (hcont.intervalIntegrable 0 1)
  have hper : py u x 1 = py u x 0 := by
    have := hu.py_periodic x 0
    simpa using this
  rw [show (fun y => py (py u) x y) = fun y => deriv (fun t => py u x t) y from rfl]
  rw [hFTC, hper, sub_self]

lemma IsPotential.integral_pxx (hu : IsPotential u) (y : ℝ) :
    ∫ x in (0 : ℝ)..1, px (px u) x y = 0 := by
  have hcont : Continuous fun s => px (px u) s y :=
    hu.cont_fst_fst.comp (continuous_id.prodMk continuous_const)
  have hFTC : ∫ x in (0 : ℝ)..1, deriv (fun s => px u s y) x = px u 1 y - px u 0 y :=
    intervalIntegral.integral_deriv_eq_sub (fun s _ => (hu.diff_fst_fst y) s)
      (hcont.intervalIntegrable 0 1)
  have hper : px u 1 y = px u 0 y := by
    have := hu.px_periodic 0 y
    simpa using this
  rw [show (fun x => px (px u) x y) = fun x => deriv (fun s => px u s y) x from rfl]
  rw [hFTC, hper, sub_self]

lemma IsPotential.integrableOn_pxx (hu : IsPotential u) :
    Integrable (Function.uncurry fun x y => px (px u) x y)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  refine MeasureTheory.IntegrableOn.mono_set
    (t := Set.Icc ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (1 : ℝ))) ?_ ?_
  · exact (hu.cont_fst_fst).integrableOn_Icc
  · rw [← Set.Icc_prod_Icc]
    exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self

lemma IsPotential.integral_integral_pxx (hu : IsPotential u) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, px (px u) x y = 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun x y => px (px u) x y) hu.integrableOn_pxx
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hswap ⊢
  rw [hswap]
  have : ∀ y : ℝ, ∫ x in Set.Ioc (0 : ℝ) 1, px (px u) x y = 0 := by
    intro y
    have := hu.integral_pxx y
    rwa [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at this
  simp [this]

/-- **Gauss–Bonnet for the 2-torus.**  For every conformal metric `e^{2u}(dx² + dy²)` on the
closed surface `T² = ℝ²/ℤ²` (equivalently, every doubly periodic potential `u`), the total
Gauss curvature equals `2π χ(T²) = 0`. -/
theorem gauss_bonnet_conformal_torus (hu : IsPotential u) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, gaussCurvature u x y * areaDensity u x y)
      = 2 * Real.pi * (torusEulerChar : ℝ) := by
  have hpt : ∀ x y : ℝ, gaussCurvature u x y * areaDensity u x y
      = -(px (px u) x y) - py (py u) x y := by
    intro x y
    have h : Real.exp (-(2 * u x y)) * Real.exp (2 * u x y) = 1 := by
      rw [← Real.exp_add]; simp
    simp only [gaussCurvature, areaDensity]
    linear_combination (-(px (px u) x y + py (py u) x y)) * h
  have hinner : ∀ x : ℝ,
      (∫ y in (0 : ℝ)..1, gaussCurvature u x y * areaDensity u x y)
        = ∫ y in (0 : ℝ)..1, -(px (px u) x y) := by
    intro x
    have hc1 : Continuous fun t => -(px (px u) x t) :=
      (hu.cont_fst_fst.comp (continuous_const.prodMk continuous_id)).neg
    have hc2 : Continuous fun t => py (py u) x t :=
      hu.cont_snd_snd.comp (continuous_const.prodMk continuous_id)
    calc (∫ y in (0 : ℝ)..1, gaussCurvature u x y * areaDensity u x y)
        = ∫ y in (0 : ℝ)..1, (-(px (px u) x y) + -(py (py u) x y)) := by
          refine intervalIntegral.integral_congr ?_
          intro y _
          show gaussCurvature u x y * areaDensity u x y
            = -(px (px u) x y) + -(py (py u) x y)
          rw [hpt x y]; ring
      _ = (∫ y in (0 : ℝ)..1, -(px (px u) x y)) + ∫ y in (0 : ℝ)..1, -(py (py u) x y) :=
          intervalIntegral.integral_add (hc1.intervalIntegrable 0 1)
            (hc2.neg.intervalIntegrable 0 1)
      _ = ∫ y in (0 : ℝ)..1, -(px (px u) x y) := by
          have hzero : (∫ y in (0 : ℝ)..1, -(py (py u) x y)) = 0 := by
            rw [intervalIntegral.integral_neg, hu.integral_pyy x, neg_zero]
          rw [hzero, add_zero]
  rw [intervalIntegral.integral_congr (fun x _ => hinner x)]
  simp only [intervalIntegral.integral_neg]
  rw [hu.integral_integral_pxx]
  simp [torusEulerChar]

/-! ## The hypotheses are satisfiable -/

/-- A constant potential (a flat metric on the torus) satisfies the hypotheses. -/
theorem isPotential_const (c : ℝ) : IsPotential (fun _ _ => c) := by
  refine ⟨fun x y => rfl, fun x y => rfl, fun y => differentiable_const c,
    fun x => differentiable_const c, ?_, ?_, ?_, ?_⟩ <;>
    simp only [px, py, deriv_const'] <;>
    simp [continuous_const]

private lemma deriv_cos_linear (a x : ℝ) :
    deriv (fun s => Real.cos (a * s)) x = -Real.sin (a * x) * a :=
  ((Real.hasDerivAt_cos (a * x)).comp x (by simpa using (hasDerivAt_id x).const_mul a)).deriv

/-- A genuinely curved conformal metric on the torus, with potential
`u(x, y) = cos (2πx)`. -/
noncomputable def cosPotential : ℝ → ℝ → ℝ := fun x _ => Real.cos (2 * Real.pi * x)

private lemma px_cosPotential :
    px cosPotential = fun x _ => -Real.sin (2 * Real.pi * x) * (2 * Real.pi) := by
  funext x y
  exact deriv_cos_linear (2 * Real.pi) x

private lemma py_cosPotential : py cosPotential = fun _ _ => 0 := by
  funext x y
  simp [py, cosPotential]

private lemma pxx_cosPotential :
    px (px cosPotential) =
      fun x _ => -(Real.cos (2 * Real.pi * x) * (2 * Real.pi)) * (2 * Real.pi) := by
  funext x y
  rw [px, px_cosPotential]
  have hs : HasDerivAt (fun s : ℝ => Real.sin (2 * Real.pi * s))
      (Real.cos (2 * Real.pi * x) * (2 * Real.pi)) x := by
    simpa using (Real.hasDerivAt_sin (2 * Real.pi * x)).comp x
      (by simpa using (hasDerivAt_id x).const_mul (2 * Real.pi))
  exact (hs.neg.mul_const (2 * Real.pi)).deriv

/-- The curved potential `u(x, y) = cos (2πx)` satisfies the hypotheses. -/
theorem isPotential_cosPotential : IsPotential cosPotential := by
  constructor
  · intro x y
    show Real.cos (2 * Real.pi * (x + 1)) = Real.cos (2 * Real.pi * x)
    rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  · intro x y; rfl
  · intro y
    exact (Real.differentiable_cos.comp (differentiable_id.const_mul (2 * Real.pi)))
  · intro x; exact differentiable_const _
  · intro y
    rw [px_cosPotential]
    exact ((Real.differentiable_sin.comp
      (differentiable_id.const_mul (2 * Real.pi))).neg).mul_const _
  · intro x
    rw [py_cosPotential]
    exact differentiable_const _
  · rw [pxx_cosPotential]
    fun_prop
  · rw [py_cosPotential]
    simp only [py, deriv_const']
    fun_prop

/-- The curved example really is curved: its Gauss curvature is nonzero at the origin. -/
theorem gaussCurvature_cosPotential_ne_zero : gaussCurvature cosPotential 0 0 ≠ 0 := by
  have hx : px (px cosPotential) 0 0 = -(4 * Real.pi ^ 2) := by
    rw [pxx_cosPotential]; simp; ring
  have hy : py (py cosPotential) 0 0 = 0 := by
    rw [py_cosPotential]
    simp [py]
  rw [gaussCurvature, hx, hy]
  have hpi : Real.pi ^ 2 > 0 := by positivity
  have hexp : Real.exp (-(2 * cosPotential 0 0)) > 0 := Real.exp_pos _
  nlinarith [hexp, hpi]

/-- Gauss–Bonnet for this curved metric: even though the curvature is not identically zero,
its total integral vanishes. -/
theorem gauss_bonnet_cosPotential :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        gaussCurvature cosPotential x y * areaDensity cosPotential x y)
      = 2 * Real.pi * (torusEulerChar : ℝ) :=
  gauss_bonnet_conformal_torus isPotential_cosPotential

end Math2.Torus

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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

set_option grind.warning false

namespace Math2

/-!
## Setting

Mathlib currently contains no theory of connections, curvature tensors, Pfaffians of
curvature forms, or integration of differential forms over manifolds, so the smooth
Chern–Gauss–Bonnet theorem cannot even be *stated* against the library as it stands.

We therefore develop, from scratch, the combinatorial (Regge/Knill) incarnation of the
theorem, which is a genuine Gauss–Bonnet theorem valid in **every** dimension and in
particular for even-dimensional closed manifolds: a finite simplicial complex `K`
(a triangulated space) carries a local *curvature* `K.curvature v` attached to each
vertex `v`, defined purely in terms of the simplices around `v` (equivalently, in terms
of the f-vector of the unit sphere / link of `v`), and the total curvature equals the
Euler characteristic:

`∑ v, curvature v = χ(K)`.

This is the exact discrete analogue of `∫_M Pf(Ω)/(2π)^n = χ(M)`: the curvature integral
is replaced by a finite sum of local curvatures.

The companion file `RequestProject/Torus.lean` proves a *smooth* instance of the theorem,
namely `∫_{T²} K dA = 2π χ(T²)` for an arbitrary conformal metric on the closed
even-dimensional manifold `T² = ℝ²/ℤ²`.
-/

/-- A finite abstract simplicial complex on a vertex type `V`: a finite family of
nonempty finite subsets of `V` (the *faces*, or *simplices*) closed under passing to
nonempty subsets. -/
structure SimplicialComplex (V : Type*) [DecidableEq V] where
  /-- The finite set of faces (simplices) of the complex. -/
  faces : Finset (Finset V)
  /-- Every face is nonempty. -/
  nonempty_of_mem : ∀ s ∈ faces, s.Nonempty
  /-- The set of faces is closed under nonempty subsets. -/
  downward_closed : ∀ s ∈ faces, ∀ t ⊆ s, t.Nonempty → t ∈ faces

namespace SimplicialComplex

variable {V : Type*} [DecidableEq V] (K : SimplicialComplex V)

/-- The vertices of `K`: all points occurring in some face. -/
def vertices : Finset V := K.faces.biUnion id

@[simp] lemma mem_vertices {v : V} : v ∈ K.vertices ↔ ∃ s ∈ K.faces, v ∈ s := by
  simp [vertices]

lemma subset_vertices {s : Finset V} (hs : s ∈ K.faces) : s ⊆ K.vertices :=
  fun _ hv => K.mem_vertices.2 ⟨s, hs, hv⟩

lemma singleton_mem_faces {v : V} (hv : v ∈ K.vertices) : ({v} : Finset V) ∈ K.faces := by
  obtain ⟨s, hs, hvs⟩ := K.mem_vertices.1 hv
  exact K.downward_closed s hs {v} (by simpa using hvs) ⟨v, by simp⟩

lemma card_pos_of_mem {s : Finset V} (hs : s ∈ K.faces) : 0 < s.card :=
  Finset.card_pos.2 (K.nonempty_of_mem s hs)

/-- The Euler characteristic of a finite simplicial complex,
`χ = ∑_k (-1)^k · #{k-dimensional faces}`.  A face `s` has dimension `s.card - 1`, so its
contribution is `(-1)^(s.card + 1)`. -/
def eulerChar : ℤ := ∑ s ∈ K.faces, (-1 : ℤ) ^ (s.card + 1)

/-- The local (Regge/Knill) curvature of `K` at a vertex `v`: each simplex `s` containing
`v` contributes its Euler weight `(-1)^(dim s)` shared equally among its `s.card`
vertices. -/
def curvature (v : V) : ℚ :=
  ∑ s ∈ K.faces with v ∈ s, (-1 : ℚ) ^ (s.card + 1) / (s.card : ℚ)

/-- The *link* (combinatorial unit sphere) of a vertex `v`, together with the empty
simplex: the faces `s` with `v ∉ s` and `insert v s ∈ K.faces`. -/
def link (v : V) : Finset (Finset V) :=
  (K.faces.filter (fun s => v ∈ s)).image (fun s => s.erase v)

/-- `linkFVector v k` counts the `(k-1)`-dimensional simplices of the link of `v`
(i.e. the faces of the link with exactly `k` vertices).  In particular
`linkFVector v 0 = 1` for a vertex `v`, coming from the empty simplex. -/
def linkFVector (v : V) (k : ℕ) : ℕ := ((K.link v).filter (fun s => s.card = k)).card

lemma mem_link {v : V} {s : Finset V} :
    s ∈ K.link v ↔ v ∉ s ∧ insert v s ∈ K.faces := by
  classical
  constructor
  · intro hs
    simp only [link, Finset.mem_image, Finset.mem_filter] at hs
    obtain ⟨t, ⟨ht, hvt⟩, rfl⟩ := hs
    refine ⟨Finset.notMem_erase v t, ?_⟩
    rwa [Finset.insert_erase hvt]
  · rintro ⟨hvs, hins⟩
    simp only [link, Finset.mem_image, Finset.mem_filter]
    exact ⟨insert v s, ⟨hins, Finset.mem_insert_self v s⟩, by
      simp [Finset.erase_insert hvs]⟩

/-- The curvature at `v` computed from the link (combinatorial unit sphere) of `v`:
`K(v) = ∑_{σ ∈ link(v) ∪ {∅}} (-1)^{|σ|} / (|σ| + 1)`. -/
lemma curvature_eq_sum_link (v : V) :
    K.curvature v = ∑ s ∈ K.link v, (-1 : ℚ) ^ s.card / ((s.card : ℚ) + 1) := by
  classical
  have hinj : ∀ x ∈ K.faces.filter (fun s => v ∈ s), ∀ y ∈ K.faces.filter (fun s => v ∈ s),
      x.erase v = y.erase v → x = y := by
    intro x hx y hy hxy
    simp only [Finset.mem_filter] at hx hy
    rw [← Finset.insert_erase hx.2, ← Finset.insert_erase hy.2, hxy]
  rw [link, Finset.sum_image hinj, SimplicialComplex.curvature]
  refine Finset.sum_congr rfl ?_
  intro t ht
  simp only [Finset.mem_filter] at ht
  obtain ⟨htf, hvt⟩ := ht
  obtain ⟨m, hm⟩ : ∃ m, t.card = m + 1 :=
    ⟨t.card - 1, (Nat.succ_pred_eq_of_pos (K.card_pos_of_mem htf)).symm⟩
  have hcard : (t.erase v).card = m := by
    rw [Finset.card_erase_of_mem hvt, hm]; rfl
  rw [hcard, hm]
  push_cast
  ring_nf

/-- Knill's form of the curvature: `K(v) = ∑_k (-1)^k V_{k-1}(v) / (k+1)`, where `V_{k-1}(v)`
is the number of `(k-1)`-dimensional simplices of the unit sphere (link) of `v`. -/
lemma curvature_eq_linkFVector (v : V) (N : ℕ) (hN : ∀ s ∈ K.link v, s.card ≤ N) :
    K.curvature v =
      ∑ k ∈ Finset.range (N + 1), (-1 : ℚ) ^ k * (K.linkFVector v k : ℚ) / ((k : ℚ) + 1) := by
  classical
  rw [K.curvature_eq_sum_link v]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (N + 1))
      (g := fun s : Finset V => s.card)
      (fun s hs => Finset.mem_range.2 (Nat.lt_succ_of_le (hN s hs)))
      (fun s : Finset V => (-1 : ℚ) ^ s.card / ((s.card : ℚ) + 1))]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.sum_congr rfl (fun s hs => by
        rw [(Finset.mem_filter.1 hs).2]), Finset.sum_const, nsmul_eq_mul]
  rw [SimplicialComplex.linkFVector]
  ring

/-- A finite simplicial complex is a *closed combinatorial `d`-manifold* (in the weak,
pseudomanifold sense) when it is pure of dimension `d` and every codimension-one face is
contained in exactly two `d`-dimensional faces. -/
structure IsClosedManifold (d : ℕ) : Prop where
  /-- The complex is nonempty. -/
  faces_nonempty : K.faces.Nonempty
  /-- No simplex has dimension larger than `d`. -/
  dim_le : ∀ s ∈ K.faces, s.card ≤ d + 1
  /-- Every simplex is contained in a `d`-dimensional one (purity). -/
  pure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = d + 1
  /-- Every codimension-one simplex lies in exactly two facets (closedness). -/
  two_facets : ∀ s ∈ K.faces, s.card = d →
    (K.faces.filter (fun t => s ⊆ t ∧ t.card = d + 1)).card = 2

end SimplicialComplex

/-! ## The Gauss–Bonnet theorem -/

open Finset in
/-- **Chern–Gauss–Bonnet (combinatorial form).**  For every finite simplicial complex —
in particular for every triangulated closed manifold of even dimension — the total
curvature equals the Euler characteristic:
`∑_{v} K(v) = χ(M)`. -/
theorem chern_gauss_bonnet {V : Type*} [DecidableEq V] (K : SimplicialComplex V) :
    ∑ v ∈ K.vertices, K.curvature v = (K.eulerChar : ℚ) := by
  classical
  have key : ∀ v ∈ K.vertices, K.curvature v
      = ∑ s ∈ K.faces, (if v ∈ s then (-1 : ℚ) ^ (s.card + 1) / (s.card : ℚ) else 0) := by
    intro v _
    simpa [SimplicialComplex.curvature] using
      Finset.sum_filter (s := K.faces) (fun s => v ∈ s)
        (fun s => (-1 : ℚ) ^ (s.card + 1) / (s.card : ℚ))
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  have step : ∀ s ∈ K.faces,
      (∑ v ∈ K.vertices, (if v ∈ s then (-1 : ℚ) ^ (s.card + 1) / (s.card : ℚ) else 0))
        = (-1 : ℚ) ^ (s.card + 1) := by
    intro s hs
    rw [← Finset.sum_filter]
    have hsub : K.vertices.filter (fun v => v ∈ s) = s := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨K.subset_vertices hs h, h⟩⟩
    rw [hsub, Finset.sum_const, nsmul_eq_mul]
    have hcard : (s.card : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (K.card_pos_of_mem hs).ne'
    field_simp
  rw [Finset.sum_congr rfl step]
  simp [SimplicialComplex.eulerChar]

/-- **Chern–Gauss–Bonnet for even-dimensional closed manifolds** (combinatorial form).
For a triangulated closed manifold of even dimension `d`, the total curvature, with the
curvature at each vertex written in Knill's form `K(v) = ∑_{k=0}^{d} (-1)^k V_{k-1}(v)/(k+1)`
in terms of the f-vector `V_{k-1}(v) = linkFVector v k` of the unit sphere of `v`, equals the
Euler characteristic.  The closed-manifold hypothesis is used only to bound the dimension of
the links; the evenness of `d` is included because it was requested, but the identity in fact
holds for arbitrary finite simplicial complexes (`Math2.chern_gauss_bonnet`). -/
theorem chern_gauss_bonnet_even_closed_manifold {V : Type*} [DecidableEq V]
    (K : SimplicialComplex V) (d : ℕ) (hd : Even d) (hK : K.IsClosedManifold d) :
    ∑ v ∈ K.vertices, ∑ k ∈ Finset.range (d + 1),
        (-1 : ℚ) ^ k * (K.linkFVector v k : ℚ) / ((k : ℚ) + 1) = (K.eulerChar : ℚ) := by
  obtain ⟨m, rfl⟩ := hd
  rw [← chern_gauss_bonnet K]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine (K.curvature_eq_linkFVector v (m + m) ?_).symm
  intro s hs
  have h := hK.dim_le _ (K.mem_link.1 hs).2
  have hcard : (insert v s).card = s.card + 1 :=
    Finset.card_insert_of_notMem (K.mem_link.1 hs).1
  omega

/-! ## A worked even-dimensional closed manifold: the octahedral triangulation of `S²`

The octahedron is the simplicial complex on six vertices `0,…,5`, thought of as three pairs of
antipodal points `{0,1}, {2,3}, {4,5}`, whose simplices are the nonempty subsets containing at
most one point of each antipodal pair.  It is a closed combinatorial `2`-manifold (a
triangulated `2`-sphere) with `6` vertices, `12` edges and `8` triangles.  Each vertex has a
link which is a `4`-cycle, so `V_{-1} = 1`, `V_0 = 4`, `V_1 = 4` and the curvature at each
vertex is `1 - 4/2 + 4/3 = 1/3`; the total curvature is `6 · (1/3) = 2 = χ(S²)`. -/

/-- The octahedral triangulation of the `2`-sphere. -/
def octahedron : SimplicialComplex (Fin 6) where
  faces := (Finset.univ : Finset (Finset (Fin 6))).filter
    (fun s => s.Nonempty ∧ ∀ x ∈ s, ∀ y ∈ s, (x : ℕ) / 2 = (y : ℕ) / 2 → x = y)
  nonempty_of_mem := by decide
  downward_closed := by decide

/-- The octahedron is a closed combinatorial manifold of (even) dimension `2`. -/
theorem octahedron_isClosedManifold : octahedron.IsClosedManifold 2 :=
  ⟨by decide, by decide, by decide, by decide⟩

@[simp] theorem octahedron_eulerChar : octahedron.eulerChar = 2 := by decide

@[simp] theorem octahedron_vertices : octahedron.vertices = Finset.univ := by decide

/-- The unit sphere of every vertex of the octahedron is a `4`-cycle. -/
theorem octahedron_linkFVector (v : Fin 6) :
    octahedron.linkFVector v 0 = 1 ∧ octahedron.linkFVector v 1 = 4 ∧
      octahedron.linkFVector v 2 = 4 := by
  revert v; decide

/-- Every vertex of the octahedron carries curvature `1/3`. -/
theorem octahedron_curvature (v : Fin 6) : octahedron.curvature v = 1 / 3 := by
  have hN : ∀ s ∈ octahedron.link v, s.card ≤ 2 := by revert v; decide
  obtain ⟨h0, h1, h2⟩ := octahedron_linkFVector v
  rw [octahedron.curvature_eq_linkFVector v 2 hN]
  norm_num [Finset.sum_range_succ, h0, h1, h2]

/-- Gauss–Bonnet made explicit on the octahedral `2`-sphere:
`6 · (1/3) = 2 = χ(S²)`. -/
example : ∑ v ∈ octahedron.vertices, octahedron.curvature v = (octahedron.eulerChar : ℚ) :=
  chern_gauss_bonnet octahedron

theorem octahedron_total_curvature :
    ∑ v ∈ octahedron.vertices, octahedron.curvature v = 2 := by
  rw [chern_gauss_bonnet octahedron, octahedron_eulerChar]
  norm_num

end Math2

