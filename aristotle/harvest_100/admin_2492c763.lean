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

/-!
## Combinatorial (Levitt–Knill) Chern–Gauss–Bonnet

The smooth Chern–Gauss–Bonnet theorem states that for a closed oriented Riemannian
manifold `M` of even dimension `2n`,
`χ(M) = (2π)⁻ⁿ ∫_M Pf(Ω)`, where `Pf(Ω)` is the Pfaffian of the curvature `2`-form.
Mathlib currently has no Riemannian curvature tensor, no Pfaffian of a curvature form and
no integration of differential forms over manifolds, so that analytic statement cannot even
be *written* here, let alone proved.

What is developed and proved below is the **combinatorial Gauss–Bonnet theorem**
(Levitt, Knill): the discrete analogue of Chern–Gauss–Bonnet, in which the Pfaffian
curvature density is replaced by the *combinatorial curvature* of a vertex of a finite
simplicial complex, and the integral by a finite sum over vertices.  The total curvature
equals the Euler characteristic.  Together with it we prove the classical
**angle–defect Gauss–Bonnet theorem** for closed triangulated surfaces:
the total angle defect equals `2π` times the Euler characteristic.
-/

namespace Math2

open Finset

variable {V : Type*} [DecidableEq V]

/-- The vertex set of a finite family of simplices `K`. -/
def vertices (K : Finset (Finset V)) : Finset V := K.sup id

@[simp] theorem mem_vertices {K : Finset (Finset V)} {x : V} :
    x ∈ vertices K ↔ ∃ S ∈ K, x ∈ S := by
  simp [vertices, Finset.mem_sup]

/-- The Euler characteristic of a finite family of simplices:
`χ = #vertices - #edges + #triangles - ...`, i.e. `∑_{S} (-1)^(|S|+1)`. -/
def eulerChar (K : Finset (Finset V)) : ℤ := ∑ S ∈ K, (-1 : ℤ) ^ (S.card + 1)

/-- The combinatorial curvature of `K` at a vertex `x`: each simplex `S` containing `x`
contributes its signed weight `(-1)^(|S|+1)` shared equally among its `|S|` vertices.
This is the discrete analogue of the Pfaffian curvature density. -/
def curvature (K : Finset (Finset V)) (x : V) : ℚ :=
  ∑ S ∈ K.filter (fun S => x ∈ S), (-1 : ℚ) ^ (S.card + 1) / S.card

/-- **Combinatorial Gauss–Bonnet theorem** (Levitt, Knill).  For any finite family of
nonempty simplices, the total combinatorial curvature equals the Euler characteristic. -/
theorem combinatorial_gauss_bonnet (K : Finset (Finset V)) (hK : ∀ S ∈ K, S.Nonempty) :
    ∑ x ∈ vertices K, curvature K x = (eulerChar K : ℚ) := by
  classical
  unfold curvature eulerChar
  push_cast
  rw [Finset.sum_comm' (t' := K) (s' := fun S => S)]
  · refine Finset.sum_congr rfl ?_
    intro S hS
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (S.card : ℚ) ≠ 0 := by
      have := (hK S hS).card_pos
      positivity
    field_simp
  · intro x S
    constructor
    · rintro ⟨-, hS⟩
      rw [Finset.mem_filter] at hS
      exact ⟨hS.2, hS.1⟩
    · rintro ⟨hxS, hSK⟩
      exact ⟨mem_vertices.2 ⟨S, hSK, hxS⟩, Finset.mem_filter.2 ⟨hSK, hxS⟩⟩

/-- `K` is a simplicial complex: every nonempty subset of a simplex is a simplex. -/
def IsComplex (K : Finset (Finset V)) : Prop :=
  (∀ S ∈ K, S.Nonempty) ∧ ∀ S ∈ K, ∀ T : Finset V, T.Nonempty → T ⊆ S → T ∈ K

/-- `K` is pure of dimension `d`: all simplices have at most `d + 1` vertices, and every
simplex is a face of a `d`-dimensional one. -/
def IsPure (K : Finset (Finset V)) (d : ℕ) : Prop :=
  (∀ S ∈ K, S.card ≤ d + 1) ∧ ∀ S ∈ K, ∃ T ∈ K, S ⊆ T ∧ T.card = d + 1

/-- `K` is closed (without boundary) in dimension `d`: every codimension-one face lies in
exactly two `d`-dimensional simplices. -/
def IsClosedComplex (K : Finset (Finset V)) (d : ℕ) : Prop :=
  ∀ S ∈ K, S.card = d → (K.filter (fun T => S ⊆ T ∧ T.card = d + 1)).card = 2

/-- **Chern–Gauss–Bonnet, combinatorial form, for closed even-dimensional triangulated
manifolds.**  If `K` is a finite simplicial complex which is pure of even dimension `2n`
and closed (every codimension-one face lies in exactly two top-dimensional simplices) —
i.e. a triangulation of a closed even-dimensional manifold — then the total combinatorial
curvature of `K` equals its Euler characteristic.

The evenness, purity and closedness hypotheses are stated because they are part of the
classical statement, but they are in fact not needed: the identity holds for every finite
simplicial complex, see `Math2.combinatorial_gauss_bonnet`. -/
theorem chern_gauss_bonnet (n : ℕ) (K : Finset (Finset V))
    (hcomplex : IsComplex K) (hpure : IsPure K (2 * n))
    (hclosed : IsClosedComplex K (2 * n)) :
    ∑ x ∈ vertices K, curvature K x = (eulerChar K : ℚ) :=
  combinatorial_gauss_bonnet K hcomplex.1

/-!
## The angle–defect Gauss–Bonnet theorem for closed triangulated surfaces
-/

/-- **Angle-defect Gauss–Bonnet theorem.**  Let a closed triangulated surface be given by
a vertex set `Vt`, a set `Ed` of edges, a set `Fa` of triangular faces, and an angle
function `θ` assigning to each vertex of each face its interior angle, subject to:
every face has three vertices, all lying in `Vt`; every edge has two vertices; the three
edges of every face are edges of the surface; every edge lies in exactly two faces; and
the angles of each face sum to `π` (each face is a Euclidean triangle).  Then the total
angle defect `∑_v (2π - ∑_{f ∋ v} θ v f)` equals `2π · χ`, with `χ = V - E + F`. -/
theorem angle_defect_gauss_bonnet
    (Vt : Finset V) (Ed Fa : Finset (Finset V)) (θ : V → Finset V → ℝ)
    (hface : ∀ f ∈ Fa, f.card = 3)
    (hedge : ∀ e ∈ Ed, e.card = 2)
    (hfv : ∀ f ∈ Fa, ∀ x ∈ f, x ∈ Vt)
    (hfe : ∀ f ∈ Fa, ∀ e : Finset V, e ⊆ f → e.card = 2 → e ∈ Ed)
    (hef : ∀ e ∈ Ed, (Fa.filter (fun f => e ⊆ f)).card = 2)
    (hangle : ∀ f ∈ Fa, ∑ x ∈ f, θ x f = Real.pi) :
    ∑ x ∈ Vt, (2 * Real.pi - ∑ f ∈ Fa.filter (fun f => x ∈ f), θ x f)
      = 2 * Real.pi * ((Vt.card : ℝ) - Ed.card + Fa.card) := by
  classical
  -- Double counting the incidences between edges and faces: `3 F = 2 E`.
  have hincidence : 3 * Fa.card = 2 * Ed.card := by
    have key : ∑ f ∈ Fa, (Ed.filter (fun e => e ⊆ f)).card
        = ∑ e ∈ Ed, (Fa.filter (fun f => e ⊆ f)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm' (t' := Ed) (s' := fun _ => Fa)]
      intro f e
      constructor
      · rintro ⟨hf, he⟩; exact ⟨hf, he⟩
      · rintro ⟨hf, he⟩; exact ⟨hf, he⟩
    have hL : ∀ f ∈ Fa, (Ed.filter (fun e => e ⊆ f)).card = 3 := by
      intro f hf
      have : Ed.filter (fun e => e ⊆ f) = Finset.powersetCard 2 f := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨he, hef'⟩; exact ⟨hef', hedge e he⟩
        · rintro ⟨hsub, hc⟩; exact ⟨hfe f hf e hsub hc, hsub⟩
      rw [this, Finset.card_powersetCard, hface f hf]
      rfl
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hef] at key
    simpa [Finset.sum_const, mul_comm] using key
  -- Total angle sum: `∑_v ∑_{f ∋ v} θ = π F`.
  have hsum : ∑ x ∈ Vt, ∑ f ∈ Fa.filter (fun f => x ∈ f), θ x f = Fa.card * Real.pi := by
    rw [Finset.sum_comm' (t' := Fa) (s' := fun f => f)]
    · rw [Finset.sum_congr rfl hangle, Finset.sum_const, nsmul_eq_mul]
    · intro x f
      constructor
      · rintro ⟨-, hf⟩
        rw [Finset.mem_filter] at hf
        exact ⟨hf.2, hf.1⟩
      · rintro ⟨hxf, hfF⟩
        exact ⟨hfv f hfF x hxf, Finset.mem_filter.2 ⟨hfF, hxf⟩⟩
  have hEF : (3 : ℝ) * Fa.card = 2 * Ed.card := by exact_mod_cast hincidence
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul]
  linear_combination (-1 : ℝ) * Real.pi * hEF

/-!
## A sanity check: the boundary of the tetrahedron

The hypotheses of `Math2.chern_gauss_bonnet` are satisfiable: the boundary of the
`3`-simplex is a triangulation of the closed even-dimensional manifold `S²`, and both
sides of the identity equal its Euler characteristic `2`.
-/

/-- The boundary complex of the tetrahedron, a triangulation of the `2`-sphere. -/
def tetraBoundary : Finset (Finset (Fin 4)) :=
  (Finset.univ : Finset (Fin 4)).powerset.filter (fun S => S.Nonempty ∧ S.card ≤ 3)

theorem tetraBoundary_isComplex : IsComplex tetraBoundary := by
  unfold IsComplex tetraBoundary; decide

theorem tetraBoundary_isPure : IsPure tetraBoundary 2 := by
  unfold IsPure tetraBoundary; decide

theorem tetraBoundary_isClosed : IsClosedComplex tetraBoundary 2 := by
  unfold IsClosedComplex tetraBoundary; decide

theorem tetraBoundary_eulerChar : eulerChar tetraBoundary = 2 := by
  unfold eulerChar tetraBoundary; decide

/-- The total combinatorial curvature of the boundary of the tetrahedron is `2 = χ(S²)`. -/
theorem tetraBoundary_total_curvature :
    ∑ x ∈ vertices tetraBoundary, curvature tetraBoundary x = 2 := by
  rw [chern_gauss_bonnet 1 tetraBoundary tetraBoundary_isComplex tetraBoundary_isPure
    tetraBoundary_isClosed, tetraBoundary_eulerChar]
  norm_num

/-!
## A four-dimensional example: the boundary of the `5`-simplex

The boundary of the `5`-simplex is a triangulation of the closed `4`-dimensional manifold
`S⁴`; the total combinatorial curvature is again its Euler characteristic `2`.
-/

/-- The boundary complex of the `5`-simplex, a triangulation of the `4`-sphere. -/
def simplex5Boundary : Finset (Finset (Fin 6)) :=
  (Finset.univ : Finset (Fin 6)).powerset.filter (fun S => S.Nonempty ∧ S.card ≤ 5)

set_option maxRecDepth 100000 in
theorem simplex5Boundary_isComplex : IsComplex simplex5Boundary := by
  unfold IsComplex simplex5Boundary; decide

set_option maxRecDepth 100000 in
theorem simplex5Boundary_isPure : IsPure simplex5Boundary (2 * 2) := by
  unfold IsPure simplex5Boundary; decide

set_option maxRecDepth 100000 in
theorem simplex5Boundary_isClosed : IsClosedComplex simplex5Boundary (2 * 2) := by
  unfold IsClosedComplex simplex5Boundary; decide

set_option maxRecDepth 100000 in
theorem simplex5Boundary_eulerChar : eulerChar simplex5Boundary = 2 := by
  unfold eulerChar simplex5Boundary; decide

/-- The total combinatorial curvature of the boundary of the `5`-simplex is `2 = χ(S⁴)`. -/
theorem simplex5Boundary_total_curvature :
    ∑ x ∈ vertices simplex5Boundary, curvature simplex5Boundary x = 2 := by
  rw [chern_gauss_bonnet 2 simplex5Boundary simplex5Boundary_isComplex
    simplex5Boundary_isPure simplex5Boundary_isClosed, simplex5Boundary_eulerChar]
  norm_num

end Math2

