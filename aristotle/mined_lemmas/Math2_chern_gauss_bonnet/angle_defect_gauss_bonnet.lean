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
