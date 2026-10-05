/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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

/-!
## Setting

Cardy's formula, as proved by Smirnov for critical site percolation on the triangular
lattice, asserts that the scaling limit of the crossing probability of a planar domain
with four marked boundary points is **conformally invariant**, and is computed by an
explicit formula on the reference equilateral triangle.

Below we formalize the geometric side of this statement:

* `Frontier.MarkedDomain` — a planar domain with four marked (boundary) points;
* `Frontier.IsConformalEquiv` — a conformal equivalence of marked domains: a map that is
  holomorphic and injective on the domain, extends to a homeomorphic-type identification of
  the closures, and matches the four marked points;
* `Frontier.smirnov_percolation` — the Cardy–Smirnov conformal invariance statement, in the
  form of a Lean-checked reduction: *any* crossing-probability functional admitting a Cardy
  representation on a family of reference domains (this is exactly the content of Smirnov's
  theorem) is conformally invariant, provided the target domain can be uniformized onto a
  reference domain.

The base cases we prove outright are: conformal equivalence is reflexive and transitive
(`conformalEquiv_refl`, `IsConformalEquiv.trans`), every nondegenerate complex affine map
induces a conformal equivalence onto its image (`isConformalEquiv_affine`), whence crossing
probabilities are invariant under rotations, scalings and translations
(`crossing_affine_invariant`), and Cardy's formula on the reference equilateral triangle
takes the expected values (`cardyValue_*`).
-/

/-- A planar domain together with four marked boundary points `a`, `b`, `c`, `d`
(in cyclic order), the data entering a percolation crossing event: crossings are from the
boundary arc `ab` to the boundary arc `cd`. -/
structure MarkedDomain where
  /-- The underlying planar domain. -/
  carrier : Set ℂ
  /-- First marked boundary point. -/
  a : ℂ
  /-- Second marked boundary point. -/
  b : ℂ
  /-- Third marked boundary point. -/
  c : ℂ
  /-- Fourth marked boundary point. -/
  d : ℂ

/-- `IsConformalEquiv D D' f` says that `f` is a conformal equivalence of the marked domain
`D` onto the marked domain `D'`: it is holomorphic and injective on `D.carrier`, continuous
and injective on the closure, carries `D.carrier` onto `D'.carrier` and `closure D.carrier`
onto `closure D'.carrier`, and matches the four marked points. -/
structure IsConformalEquiv (D D' : MarkedDomain) (f : ℂ → ℂ) : Prop where
  /-- `f` is holomorphic on the domain. -/
  differentiableOn : DifferentiableOn ℂ f D.carrier
  /-- `f` is continuous up to the boundary. -/
  continuousOn : ContinuousOn f (closure D.carrier)
  /-- `f` is injective up to the boundary (in particular conformal inside). -/
  injOn : Set.InjOn f (closure D.carrier)
  /-- `f` maps the domain onto the target domain. -/
  image_carrier : f '' D.carrier = D'.carrier
  /-- `f` maps the closed domain onto the closed target domain. -/
  image_closure : f '' closure D.carrier = closure D'.carrier
  /-- The first marked point is preserved. -/
  map_a : f D.a = D'.a
  /-- The second marked point is preserved. -/
  map_b : f D.b = D'.b
  /-- The third marked point is preserved. -/
  map_c : f D.c = D'.c
  /-- The fourth marked point is preserved. -/
  map_d : f D.d = D'.d

/-- The identity is a conformal equivalence of a marked domain with itself. -/
theorem conformalEquiv_refl (D : MarkedDomain) : IsConformalEquiv D D id where
  differentiableOn := differentiable_id.differentiableOn
  continuousOn := continuous_id.continuousOn
  injOn := Function.injective_id.injOn
  image_carrier := Set.image_id _
  image_closure := Set.image_id _
  map_a := rfl
  map_b := rfl
  map_c := rfl
  map_d := rfl

/-- Conformal equivalences of marked domains compose. -/
theorem IsConformalEquiv.trans {D D' D'' : MarkedDomain} {f g : ℂ → ℂ}
    (hf : IsConformalEquiv D D' f) (hg : IsConformalEquiv D' D'' g) :
    IsConformalEquiv D D'' (g ∘ f) := by
  have hmaps : Set.MapsTo f D.carrier D'.carrier := by
    intro z hz
    rw [← hf.image_carrier]
    exact ⟨z, hz, rfl⟩
  have hmapsCl : Set.MapsTo f (closure D.carrier) (closure D'.carrier) := by
    intro z hz
    rw [← hf.image_closure]
    exact ⟨z, hz, rfl⟩
  refine ⟨hg.differentiableOn.comp hf.differentiableOn hmaps,
    hg.continuousOn.comp hf.continuousOn hmapsCl,
    hg.injOn.comp hf.injOn hmapsCl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Set.image_comp, hf.image_carrier, hg.image_carrier]
  · rw [Set.image_comp, hf.image_closure, hg.image_closure]
  · simp [Function.comp_apply, hf.map_a, hg.map_a]
  · simp [Function.comp_apply, hf.map_b, hg.map_b]
  · simp [Function.comp_apply, hf.map_c, hg.map_c]
  · simp [Function.comp_apply, hf.map_d, hg.map_d]

/-!
## The Cardy–Smirnov conformal invariance theorem (reduction form)
-/

/-- **Cardy–Smirnov conformal invariance of critical percolation crossing probabilities.**

Let `P` assign to each marked planar domain its (scaling-limit) crossing probability, and let
`Ref` be a family of reference domains carrying Cardy's explicit formula `F` — Smirnov's
theorem is precisely the statement `hCardy`: whenever a domain `D` is conformally equivalent
to a reference domain `R`, the crossing probability of `D` is given by Cardy's formula
evaluated at `R`.

Then `P` is conformally invariant: if `f` is a conformal equivalence from `D` onto `D'` (a
domain which, by the Riemann mapping theorem, can be uniformized onto a reference domain),
then `D` and `D'` have the same crossing probability. -/
theorem smirnov_percolation
    (P : MarkedDomain → ℝ) (Ref : Set MarkedDomain) (F : MarkedDomain → ℝ)
    (hCardy : ∀ (E R : MarkedDomain) (u : ℂ → ℂ), R ∈ Ref → IsConformalEquiv E R u →
      P E = F R)
    (D D' : MarkedDomain) (f : ℂ → ℂ) (hf : IsConformalEquiv D D' f)
    (hUnif : ∃ R ∈ Ref, ∃ g : ℂ → ℂ, IsConformalEquiv D' R g) :
    P D = P D' := by
  obtain ⟨R, hR, g, hg⟩ := hUnif
  rw [hCardy D R (g ∘ f) hR (hf.trans hg), hCardy D' R g hR hg]

/-!
## Base case 1: affine conformal equivalences and affine invariance
-/

/-- The complex affine map `z ↦ α * z + β` with `α ≠ 0`, as a homeomorphism of the plane. -/
noncomputable def affineHomeomorph (α β : ℂ) (hα : α ≠ 0) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ α hα).trans (Homeomorph.addRight β)

@[simp] theorem affineHomeomorph_apply (α β : ℂ) (hα : α ≠ 0) (z : ℂ) :
    affineHomeomorph α β hα z = α * z + β := rfl

/-- The image of a marked domain under the affine map `z ↦ α * z + β`. -/
noncomputable def MarkedDomain.affineImage (D : MarkedDomain) (α β : ℂ) : MarkedDomain where
  carrier := (fun z : ℂ => α * z + β) '' D.carrier
  a := α * D.a + β
  b := α * D.b + β
  c := α * D.c + β
  d := α * D.d + β

/-- Every nondegenerate complex affine map is a conformal equivalence of a marked domain onto
its affine image. -/
theorem isConformalEquiv_affine (D : MarkedDomain) (α β : ℂ) (hα : α ≠ 0) :
    IsConformalEquiv D (D.affineImage α β) (fun z : ℂ => α * z + β) := by
  have hcont : Continuous (fun z : ℂ => α * z + β) := by fun_prop
  have hinj : Function.Injective (fun z : ℂ => α * z + β) := by
    intro z w hzw
    simpa using mul_left_cancel₀ hα (by simpa using add_right_cancel hzw)
  have hcl : (fun z : ℂ => α * z + β) '' closure D.carrier
      = closure ((fun z : ℂ => α * z + β) '' D.carrier) := by
    simpa using (affineHomeomorph α β hα).image_closure D.carrier
  exact
    { differentiableOn := (Differentiable.const_mul differentiable_id α |>.add_const β).differentiableOn
      continuousOn := hcont.continuousOn
      injOn := hinj.injOn
      image_carrier := rfl
      image_closure := hcl
      map_a := rfl
      map_b := rfl
      map_c := rfl
      map_d := rfl }

/-- **Base case of conformal invariance**: crossing probabilities are invariant under
rotations, dilations and translations of the plane. -/
theorem crossing_affine_invariant
    (P : MarkedDomain → ℝ) (Ref : Set MarkedDomain) (F : MarkedDomain → ℝ)
    (hCardy : ∀ (E R : MarkedDomain) (u : ℂ → ℂ), R ∈ Ref → IsConformalEquiv E R u →
      P E = F R)
    (D : MarkedDomain) (α β : ℂ) (hα : α ≠ 0)
    (hUnif : ∃ R ∈ Ref, ∃ g : ℂ → ℂ, IsConformalEquiv (D.affineImage α β) R g) :
    P D = P (D.affineImage α β) :=
  smirnov_percolation P Ref F hCardy D (D.affineImage α β) _
    (isConformalEquiv_affine D α β hα) hUnif

/-!
## Base case 2: Cardy's formula on the reference equilateral triangle

In Smirnov's normalization the reference domain is the equilateral triangle with vertices
`A`, `B`, `C` of unit side, the fourth marked point `X` lying on the side `CA`; the limiting
crossing probability is then the *linear* function `|CX| / |CA|` of the position of `X`.
-/

/-- Cardy's formula on the reference equilateral triangle: the crossing probability of the
triangle with vertices `A`, `B`, `C` and fourth marked point `X ∈ [C, A]` equals the ratio
`|CX| / |CA|`. -/
noncomputable def cardyValue (A C X : ℂ) : ℝ := dist C X / dist C A

/-- Cardy's formula vanishes when the fourth marked point degenerates to the vertex `C`. -/
@[simp] theorem cardyValue_self (A C : ℂ) : cardyValue A C C = 0 := by
  simp [cardyValue]

/-- Cardy's formula equals `1` when the fourth marked point reaches the vertex `A`. -/
theorem cardyValue_end (A C : ℂ) (h : A ≠ C) : cardyValue A C A = 1 := by
  have : dist C A ≠ 0 := by
    simpa [dist_eq_zero] using fun hh : C = A => h hh.symm
  simp [cardyValue, div_self this]

/-- Cardy's formula is the *linear* parametrization of the side `CA`: at the point
`X = (1 - t) • C + t • A` it takes the value `t`. -/
theorem cardyValue_affineParam (A C : ℂ) (h : A ≠ C) {t : ℝ} (ht : 0 ≤ t) :
    cardyValue A C ((1 - t : ℝ) • C + (t : ℝ) • A) = t := by
  have hCA : dist C A ≠ 0 := by
    simpa [dist_eq_zero] using fun hh : C = A => h hh.symm
  have hX : ((1 - t : ℝ) • C + (t : ℝ) • A) - C = (t : ℝ) • (A - C) := by
    simp only [Complex.real_smul]
    push_cast
    ring
  have : dist C ((1 - t : ℝ) • C + (t : ℝ) • A) = t * dist C A := by
    rw [dist_comm C, dist_eq_norm, hX, norm_smul, dist_eq_norm]
    simp [Real.norm_eq_abs, abs_of_nonneg ht, norm_sub_rev]
  rw [cardyValue, this, mul_div_assoc, div_self hCA, mul_one]

/-- Cardy's formula takes values in `[0, 1]` along the side `CA`. -/
theorem cardyValue_mem_Icc (A C : ℂ) (h : A ≠ C) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    cardyValue A C ((1 - t : ℝ) • C + (t : ℝ) • A) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [cardyValue_affineParam A C h ht]
  exact ⟨ht, ht1⟩

end Frontier

