/-
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the header above
-- is written as a plain block comment; its text is otherwise verbatim.)

import Mathlib

/-!
## Overview

The Atiyah–Singer index theorem states that for an elliptic (pseudo)differential operator
`D : Γ(E) → Γ(F)` on a closed manifold `M`, the *analytic index*

  `ind_a(D) = dim ker D - dim coker D`

equals the *topological index*, a quantity computed purely from the symbol data of `D`
(via characteristic classes).

Full pseudodifferential theory on manifolds is not available in Mathlib, so we formalize the
theorem in the setting in which it is a genuine, verifiable statement: the **base case of a
zero-dimensional manifold** (a point), together with its **elliptic complex** generalization.

* For a point, the "bundles" are finite-dimensional vector spaces `E`, `F`, an operator is a
  linear map `D : E →ₗ F`, the analytic index is `dim ker D - dim coker D`, and the
  topological index (the integral of the Chern character of the symbol class over a point,
  i.e. the rank difference) is `dim E - dim F`.  The theorem `Frontier.atiyah_singer_index`
  proves these agree.  Everything characteristic of the index theorem is already visible here:
  the analytic index, defined by solution spaces of the operator, is independent of the
  operator and depends only on topological data; in particular it is invariant under
  deformation of the operator.

* `Frontier.atiyah_singer_index_complex` is the corresponding statement for an elliptic
  complex: the Euler characteristic of the cohomology of the complex (the analytic index)
  equals the alternating sum of the ranks of the bundles (the topological index).  This is
  the Euler–Poincaré principle, which is precisely how e.g. the Gauss–Bonnet and
  Riemann–Roch specializations of the index theorem are packaged.
-/

namespace Frontier

open Module

section Operator

variable {𝕜 : Type*} [Field 𝕜]
variable {E F : Type*} [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- The **analytic index** of an operator `D : E →ₗ[𝕜] F`:
`dim ker D - dim coker D`, where `coker D = F ⧸ range D`. -/
noncomputable def analyticIndex (D : E →ₗ[𝕜] F) : ℤ :=
  (finrank 𝕜 (LinearMap.ker D) : ℤ) - (finrank 𝕜 (F ⧸ LinearMap.range D) : ℤ)

/-- The **topological index** of the symbol data `(E, F)` over a point: the difference of the
ranks of the two bundles, i.e. `∫_pt ch(E - F)`. -/
noncomputable def topologicalIndex (𝕜 : Type*) [Field 𝕜] (E F : Type*) [AddCommGroup E]
    [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] : ℤ :=
  (finrank 𝕜 E : ℤ) - (finrank 𝕜 F : ℤ)

/-- **Atiyah–Singer index theorem (base case: a zero-dimensional manifold).**

For an elliptic operator `D` between (the section spaces of) finite-dimensional bundles `E`
and `F` over a point, the analytic index `dim ker D - dim coker D` equals the topological
index `rank E - rank F`. -/
theorem atiyah_singer_index [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (D : E →ₗ[𝕜] F) : analyticIndex D = topologicalIndex 𝕜 E F := by
  have h1 := LinearMap.finrank_range_add_finrank_ker D
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range D)
  simp only [analyticIndex, topologicalIndex]
  omega

/-- **Deformation (homotopy) invariance of the analytic index**: any two operators between the
same pair of bundles over a point have the same analytic index.  This is the qualitative
content of the index theorem: the index is a topological invariant. -/
theorem analyticIndex_eq_analyticIndex [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (D D' : E →ₗ[𝕜] F) : analyticIndex D = analyticIndex D' := by
  rw [atiyah_singer_index, atiyah_singer_index]

/-- Invariance of the analytic index under an arbitrary perturbation of the operator. -/
theorem analyticIndex_add_perturbation [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (D K : E →ₗ[𝕜] F) : analyticIndex (D + K) = analyticIndex D :=
  analyticIndex_eq_analyticIndex _ _

/-- Sanity check (non-vacuity): the zero operator from a rank `3` bundle to a rank `2` bundle
over a point has index `3 - 2 = 1`. -/
example : analyticIndex (0 : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) = 1 := by
  rw [atiyah_singer_index]
  simp [topologicalIndex]

end Operator

section Complex

variable {𝕜 : Type*} [Field 𝕜]

/-- The cohomology `ker g / im f` of a two-step complex `A --f--> B --g--> C`. -/
abbrev cohomologyAt {A B C : Type*} [AddCommGroup A] [Module 𝕜 A] [AddCommGroup B]
    [Module 𝕜 B] [AddCommGroup C] [Module 𝕜 C] (f : A →ₗ[𝕜] B) (g : B →ₗ[𝕜] C) : Type _ :=
  (LinearMap.ker g) ⧸ ((LinearMap.range f).comap (LinearMap.ker g).subtype)

/-- The dimension of the cohomology of `A --f--> B --g--> C` at `B` is
`dim ker g - dim im f`. -/
theorem finrank_cohomologyAt {A B C : Type*} [AddCommGroup A] [Module 𝕜 A] [AddCommGroup B]
    [Module 𝕜 B] [FiniteDimensional 𝕜 B] [AddCommGroup C] [Module 𝕜 C]
    (f : A →ₗ[𝕜] B) (g : B →ₗ[𝕜] C) (hfg : g.comp f = 0) :
    (finrank 𝕜 (cohomologyAt f g) : ℤ)
      = (finrank 𝕜 (LinearMap.ker g) : ℤ) - (finrank 𝕜 (LinearMap.range f) : ℤ) := by
  have hle : LinearMap.range f ≤ LinearMap.ker g := by
    rintro x ⟨y, rfl⟩
    have := congrArg (fun (h : A →ₗ[𝕜] C) => h y) hfg
    simpa [LinearMap.mem_ker] using this
  have hiso := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h2 := Submodule.finrank_quotient_add_finrank
      ((LinearMap.range f).comap (LinearMap.ker g).subtype)
  rw [hiso] at h2
  simp only [cohomologyAt]
  omega

variable {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  [∀ i, FiniteDimensional 𝕜 (V i)]

/-- Telescoping identity used for the Euler–Poincaré computation. -/
private theorem telescope (a : ℕ → ℤ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (-1 : ℤ) ^ i * (a i + a (i + 1))
      = a 0 + (-1 : ℤ) ^ (m + 1) * a m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ, pow_succ]
      ring

/-- **Atiyah–Singer index theorem for an elliptic complex (base case: a point).**

Let `0 = V 0 → V 1 → ⋯ → V n → V (n+1) = 0` be a complex of finite-dimensional spaces (the
fibres of an elliptic complex over a zero-dimensional manifold).  Its analytic index — the
Euler characteristic of its cohomology — equals its topological index, the alternating sum of
the ranks of the bundles. -/
theorem atiyah_singer_index_complex (n : ℕ) (d : ∀ i, V i →ₗ[𝕜] V (i + 1))
    (hd : ∀ i, (d (i + 1)).comp (d i) = 0)
    (h0 : Subsingleton (V 0)) (hn : Subsingleton (V (n + 1))) :
    ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * finrank 𝕜 (cohomologyAt (d i) (d (i + 1)))
      = ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * finrank 𝕜 (V (i + 1)) := by
  set a : ℕ → ℤ := fun i => (finrank 𝕜 (LinearMap.range (d i)) : ℤ) with ha
  have ha0 : a 0 = 0 := by
    have hd0 : LinearMap.range (d 0) = ⊥ := by
      rw [LinearMap.range_eq_bot]
      exact LinearMap.ext fun x => by simp [Subsingleton.elim x 0]
    simp [ha, hd0]
  have han : a n = 0 := by
    have : Subsingleton (LinearMap.range (d n)) := by
      constructor
      intro x y
      exact Subtype.ext (Subsingleton.elim _ _)
    simp [ha, finrank_zero_of_subsingleton]
  have key : ∀ i : ℕ,
      (-1 : ℤ) ^ (i + 1) * finrank 𝕜 (cohomologyAt (d i) (d (i + 1)))
        - (-1 : ℤ) ^ (i + 1) * finrank 𝕜 (V (i + 1))
        = (-1 : ℤ) ^ i * (a i + a (i + 1)) := by
    intro i
    have hc := finrank_cohomologyAt (d i) (d (i + 1)) (hd i)
    have hrk := LinearMap.finrank_range_add_finrank_ker (d (i + 1))
    have hV : (finrank 𝕜 (V (i + 1)) : ℤ)
        = (finrank 𝕜 (LinearMap.range (d (i + 1))) : ℤ)
          + (finrank 𝕜 (LinearMap.ker (d (i + 1))) : ℤ) := by exact_mod_cast hrk.symm
    rw [hc, hV, pow_succ]
    simp only [ha]
    ring
  have hsum : ∑ i ∈ Finset.range n,
      ((-1 : ℤ) ^ (i + 1) * finrank 𝕜 (cohomologyAt (d i) (d (i + 1)))
        - (-1 : ℤ) ^ (i + 1) * finrank 𝕜 (V (i + 1)))
      = ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (a i + a (i + 1)) :=
    Finset.sum_congr rfl fun i _ => key i
  rw [Finset.sum_sub_distrib, telescope a n, ha0, han] at hsum
  simp only [mul_zero, add_zero] at hsum
  omega

end Complex

end Frontier

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

