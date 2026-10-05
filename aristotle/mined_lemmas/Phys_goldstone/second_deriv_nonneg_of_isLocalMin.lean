import Mathlib

/-!
# Goldstone
Category: Frontier Phys
Target: Phys.goldstone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede any module docstring, so the required
header comment appears immediately after the single `import Mathlib` line.)

## Statement

Spontaneous breaking of a continuous global symmetry yields a massless mode (Goldstone).

We work with a scalar potential `V : E → ℝ` on a real normed space `E` of field values,
assumed `C²`.  A *vacuum* is a local minimum `v` of `V`.  The *mass form* at `v` is the
Hessian `massForm V v = D²V(v)`, whose matrix in an orthonormal basis is the mass matrix
`M_{ij} = ∂_i∂_j V(v)` of the quadratic fluctuations around `v`; a nonzero vector in its
kernel is a zero-eigenvalue direction, i.e. a **massless mode**.

A *continuous global symmetry* is a smooth one-parameter group `R : ℝ → (E →L[ℝ] E)`
(`R (s+t) = R s ∘ R t`, `R 0 = id`) of linear transformations of the field values leaving
the potential invariant: `V (R t x) = V x`.  It is *spontaneously broken* at the vacuum `v`
when `v` itself is not invariant, i.e. `R t v ≠ v` for some `t`.

`Phys.goldstone` then produces a nonzero `X` in the kernel of the mass form.
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

open Set Filter Topology

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **mass form** (Hessian of the potential) of a scalar potential `V` at a
configuration `v`.  In finite dimensions, in an orthonormal basis, this is the mass matrix
`M_{ij} = ∂_i ∂_j V (v)` of the small fluctuations around `v`; a nonzero vector in its
kernel is a **massless mode**. -/

lemma second_deriv_nonneg_of_isLocalMin {f g : ℝ → ℝ} {c : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hmin : IsLocalMin f 0)
    (hg : HasDerivAt g c 0) : 0 ≤ c := by
  by_contra hcon
  push_neg at hcon
  have hg0 : g 0 = 0 := hmin.hasDerivAt_eq_zero (hf 0)
  have hslope : Filter.Tendsto (slope g 0) (𝓝[≠] (0 : ℝ)) (𝓝 c) :=
    hasDerivAt_iff_tendsto_slope.mp hg
  have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), slope g 0 t < 0 := hslope.eventually_lt_const hcon
  have h1' : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t < 0 := by
    have h1'' : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope g 0 t < 0 :=
      nhdsWithin_mono _ (fun x hx => (mem_Ioi.mp hx).ne') h1
    filter_upwards [h1'', self_mem_nhdsWithin] with t ht htpos
    rw [slope_def_field, hg0] at ht
    simp only [sub_zero, div_neg_iff] at ht
    rcases ht with ⟨h, h'⟩ | ⟨h, _⟩
    · exact absurd (mem_Ioi.mp htpos) (by linarith)
    · exact h
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), f 0 ≤ f t := nhdsWithin_le_nhds hmin
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (h1'.and h2)
  have hδ0 : (0 : ℝ) < δ := mem_Ioi.mp hδ
  have hb0 : (0 : ℝ) < δ / 2 := by linarith
  have hbδ : δ / 2 < δ := by linarith
  obtain ⟨c₀, hc₀, hc₀eq⟩ := exists_hasDerivAt_eq_slope f g hb0
    (fun x _ => (hf x).continuousAt.continuousWithinAt) (fun x _ => hf x)
  have hneg : g c₀ < 0 := (hsub ⟨hc₀.1, lt_trans hc₀.2 hbδ⟩).1
  have hfb : f 0 ≤ f (δ / 2) := (hsub ⟨hb0, hbδ⟩).2
  rw [hc₀eq] at hneg
  have hnn : 0 ≤ (f (δ / 2) - f 0) / (δ / 2 - 0) := div_nonneg (by linarith) (by linarith)
  linarith

/-- At a (local) minimum of the potential the mass form is positive semidefinite:
all squared masses are nonnegative. -/
