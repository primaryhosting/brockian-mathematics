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

lemma clm_apply_eq_zero_of_quadratic_eq_zero {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hpsd : ∀ w, 0 ≤ B w w) (hsymm : ∀ v w, B v w = B w v) {X : E} (hX : B X X = 0) :
    B X = 0 := by
  ext w
  show B X w = 0
  by_contra ha
  have hb : 0 ≤ B w w := hpsd w
  set a : ℝ := B X w with hadef
  set b : ℝ := B w w with hbdef
  set ep : ℝ := 1 / (b + 1) with hepdef
  have hep : 0 < ep := by positivity
  have hepb : ep * b < 1 := by
    rw [hepdef, div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]
    linarith
  set t : ℝ := -(a * ep) with htdef
  have key : 0 ≤ B (X + t • w) (X + t • w) := hpsd _
  have expand : B (X + t • w) (X + t • w) = B X X + t * a + t * (B w X) + t * t * b := by
    simp [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      hadef, hbdef]
    ring
  rw [expand, hX, hsymm w X, ← hadef] at key
  have ha2 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
  have e1 : 0 + t * a + t * a + t * t * b = a ^ 2 * ep * (ep * b - 2) := by
    rw [htdef]; ring
  rw [e1] at key
  have hneg : a ^ 2 * ep * (ep * b - 2) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos ha2 hep) (by linarith)
  linarith

/-- **Goldstone's theorem, curve form.**  If a `C²` potential `V` is constant along a `C²`
curve `γ` through a vacuum `v = γ 0` (a local minimum of `V`), then the velocity `γ'(0)` of
the curve lies in the kernel of the mass form: it is a massless mode. -/
