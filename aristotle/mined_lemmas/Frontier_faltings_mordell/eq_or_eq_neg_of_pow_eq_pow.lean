import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MvPolynomial

/-! ## Setting up plane curves over `ℚ` -/

/-- The set of `ℚ`-rational points of the projective plane curve cut out by a homogeneous
form `F` in three variables. A point of `ℙ²(ℚ)` is represented as a point of
`Projectivization ℚ (Fin 3 → ℚ)`; since `F` is homogeneous, vanishing of `F` at a
representative does not depend on the chosen representative (see
`Frontier.mem_projPoints_fermatForm_iff` for the case used below). -/

theorem eq_or_eq_neg_of_pow_eq_pow {x y : ℚ} {n : ℕ} (hn : n ≠ 0) (he : Even n)
    (h : x ^ n = y ^ n) : x = y ∨ x = -y := by
  rw [← abs_eq_abs]
  have habs : |x| ^ n = |y| ^ n := by rw [he.pow_abs, he.pow_abs, h]
  exact (pow_left_inj₀ (abs_nonneg _) (abs_nonneg _) hn).mp habs

/-- The rational points of the Fermat curve of degree `n`, for `n` a positive multiple of `4`,
are among the four "trivial" points. -/
