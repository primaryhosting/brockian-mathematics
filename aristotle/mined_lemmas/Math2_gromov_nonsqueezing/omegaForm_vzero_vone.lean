import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

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

namespace Math2

/-- The standard symplectic vector space `ℝ^{2(n+1)}`, realized as the Euclidean space with
index set `Fin (n+1) × Fin 2`: the index `(i, 0)` is the position coordinate `q i` and the
index `(i, 1)` is the momentum coordinate `p i`. -/
abbrev SympSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1) × Fin 2)

/-- The standard symplectic form `ω = ∑ i, dq i ∧ dp i` on `SympSpace n`. -/

lemma omegaForm_vzero_vone {n : ℕ} : omegaForm (vzero n) (vone n) = 1 := by
  rw [omegaForm_vzero]
  simp [vone]

/-! ### Linear Gromov nonsqueezing -/

/--
**Gromov's nonsqueezing theorem** (the linear case).

If a linear symplectomorphism `Φ` of the standard symplectic vector space `ℝ^{2(n+1)}`
maps the open ball of radius `r` into the open symplectic cylinder of radius `R`
(the set of points whose first conjugate pair of coordinates has norm `< R`), then `r ≤ R`.

In other words, a symplectic map cannot squeeze a ball into a thinner cylinder: no
volume-preserving trickery in the remaining `2n` directions can help.
-/
