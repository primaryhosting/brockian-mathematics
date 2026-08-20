/-!
# Pell 6
Category: Pure Mathematics
Target: Math.pell_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² - 6·y² = 1` has a nontrivial integer solution, i.e. one
with `y ≠ 0`: take `(x, y) = (5, 2)`, since `5² - 6·2² = 25 - 24 = 1`.

Since the required header comment must be the first thing in this file, the file cannot
carry an `import` line (Lean requires imports to precede any module documentation), so the
statement is phrased with core `Int` multiplication `x * x` in place of `x ^ 2`.  A version
using `^` and stated over `ℤ`, together with the fact that there are infinitely many
solutions, is proved in `RequestProject.Pell6Extra`. -/

theorem pell_6_infinite : {p : ℤ × ℤ | p.1 ^ 2 - 6 * p.2 ^ 2 = 1}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨⟨a, b⟩, hab⟩
  obtain ⟨x, y, hsol, _, hy⟩ := pell_6_large (b.toNat + 1)
  have hmem : ((x, y) : ℤ × ℤ) ∈ {p : ℤ × ℤ | p.1 ^ 2 - 6 * p.2 ^ 2 = 1} := hsol
  have := (hab hmem).2
  have hb : (b : ℤ) ≤ b.toNat := Int.self_le_toNat b
  push_cast at hy
  omega

end Math

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

