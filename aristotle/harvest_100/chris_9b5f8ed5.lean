/-
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28 requires `import` before any module docstring `/-! ... -/`,
-- so the header above is given as a plain block comment and repeated below.)

import Mathlib

/-!
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
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

universe u

namespace Ordinal

/-- **Key intermediate lemma.** Every normal function on the ordinals has a fixed point:
the next fixed point `nfp f a` above any ordinal `a` is one. -/
theorem exists_fixed_point_of_isNormal {f : Ordinal.{u} → Ordinal.{u}} (hf : Order.IsNormal f)
    (a : Ordinal.{u}) : ∃ o : Ordinal.{u}, a ≤ o ∧ f o = o :=
  ⟨nfp f a, le_nfp f a, nfp_fp hf a⟩

end Ordinal

namespace Cardinal

/-- **Aleph fixed point.** The aleph function, viewed as a normal function on the ordinals via
`fun o => (aleph o).ord`, has a fixed point: there is an ordinal `o` with `(aleph o).ord = o`
(equivalently `ω_ o = o`), and such `o` can be found above any given ordinal. -/
theorem aleph_fixed_point_statement :
    ∃ o : Ordinal.{u}, (Cardinal.aleph o).ord = o := by
  have hnormal : Order.IsNormal (fun o : Ordinal.{u} => (Cardinal.aleph o).ord) := by
    simpa [Cardinal.ord_aleph] using Ordinal.isNormal_omega.{u}
  obtain ⟨o, -, ho⟩ := Ordinal.exists_fixed_point_of_isNormal hnormal 0
  exact ⟨o, ho⟩

end Cardinal

