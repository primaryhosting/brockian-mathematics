/-
# Fermat Little
Category: Pure Mathematics
Target: Math.fermat_little
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede every command, including
-- module docstrings (`/-! ... -/`), so the header above is a plain block
-- comment; it is repeated as the module docstring after the import below.
import Mathlib

/-!
# Fermat Little
Category: Pure Mathematics
Target: Math.fermat_little
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Fermat's little theorem**: if `p` is prime and `p ∤ a`, then
`a ^ (p - 1) ≡ 1 [ZMOD p]`, stated for integers `a`.
The key Mathlib ingredient is `ZMod.pow_card_sub_one_eq_one`. -/
theorem fermat_little {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    a ^ (p - 1) ≡ 1 [ZMOD (p : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha' : (a : ZMod p) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha
  have h1 := ZMod.pow_card_sub_one_eq_one ha'
  have h : ((a ^ (p - 1) : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) := by
    push_cast
    simpa using h1
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp (by simpa using h)

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

