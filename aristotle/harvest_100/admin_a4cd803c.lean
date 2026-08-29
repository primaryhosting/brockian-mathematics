import Mathlib
/-!
# Chinese Remainder
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace NumberTheory

/-- The Chinese remainder ring equivalence: for coprime `m n : ℕ`,
`ZMod (m * n)` is ring-isomorphic to `ZMod m × ZMod n`. -/
noncomputable def chineseRemainderEquiv {m n : ℕ} (h : Nat.Coprime m n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- **Chinese remainder theorem**: for coprime `m n : ℕ` there is a ring equivalence
`ZMod (m * n) ≃+* ZMod m × ZMod n`. -/
theorem chinese_remainder {m n : ℕ} (h : Nat.Coprime m n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨chineseRemainderEquiv h⟩

/-- The equivalence is given by the pair of the canonical ring homomorphisms
(reduction of residues mod `m * n` to residues mod `m` and mod `n`). -/
theorem chineseRemainderEquiv_apply {m n : ℕ} (h : Nat.Coprime m n) (x : ZMod (m * n)) :
    chineseRemainderEquiv h x =
      (ZMod.castHom (Dvd.intro n rfl) (ZMod m) x,
        ZMod.castHom (Dvd.intro_left m rfl) (ZMod n) x) := by
  simp [chineseRemainderEquiv, ZMod.chineseRemainder, Prod.ext_iff]

end NumberTheory

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

