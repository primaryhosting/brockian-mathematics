/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment; the same text is repeated below as the module docstring.)

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
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

open Polynomial

/-! ### Hermite polynomials: the Hermite differential equation

Mathlib provides `Polynomial.hermite : ℕ → ℤ[X]` (the *probabilists'* Hermite polynomials)
together with `Polynomial.hermite_succ`, but not the Hermite ODE, which we derive here. -/

/-- The Hermite differential equation `He_n'' = X * He_n' - n * He_n`. -/

theorem landau_levels_explicit (hbar m charge B k : ℝ) (hh : 0 < hbar) (hm : 0 < m)
    (hcharge : 0 < charge) (hB : 0 < B) (n : ℕ) (x y : ℝ) :
    (1 / (2 * (m : ℂ)))
        * (kineticPx hbar (kineticPx hbar (landauState hbar m charge B k n)) x y
          + kineticPy hbar charge B
              (kineticPy hbar charge B (landauState hbar m charge B k n)) x y)
      = ((hbar * cyclotronFreq charge B m * (n + 1 / 2) : ℝ) : ℂ)
          * landauState hbar m charge B k n x y :=
  landau_levels hbar m charge B k hh hm hcharge hB n _ rfl _ rfl _ rfl
    (landauProfile hbar m charge B k n) (fun _ => rfl)
    (landauState hbar m charge B k n) (fun _ _ => rfl)
    (kineticPx hbar) (kineticPy hbar charge B) (fun _ _ _ => rfl) (fun _ _ _ => rfl) x y

end Frontier

