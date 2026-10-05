/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command, so the header above is a
-- block comment; the same header is repeated as a module docstring below.)

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## The spin–statistics connection

We formalize the algebraic core of the spin–statistics theorem in the Wightman
framework, in the form of Pauli's argument.

A relativistic quantum field is described by:

* a complex inner product space `H` of states with a distinguished vacuum vector `Ω`;
* smeared field operators `φ(f)` and their adjoints `φ(f)†`, indexed by a type `T`
  of test functions;
* a relation `spacelike f g` recording that the supports of `f` and `g` are
  mutually spacelike separated;
* the number `twiceSpin = 2j ∈ ℕ` attached to the (finite dimensional) Lorentz
  representation carried by the field;
* a statistics sign `stat = ε ∈ {+1, -1}`, namely `ε = +1` if the field is
  quantized with commutators (Bose statistics) and `ε = -1` if it is quantized
  with anticommutators (Fermi statistics).

The two dynamical inputs are:

* **Locality**: for spacelike separated `f, g`, the fields (anti)commute, so the
  two Wightman functions `⟪Ω, φ(f) φ(g)† Ω⟫` and `⟪Ω, φ(g)† φ(f) Ω⟫` agree up to
  the statistics sign `ε`.
* **Rotation covariance / analyticity** (the "PCT / Bargmann–Hall–Wightman" input):
  the analytic continuation of the Wightman function to the extended tube, together
  with the behaviour of a spin-`j` field under a `2π` rotation, exchanges the two
  orderings up to the factor `(-1)^{2j}`.

The conclusion, `Frontier.spin_statistics`, is that a field whose two-point
function does not vanish identically at spacelike separation must satisfy
`ε = (-1)^{2j}`: integer spin forces Bose statistics, half-integer spin forces
Fermi statistics.  Equivalently (`Frontier.RelativisticField.wightman_eq_zero_of_wrong_statistics`),
quantizing with the wrong statistics kills the two-point function.

The last two sections show that the hypotheses are not vacuous by exhibiting
an explicit spin-`0` Bose model and an explicit spin-`1/2` Fermi model.
-/

/-- The data and axioms of (the two-point sector of) a relativistic quantum field:
a vacuum vector, smeared field operators together with their adjoints, a notion of
spacelike separation of test functions, the doubled spin `2j`, the statistics sign
`ε`, locality, and the rotation/analyticity relation. -/
structure RelativisticField (T : Type*) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The vacuum state. -/
  vacuum : H
  /-- The smeared field operator `φ(f)`. -/
  field : T → (H →ₗ[ℂ] H)
  /-- The adjoint field operator `φ(f)†`. -/
  adjField : T → (H →ₗ[ℂ] H)
  /-- `adjField f` really is the adjoint of `field f`. -/
  adj_inner : ∀ (f : T) (x y : H), ⟪adjField f x, y⟫_ℂ = ⟪x, field f y⟫_ℂ
  /-- Mutual spacelike separation of the supports of two test functions. -/
  spacelike : T → T → Prop
  /-- Twice the spin, `2j`, of the Lorentz representation carried by the field. -/
  twiceSpin : ℕ
  /-- The statistics sign: `+1` for commutators, `-1` for anticommutators. -/
  stat : ℤ
  /-- The statistics parameter is a sign. -/
  stat_isSign : stat = 1 ∨ stat = -1
  /-- Locality: at spacelike separation the fields commute (`ε = 1`) or
  anticommute (`ε = -1`). -/
  locality : ∀ f g : T, spacelike f g →
    ⟪vacuum, field f (adjField g vacuum)⟫_ℂ
      = (stat : ℂ) * ⟪vacuum, adjField g (field f vacuum)⟫_ℂ
  /-- Rotation covariance together with the analyticity of the Wightman function
  exchanges the two orderings up to the `2π`-rotation phase `(-1)^{2j}`. -/
  rotation : ∀ f g : T, spacelike f g →
    ⟪vacuum, field f (adjField g vacuum)⟫_ℂ
      = (-1 : ℂ) ^ twiceSpin * ⟪vacuum, adjField g (field f vacuum)⟫_ℂ

namespace RelativisticField

variable {T H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (F : RelativisticField T H)

/-- The two-point Wightman function `W(f, g) = ⟪Ω, φ(g)† φ(f) Ω⟫`. -/

def Nondegenerate : Prop :=
  ∃ f g : T, F.spacelike f g ∧ F.wightman f g ≠ 0

/-- The two-point function is the overlap of the states `φ(f) Ω` and `φ(g) Ω`. -/
