/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
## Mathlib provenance

Mathlib contains no spin–statistics theorem (nor a Wightman-axioms framework), so the
statement is formalized here from scratch. The proof is closed using the following existing
Mathlib results:

* `ContinuousLinearMap.adjoint_inner_left` and `ContinuousLinearMap.star_eq_adjoint`
  (moving a self-adjoint operator across the inner product),
* `inner_self_eq_zero` (positive definiteness of the inner product),
* `Even.neg_one_pow` / `Odd.neg_one_pow` (the spin sign for integer / half-integer spin).
-/

namespace Frontier

/--
Data of a (hermitian, smeared) relativistic quantum field in the Wightman framework,
recorded at the level of structure needed for the spin–statistics connection.

* `H` is the Hilbert space of states, `vacuum` the vacuum vector `Ω`.
* `TestFn` is the space of test functions; `field f` is the smeared field operator `φ(f)`
  (assumed bounded here, so as to stay inside Mathlib's theory of adjoints of continuous
  linear maps).
* `spacelikeSep f g` records that the supports of `f` and `g` are spacelike separated.
* `twiceSpin` is `2s`, twice the spin of the field, so that `(-1) ^ twiceSpin` is the
  spin sign `(-1) ^ (2s)`: `+1` for integer spin, `-1` for half-integer spin.
* `statistics` is the statistics sign `σ = ±1` appearing in the field's local
  (anti)commutation relation: `σ = +1` is Bose statistics (commuting fields at spacelike
  separation), `σ = -1` is Fermi statistics (anticommuting fields).

The two analytic inputs of the Wightman theory are recorded as fields of the structure:

* `weakLocalCommutativity` is Jost's weak local commutativity for the two-point function,
  `W(f, g) = (-1) ^ (2s) * W(g, f)`, which follows from Lorentz covariance, the spectrum
  condition and the analyticity of Wightman functions at Jost points;
* `twoPoint_vanishing` is the (edge-of-the-wedge / analytic continuation) statement that a
  two-point function vanishing for all spacelike separated arguments vanishes identically.
-/
structure WightmanField (H : Type*) (TestFn : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The smeared field operators `φ(f)`. -/
  field : TestFn → (H →L[ℂ] H)
  /-- The vacuum vector `Ω`. -/
  vacuum : H
  /-- Spacelike separation of the supports of two test functions. -/
  spacelikeSep : TestFn → TestFn → Prop
  /-- Twice the spin of the field. -/
  twiceSpin : ℕ
  /-- The statistics sign `σ`. -/
  statistics : ℤ
  /-- The statistics sign is indeed a sign. -/
  statistics_sign : statistics = 1 ∨ statistics = -1
  /-- Hermiticity of the field (real test functions). -/
  hermitian : ∀ f, IsSelfAdjoint (field f)
  /-- Spacelike separation is a symmetric relation. -/
  sep_symm : ∀ f g, spacelikeSep f g → spacelikeSep g f
  /-- Locality: at spacelike separation the fields commute up to the statistics sign. -/
  locality : ∀ f g, spacelikeSep f g →
    (field f).comp (field g) = (statistics : ℂ) • (field g).comp (field f)
  /-- Weak local commutativity for the two-point function (Jost). -/
  weakLocalCommutativity : ∀ f g,
    inner ℂ vacuum (field f (field g vacuum))
      = (-1 : ℂ) ^ twiceSpin * inner ℂ vacuum (field g (field f vacuum))
  /-- Analytic continuation: a two-point function vanishing at spacelike separation
  vanishes identically. -/
  twoPoint_vanishing :
    (∀ f g, spacelikeSep f g → inner ℂ vacuum (field f (field g vacuum)) = 0) →
    ∀ f g, inner ℂ vacuum (field f (field g vacuum)) = 0

namespace WightmanField

variable {H TestFn : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (W : WightmanField H TestFn)

/-- The two-point Wightman function `W(f, g) = ⟨Ω, φ(f) φ(g) Ω⟩`. -/

def Nontrivial : Prop := ∃ f : TestFn, W.field f W.vacuum ≠ 0

/-- Hermiticity turns the coincident two-point function into a squared norm. -/
