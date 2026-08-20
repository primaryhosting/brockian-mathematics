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

import Brockian.Weyl.Primitive

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Deficiency elements of a Sturm–Liouville operator are genuine ODE solutions

Let `q : ℝ → ℝ` be a continuous potential on an interval `(a, b)` and let `lam : ℂ`.  The
*minimal operator* associated with the formally symmetric differential expression
`τ u = -u'' + q u` is the restriction of `τ` to smooth compactly supported functions in
`(a, b)`.  A function `y ∈ L²(a, b)` lies in the deficiency space of the minimal operator
at `lam` exactly when it is orthogonal to the range of `τ - conj lam` on test functions,
that is when
`∫ conj (y x) * (-(g'' x) + q x * g x - conj lam * g x) = 0`
for every test function `g` supported in `(a, b)`; see `InDeficiencySpace`.

The main theorem `deficiencyRepresentsODE_of_weakRegularity` states that the deficiency
space is exactly the space of `L²` solutions of the ordinary differential equation
`-u'' + q u = lam * u`, i.e. every deficiency element is (a.e. equal to) a genuine, twice
differentiable, classical solution of the ODE.

The hard direction rests on the one-dimensional elliptic regularity statement
`weakRegularity` (Weyl's lemma): a locally integrable distributional solution of
`-y'' + q y = lam y` agrees a.e. with a classical solution.  It is proved here, so the
main theorem is unconditional.
-/

namespace Brockian.Weyl.DeficiencyODE

open MeasureTheory Set Function Brockian.Weyl

/-- The smoothness exponent `∞`. -/
local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `IsODESolutionOn q lam s u` says that `u` is a classical solution of
`-u'' + q u = lam * u` on the set `s`: `u` is differentiable with a differentiable
derivative `u'` and `u'' = (q - lam) * u` on `s`. -/

def IsODESolutionOn (q : ℝ → ℝ) (lam : ℂ) (s : Set ℝ) (u : ℝ → ℂ) : Prop :=
  ∃ u' : ℝ → ℂ, (∀ x ∈ s, HasDerivAt u (u' x) x) ∧
    ∀ x ∈ s, HasDerivAt u' (((q x : ℂ) - lam) * u x) x

/-- `InDeficiencySpace q lam a b y` says that `y` is an `L²` function on `(a, b)` which is
orthogonal to the range of `τ - conj lam` applied to test functions, where
`τ u = -u'' + q u`; i.e. `y` belongs to the deficiency space of the minimal operator
at `lam`. -/
