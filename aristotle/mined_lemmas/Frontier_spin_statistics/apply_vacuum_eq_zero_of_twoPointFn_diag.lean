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

namespace Frontier

/-!
## The spin–statistics connection

We formalize the Pauli spin–statistics theorem in its standard *contrapositive*
(Wightman) form:

> A relativistic quantum field whose *statistics sign* `σ` does not match the
> *exchange symmetry sign* `ε = (-1)^{2s}` of its two–point Wightman function
> must vanish identically.

The setting is an abstract Wightman-type framework:

* `H` is the (complex) Hilbert space of states and `Ω : H` the vacuum vector;
* `V` is the spacetime (or the index set of smeared field operators) and
  `S : V → V → Prop` is the relation *"the two arguments are spacelike
  separated"* (symmetric, by `hSsymm`);
* `Φ : V → H →ₗ[ℂ] H` is the (hermitian) field operator;
* `Frontier.twoPointFn Ω Φ x y = ⟪Ω, Φ x (Φ y Ω)⟫` is the two-point Wightman
  function.

The physical inputs appear as hypotheses:

* `hherm`  : hermiticity of the field, `⟪Φ x u, v⟫ = ⟪u, Φ x v⟫`;
* `hstat`  : the (generalized) locality / statistics axiom, saying that at
  spacelike separation the fields commute up to the sign `σ`
  (`σ = 1`: bosonic commutation, `σ = -1`: fermionic anticommutation);
* `hsymm`  : Lorentz covariance of the two-point function, which for a field of
  spin `s` exchanges its arguments with the sign `ε = (-1)^{2s}`
  (`ε = 1` for integer spin, `ε = -1` for half-integer spin);
* `hmismatch` : `σ * ε = -1`, i.e. the statistics is the *wrong* one for the
  spin (integer spin quantized with anticommutators, or half-integer spin
  quantized with commutators);
* `hanalytic` : the analyticity / edge-of-the-wedge input of the Wightman
  framework: a two-point function vanishing at all spacelike separations
  vanishes at coincident points as well;
* `hReehSchlieder` : the Reeh–Schlieder property, i.e. the vacuum is separating
  for the field algebra: if `Φ x Ω = 0` for all `x` then `Φ x = 0`.

The conclusion is that the field is trivial, `Φ x = 0` for every `x`.
-/

section

variable {V H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The two-point Wightman function `W(x, y) = ⟪Ω, Φ(x) Φ(y) Ω⟫` of a field `Φ`
in the state `Ω`. -/

theorem apply_vacuum_eq_zero_of_twoPointFn_diag
    {Ω : H} {Φ : V → H →ₗ[ℂ] H}
    (hherm : ∀ (x : V) (u v : H), inner ℂ (Φ x u) v = inner ℂ u (Φ x v))
    (hdiag : ∀ x : V, twoPointFn Ω Φ x x = 0) :
    ∀ x : V, Φ x Ω = 0 := by
  intro x
  have : inner ℂ (Φ x Ω) (Φ x Ω) = (0 : ℂ) := by
    rw [hherm x Ω (Φ x Ω)]
    exact hdiag x
  exact inner_self_eq_zero.mp this

/-- **Spin–statistics theorem** (Wightman form, stated contrapositively).

A hermitian relativistic quantum field `Φ` on a Hilbert space `H` with vacuum
`Ω`, obeying at spacelike separation the (anti)commutation relation with
statistics sign `σ`, and whose two-point Wightman function has exchange
symmetry sign `ε = (-1)^{2s}` dictated by its spin `s`, must vanish identically
whenever the two signs are mismatched, i.e. `σ * ε = -1`.

Concretely: an integer-spin field (`ε = 1`) quantized with anticommutators
(`σ = -1`), or a half-integer-spin field (`ε = -1`) quantized with commutators
(`σ = 1`), is the zero field. -/
