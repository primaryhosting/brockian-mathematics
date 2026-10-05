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
noncomputable def twoPointFn (Ω : H) (Φ : V → H →ₗ[ℂ] H) (x y : V) : ℂ :=
  inner ℂ Ω (Φ x (Φ y Ω))

/-- With the *wrong* statistics, the two-point function vanishes at spacelike
separation: the statistics sign `σ` and the exchange sign `ε` of the two-point
function force `W(x,y) = σ * ε * W(x,y) = -W(x,y)`. -/
theorem twoPointFn_eq_zero_of_spacelike
    {S : V → V → Prop} {Ω : H} {Φ : V → H →ₗ[ℂ] H} {σ ε : ℂ}
    (hSsymm : ∀ x y : V, S x y → S y x)
    (hstat : ∀ x y : V, S x y → ∀ u : H, Φ x (Φ y u) = σ • Φ y (Φ x u))
    (hsymm : ∀ x y : V, S x y → twoPointFn Ω Φ x y = ε * twoPointFn Ω Φ y x)
    (hmismatch : σ * ε = -1) :
    ∀ x y : V, S x y → twoPointFn Ω Φ x y = 0 := by
  intro x y hxy
  -- From the statistics axiom: `W(x,y) = σ * W(y,x)`.
  have h1 : twoPointFn Ω Φ x y = σ * twoPointFn Ω Φ y x := by
    unfold twoPointFn
    rw [hstat x y hxy Ω, inner_smul_right]
  -- From Lorentz covariance: `W(y,x) = ε * W(x,y)`.
  have h2 : twoPointFn Ω Φ y x = ε * twoPointFn Ω Φ x y := hsymm y x (hSsymm x y hxy)
  -- hence `W(x,y) = σ * ε * W(x,y) = -W(x,y)`, so `2 * W(x,y) = 0`.
  linear_combination (h1 + σ * h2) / 2 + twoPointFn Ω Φ x y * hmismatch / 2

/-- If the two-point function vanishes at coincident points, then the field
annihilates the vacuum (positivity of the inner product). -/
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
theorem spin_statistics
    (S : V → V → Prop) (Ω : H) (Φ : V → H →ₗ[ℂ] H) (σ ε : ℂ)
    -- the field is hermitian
    (hherm : ∀ (x : V) (u v : H), inner ℂ (Φ x u) v = inner ℂ u (Φ x v))
    -- spacelike separation is a symmetric relation
    (hSsymm : ∀ x y : V, S x y → S y x)
    -- locality with statistics sign `σ`
    (hstat : ∀ x y : V, S x y → ∀ u : H, Φ x (Φ y u) = σ • Φ y (Φ x u))
    -- Lorentz covariance: exchange symmetry sign `ε = (-1)^{2s}` of the
    -- two-point function
    (hsymm : ∀ x y : V, S x y → twoPointFn Ω Φ x y = ε * twoPointFn Ω Φ y x)
    -- wrong statistics for the spin
    (hmismatch : σ * ε = -1)
    -- Wightman analyticity (edge of the wedge)
    (hanalytic : (∀ x y : V, S x y → twoPointFn Ω Φ x y = 0) →
      ∀ x : V, twoPointFn Ω Φ x x = 0)
    -- Reeh–Schlieder: the vacuum is separating for the field
    (hReehSchlieder : (∀ x : V, Φ x Ω = 0) → ∀ x : V, Φ x = 0) :
    ∀ x : V, Φ x = 0 := by
  refine hReehSchlieder (apply_vacuum_eq_zero_of_twoPointFn_diag hherm
    (hanalytic ?_))
  exact twoPointFn_eq_zero_of_spacelike hSsymm hstat hsymm hmismatch

end

/-!
### The hypotheses are not vacuous

The sign mismatch `σ * ε = -1` is genuinely responsible for the conclusion: all
the remaining hypotheses of `Frontier.spin_statistics` are simultaneously
satisfiable by a *nonzero* field (here the identity operator on `H = ℂ` with
vacuum `Ω = 1`, which has bosonic statistics `σ = 1` and integer-spin exchange
symmetry `ε = 1`, so that `σ * ε = 1 ≠ -1`).
-/
theorem spin_statistics_hypotheses_nonvacuous :
    ∃ (Ω : ℂ) (Φ : Unit → ℂ →ₗ[ℂ] ℂ) (σ ε : ℂ),
      (∀ (x : Unit) (u v : ℂ), inner ℂ (Φ x u) v = inner ℂ u (Φ x v)) ∧
      (∀ x y : Unit, (fun _ _ : Unit => True) x y → (fun _ _ : Unit => True) y x) ∧
      (∀ x y : Unit, (fun _ _ : Unit => True) x y → ∀ u : ℂ,
        Φ x (Φ y u) = σ • Φ y (Φ x u)) ∧
      (∀ x y : Unit, (fun _ _ : Unit => True) x y →
        twoPointFn Ω Φ x y = ε * twoPointFn Ω Φ y x) ∧
      ((∀ x y : Unit, (fun _ _ : Unit => True) x y → twoPointFn Ω Φ x y = 0) →
        ∀ x : Unit, twoPointFn Ω Φ x x = 0) ∧
      ((∀ x : Unit, Φ x Ω = 0) → ∀ x : Unit, Φ x = 0) ∧
      ¬ (∀ x : Unit, Φ x = 0) := by
  refine ⟨1, fun _ => LinearMap.id, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ u v
    simp [RCLike.inner_apply]
  · intro _ _ _; trivial
  · intro _ _ _ u; simp
  · intro _ _ _; simp
  · intro h
    exact absurd (h () () trivial) (by simp [twoPointFn])
  · intro h
    exact absurd (h ()) (by simp)
  · intro h
    have := congrArg (fun f => f (1 : ℂ)) (h ())
    simp at this

/-- The classical **base case**: a *scalar* (spin `0`, hence `ε = 1`) field
quantized with *anticommutators* (`σ = -1`) is identically zero. -/
theorem spin_zero_anticommuting_field_eq_zero
    {V H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : V → V → Prop) (Ω : H) (Φ : V → H →ₗ[ℂ] H)
    (hherm : ∀ (x : V) (u v : H), inner ℂ (Φ x u) v = inner ℂ u (Φ x v))
    (hSsymm : ∀ x y : V, S x y → S y x)
    -- anticommutation at spacelike separation: `{Φ(x), Φ(y)} = 0`
    (hanti : ∀ x y : V, S x y → ∀ u : H, Φ x (Φ y u) + Φ y (Φ x u) = 0)
    -- spin 0: the two-point function is symmetric at spacelike separation
    (hsymm : ∀ x y : V, S x y → twoPointFn Ω Φ x y = twoPointFn Ω Φ y x)
    (hanalytic : (∀ x y : V, S x y → twoPointFn Ω Φ x y = 0) →
      ∀ x : V, twoPointFn Ω Φ x x = 0)
    (hReehSchlieder : (∀ x : V, Φ x Ω = 0) → ∀ x : V, Φ x = 0) :
    ∀ x : V, Φ x = 0 := by
  refine spin_statistics S Ω Φ (-1) 1 hherm hSsymm ?_ ?_ (by ring) hanalytic
    hReehSchlieder
  · intro x y hxy u
    have := hanti x y hxy u
    rw [neg_one_smul]
    linear_combination (norm := module) this
  · intro x y hxy
    rw [hsymm x y hxy, one_mul]

/-- The dual **base case**: a *spinor* (half-integer spin, hence `ε = -1`) field
quantized with *commutators* (`σ = 1`) is identically zero. -/
theorem spin_half_commuting_field_eq_zero
    {V H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : V → V → Prop) (Ω : H) (Φ : V → H →ₗ[ℂ] H)
    (hherm : ∀ (x : V) (u v : H), inner ℂ (Φ x u) v = inner ℂ u (Φ x v))
    (hSsymm : ∀ x y : V, S x y → S y x)
    -- commutation at spacelike separation: `[Φ(x), Φ(y)] = 0`
    (hcomm : ∀ x y : V, S x y → ∀ u : H, Φ x (Φ y u) = Φ y (Φ x u))
    -- half-integer spin: the two-point function is antisymmetric at spacelike
    -- separation
    (hsymm : ∀ x y : V, S x y → twoPointFn Ω Φ x y = -twoPointFn Ω Φ y x)
    (hanalytic : (∀ x y : V, S x y → twoPointFn Ω Φ x y = 0) →
      ∀ x : V, twoPointFn Ω Φ x x = 0)
    (hReehSchlieder : (∀ x : V, Φ x Ω = 0) → ∀ x : V, Φ x = 0) :
    ∀ x : V, Φ x = 0 := by
  refine spin_statistics S Ω Φ 1 (-1) hherm hSsymm ?_ ?_ (by ring) hanalytic
    hReehSchlieder
  · intro x y hxy u
    rw [one_smul]
    exact hcomm x y hxy u
  · intro x y hxy
    rw [hsymm x y hxy]; ring

end Frontier

