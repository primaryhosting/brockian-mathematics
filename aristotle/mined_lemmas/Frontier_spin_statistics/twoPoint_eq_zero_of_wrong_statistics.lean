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

open scoped InnerProductSpace

namespace Frontier

/-!
## The spin–statistics connection

We formalize the algebraic core of the spin–statistics theorem of relativistic quantum field
theory in the Wightman framework.

A *quantum field system* consists of

* a complex Hilbert space `H` of states with a distinguished vacuum vector `Ω`;
* a family of field operators `φ f`, indexed by a type `T` of (real) test functions, each of
  which is a symmetric (hermitian) operator on `H`;
* a relation `spacelike f g`, expressing that the supports of `f` and `g` are spacelike
  separated;
* a number `twoSpin : ℕ`, twice the spin of the field (so integer spin means `twoSpin` even,
  half-integer spin means `twoSpin` odd);
* a statistics sign `stat = ±1`: `+1` for Bose (commutation) statistics, `-1` for Fermi
  (anticommutation) statistics, appearing in the *locality* axiom
  `φ f ∘ φ g = stat • (φ g ∘ φ f)` for spacelike separated `f, g`.

The nontrivial analytic input of the Wightman proof — Lorentz covariance, the spectral
condition and the Bargmann–Hall–Wightman analytic continuation of the two point function — is
summarized in the axiom of *weak local commutativity*: for spacelike separated `f, g` the
two point function satisfies `W f g = (-1)^twoSpin * W g f`.  This is the point at which the
spin enters, and it is Wightman's formulation of the input to the theorem.

The theorem then states: a field system whose fields do not all annihilate the vacuum must have
`stat = (-1)^twoSpin`, i.e. integer spin fields are bosonic and half-integer spin fields are
fermionic.  Wrong statistics forces all two point functions at spacelike separation to vanish,
hence (by the analytic continuation of the two point function to coincident arguments, which we
carry as an explicit hypothesis `hAC`) `‖φ f Ω‖ = 0` for every `f`.
-/

/-- A Wightman-type relativistic quantum field system on a complex Hilbert space `H`, with
fields indexed by a type `T` of test functions. -/
structure WightmanField (T : Type*) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- Spacelike separation of the supports of two test functions. -/
  spacelike : T → T → Prop
  /-- The smeared field operators. -/
  field : T → (H →ₗ[ℂ] H)
  /-- The vacuum vector. -/
  vacuum : H
  /-- Twice the spin of the field. -/
  twoSpin : ℕ
  /-- The statistics sign: `1` for Bose–Einstein, `-1` for Fermi–Dirac statistics. -/
  stat : ℤ
  /-- The statistics sign is `±1`. -/
  stat_sq : stat * stat = 1
  /-- Fields smeared with real test functions are hermitian. -/
  hermitian : ∀ f : T, (field f).IsSymmetric
  /-- Locality: fields at spacelike separation commute (`stat = 1`) or anticommute
  (`stat = -1`). -/
  locality : ∀ f g : T, spacelike f g →
    ∀ x : H, field f (field g x) = (stat : ℂ) • field g (field f x)
  /-- Weak local commutativity: the consequence of Lorentz covariance, the spectral condition
  and the Bargmann–Hall–Wightman theorem which ties the exchange symmetry of the two point
  function to the spin. -/
  weakLocalCommutativity : ∀ f g : T, spacelike f g →
    ⟪vacuum, field f (field g vacuum)⟫_ℂ
      = ((-1 : ℂ) ^ twoSpin) * ⟪vacuum, field g (field f vacuum)⟫_ℂ

namespace WightmanField

variable {T : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The two point Wightman function `W f g = ⟪Ω, φ f φ g Ω⟫`. -/

theorem twoPoint_eq_zero_of_wrong_statistics (W : WightmanField T H)
    (hwrong : (W.stat : ℂ) = -(-1 : ℂ) ^ W.twoSpin) {f g : T} (hfg : W.spacelike f g) :
    W.twoPoint f g = 0 := by
  have hloc : W.twoPoint f g = (W.stat : ℂ) * W.twoPoint g f := by
    unfold twoPoint
    rw [W.locality f g hfg W.vacuum, inner_smul_right]
  have hwlc : W.twoPoint f g = ((-1 : ℂ) ^ W.twoSpin) * W.twoPoint g f :=
    W.weakLocalCommutativity f g hfg
  have hpow : ((-1 : ℂ) ^ W.twoSpin) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hzero : W.twoPoint g f = 0 := by
    have h2 : ((-1 : ℂ) ^ W.twoSpin) * W.twoPoint g f
        = -((-1 : ℂ) ^ W.twoSpin) * W.twoPoint g f := by
      rw [← hwlc, hloc, hwrong]
    have : (2 : ℂ) * (((-1 : ℂ) ^ W.twoSpin) * W.twoPoint g f) = 0 := by linear_combination h2
    have := mul_eq_zero.mp this
    rcases this with h | h
    · norm_num at h
    · exact (mul_eq_zero.mp h).resolve_left hpow
  rw [hwlc, hzero, mul_zero]

/-- **Wrong statistics forces the field to annihilate the vacuum.**  Here `hAC` is the analytic
continuation input: a two point function vanishing at all spacelike separations vanishes at
coincident arguments as well. -/
