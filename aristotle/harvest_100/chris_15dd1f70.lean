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
noncomputable def twoPoint (f g : TestFn) : ℂ :=
  inner ℂ W.vacuum (W.field f (W.field g W.vacuum))

/-- The field is nontrivial if some smeared field operator does not annihilate the vacuum. -/
def Nontrivial : Prop := ∃ f : TestFn, W.field f W.vacuum ≠ 0

/-- Hermiticity turns the coincident two-point function into a squared norm. -/
theorem twoPoint_self (f : TestFn) :
    W.twoPoint f f = inner ℂ (W.field f W.vacuum) (W.field f W.vacuum) := by
  rw [twoPoint, ← ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.star_eq_adjoint, W.hermitian f]

/-- If the statistics sign disagrees with the spin sign, then the two-point function
vanishes for spacelike separated test functions. -/
theorem twoPoint_eq_zero_of_spacelike
    (h : (W.statistics : ℂ) ≠ (-1 : ℂ) ^ W.twiceSpin)
    (f g : TestFn) (hfg : W.spacelikeSep f g) : W.twoPoint f g = 0 := by
  have hloc : W.twoPoint g f = (W.statistics : ℂ) * W.twoPoint f g := by
    have := W.locality g f (W.sep_symm f g hfg)
    have h2 : W.field g (W.field f W.vacuum)
        = (W.statistics : ℂ) • W.field f (W.field g W.vacuum) := by
      have := congrArg (fun A : H →L[ℂ] H => A W.vacuum) this
      simpa using this
    simp [twoPoint, h2]
  have hwlc : W.twoPoint g f = (-1 : ℂ) ^ W.twiceSpin * W.twoPoint f g :=
    W.weakLocalCommutativity g f
  have : ((W.statistics : ℂ) - (-1 : ℂ) ^ W.twiceSpin) * W.twoPoint f g = 0 := by
    rw [sub_mul, ← hloc, ← hwlc, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) h
  · exact h0

/-- If the statistics sign disagrees with the spin sign, the field annihilates the vacuum. -/
theorem field_vacuum_eq_zero_of_wrong_statistics
    (h : (W.statistics : ℂ) ≠ (-1 : ℂ) ^ W.twiceSpin) (f : TestFn) :
    W.field f W.vacuum = 0 := by
  have hall : ∀ f g : TestFn, W.twoPoint f g = 0 :=
    W.twoPoint_vanishing fun f g hfg => W.twoPoint_eq_zero_of_spacelike h f g hfg
  have := (W.twoPoint_self f).symm.trans (hall f f)
  exact inner_self_eq_zero.mp this

end WightmanField

/--
**Spin–statistics connection.**

For a hermitian relativistic quantum field satisfying the Wightman framework recorded in
`Frontier.WightmanField` (locality with statistics sign `σ` at spacelike separation, Jost's
weak local commutativity for the two-point function with spin sign `(-1) ^ (2s)`, and analytic
continuation of the two-point function), nontriviality of the field forces

  `σ = (-1) ^ (2s)`,

i.e. integer-spin fields obey Bose statistics and half-integer-spin fields obey Fermi
statistics. Equivalently: a field quantized with the wrong statistics annihilates the vacuum
(and hence, by Reeh–Schlieder, vanishes).
-/
theorem spin_statistics {H TestFn : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (W : WightmanField H TestFn) (hW : W.Nontrivial) :
    W.statistics = (-1 : ℤ) ^ W.twiceSpin := by
  by_contra h
  obtain ⟨f, hf⟩ := hW
  refine hf (W.field_vacuum_eq_zero_of_wrong_statistics ?_ f)
  intro hc
  exact h (by exact_mod_cast hc)

/-- Integer spin (`2s` even) implies Bose statistics for a nontrivial field. -/
theorem bose_statistics_of_integer_spin {H TestFn : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (W : WightmanField H TestFn)
    (hW : W.Nontrivial) (hs : Even W.twiceSpin) : W.statistics = 1 := by
  rw [spin_statistics W hW, hs.neg_one_pow]

/-- Half-integer spin (`2s` odd) implies Fermi statistics for a nontrivial field. -/
theorem fermi_statistics_of_half_integer_spin {H TestFn : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (W : WightmanField H TestFn)
    (hW : W.Nontrivial) (hs : Odd W.twiceSpin) : W.statistics = -1 := by
  rw [spin_statistics W hW, hs.neg_one_pow]

/-- A nontrivial model of the axioms, showing the hypotheses of `Frontier.spin_statistics`
are not vacuous: the spin-`0`, Bose-quantized field `φ(f) = 1` on `H = ℂ`. -/
noncomputable def trivialSpinZeroField : WightmanField ℂ Unit where
  field := fun _ => ContinuousLinearMap.id ℂ ℂ
  vacuum := 1
  spacelikeSep := fun _ _ => True
  twiceSpin := 0
  statistics := 1
  statistics_sign := Or.inl rfl
  hermitian := fun _ => by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
  sep_symm := fun _ _ _ => trivial
  locality := fun _ _ _ => by simp
  weakLocalCommutativity := fun _ _ => by simp
  twoPoint_vanishing := fun h => fun f g => h f g trivial

theorem trivialSpinZeroField_nontrivial : trivialSpinZeroField.Nontrivial :=
  ⟨(), by simp [trivialSpinZeroField]⟩

end Frontier

