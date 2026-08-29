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
def twoPoint (W : WightmanField T H) (f g : T) : ℂ :=
  ⟪W.vacuum, W.field f (W.field g W.vacuum)⟫_ℂ

/-- The statistics sign is `1` or `-1`. -/
theorem stat_eq_one_or (W : WightmanField T H) : W.stat = 1 ∨ W.stat = -1 :=
  Int.isUnit_iff.mp (IsUnit.of_mul_eq_one W.stat W.stat_sq)

/-- The norm squared of `φ f Ω` is the two point function at coincident arguments. -/
theorem twoPoint_self (W : WightmanField T H) (f : T) :
    W.twoPoint f f = ⟪W.field f W.vacuum, W.field f W.vacuum⟫_ℂ :=
  (W.hermitian f W.vacuum (W.field f W.vacuum)).symm

/-- **Wrong statistics kills the two point function.**  If the statistics sign is opposite to
the sign `(-1)^(2s)` dictated by the spin, then all two point functions at spacelike separation
vanish. -/
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
theorem field_vacuum_eq_zero_of_wrong_statistics (W : WightmanField T H)
    (hwrong : (W.stat : ℂ) = -(-1 : ℂ) ^ W.twoSpin)
    (hAC : (∀ f g : T, W.spacelike f g → W.twoPoint f g = 0) → ∀ f : T, W.twoPoint f f = 0)
    (f : T) : W.field f W.vacuum = 0 := by
  have h := hAC (fun f g hfg => W.twoPoint_eq_zero_of_wrong_statistics hwrong hfg) f
  rw [W.twoPoint_self f] at h
  exact inner_self_eq_zero.mp h

end WightmanField

/-- **The spin–statistics theorem.**  In a Wightman quantum field system whose field does not
annihilate the vacuum, the statistics sign is determined by the spin:
`stat = (-1)^(2s)`, i.e. integer spin fields obey Bose statistics and half-integer spin fields
obey Fermi statistics.

The analytic input of the Wightman proof enters through the weak local commutativity axiom of
`Frontier.WightmanField` and through the hypothesis `hAC` (analytic continuation of the two
point function to coincident arguments). -/
theorem spin_statistics {T : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (W : WightmanField T H)
    (hAC : (∀ f g : T, W.spacelike f g → W.twoPoint f g = 0) → ∀ f : T, W.twoPoint f f = 0)
    (hnontrivial : ∃ f : T, W.field f W.vacuum ≠ 0) :
    (W.stat : ℂ) = (-1 : ℂ) ^ W.twoSpin := by
  by_contra hne
  obtain ⟨f, hf⟩ := hnontrivial
  refine hf (W.field_vacuum_eq_zero_of_wrong_statistics ?_ hAC f)
  rcases W.stat_eq_one_or with hs | hs <;> rcases neg_one_pow_eq_or ℂ W.twoSpin with he | he <;>
    rw [hs, he] at hne ⊢ <;> revert hne <;> norm_num

/-- Integer spin fields are bosons. -/
theorem integer_spin_bose {T : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (W : WightmanField T H)
    (hAC : (∀ f g : T, W.spacelike f g → W.twoPoint f g = 0) → ∀ f : T, W.twoPoint f f = 0)
    (hnontrivial : ∃ f : T, W.field f W.vacuum ≠ 0) (hspin : Even W.twoSpin) :
    W.stat = 1 := by
  have h := spin_statistics W hAC hnontrivial
  rw [hspin.neg_one_pow] at h
  exact_mod_cast h

/-- Half-integer spin fields are fermions. -/
theorem half_integer_spin_fermi {T : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (W : WightmanField T H)
    (hAC : (∀ f g : T, W.spacelike f g → W.twoPoint f g = 0) → ∀ f : T, W.twoPoint f f = 0)
    (hnontrivial : ∃ f : T, W.field f W.vacuum ≠ 0) (hspin : Odd W.twoSpin) :
    W.stat = -1 := by
  have h := spin_statistics W hAC hnontrivial
  rw [hspin.neg_one_pow] at h
  exact_mod_cast h

/-!
## Consistency: the hypotheses are not vacuous

We exhibit two nontrivial models: a spin `0` bosonic field, and a fermionic (`twoSpin = 1`)
field built from the Pauli matrices `σ_x` and `σ_z` on a two dimensional state space.  Both
have fields that do not annihilate the vacuum, in accordance with the theorem.
-/

/-- A nontrivial spin `0` field with Bose statistics. -/
def boseModel : WightmanField Unit ℂ where
  spacelike := fun _ _ => True
  field := fun _ => LinearMap.id
  vacuum := 1
  twoSpin := 0
  stat := 1
  stat_sq := by norm_num
  hermitian := fun _ _ _ => rfl
  locality := fun _ _ _ x => by simp
  weakLocalCommutativity := fun _ _ _ => by simp

theorem boseModel_nontrivial : ∃ f : Unit, boseModel.field f boseModel.vacuum ≠ 0 :=
  ⟨(), one_ne_zero⟩

/-- The Pauli matrix `σ_x`, as an operator on `EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def sigmaX : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![0, 1; 1, 0]

/-- The Pauli matrix `σ_z`, as an operator on `EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def sigmaZ : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanLin !![1, 0; 0, -1]

theorem sigmaX_isSymmetric : sigmaX.IsSymmetric := by
  apply Matrix.isHermitian_iff_isSymmetric.mp
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sigmaZ_isSymmetric : sigmaZ.IsSymmetric := by
  apply Matrix.isHermitian_iff_isSymmetric.mp
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The Pauli matrices `σ_z` and `σ_x` anticommute. -/
theorem sigmaZ_sigmaX_anticomm (x : EuclideanSpace ℂ (Fin 2)) :
    sigmaZ (sigmaX x) = (-1 : ℂ) • sigmaX (sigmaZ x) := by
  ext i
  fin_cases i <;> simp [sigmaX, sigmaZ, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_succ]

/-- The anticommutation relation for the fields of the fermionic model. -/
theorem fermi_field_anticomm (f g : Bool) (hfg : f ≠ g) (x : EuclideanSpace ℂ (Fin 2)) :
    (if f then sigmaZ else sigmaX) ((if g then sigmaZ else sigmaX) x)
      = (-1 : ℂ) • (if g then sigmaZ else sigmaX) ((if f then sigmaZ else sigmaX) x) := by
  cases f <;> cases g
  · exact absurd rfl hfg
  · show sigmaX (sigmaZ x) = (-1 : ℂ) • sigmaZ (sigmaX x)
    rw [sigmaZ_sigmaX_anticomm x, smul_smul]
    norm_num
  · exact sigmaZ_sigmaX_anticomm x
  · exact absurd rfl hfg

/-- A nontrivial spin `1/2` field with Fermi statistics. -/
noncomputable def fermiModel : WightmanField Bool (EuclideanSpace ℂ (Fin 2)) where
  spacelike := fun f g => f ≠ g
  field := fun b => if b then sigmaZ else sigmaX
  vacuum := EuclideanSpace.single 0 1
  twoSpin := 1
  stat := -1
  stat_sq := by norm_num
  hermitian := by
    intro f
    cases f
    · simpa using sigmaX_isSymmetric
    · simpa using sigmaZ_isSymmetric
  locality := by
    intro f g hfg x
    simpa using fermi_field_anticomm f g hfg x
  weakLocalCommutativity := by
    intro f g hfg
    rw [fermi_field_anticomm f g hfg, inner_smul_right]
    simp

theorem fermiModel_nontrivial : ∃ f : Bool, fermiModel.field f fermiModel.vacuum ≠ 0 := by
  refine ⟨false, ?_⟩
  intro h
  have h1 : (sigmaX (EuclideanSpace.single 0 (1 : ℂ))) 1 = 0 := by
    rw [show sigmaX (EuclideanSpace.single 0 (1 : ℂ))
      = fermiModel.field false fermiModel.vacuum from rfl, h]
    rfl
  simp [sigmaX, Matrix.toLpLin_apply, Fin.sum_univ_succ] at h1

end Frontier

