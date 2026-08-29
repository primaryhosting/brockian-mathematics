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

We formalize the Wightman-style two-point-function argument for the spin–statistics
theorem.  The data of a (smeared) relativistic quantum field theory that the argument
actually uses is packaged in `Frontier.SpinStatisticsSetup`:

* a complex inner product space `H` of states with a distinguished vacuum vector `vac`;
* smeared field operators `phi f : H → H` indexed by test functions `f : ι`;
* an involution `conjTest` on test functions (complex conjugation of the smearing
  function), for which the field is hermitian in the sense that
  `⟪x, phi f y⟫ = ⟪phi (conjTest f) x, y⟫`;
* a relation `spacelike f g` recording that the supports of `f` and `g` are mutually
  spacelike separated;
* a natural number `twoJ = 2j`, twice the spin of the field, and a statistics sign
  `eps = ±1` (`+1` for canonical commutation relations, `-1` for canonical
  anticommutation relations).

The two physical inputs are stated for spacelike separated test functions:

* `statistics`: the assumed (anti)commutation relations at spacelike separation give
  `W f g = eps * W g f` for the two-point function `W`;
* `spinRelation`: Lorentz covariance of a field of spin `j` together with the
  Bargmann–Hall–Wightman analytic continuation to the Jost points gives
  `W f g = (-1)^(2j) * W g f` at spacelike separation.

The remaining input, `analyticity`, is the standard Wightman analyticity /
edge-of-the-wedge statement: a two-point function that vanishes on the (open, nonempty)
set of spacelike separated configurations vanishes identically.

From these, the theorem `Frontier.spin_statistics` shows that a field which does not
annihilate the vacuum must have `eps = (-1)^(2j)`: integer spin forces commutation
relations, half-integer spin forces anticommutation relations.  Equivalently
(`Frontier.SpinStatisticsSetup.phi_vac_eq_zero_of_wrong_statistics`), quantizing with the
wrong statistics forces the field to be trivial on the vacuum.

Both conclusions are shown to be non-vacuous: `Frontier.bosonModel` and
`Frontier.fermionModel` are explicit finite-dimensional models with `2j = 0, eps = 1`
and `2j = 1, eps = -1` respectively, whose fields do not annihilate the vacuum.
-/

/-- The data and hypotheses of a relativistic quantum field entering the
spin–statistics connection, at the level of the vacuum two-point function. -/
structure SpinStatisticsSetup (ι : Type*) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The vacuum state. -/
  vac : H
  /-- The smeared field operator attached to a test function. -/
  phi : ι → H → H
  /-- Complex conjugation of test functions. -/
  conjTest : ι → ι
  /-- Twice the spin of the field. -/
  twoJ : ℕ
  /-- The statistics sign: `+1` for commutation, `-1` for anticommutation relations. -/
  eps : ℂ
  /-- `spacelike f g` holds when the supports of `f` and `g` are mutually spacelike
  separated. -/
  spacelike : ι → ι → Prop
  /-- The statistics sign is `±1`. -/
  eps_sq_eq_one : eps ^ 2 = 1
  /-- Conjugation of test functions is an involution. -/
  conjTest_involutive : ∀ f : ι, conjTest (conjTest f) = f
  /-- Hermiticity of the smeared field: `phi (conjTest f)` is the adjoint of `phi f`. -/
  hermitian : ∀ (f : ι) (x y : H), inner ℂ x (phi f y) = inner ℂ (phi (conjTest f) x) y
  /-- The assumed (anti)commutation relations at spacelike separation, evaluated on the
  vacuum two-point function. -/
  statistics : ∀ f g : ι, spacelike f g →
    inner ℂ vac (phi f (phi g vac)) = eps * inner ℂ vac (phi g (phi f vac))
  /-- Lorentz covariance for spin `j` plus analytic continuation to the Jost points:
  at spacelike separation the two-point function is `(-1)^(2j)`-symmetric. -/
  spinRelation : ∀ f g : ι, spacelike f g →
    inner ℂ vac (phi f (phi g vac)) = (-1 : ℂ) ^ twoJ * inner ℂ vac (phi g (phi f vac))
  /-- Wightman analyticity (edge of the wedge): a two-point function vanishing at all
  spacelike separations vanishes identically. -/
  analyticity : (∀ f g : ι, spacelike f g → inner ℂ vac (phi f (phi g vac)) = 0) →
    ∀ f g : ι, inner ℂ vac (phi f (phi g vac)) = 0

namespace SpinStatisticsSetup

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The vacuum two-point (Wightman) function of the field. -/
def twoPoint (S : SpinStatisticsSetup ι H) (f g : ι) : ℂ :=
  inner ℂ S.vac (S.phi f (S.phi g S.vac))

/-- The statistics sign is `1` or `-1`. -/
theorem eps_eq_one_or_neg_one (S : SpinStatisticsSetup ι H) : S.eps = 1 ∨ S.eps = -1 := by
  have h : (S.eps - 1) * (S.eps + 1) = 0 := by
    have := S.eps_sq_eq_one
    ring_nf
    linear_combination this
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination h)

/-- Positivity: the squared norm of `phi f vac` is the two-point function
`W (conjTest f) f`. -/
theorem twoPoint_conjTest_self (S : SpinStatisticsSetup ι H) (f : ι) :
    S.twoPoint (S.conjTest f) f = inner ℂ (S.phi f S.vac) (S.phi f S.vac) := by
  have h := S.hermitian (S.conjTest f) S.vac (S.phi f S.vac)
  rw [S.conjTest_involutive f] at h
  exact h

/-- With the wrong statistics, the two-point function vanishes at spacelike separation. -/
theorem twoPoint_eq_zero_spacelike_of_wrong_statistics (S : SpinStatisticsSetup ι H)
    (hwrong : S.eps ≠ (-1 : ℂ) ^ S.twoJ) {f g : ι} (hfg : S.spacelike f g) :
    S.twoPoint f g = 0 := by
  have h1 := S.statistics f g hfg
  have h2 := S.spinRelation f g hfg
  have hsub : (S.eps - (-1 : ℂ) ^ S.twoJ) * S.twoPoint g f = 0 := by
    have : S.eps * S.twoPoint g f = (-1 : ℂ) ^ S.twoJ * S.twoPoint g f := by
      simpa [twoPoint] using h1.symm.trans h2
    linear_combination this
  have hgf : S.twoPoint g f = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hwrong
    · exact h
  calc S.twoPoint f g = S.eps * S.twoPoint g f := by simpa [twoPoint] using h1
    _ = 0 := by rw [hgf, mul_zero]

/-- With the wrong statistics, the two-point function vanishes identically. -/
theorem twoPoint_eq_zero_of_wrong_statistics (S : SpinStatisticsSetup ι H)
    (hwrong : S.eps ≠ (-1 : ℂ) ^ S.twoJ) (f g : ι) : S.twoPoint f g = 0 :=
  S.analyticity (fun _ _ h => S.twoPoint_eq_zero_spacelike_of_wrong_statistics hwrong h) f g

/-- **Wrong statistics kills the field.**  If a field of spin `j` is quantized with the
statistics sign `eps ≠ (-1)^(2j)`, then it annihilates the vacuum. -/
theorem phi_vac_eq_zero_of_wrong_statistics (S : SpinStatisticsSetup ι H)
    (hwrong : S.eps ≠ (-1 : ℂ) ^ S.twoJ) (f : ι) : S.phi f S.vac = 0 := by
  have h : inner ℂ (S.phi f S.vac) (S.phi f S.vac) = (0 : ℂ) := by
    rw [← S.twoPoint_conjTest_self f]
    exact S.twoPoint_eq_zero_of_wrong_statistics hwrong _ _
  exact inner_self_eq_zero.mp h

end SpinStatisticsSetup

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The spin–statistics connection.**  In a relativistic quantum field theory in the
sense of `Frontier.SpinStatisticsSetup`, a field of spin `j` which does not annihilate
the vacuum must obey the statistics sign `(-1)^(2j)`: integer spin forces commutation
relations (`eps = 1`) and half-integer spin forces anticommutation relations
(`eps = -1`). -/
theorem spin_statistics (S : SpinStatisticsSetup ι H) {f : ι} (hf : S.phi f S.vac ≠ 0) :
    S.eps = (-1 : ℂ) ^ S.twoJ := by
  by_contra hwrong
  exact hf (S.phi_vac_eq_zero_of_wrong_statistics hwrong f)

/-- Integer spin ⟹ Bose statistics. -/
theorem spin_statistics_boson (S : SpinStatisticsSetup ι H) {f : ι}
    (hf : S.phi f S.vac ≠ 0) (hspin : Even S.twoJ) : S.eps = 1 := by
  rw [spin_statistics S hf, hspin.neg_one_pow]

/-- Half-integer spin ⟹ Fermi statistics. -/
theorem spin_statistics_fermion (S : SpinStatisticsSetup ι H) {f : ι}
    (hf : S.phi f S.vac ≠ 0) (hspin : Odd S.twoJ) : S.eps = -1 := by
  rw [spin_statistics S hf, hspin.neg_one_pow]

/-!
## Non-vacuity: explicit models

To show that the hypotheses of `Frontier.SpinStatisticsSetup` are consistent and that
both conclusions occur, we exhibit two finite-dimensional models whose fields do not
annihilate the vacuum.
-/

/-- A one-dimensional bosonic model: spin `0`, statistics sign `+1`. -/
def bosonModel : SpinStatisticsSetup Unit ℂ where
  vac := 1
  phi := fun _ x => x
  conjTest := id
  twoJ := 0
  eps := 1
  spacelike := fun _ _ => True
  eps_sq_eq_one := by norm_num
  conjTest_involutive := fun _ => rfl
  hermitian := fun _ x y => rfl
  statistics := fun _ _ _ => by simp
  spinRelation := fun _ _ _ => by simp
  analyticity := by
    intro h f g
    have := h () () trivial
    simp at this

theorem bosonModel_phi_vac_ne_zero (f : Unit) :
    bosonModel.phi f bosonModel.vac ≠ 0 := one_ne_zero

theorem bosonModel_eps : bosonModel.eps = 1 :=
  spin_statistics_boson bosonModel (bosonModel_phi_vac_ne_zero ()) (by decide)

/-- The two "field operators" of the fermionic model: the Pauli matrices `σₓ` and `σ_y`
acting on `ℂ²`. -/
noncomputable def pauliField (b : Bool) (x : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Fin 2) :=
  if b then !₂[-Complex.I * x.ofLp 1, Complex.I * x.ofLp 0]
  else !₂[x.ofLp 1, x.ofLp 0]

/-- A two-dimensional fermionic model: spin `1/2` (`2j = 1`), statistics sign `-1`,
with two spacelike separated "regions" indexed by `Bool`. -/
noncomputable def fermionModel : SpinStatisticsSetup Bool (EuclideanSpace ℂ (Fin 2)) where
  vac := !₂[1, 0]
  phi := pauliField
  conjTest := id
  twoJ := 1
  eps := -1
  spacelike := fun a b => a ≠ b
  eps_sq_eq_one := by norm_num
  conjTest_involutive := fun _ => rfl
  hermitian := by
    rintro (_ | _) x y <;>
      simp [pauliField, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
        Complex.ext_iff] <;> constructor <;> ring
  statistics := by
    rintro (_ | _) (_ | _) h <;>
      first
        | exact absurd rfl h
        | simp [pauliField, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
  spinRelation := by
    rintro (_ | _) (_ | _) h <;>
      first
        | exact absurd rfl h
        | simp [pauliField, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
  analyticity := by
    intro h f g
    have h1 := h false true (by decide)
    simp [pauliField, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply] at h1

theorem fermionModel_phi_vac_ne_zero : fermionModel.phi false fermionModel.vac ≠ 0 := by
  intro h
  have h1 : (fermionModel.phi false fermionModel.vac).ofLp 1 = (0 : ℂ) := by
    rw [h]; rfl
  simp [fermionModel, pauliField] at h1

theorem fermionModel_eps : fermionModel.eps = -1 :=
  spin_statistics_fermion fermionModel fermionModel_phi_vac_ne_zero (by decide)

end Frontier

