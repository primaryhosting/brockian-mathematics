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

This file formalises the spin–statistics connection for a relativistic quantum field in the
Wightman framework, at the level of the two–point function, and proves it from the standard
axiomatic inputs.

## Setup

* `Frontier.Minkowski` is `ℝ^{1,3}` with quadratic form `Frontier.minkowskiSq` of signature
  `(+,-,-,-)`; two events are spacelike separated when the interval between them is negative.
* Test functions are complex valued functions on Minkowski space; two of them are *causally
  disjoint* (`Frontier.SpacelikeSupported`) when every point of the support of the first is
  spacelike separated from every point of the support of the second.
* A `Frontier.WightmanField` packages a Hilbert space with a vacuum vector, smeared field
  operators `op f`, a spin (recorded through `twoSpin`, twice the spin, so that integer spin
  means `twoSpin` even) and a choice of statistics (`fermionic`), together with three of the
  Wightman axioms that are used here:
  - hermiticity of the smeared field,
  - the (graded) local commutation relation at spacelike separation, with the sign dictated by
    the chosen statistics,
  - *weak locality*: at spacelike separation the two point function is symmetric up to the sign
    `(-1)^{2j}` dictated by the spin.  This is the Bargmann–Hall–Wightman consequence of Lorentz
    covariance, the spectral condition and the existence of Jost points.

## Results

* `Frontier.twoPoint_eq_zero_of_wrong_statistics`: if the statistics sign disagrees with the
  spin sign, the two point function vanishes for all causally disjoint test functions.
* `Frontier.op_vac_eq_zero_of_wrong_statistics`: adding the Reeh–Schlieder / edge–of–the–wedge
  input (a two point function vanishing on an open set of spacelike configurations vanishes
  identically) the field annihilates the vacuum, i.e. the theory is trivial.
* `Frontier.spin_statistics`: the spin–statistics connection.  A field that does not annihilate
  the vacuum must have statistics matching its spin: Bose statistics for integer spin, Fermi
  statistics for half–integer spin.
-/

namespace Frontier

open scoped InnerProductSpace

/-! ## Minkowski space and causal disjointness -/

/-- Minkowski spacetime `ℝ^{1,3}`, coordinates indexed by `Fin 4` with `0` the time coordinate. -/
abbrev Minkowski := Fin 4 → ℝ

/-- The Minkowski quadratic form, in signature `(+,-,-,-)`. -/

lemma eq_neg_of_sign_ne {a b : ℂ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hab : a ≠ b) :
    a = -b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-! ## Wightman fields -/

/-- A (scalar-smeared) relativistic quantum field in the Wightman framework, carrying a spin and
a choice of statistics, together with the axioms needed for the spin–statistics connection.

`twoSpin` is twice the spin of the field, so integer spin corresponds to `twoSpin` even and
half-integer spin to `twoSpin` odd. -/
structure WightmanField (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The vacuum vector. -/
  vac : H
  /-- The smeared field operator `φ(f)`. -/
  op : TestFn → (H →ₗ[ℂ] H)
  /-- Twice the spin of the field. -/
  twoSpin : ℕ
  /-- Whether the field is quantised with anticommutators. -/
  fermionic : Bool
  /-- Hermiticity of the smeared field: `φ(f)† = φ(f̄)`. -/
  herm : ∀ (f : TestFn) (x y : H), inner ℂ (op f x) y = inner ℂ x (op f.conj y)
  /-- Local (anti)commutation relations: at spacelike separation the fields commute or
  anticommute according to the chosen statistics. -/
  locality : ∀ (f g : TestFn), SpacelikeSupported f g →
    ∀ x : H, op f (op g x) = statSign fermionic • op g (op f x)
  /-- Weak locality: the Bargmann–Hall–Wightman consequence of Lorentz covariance and the
  spectral condition, stating that at spacelike separation the two point function is symmetric
  up to the sign `(-1)^{2j}`. -/
  weakLocality : ∀ (f g : TestFn), SpacelikeSupported f g →
    inner ℂ vac (op f (op g vac)) = spinSign twoSpin * inner ℂ vac (op g (op f vac))

namespace WightmanField

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The two point Wightman function `W(f, g) = ⟨Ω, φ(f) φ(g) Ω⟩`. -/
