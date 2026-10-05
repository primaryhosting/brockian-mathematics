/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard, and the central object of McMullen's work on
renormalization) is a holomorphic map `f : U → V` between bounded open subsets of `ℂ`
with `U ⋐ V`, which is a proper degree-two branched covering onto `V`.

We encode "proper degree two branched covering" concretely and checkably:
`f` maps `U` into `V`, `f` is onto `V`, every fibre over `V` has at most two points,
and `f` has a unique critical point in `U`.
-/

/-- A quadratic-like map: a holomorphic degree-two proper map `f : U → V` with
`closure U ⊆ V` and `U` bounded. -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the large domain -/
  V : Set ℂ
  /-- the map -/
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  /-- `U ⋐ V` : the closure of `U` is contained in `V`. -/
  closure_subset : closure U ⊆ V
  bounded_U : Bornology.IsBounded U
  /-- `f` is holomorphic on `U`. -/
  analytic : AnalyticOnNhd ℂ f U
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is onto. -/
  surjOn : Set.SurjOn f U V
  /-- every fibre of `f : U → V` has at most two points (degree two). -/
  fiber_le_two : ∀ w ∈ V, {z | z ∈ U ∧ f z = w}.ncard ≤ 2
  /-- `f` has a unique critical point in `U`. -/
  unique_crit : ∃! c : ℂ, c ∈ U ∧ deriv f c = 0

namespace QuadraticLike

variable (Q : QuadraticLike)


theorem IsRenormalization.comp {Q R S : QuadraticLike} {n m : ℕ}
    (hQR : IsRenormalization Q R n) (hRS : IsRenormalization R S m) :
    IsRenormalization Q S (n * m) where
  pos := Nat.mul_pos hQR.pos hRS.pos
  subset := hRS.subset.trans hQR.subset
  eq_iterate := by
    intro z hz
    rw [hRS.eq_iterate z hz]
    exact iterate_eq_iterate_of_isRenormalization hQR hRS hz m le_rfl
  orbit := by
    intro i hi z hz
    have hn : 0 < n := hQR.pos
    obtain ⟨q, r, hr, hi'⟩ : ∃ q r : ℕ, r < n ∧ i = r + n * q :=
      ⟨i / n, i % n, Nat.mod_lt _ hn, (Nat.mod_add_div i n).symm⟩
    have hqm : q < m := by
      have h1 : n * q < n * m := by omega
      exact lt_of_mul_lt_mul_left h1 (Nat.zero_le n)
    have hmem : R.f^[q] z ∈ R.U := hRS.orbit q hqm hz
    have hEq : R.f^[q] z = Q.f^[n * q] z :=
      iterate_eq_iterate_of_isRenormalization hQR hRS hz q hqm.le
    have hsplit : Q.f^[i] z = Q.f^[r] (R.f^[q] z) := by
      rw [hEq, hi', Function.iterate_add_apply]
    rw [hsplit]
    exact hQR.orbit r hr hmem

/-! ## The base case: quadratic polynomials are quadratic-like -/

/-- For `R = ‖c‖ + 2`, the polynomial `z ↦ z² + c` restricted to `U = f⁻¹(B(0,R))` is a
quadratic-like map onto `V = B(0,R)`. -/
