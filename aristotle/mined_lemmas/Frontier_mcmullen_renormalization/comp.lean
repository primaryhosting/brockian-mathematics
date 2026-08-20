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

/-!
## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard, and the central object of McMullen's work on
renormalization) is a proper holomorphic map of degree two `f : U → V` between topological
discs in `ℂ` with `closure U` a compact subset of `V`.

We encode this as a structure.  The degree-two condition is encoded by:
* surjectivity of `f : U → V` (`surjOn`),
* every fibre over `V` has at most two points (`deg_le_two`),
* there is a unique critical point `crit ∈ U` (`crit_mem`, `deriv_crit`, `crit_unique`).

Properness of `f : U → V` is recorded in the field `proper`.
-/

/-- A quadratic-like map: a proper degree-two holomorphic map `f : U → V` of plane domains
with `closure U` compact and contained in `V`. -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the big domain -/
  V : Set ℂ
  /-- the map, given as a globally defined function which is holomorphic on `U` -/
  f : ℂ → ℂ
  /-- the (unique) critical point -/
  crit : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isBounded_V : Bornology.IsBounded V
  closure_U_subset_V : closure U ⊆ V
  analytic : AnalyticOnNhd ℂ f U
  mapsTo : Set.MapsTo f U V
  surjOn : V ⊆ f '' U
  proper : ∀ C ⊆ V, IsCompact C → IsCompact (U ∩ f ⁻¹' C)
  crit_mem : crit ∈ U
  deriv_crit : deriv f crit = 0
  crit_unique : ∀ z ∈ U, deriv f z = 0 → z = crit
  deg_le_two : ∀ w ∈ V, (U ∩ f ⁻¹' {w}).ncard ≤ 2

namespace QuadraticLike

variable (F : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit stays
in the small domain `U`. -/

def comp {q : ℕ} (R₁ : Restriction F p) (R₂ : Restriction R₁.G q) :
    Restriction F (p * q) where
  G := R₂.G
  pos := Nat.mul_pos R₁.pos R₂.pos
  eqOn := by
    intro z hz
    have h1 : R₂.G.f z = R₁.G.f^[q] z := R₂.eqOn hz
    have h2 : R₁.G.f^[q] z = (F.f^[p])^[q] z :=
      R₁.iterate_eq_of_forall_mem (fun k hk => R₂.orbit k hk hz)
    rw [h1, h2, ← Function.iterate_mul]
  subset := R₂.subset.trans R₁.subset
  orbit := by
    intro j hj z hz
    have hr : j % p < p := Nat.mod_lt _ R₁.pos
    have hs : j / p < q := by
      rw [Nat.div_lt_iff_lt_mul R₁.pos]
      simpa [Nat.mul_comm] using hj
    have hj' : j = j % p + p * (j / p) := (Nat.mod_add_div j p).symm
    have h1 : F.f^[j] z = F.f^[j % p] ((F.f^[p])^[j / p] z) := by
      conv_lhs => rw [hj']
      rw [Function.iterate_add_apply, Function.iterate_mul]
    have h2 : (F.f^[p])^[j / p] z = R₁.G.f^[j / p] z :=
      (R₁.iterate_eq_of_forall_mem (fun k hk => R₂.orbit k (by omega) hz)).symm
    rw [h1, h2]
    exact R₁.orbit _ hr (R₂.orbit _ hs hz)
  crit_eq := R₂.crit_eq.trans R₁.crit_eq

end Restriction

/-- **Composition of renormalizations.**  Renormalizing a renormalization of period `p` with
period `q` gives a renormalization of period `p * q`. -/
