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

/-
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace EquidistributionUniformity

open MulAction

/-- The fibre `{g : G | g • a = x}` of the orbit map at `a` over a point `x` in the orbit is
in bijection with the stabilizer of `a`.  (Any such fibre is a left coset of `stabilizer G a`.) -/
def fiberEquivStabilizer {G α : Type*} [Group G] [MulAction G α] {a x : α}
    (g₀ : G) (hg₀ : g₀ • a = x) : {g : G // g • a = x} ≃ stabilizer G a where
  toFun g := ⟨g₀⁻¹ * g.1, by
    simp only [mem_stabilizer_iff, mul_smul, g.2, ← hg₀, inv_smul_smul]⟩
  invFun h := ⟨g₀ * h.1, by
    have := h.2
    rw [mem_stabilizer_iff] at this
    rw [mul_smul, this, hg₀]⟩
  left_inv g := by ext; simp
  right_inv h := by ext; simp

/-- **Uniformity of singleton masses for a transitive action.**

If a group `G` acts (pre)transitively on `α`, then for every base point `a` and every point `x`
the number of group elements sending `a` to `x` is the same for all `x`, namely `|G| / |α|`:
the pushforward of the uniform distribution on `G` under `g ↦ g • a` is the uniform
distribution on `α`.

This is the orbit–stabilizer theorem
(`MulAction.orbitProdStabilizerEquivGroup`) combined with `MulAction.orbit_eq_univ`.
No finiteness hypothesis is required (with `Nat.card`, both sides are `0` in the infinite
case). -/
theorem sing_uniform_of_transitive {G α : Type*} [Group G] [MulAction G α]
    [IsPretransitive G α] (a x : α) :
    Nat.card {g : G // g • a = x} * Nat.card α = Nat.card G := by
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G a x
  have hfib : Nat.card {g : G // g • a = x} = Nat.card (stabilizer G a) :=
    Nat.card_congr (fiberEquivStabilizer g₀ hg₀)
  have horb : Nat.card α = Nat.card (orbit G a) := by
    refine (Nat.card_congr ?_).symm
    rw [orbit_eq_univ]
    exact Equiv.Set.univ α
  rw [hfib, horb, mul_comm, ← Nat.card_prod]
  exact Nat.card_congr (orbitProdStabilizerEquivGroup G a)

/-- Real-valued form of `sing_uniform_of_transitive`: for a transitive action of a finite
group `G` on a nonempty type `α`, the proportion of group elements mapping the base point `a`
to a given point `x` equals `1 / |α|`, independently of `x`. -/
theorem sing_uniform_ratio_of_transitive {G α : Type*} [Group G] [Finite G] [MulAction G α]
    [IsPretransitive G α] [Nonempty α] (a x : α) :
    (Nat.card {g : G // g • a = x} : ℝ) / Nat.card G = 1 / Nat.card α := by
  haveI : Finite α := Finite.of_surjective (fun g : G => g • a) (fun y => exists_smul_eq G a y)
  have hG : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hα : (0 : ℝ) < Nat.card α := by exact_mod_cast Nat.card_pos
  have h' : (Nat.card {g : G // g • a = x} : ℝ) * (Nat.card α : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast sing_uniform_of_transitive (G := G) a x
  field_simp
  linarith [h']

end EquidistributionUniformity
end Brockian

