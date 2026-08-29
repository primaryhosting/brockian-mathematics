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

/-!
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian.EquidistributionUniformity

variable {G X : Type*} [Group G] [MulAction G X]

/-- The set of group elements carrying a fixed base point `x` to the point `y`:
the "fiber" of the orbit map `g ↦ g • x` over `y`. -/
def fiber (x y : X) : Set G := {g : G | g • x = y}

/-- For a transitive action, all fibers of the orbit map `g ↦ g • x` are in bijection:
translating by an element `h` with `h • y = z` is a bijection from the fiber over `y`
to the fiber over `z`. -/
def fiberEquiv (x : X) {y z : X} {h : G} (hh : h • y = z) :
    fiber (G := G) x y ≃ fiber (G := G) x z where
  toFun g := ⟨h * g.1, by
    have hg : g.1 • x = y := g.2
    simp [fiber, mul_smul, hg, hh]⟩
  invFun g := ⟨h⁻¹ * g.1, by
    have hg : g.1 • x = z := g.2
    simp [fiber, mul_smul, hg, ← hh]⟩
  left_inv g := by ext; simp
  right_inv g := by ext; simp

/-- **Uniformity of singleton fibers for a transitive action.**

If a group `G` acts transitively on `X`, then for any base point `x` the orbit map
`g ↦ g • x` distributes `G` uniformly over `X`: the fibers over any two points `y` and `z`
have the same cardinality.  (This is the combinatorial heart of the statement that the
uniform measure on `G` pushes forward to the uniform measure on `X`.) -/
theorem sing_uniform_of_transitive
    (htrans : ∀ a b : X, ∃ g : G, g • a = b) (x y z : X) :
    Nat.card (fiber (G := G) x y) = Nat.card (fiber (G := G) x z) := by
  obtain ⟨h, hh⟩ := htrans y z
  exact Nat.card_congr (fiberEquiv x hh)

/-- Finite form: for a transitive action of a finite group, the number of `g : G` with
`g • x = y` is the same for every `y`. -/
theorem card_filter_smul_eq_of_transitive [Fintype G] [DecidableEq X]
    (htrans : ∀ a b : X, ∃ g : G, g • a = b) (x y z : X) :
    (Finset.univ.filter fun g : G => g • x = y).card
      = (Finset.univ.filter fun g : G => g • x = z).card := by
  have h1 : (Finset.univ.filter fun g : G => g • x = y).card
      = Nat.card (fiber (G := G) x y) := by
    simp [fiber, Nat.card_eq_card_toFinset, Set.toFinset_setOf]
  have h2 : (Finset.univ.filter fun g : G => g • x = z).card
      = Nat.card (fiber (G := G) x z) := by
    simp [fiber, Nat.card_eq_card_toFinset, Set.toFinset_setOf]
  rw [h1, h2, sing_uniform_of_transitive htrans]

end Brockian.EquidistributionUniformity

