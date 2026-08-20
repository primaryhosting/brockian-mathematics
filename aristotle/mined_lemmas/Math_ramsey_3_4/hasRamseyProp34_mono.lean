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

set_option maxRecDepth 10000
set_option synthInstance.maxSize 400
set_option synthInstance.maxHeartbeats 1000000

namespace Math

open Finset SimpleGraph

/-- `HasRamseyProp34 n` holds when every simple graph on `n` vertices contains either a
clique of size `3` or an independent set of size `4`; equivalently, every red/blue colouring
of the edges of `K n` contains a red triangle or a blue `K 4`. -/

theorem hasRamseyProp34_mono {m n : ℕ} (hmn : m ≤ n) (hm : HasRamseyProp34 m) :
    HasRamseyProp34 n := by
  intro G
  have hinj : Function.Injective (Fin.castLE hmn) := Fin.castLE_injective hmn
  rcases hm (G.comap (Fin.castLE hmn)) with ⟨s, hs, hcl⟩ | ⟨t, ht, hin⟩
  · left
    refine ⟨s.image (Fin.castLE hmn), by rw [Finset.card_image_of_injective _ hinj]; exact hs, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hcl hx' hy' (fun h => hxy (by rw [h]))
  · right
    refine ⟨t.image (Fin.castLE hmn), by rw [Finset.card_image_of_injective _ hinj]; exact ht, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hin hx' hy' (fun h => hxy (by rw [h]))

/-! ### The main theorem -/

