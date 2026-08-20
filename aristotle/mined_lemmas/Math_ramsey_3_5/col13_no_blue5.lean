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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `Mono c col S` says that the finite set `S` is monochromatic of colour `col`
for the edge-colouring `c` : every pair of distinct vertices of `S` gets colour `col`. -/

theorem col13_no_blue5 : ∀ S : Finset (Fin 13), S.card = 5 → ¬ Mono col13 false S := by
  intro S hS hM
  obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hinj : Function.Injective (shift13 a) := fun x y h => shift13_inj a x y h
  set S' := S.image (shift13 a) with hS'def
  have hcard : S'.card = 5 := by rw [hS'def, Finset.card_image_of_injective _ hinj, hS]
  have hM' : Mono col13 false S' := by
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    rw [shift13_col]
    exact hM x hx y hy (fun e => huv (by rw [e]))
  have h0 : (0 : Fin 13) ∈ S' := by
    have h := Finset.mem_image_of_mem (shift13 a) ha
    rwa [shift13_self] at h
  set S'' := S'.erase 0 with hS''def
  have hc'' : S''.card = 4 := by rw [hS''def, Finset.card_erase_of_mem h0, hcard]
  obtain ⟨p, hp⟩ : S''.Nonempty := Finset.card_pos.mp (by omega)
  have hcp : (S''.erase p).card = 3 := by rw [Finset.card_erase_of_mem hp, hc'']
  obtain ⟨q, r, s, hqr, hqs, hrs, hqrs⟩ := Finset.card_eq_three.mp hcp
  have hmemq : q ∈ S''.erase p := by rw [hqrs]; simp
  have hmemr : r ∈ S''.erase p := by rw [hqrs]; simp
  have hmems : s ∈ S''.erase p := by rw [hqrs]; simp
  have hq : q ∈ S'' := (Finset.mem_erase.mp hmemq).2
  have hr : r ∈ S'' := (Finset.mem_erase.mp hmemr).2
  have hs' : s ∈ S'' := (Finset.mem_erase.mp hmems).2
  have hpq : p ≠ q := Ne.symm (Finset.mem_erase.mp hmemq).1
  have hpr : p ≠ r := Ne.symm (Finset.mem_erase.mp hmemr).1
  have hps : p ≠ s := Ne.symm (Finset.mem_erase.mp hmems).1
  have hnb : ∀ u ∈ S'', inNB u = true := by
    intro u hu
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    have huS' : u ∈ S' := (Finset.mem_erase.mp hu).2
    exact col13_inNB u hu0 (hM' u huS' 0 h0 hu0)
  have hblue : ∀ u ∈ S'', ∀ v ∈ S'', u ≠ v → col13 u v = false := by
    intro u hu v hv huv
    exact hM' u (Finset.mem_erase.mp hu).2 v (Finset.mem_erase.mp hv).2 huv
  exact col13_no_blue4_inNB p q r s (hnb p hp) (hnb q hq) (hnb r hr) (hnb s hs')
    hpq hpr hps hqr hqs hrs
    ⟨hblue p hp q hq hpq, hblue p hp r hr hpr, hblue p hp s hs' hps,
      hblue q hq r hr hqr, hblue q hq s hs' hqs, hblue r hr s hs' hrs⟩

