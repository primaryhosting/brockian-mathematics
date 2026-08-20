import Mathlib

/-!
# Plunnecke Ruzsa Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.plunnecke_ruzsa_shadow
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

namespace AdditiveComb

open Classical in
/-- For an integer `d`, a chosen pair `(a, c) ∈ A × C` with `a - c = d`, whenever `d ∈ A - C`
(and a junk value otherwise). -/

theorem plunnecke_ruzsa_shadow (A B C : Finset ℤ)
    (_hA : A.Nonempty) (_hB : B.Nonempty) (_hC : C.Nonempty) :
    (A - C).card * B.card ≤ (A - B).card * (B - C).card := by
  rw [← Finset.card_product (A - C) B, ← Finset.card_product (A - B) (B - C)]
  refine Finset.card_le_card_of_injOn
    (fun p => ((subWitness A C p.1).1 - p.2, p.2 - (subWitness A C p.1).2)) ?_ ?_
  · rintro ⟨d, b⟩ hp
    simp only [Finset.mem_coe, Finset.mem_product] at hp ⊢
    obtain ⟨hd, hb⟩ := hp
    obtain ⟨ha, hc, -⟩ := subWitness_spec hd
    exact ⟨Finset.sub_mem_sub ha hb, Finset.sub_mem_sub hb hc⟩
  · rintro ⟨d, b⟩ hp ⟨d', b'⟩ hp' h
    simp only [Finset.mem_coe, Finset.mem_product] at hp hp'
    obtain ⟨-, -, hsum⟩ := subWitness_spec hp.1
    obtain ⟨-, -, hsum'⟩ := subWitness_spec hp'.1
    simp only [Prod.mk.injEq] at h hsum hsum' ⊢
    have hdd : d = d' := by omega
    subst hdd
    exact ⟨rfl, by omega⟩

end AdditiveComb

