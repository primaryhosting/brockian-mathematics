import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem card_filter_coord {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (i : ι) (Q : β → Prop) :
    (univ.filter (fun ρ : ι → β => Q (ρ i))).card * Fintype.card β
      = (univ.filter Q).card * Fintype.card (ι → β) := by
  have hset : (univ.filter (fun ρ : ι → β => Q (ρ i)))
      = Fintype.piFinset (fun i' => if i' = i then univ.filter Q else univ) := by
    ext ρ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i'
      by_cases hi : i' = i
      · subst hi; simpa using h
      · simp [hi]
    · intro h
      simpa using h i
  rw [hset, Fintype.card_piFinset]
  have h1 : ∏ i' : ι, (if i' = i then univ.filter Q else univ).card
      = (univ.filter Q).card * ∏ _i' ∈ univ.erase i, (Fintype.card β) := by
    rw [← Finset.mul_prod_erase _ _ (mem_univ i)]
    simp only
    congr 1
    refine Finset.prod_congr rfl (fun i' hi' => ?_)
    rw [if_neg (Finset.mem_erase.1 hi').1]
    simp
  rw [h1]
  have h2 : Fintype.card (ι → β) = Fintype.card β * ∏ _i' ∈ univ.erase i, (Fintype.card β) := by
    simp only [Finset.prod_const, Fintype.card_fun]
    rw [Finset.card_erase_of_mem (mem_univ i)]
    have h3 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    rw [← pow_succ']
    congr 1
    simp only [Finset.card_univ]
    omega
  rw [h2]
  ring

/-- If a property of a single coordinate has density at most `2^{-t}`, then so does the set of
functions whose value at a fixed coordinate has the property. -/
