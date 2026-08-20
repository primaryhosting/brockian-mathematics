import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Ramsey

/-- A `b`-monochromatic set of vertices for the edge colouring `c`. -/

lemma even_sum_deg (c : ℕ → ℕ → Bool) (hsym : ∀ x y, c x y = c y x) (s : Finset ℕ) :
    Even (∑ v ∈ s, (Nbr c s v true).card) := by
  classical
  set f : ℕ → ℕ → ℕ := fun v u => if v ≠ u ∧ c v u = true then 1 else 0 with hf
  have hfsym : ∀ v u, f v u = f u v := by
    intro v u
    simp only [hf]
    rw [hsym v u]
    by_cases h : v = u
    · subst h; simp
    · simp [h, Ne.symm h]
  have hdeg : ∀ v, (Nbr c s v true).card = ∑ u ∈ s, f v u := by
    intro v
    have : Nbr c s v true = s.filter (fun u => v ≠ u ∧ c v u = true) := by
      ext u
      simp only [mem_Nbr, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hu, hne⟩, hc⟩; exact ⟨hu, Ne.symm hne, hc⟩
      · rintro ⟨hu, hne, hc⟩; exact ⟨⟨hu, Ne.symm hne⟩, hc⟩
    rw [this, Finset.card_filter]
  have hsum : ∑ v ∈ s, (Nbr c s v true).card = ∑ v ∈ s, ∑ u ∈ s, f v u :=
    Finset.sum_congr rfl (fun v _ => hdeg v)
  set g : ℕ → ℕ → ℕ := fun v u => if v < u then f v u else 0 with hg
  set h : ℕ → ℕ → ℕ := fun v u => if u < v then f v u else 0 with hh
  have hsplit : ∀ v u, f v u = g v u + h v u := by
    intro v u
    simp only [hg, hh]
    rcases lt_trichotomy v u with hlt | rfl | hlt
    · simp [hlt, not_lt.mpr hlt.le]
    · simp [hf]
    · simp [hlt, not_lt.mpr hlt.le]
  have hgh : ∑ v ∈ s, ∑ u ∈ s, h v u = ∑ v ∈ s, ∑ u ∈ s, g v u := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun u _ => ?_))
    simp only [hg, hh]
    by_cases hvu : v < u
    · simp [hvu, hfsym u v]
    · simp [hvu]
  refine ⟨∑ v ∈ s, ∑ u ∈ s, g v u, ?_⟩
  rw [hsum]
  have : ∑ v ∈ s, ∑ u ∈ s, f v u
      = (∑ v ∈ s, ∑ u ∈ s, g v u) + ∑ v ∈ s, ∑ u ∈ s, h v u := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => hsplit v u)
  rw [this, hgh]

/-- `R(3,4) ≤ 9`. -/
