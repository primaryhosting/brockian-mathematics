import Mathlib
import RequestProject.Paley

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset

/-! ## Monochromatic cliques for a two-colouring -/

variable {α : Type*} [DecidableEq α] {c : α → α → Bool} {x : Bool}

/-- `S` is a monochromatic clique of colour `x` for the two-colouring `c`. -/

lemma even_sum_redDeg (hsym : ∀ a b, c a b = c b a) (W : Finset α) :
    Even (∑ v ∈ W, (redN c W v).card) := by
  classical
  set f : α × α → ZMod 2 := fun p => if p.2 ≠ p.1 ∧ c p.1 p.2 = true then 1 else 0 with hf
  have hswap : ∀ p : α × α, f (p.2, p.1) = f p := by
    intro p
    have hcond : (p.1 ≠ p.2 ∧ c p.2 p.1 = true) ↔ (p.2 ≠ p.1 ∧ c p.1 p.2 = true) := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, by rw [hsym]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, by rw [hsym]; exact h2⟩
    simp only [hf]
    exact if_congr hcond rfl rfl
  have hzero : ∑ p ∈ W ×ˢ W, f p = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p _
      rw [hswap p]
      exact CharTwo.add_self_eq_zero (f p)
    · intro p _ hfp hpe
      apply hfp
      have h12 : p.1 = p.2 := congrArg Prod.fst hpe.symm ▸ rfl
      simp only [hf]
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact h1 h12.symm
    · intro p hp
      simp only [Finset.mem_product] at hp ⊢
      exact ⟨hp.2, hp.1⟩
    · intro p _
      rfl
  have hcast : ((∑ v ∈ W, (redN c W v).card : ℕ) : ZMod 2) = 0 := by
    rw [← hzero, Finset.sum_product]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro v _
    have hset : redN c W v = W.filter (fun u => u ≠ v ∧ c v u = true) := by
      ext u
      simp only [mem_redN, Finset.mem_filter]
      tauto
    rw [hset, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro u _
    simp only [hf]
    split <;> simp
  exact ZMod.natCast_eq_zero_iff_even.mp hcast

/-! ## R(3,3) ≤ 6 -/

