import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

lemma fiber_structure {V α : Type*} [DecidableEq V] [DecidableEq α] (σ : Finset V) (f : V → α)
    (J : Finset α) (himg : σ.image f = J) (hcard : σ.card = J.card + 1) :
    ∃ j₀ ∈ J, (σ.filter (fun v => f v = j₀)).card = 2 ∧
      ∀ j ∈ J, j ≠ j₀ → (σ.filter (fun v => f v = j)).card = 1 := by
  classical
  set g : α → ℕ := fun j => (σ.filter (fun v => f v = j)).card with hg
  have hmem : ∀ v ∈ σ, f v ∈ J := by
    intro v hv; rw [← himg]; exact Finset.mem_image_of_mem f hv
  have hsum : σ.card = ∑ j ∈ J, g j := Finset.card_eq_sum_card_fiberwise hmem
  have hge : ∀ j ∈ J, 1 ≤ g j := by
    intro j hj
    rw [← himg] at hj
    obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hj
    exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hfv⟩⟩
  have hsum' : ∑ j ∈ J, (g j - 1) = 1 := by
    have h2 : ∑ j ∈ J, g j = ∑ j ∈ J, ((g j - 1) + 1) := by
      refine Finset.sum_congr rfl ?_
      intro j hj; have := hge j hj; omega
    rw [Finset.sum_add_distrib] at h2
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h2
    omega
  have hex : ∃ j₀ ∈ J, g j₀ - 1 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [Finset.sum_eq_zero hcon] at hsum'
    exact absurd hsum' (by norm_num)
  obtain ⟨j₀, hj₀, hne⟩ := hex
  have hsplit : (g j₀ - 1) + ∑ x ∈ J.erase j₀, (g x - 1) = ∑ j ∈ J, (g j - 1) :=
    Finset.add_sum_erase J (fun j => g j - 1) hj₀
  rw [hsum'] at hsplit
  have hgj₀ : g j₀ = 2 := by have := hge j₀ hj₀; omega
  refine ⟨j₀, hj₀, hgj₀, ?_⟩
  intro j hj hjne
  have hz : ∑ x ∈ J.erase j₀, (g x - 1) = 0 := by omega
  have h0 := (Finset.sum_eq_zero_iff.mp hz) j (Finset.mem_erase.mpr ⟨hjne, hj⟩)
  have := hge j hj
  show g j = 1
  omega

/-- If `f` is a bijection from `σ` onto `J` then exactly one vertex can be deleted from `σ`
so that the remaining colours are `J \ {i₀}`. -/
