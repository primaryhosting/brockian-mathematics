import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma lengths_pos (s : Multiset (ℝ × ℕ)) (hk : mkraft s ≤ 1) (hcard : 2 ≤ s.card) :
    ∀ p ∈ s, 1 ≤ p.2 := by
  intro p hp
  by_contra hcon
  have hp2 : p.2 = 0 := by omega
  have hs : s = p ::ₘ s.erase p := (Multiset.cons_erase hp).symm
  have hcard' : 1 ≤ (s.erase p).card := by
    have := Multiset.card_erase_of_mem hp
    rw [Nat.pred_eq_sub_one] at this
    omega
  have hne : s.erase p ≠ 0 := by
    intro h; rw [h] at hcard'; simp at hcard'
  obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hne
  have hs2 : s.erase p = q ::ₘ (s.erase p).erase q := (Multiset.cons_erase hq).symm
  have e1 := mkraft_cons p (s.erase p)
  rw [← hs] at e1
  have e2 := mkraft_cons q ((s.erase p).erase q)
  rw [← hs2] at e2
  rw [e1, e2, hp2] at hk
  have h1 : (0:ℝ) < (2 : ℝ)⁻¹ ^ q.2 := by positivity
  have h2 : (0:ℝ) ≤ mkraft ((s.erase p).erase q) := mkraft_nonneg _
  simp only [pow_zero] at hk
  linarith

/-- Exchange argument: a symbol of minimal weight may be assumed to have a codeword of
maximal length, without increasing the expected length. -/
