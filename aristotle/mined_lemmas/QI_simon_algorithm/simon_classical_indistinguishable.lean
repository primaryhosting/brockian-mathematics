/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is reproduced above as a plain block comment: Lean 4 does not allow a
-- module docstring `/-! ... -/` to precede the `import` lines.)

import Mathlib

/-!
## Simon's problem

Simon's problem: a function `f` on `n`-bit strings is promised to be two-to-one with
`f x = f y ↔ y = x ∨ y = x + s` for a hidden nonzero secret `s`; the task is to find `s`.

This file formalises the two information-theoretic facts behind the statement
"Simon's problem takes `O(n)` quantum queries but `Ω(2^(n/2))` classical queries":

* **Quantum side.** Each run of Simon's quantum subroutine returns a uniformly random
  vector `y` in the hyperplane `s^⊥`. We show that `n` such vectors always suffice:
  for every nonzero `s` there is a set `Y` of at most `n` vectors orthogonal to `s`
  such that `s` is the unique nonzero vector orthogonal to all of `Y`. Hence `O(n)`
  quantum queries pin down the secret.

* **Classical side.** A classical algorithm only learns something about `s` when two of
  its queries collide. We show that a query set `Q` that is guaranteed to contain a
  collision for *every* possible secret must satisfy `2 ^ n ≤ Q.card ^ 2`, i.e.
  `Q.card ≥ 2 ^ (n / 2)`. Moreover, if `Q.card ^ 2 + 3 ≤ 2 ^ n`, then there are two
  *different* secrets whose Simon functions agree on `Q` up to a global relabelling of
  the output values, so no classical algorithm making those queries can tell them apart.
-/

namespace QI

open Finset

/-- `n`-bit strings, viewed as vectors over the field with two elements. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The mod-2 inner product of two bit strings. -/

theorem simon_classical_indistinguishable {n : ℕ} (Q : Finset (Bits n))
    (hQ : Q.card ^ 2 + 3 ≤ 2 ^ n) :
    ∃ s₁ s₂ : Bits n, ∃ j₁ j₂ : Fin n, s₁ ≠ 0 ∧ s₂ ≠ 0 ∧ s₁ ≠ s₂ ∧ s₁ j₁ = 1 ∧ s₂ j₂ = 1 ∧
      ∃ π : Bits n ≃ Bits n, ∀ x ∈ Q, π (simonFun s₁ j₁ x) = simonFun s₂ j₂ x := by
  classical
  set G := ((Finset.univ : Finset (Bits n)).erase 0).filter
      (fun s => ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → y ≠ x + s) with hGdef
  have hsub : (Finset.univ : Finset (Bits n)).erase 0 ⊆
      G ∪ Q.offDiag.image (fun p : Bits n × Bits n => p.1 + p.2) := by
    intro s hs
    by_cases hgood : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → y ≠ x + s
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hs, hgood⟩)
    · push_neg at hgood
      obtain ⟨x, hx, y, hy, hxy, hyx⟩ := hgood
      exact Finset.mem_union_right _ (collision_secret_mem_image Q ⟨x, hx, y, hy, hxy, hyx⟩)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_univ_bits] at hcard
  have hunion := Finset.card_union_le G (Q.offDiag.image (fun p : Bits n × Bits n => p.1 + p.2))
  have hB := card_collision_secrets_le Q
  have hGcard : 1 < G.card := by
    rw [pow_two] at hQ
    generalize Q.card * Q.card = m at hQ hB
    generalize (2 : ℕ) ^ n = p at hQ hcard
    omega
  obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.1 hGcard
  rw [hGdef, Finset.mem_filter, Finset.mem_erase] at hs₁ hs₂
  obtain ⟨⟨hs₁0, -⟩, hgood₁⟩ := hs₁
  obtain ⟨⟨hs₂0, -⟩, hgood₂⟩ := hs₂
  obtain ⟨j₁, hj₁⟩ := exists_pivot hs₁0
  obtain ⟨j₂, hj₂⟩ := exists_pivot hs₂0
  have hinj : ∀ (s : Bits n) (j : Fin n), s j = 1 → (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → y ≠ x + s) →
      Set.InjOn (simonFun s j) Q := by
    intro s j hj hgood x hx y hy hxy
    by_cases hxy' : x = y
    · exact hxy'
    · exfalso
      rcases (simonFun_eq_iff hj x y).1 hxy with h | h
      · exact hxy' h.symm
      · exact hgood x (by simpa using hx) y (by simpa using hy) hxy' h
  obtain ⟨π, hπ⟩ :=
    exists_perm_of_injOn Q (simonFun s₁ j₁) (simonFun s₂ j₂)
      (hinj s₁ j₁ hj₁ hgood₁) (hinj s₂ j₂ hj₂ hgood₂)
  exact ⟨s₁, s₂, j₁, j₂, hs₁0, hs₂0, hne, hj₁, hj₂, π, hπ⟩

/-- **Simon's problem**: `O(n)` quantum queries suffice, while `Ω(2 ^ (n / 2))` classical
queries are necessary. -/
