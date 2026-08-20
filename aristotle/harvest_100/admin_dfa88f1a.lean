/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

variable {α : Type*}

/-- The `n`-fold concatenation of the word `b` with itself. -/
def pow (b : List α) (n : ℕ) : List α := (List.replicate n b).flatten

@[simp] lemma pow_zero (b : List α) : pow b 0 = [] := rfl

@[simp] lemma pow_succ (b : List α) (n : ℕ) : pow b (n + 1) = b ++ pow b n := by
  simp [pow, List.replicate_succ]

lemma pow_mem_kstar (b : List α) (n : ℕ) : pow b n ∈ KStar.kstar ({b} : Language α) := by
  rw [Language.mem_kstar]
  refine ⟨List.replicate n b, rfl, ?_⟩
  intro x hx
  simpa using List.eq_of_mem_replicate hx

/-- **Pumping lemma for regular languages.**
Every regular language `L` admits a pumping length `p > 0`: every word `x ∈ L` with `p ≤ |x|`
can be split as `x = a ++ b ++ c` with `|a| + |b| ≤ p` and `b ≠ []`, such that all pumped words
`a ++ bⁿ ++ c` belong to `L`. -/
theorem pumping_regular {α : Type*} {L : Language α} (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ x ∈ L, p ≤ x.length →
      ∃ a b c : List α, x = a ++ b ++ c ∧ a.length + b.length ≤ p ∧ b ≠ [] ∧
        ∀ n : ℕ, a ++ pow b n ++ c ∈ L := by
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  have hne : Nonempty σ := ⟨M.start⟩
  refine ⟨Fintype.card σ, Fintype.card_pos, ?_⟩
  intro x hx hlen
  obtain ⟨a, b, c, hsplit, hab, hbne, hsub⟩ := M.pumping_lemma hx hlen
  refine ⟨a, b, c, hsplit, hab, hbne, fun n => ?_⟩
  refine hsub ?_
  rw [Language.mem_mul]
  exact ⟨a ++ pow b n, ⟨a, rfl, pow b n, pow_mem_kstar b n, rfl⟩, c, rfl, rfl⟩

end CS

