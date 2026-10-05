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

set_option maxHeartbeats 1000000
set_option autoImplicit false

open Computability

namespace CS

/-- Repeating a word `y` exactly `n` times gives an element of the Kleene star of `{y}`. -/
theorem flatten_replicate_mem_kstar {α : Type*} (y : List α) (n : ℕ) :
    (List.replicate n y).flatten ∈ ({y} : Language α)∗ := by
  rw [Language.mem_kstar]
  refine ⟨List.replicate n y, rfl, ?_⟩
  intro z hz
  rw [List.eq_of_mem_replicate hz]
  rfl

/--
**Pumping lemma for regular languages.**

Every regular language `L` admits a pumping length `p > 0`: every word `w ∈ L` of length at
least `p` can be split as `w = x ++ y ++ z` with `|x ++ y| ≤ p` and `y ≠ []`, in such a way that
all pumped words `x ++ yⁿ ++ z` (for every `n : ℕ`) again belong to `L`.
-/
theorem pumping_regular {α : Type*} {L : Language α} (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
      ∃ x y z : List α, w = x ++ y ++ z ∧ (x ++ y).length ≤ p ∧ y ≠ [] ∧
        ∀ n : ℕ, x ++ (List.replicate n y).flatten ++ z ∈ L := by
  obtain ⟨σ, hσ, M, hM⟩ := hL
  have hne : Nonempty σ := ⟨M.start⟩
  refine ⟨Fintype.card σ, Fintype.card_pos, ?_⟩
  intro w hw hlen
  subst hM
  obtain ⟨x, y, z, hsplit, hxy, hy, hsub⟩ := M.pumping_lemma hw hlen
  refine ⟨x, y, z, hsplit, by simpa using hxy, hy, fun n => hsub ?_⟩
  rw [Language.mem_mul]
  refine ⟨x ++ (List.replicate n y).flatten, ?_, z, rfl, by simp⟩
  rw [Language.mem_mul]
  exact ⟨x, rfl, (List.replicate n y).flatten, flatten_replicate_mem_kstar y n, rfl⟩

end CS

