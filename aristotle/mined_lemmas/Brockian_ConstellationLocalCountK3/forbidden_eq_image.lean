/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- The *local count* of a constellation (admissible tuple) with shift set `H`
at the modulus `p`: the number of residue classes `a` mod `p` such that none of
the numbers `a + h`, `h ∈ H`, is divisible by `p`. -/

lemma forbidden_eq_image (p : ℕ) [NeZero p] (H : Finset ℤ) :
    (Finset.univ.filter (fun a : ZMod p => ¬ ∀ h ∈ H, a + (h : ZMod p) ≠ 0))
      = H.image (fun h : ℤ => -((h : ℤ) : ZMod p)) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_forall,
    Classical.not_not]
  constructor
  · rintro ⟨h, hH, hne⟩
    exact ⟨h, hH, by linear_combination -hne⟩
  · rintro ⟨h, hH, hEq⟩
    exact ⟨h, hH, by linear_combination -hEq⟩

/-- The local count equals `p` minus the number of distinct residues of `-H`. -/
