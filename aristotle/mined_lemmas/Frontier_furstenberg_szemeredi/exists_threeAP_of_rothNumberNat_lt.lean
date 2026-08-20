/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

open scoped Classical in
/-- The number of elements of `A` below `n`. -/

lemma exists_threeAP_of_rothNumberNat_lt {n : ℕ} {s : Finset ℕ} (hsub : s ⊆ Finset.range n)
    (hcard : rothNumberNat n < s.card) :
    ∃ a d : ℕ, 0 < d ∧ a ∈ s ∧ a + d ∈ s ∧ a + 2 * d ∈ s := by
  by_contra hcon
  push_neg at hcon
  have hfree : ThreeAPFree (s : Set ℕ) := by
    intro a ha b hb c hcmem habc
    by_contra hne
    simp only [Finset.mem_coe] at ha hb hcmem
    rcases lt_trichotomy a b with h | h | h
    · -- a < b, so b - a > 0 and a, b, c is an AP
      have hd : 0 < b - a := by omega
      have h1 : a + (b - a) = b := by omega
      have h2 : a + 2 * (b - a) = c := by omega
      exact hcon a (b - a) hd ha (by rwa [h1]) (by rwa [h2])
    · exact hne h
    · -- b < a, so c < b < a and c, b, a is an AP
      have hd : 0 < a - b := by omega
      have h1 : c + (a - b) = b := by omega
      have h2 : c + 2 * (a - b) = a := by omega
      exact hcon c (a - b) hd hcmem (by rwa [h1]) (by rwa [h2])
  have : s.card ≤ rothNumberNat n :=
    hfree.le_rothNumberNat s (fun x hx => Finset.mem_range.1 (hsub hx)) rfl
  omega

/-- **Base case (Roth's theorem, `k = 3`)**: every set of naturals of positive upper density
contains a three-term arithmetic progression. This is unconditional. -/
