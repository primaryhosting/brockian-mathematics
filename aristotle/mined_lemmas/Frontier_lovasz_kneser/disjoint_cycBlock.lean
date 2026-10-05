/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of an
`n`-element set. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of `Fin n`, and two
distinct such subsets are adjacent when they are disjoint. -/

lemma disjoint_cycBlock (k i : ℕ) : Disjoint (cycBlock k (i + k)) (cycBlock k i) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  simp only [cycBlock, Finset.mem_image, Finset.mem_range] at hx hx'
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hb'⟩ := hx'
  have h1 := congrArg Fin.val hb'
  simp only at h1
  have h2 : (i + b) % (2 * k + 1) = (i + (k + a)) % (2 * k + 1) := by
    rw [← add_assoc]; exact h1
  have h3 := cyc_key k i b (k + a) (by omega) (by omega) h2
  omega

