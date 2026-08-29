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

lemma cyc_key (k i a b : ℕ) (ha : a < 2 * k + 1) (hb : b < 2 * k + 1)
    (h : (i + a) % (2 * k + 1) = (i + b) % (2 * k + 1)) : a = b := by
  have h1 : (i + a) ≡ (i + b) [MOD 2 * k + 1] := h
  have h2 : a ≡ b [MOD 2 * k + 1] := Nat.ModEq.add_left_cancel' i h1
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

