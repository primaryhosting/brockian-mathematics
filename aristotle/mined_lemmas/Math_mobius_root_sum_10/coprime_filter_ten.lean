/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Math

/-- The Möbius function at `10` equals `1`. -/

lemma coprime_filter_ten : (range 10).filter (Nat.Coprime 10) = {1, 3, 7, 9} := by decide

/-- A primitive `10`-th root of unity `ζ` in a domain satisfies `ζ^5 = -1`. -/
