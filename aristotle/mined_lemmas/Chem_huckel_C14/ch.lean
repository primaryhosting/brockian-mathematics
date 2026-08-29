/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the C₁₄ ring

The adjacency eigenvalues of the cycle graph `C₁₄` are exactly the numbers
`2 * cos (2πk/14)` for `k = 0, …, 13`.
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

noncomputable def ch (x : Fin 14) : ℂ := om ^ x.val

