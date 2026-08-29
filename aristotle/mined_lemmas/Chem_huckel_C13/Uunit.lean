import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- The adjacency matrix of the cycle graph `C₁₃` (the Hückel matrix of the
`C₁₃` carbon ring, in units where `α = 0` and `β = 1`). -/

noncomputable def Uunit : (Matrix (Fin 13) (Fin 13) ℂ)ˣ :=
  ⟨U, V, U_mul_V, V_mul_U⟩

