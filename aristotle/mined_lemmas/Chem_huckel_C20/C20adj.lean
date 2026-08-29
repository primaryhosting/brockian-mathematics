/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/

noncomputable def C20adj : Matrix (ZMod 20) (ZMod 20) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The `k`-th Hückel eigenvalue of `C₂₀`, namely `2 cos (2πk/20)`. -/
