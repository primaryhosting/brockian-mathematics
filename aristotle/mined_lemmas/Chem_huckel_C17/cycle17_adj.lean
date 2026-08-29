import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
(The header comment above must be the first thing in the file; Lean requires
`import` lines to precede all commands, so the single `import Mathlib` line comes first.)

We compute the spectrum of the adjacency matrix of the cycle graph `C₁₇`
(the Hückel matrix of a 17-membered annulene, in units where α = 0 and β = 1):
the eigenvalues are exactly `2 cos (2πk/17)` for `k = 0, …, 16`.

The vertex set `Fin 17` is identified with the ring `ZMod 17`, and the proof uses the
standard additive character `ψ a = exp (2πi a / 17)` and discrete Fourier analysis.
-/

open Complex Matrix Finset

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₇`, i.e. the Hückel matrix of a
17-membered annulene with `α = 0`, `β = 1`. The index type `ZMod 17` is definitionally
the vertex type `Fin 17` of `SimpleGraph.cycleGraph 17`. -/

lemma cycle17_adj (i j : ZMod 17) :
    (SimpleGraph.cycleGraph 17).Adj i j ↔ (i - j = 1 ∨ j - i = 1) :=
  SimpleGraph.cycleGraph_adj (n := 15)

