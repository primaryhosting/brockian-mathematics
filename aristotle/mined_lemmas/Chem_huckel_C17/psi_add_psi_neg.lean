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

lemma psi_add_psi_neg (a : ZMod 17) :
    psi a + psi (-a) = 2 * Real.cos (2 * Real.pi * a.val / 17) := by
  rw [psi_neg, psi_apply, ← Complex.exp_neg]
  have hrw : ((2 : ℂ) * Real.pi * Complex.I * a.val / 17)
      = ((2 * Real.pi * a.val / 17 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hrw, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Orthogonality of characters: the character sum vanishes unless `d = 0`. -/
