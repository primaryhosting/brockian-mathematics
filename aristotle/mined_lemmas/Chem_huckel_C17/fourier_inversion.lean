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

lemma fourier_inversion (v : ZMod 17 → ℂ) (j : ZMod 17) :
    ∑ k : ZMod 17, fourierCoeff v k * psi (k * j) = 17 * v j := by
  have step : ∀ k : ZMod 17, fourierCoeff v k * psi (k * j)
      = ∑ j' : ZMod 17, v j' * psi (k * (j - j')) := by
    intro k
    rw [fourierCoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j' _ => ?_)
    have hk : k * (j - j') = (-(k * j')) + k * j := by ring
    rw [hk, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => step k), Finset.sum_comm]
  have step2 : ∀ j' : ZMod 17, ∑ k : ZMod 17, v j' * psi (k * (j - j'))
      = if j' = j then 17 * v j else 0 := by
    intro j'
    rw [← Finset.mul_sum, psi_orthogonality]
    by_cases h : j' = j
    · subst h; simp; ring
    · rw [if_neg (fun hz => h (by linear_combination -hz)), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl (fun j' _ => step2 j')]
  simp

/-! ### The main theorem -/

/-- **Hückel theory for the 17-annulene.** A complex number `μ` is an eigenvalue of the
adjacency (Hückel) matrix of the cycle graph `C₁₇` if and only if `μ = 2 cos (2πk/17)`
for some `k ∈ {0, …, 16}`. -/
