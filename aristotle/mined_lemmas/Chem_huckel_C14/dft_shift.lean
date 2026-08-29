import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex SimpleGraph

namespace Chem

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₄`, i.e. the Hückel matrix of the
carbon skeleton of a 14-membered annulene in units where `α = 0` and `β = 1`. -/

private lemma dft_shift (v : ZMod 14 → ℂ) (a k : ZMod 14) :
    ZMod.dft (fun j => v (j + a)) k = chi (a * k) * ZMod.dft v k := by
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight a) _ _ (fun j => ?_)
  simp only [Equiv.coe_addRight, smul_eq_mul, chi]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  ring_nf

/-- **Hückel theory for C₁₄.** The eigenvalues of the adjacency matrix of the cycle graph `C₁₄`
are exactly the numbers `2 cos (2πk/14)` for `k = 0, 1, …, 13`. -/
