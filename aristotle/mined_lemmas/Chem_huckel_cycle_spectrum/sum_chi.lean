import Mathlib
/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the first command in a file, so the header
comment above is placed immediately after the single `import Mathlib` line.)
-/

open Complex Matrix Finset

namespace Chem

/-- The standard primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma sum_chi [NeZero n] (t : Fin n) :
    ∑ k : Fin n, chi n (k * t) = if t = 0 then (n : ℂ) else 0 := by
  have h : ∑ k : Fin n, chi n (k * t) = ∑ i ∈ Finset.range n, (chi n t) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (chi n t) ^ i) n]
    exact Finset.sum_congr rfl fun k _ => chi_mul k t
  rw [h]
  split_ifs with ht
  · subst ht
    simp [chi_zero]
  · rw [geom_sum_eq (chi_ne_one ht), chi_pow_n, sub_self, zero_div]

/-- The pair of conjugate characters sums to the Hückel eigenvalue `2 cos (2πk/n)`. -/
