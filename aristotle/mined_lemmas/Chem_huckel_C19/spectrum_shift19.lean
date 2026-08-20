/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-! -/` module docstring,
-- because in Lean 4.28 a module docstring is a command and cannot precede `import`.
-- The same text is repeated below as the module docstring.)

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel spectrum of the cyclic polyene C₁₉: the eigenvalues of the adjacency matrix of the
cycle graph `C₁₉` are exactly the numbers `2 cos (2πk/19)`, `k = 0, …, 18`.

The proof identifies the adjacency matrix with `S + S¹⁸`, where `S` is the cyclic shift matrix
(a circulant matrix), computes `spectrum ℂ S` (all 19-th roots of unity), and then applies the
spectral mapping theorem `spectrum.map_polynomial_aeval_of_degree_pos` for the polynomial
`X + X ^ 18`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Matrix Complex Polynomial SimpleGraph

/-- A primitive 19-th root of unity. -/

lemma spectrum_shift19 :
    spectrum ℂ shift19 = Set.range (fun k : Fin 19 => zeta19 ^ (k : ℕ)) := by
  apply Set.eq_of_subset_of_subset
  · intro μ hμ
    have h1 : μ ^ 19 ∈ spectrum ℂ (shift19 ^ 19) := spectrum.pow_mem_pow shift19 19 hμ
    rw [shift19_pow_19, spectrum.one_eq] at h1
    have h2 : μ ^ 19 = 1 := h1
    obtain ⟨i, hi, hval⟩ := isPrimitiveRoot_zeta19.eq_pow_of_pow_eq_one h2
    exact ⟨⟨i, hi⟩, hval⟩
  · rintro _ ⟨k, rfl⟩
    exact zeta_pow_mem_spectrum_shift19 (k : ℕ)

