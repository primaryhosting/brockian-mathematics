/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian

open DihedralGroup

noncomputable section

/-! ## The root of unity -/

/-- A primitive `n`-th root of unity in `ℂ`. -/

theorem isoPlane_mul_isoPlane (n : ℕ) [NeZero n] (j k : ZMod n)
    {u v : ZMod n → ℂ} (hu : u ∈ isoPlane n j) (hv : v ∈ isoPlane n k) :
    u * v ∈ isoPlane n (j + k) ⊔ isoPlane n (j - k) := by
  rw [isoPlane, Submodule.mem_span_pair] at hu hv
  obtain ⟨a, b, rfl⟩ := hu
  obtain ⟨c, d, rfl⟩ := hv
  have key : (a • evec n j + b • evec n (-j)) * (c • evec n k + d • evec n (-k))
      = ((a * c) • evec n (j + k) + (b * d) • evec n (-(j + k)))
        + ((a * d) • evec n (j - k) + (b * c) • evec n (-(j - k))) := by
    have h1 : evec n j * evec n k = evec n (j + k) := evec_mul n j k
    have h2 : evec n (-j) * evec n (-k) = evec n (-(j + k)) := by
      rw [evec_mul]; ring_nf
    have h3 : evec n j * evec n (-k) = evec n (j - k) := by
      rw [evec_mul]; ring_nf
    have h4 : evec n (-j) * evec n k = evec n (-(j - k)) := by
      rw [evec_mul]; ring_nf
    rw [add_mul, mul_add, mul_add]
    rw [smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,
      h1, h2, h3, h4]
    abel
  rw [key]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.mem_sup_left (Submodule.add_mem _
      (Submodule.smul_mem _ _ (evec_mem_isoPlane n (j + k)))
      (Submodule.smul_mem _ _ (evec_neg_mem_isoPlane n (j + k))))
  · exact Submodule.mem_sup_right (Submodule.add_mem _
      (Submodule.smul_mem _ _ (evec_mem_isoPlane n (j - k)))
      (Submodule.smul_mem _ _ (evec_neg_mem_isoPlane n (j - k))))

/-! ## The main theorem -/

/-- **Pentagon Pentagon Isotypic, higher `n`.**

For every `n ≥ 1`, the vertex space `ZMod n → ℂ` of the regular `n`-gon, carrying the
natural representation of the dihedral group `D_n` (rotations `r i : f ↦ f(· + i)` and
reflections `sr i : f ↦ f(i - ·)`), decomposes into isotypic planes
`isoPlane n k = span {e_k, e_{-k}}`, where `e_k x = ζ^(k x)` for a primitive `n`-th root of
unity `ζ`:

1. each isotypic plane is a subrepresentation (invariant under all of `D_n`);
2. the isotypic planes exhaust the vertex space;
3. the plane `isoPlane n k` is two-dimensional exactly in the generic case `k ≠ -k`, and is
   a line in the degenerate cases `k = -k` (i.e. `k = 0`, and `k = n/2` for even `n`);
4. each isotypic plane is irreducible: its only invariant subspaces are `⊥` and itself;
5. the "pentagon ⊗ pentagon" fusion rule: the pointwise product of vectors of the `j`-th and
   `k`-th isotypic planes lies in `isoPlane n (j+k) ⊔ isoPlane n (j-k)`.

For `n = 5` this is the classical decomposition of the pentagon representation of `D₅`. -/
