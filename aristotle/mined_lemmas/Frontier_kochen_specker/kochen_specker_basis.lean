/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

The Kochen–Specker theorem states that in a Hilbert space of dimension at least three there is
no noncontextual hidden-variable assignment: one cannot assign to every ray a value in `{0, 1}`,
independently of the measurement context, in such a way that every orthonormal basis contains
exactly one ray of value `1`.

We formalise the four dimensional case, which is the base case admitting a purely combinatorial
(parity) proof, due to Cabello, Estebaranz and García-Alcaine: there are `18` vectors in
`ℝ⁴` arranged into `9` orthogonal frames so that every vector lies in exactly two frames.
Summing the value `1` over the nine frames counts each vector twice, giving `9 = 2 * k`,
which is impossible.

The main statement is `Frontier.kochen_specker`, with `Frontier.kochen_specker_basis` an
equivalent restatement in terms of `OrthonormalBasis`.
-/

set_option maxHeartbeats 1000000

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A family of four vectors which is *orthogonal and nondegenerate*: the inner product of
`v i` and `v j` vanishes exactly when `i ≠ j`.  Equivalently, the `v i` are nonzero and
pairwise orthogonal. -/

theorem kochen_specker_basis (f : EuclideanSpace ℝ (Fin 4) → Bool) :
    ¬ ∀ b : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)), ∃! i, f (b i) = true := by
  intro h
  refine kochen_specker ⟨f, ?_⟩
  intro v hv
  have hcard : Fintype.card (Fin 4) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) := by simp
  have hb : Orthonormal ℝ ⇑(basisOfOrthonormalOfCardEqFinrank hv hcard) := by
    rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hv
  have hcoe : ⇑((basisOfOrthonormalOfCardEqFinrank hv hcard).toOrthonormalBasis hb) = v := by
    rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  have := h ((basisOfOrthonormalOfCardEqFinrank hv hcard).toOrthonormalBasis hb)
  rwa [hcoe] at this

end Frontier

/-
# Kochen Specker (all finite dimensions ≥ 4)
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.KochenSpecker

/-!
# Kochen–Specker in every finite dimension at least four

Starting from the four dimensional case `Frontier.kochen_specker`, we deduce the
Kochen–Specker theorem in every finite dimension `n ≥ 4`: for a real inner product space `E`
of finite dimension at least four there is no map `f : E → Bool` such that every orthonormal
basis of `E` contains exactly one vector of value `true`.

The reduction is the standard one.  Fix an orthonormal basis `b` of `E` and let `b k` be its
unique vector of value `true`.  Reindex so that `k` belongs to a distinguished four element
block; all basis vectors outside that block then have value `false`.  Every orthonormal
`4`-frame inside the span of the block, together with the basis vectors outside the block, is
again an orthonormal basis of `E`, hence carries exactly one `true`, which must sit in the
frame.  Thus `f` would induce a Kochen–Specker valuation in dimension four.
-/

set_option maxHeartbeats 1000000

namespace Frontier

open Module

section FrameMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The image of a vector of `EuclideanSpace ℝ (Fin 4)` under the frame `u`, i.e. the
coordinate map of the four dimensional subspace spanned by `u`. -/
