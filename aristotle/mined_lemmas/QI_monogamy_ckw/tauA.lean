import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Monogamy of entanglement: the Coffman–Kundu–Wootters inequality

A pure state of three qubits `A`, `B`, `C` is described by its amplitudes
`a i j k` (`i` the `A`-index, `j` the `B`-index, `k` the `C`-index) in the
computational basis, i.e. `|ψ⟩ = ∑ a i j k • |i j k⟩`.

* `QI.rhoA a` is the reduced density matrix `ρ_A = Tr_{BC} |ψ⟩⟨ψ|`;
* `QI.tauA a = 4 det ρ_A` is the tangle of the bipartite cut `A | BC`
  (for a normalised state this equals `2 (1 - Tr ρ_A²)`, the squared
  concurrence of the pure bipartite state; see `QI.tauA_eq_two_mul_one_sub_purity`);
* `QI.Mab a` is the `2 × 2` matrix `M` of the "spin flip" bilinear form
  `⟨φ_k| σ_y ⊗ σ_y |φ_l^*⟩` built from the (unnormalised) conditional vectors
  `φ_k = ∑_{ij} a i j k • |ij⟩` on `AB` obtained by tracing out `C`.  The singular
  values `σ₁ ≥ σ₂` of `M` are exactly the square roots of the eigenvalues of
  `ρ_{AB} ρ̃_{AB}` occurring in Wootters' formula, so the squared concurrence of
  `ρ_{AB}` is `C²_{AB} = (σ₁ - σ₂)² = σ₁² + σ₂² - 2 σ₁σ₂ = ‖M‖_F² - 2 |det M|`,
  which is `QI.CABsq a`;
* symmetrically `QI.Mac a` and `QI.CACsq a` for the pair `A C`.

The main theorem `QI.monogamy_ckw` is the CKW inequality
`C²_{AB} + C²_{AC} ≤ τ_{A|BC}`.

The heart of the matter is the polynomial identity `QI.tauA_eq_frob_add_frob`,
`τ_{A|BC} = ‖M‖_F² + ‖N‖_F²`, after which monogamy follows from `|det M| ≥ 0`
and `|det N| ≥ 0`.  The deficit is exactly `2 (|det M| + |det N|)`, twice the
residual three-way entanglement (`QI.monogamy_ckw_deficit`).

All statements are homogeneous of degree `4` in the amplitudes, so no
normalisation hypothesis is needed.
-/

namespace QI

open Complex Finset Matrix

noncomputable section

variable (a : Fin 2 → Fin 2 → Fin 2 → ℂ)

/-- The reduced density matrix of qubit `A` for the three-qubit pure state with
amplitudes `a`. -/

def tauA : ℝ := 4 * ((rhoA a).det).re

/-- The `2 × 2` matrix whose singular values are the square roots of the
eigenvalues of `ρ_{AB} ρ̃_{AB}` (Wootters' matrix for the pair `A B`). -/
