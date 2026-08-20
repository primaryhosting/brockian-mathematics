/-
  Brockian/SieveHamiltonian.lean — THE SIEVE HAMILTONIAN CAMPAIGN
  (July 30, after the "invent the dynamics" program note).

  The object: on the arithmetic wheel Z/M (M odd squarefree), the twin
  sieve deletes residues a with a ≡ 0 or a ≡ −2 mod some ℓ ∣ M. Once
  3 ∣ M the admissible set is pinned to the coset a ≡ 2 (mod 3); the
  residual translation flow is +3 on that coset. The compressed
  Hamiltonian (Dirichlet deletion of forbidden sites from the residual
  cycle) decomposes into path Laplacians over the admissible RUNS, so
  its spectrum is exact and finite. Everything below is finite; no
  Hilbert–Pólya claim is made anywhere in this file — the operator
  limit M → ∞ is an OPEN PROGRAM subject to the G0–G6 gate ladder.

  Charter as Core.lean. The declarations below are the formal campaign targets.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.SieveHamiltonian

open Matrix

/-! ## 1. The no-go theorem: why the naive adjacency dies at 3 -/

/-- Twin admissibility pins the mod-3 residue. -/

theorem silver_gap_rigidity_finite : SilverGapRigidityTarget := by
  intro g hg j hj1 hjg
  have h2_3 : Real.pi * 2 / 3 = Real.pi - Real.pi / 3 := by ring
  have h3_4 : Real.pi * 3 / 4 = Real.pi - Real.pi / 4 := by ring
  have h2_4 : Real.pi * 2 / 4 = Real.pi / 2 := by ring
  interval_cases g <;> interval_cases j <;>
    norm_num [Real.cos_pi_div_two, Real.cos_pi_div_three, Real.cos_pi_div_four,
      h2_3, h3_4, h2_4, Real.cos_pi_sub]
  · exact Or.inl (by ring_nf)
  · exact Or.inr (Or.inr (Or.inr (by ring_nf)))

/-! ## 5. The triple-count law (CRT product, Hardy–Littlewood-flavored,
purely finite). A (1,4,2)-triple at wheel level M is a residue a mod M
with a, a+3, a+6 all twin-admissible. The six constraints mod ℓ
(a ≢ 0,−2,−3,−5,−6,−8) are distinct classes for every prime ℓ ≥ 7,
giving ℓ − 6 free choices; for ℓ = 3 and ℓ = 5 the counts are 1.
Empirically verified at levels 105, 1155, 15015, 255255, 4849845:
counts 1, 5, 35, 385, 5005 = ∏_{7 ≤ ℓ ∣ M} (ℓ − 6). -/

