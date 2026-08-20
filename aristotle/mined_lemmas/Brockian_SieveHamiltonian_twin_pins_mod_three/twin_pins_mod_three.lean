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

theorem twin_pins_mod_three (a : ZMod 3) :
    (a ≠ 0 ∧ a + 2 ≠ 0) ↔ a = 2 := by
  fin_cases a <;> simp_all [ZMod]

/-- NO-GO (target): two twin-admissible integers are never at distance
1 or 2; the +1 and +2 adjacencies on any wheel containing 3 carry no
admissible edges, so their Dirichlet compressions trivialize to 2·I.
The residual flow is +3 on the surviving coset. -/
