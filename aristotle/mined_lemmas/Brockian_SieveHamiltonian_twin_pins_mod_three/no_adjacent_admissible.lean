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

theorem no_adjacent_admissible (a b : ℤ)
    (ha : (a : ZMod 3) = 2) (hb : (b : ZMod 3) = 2)
    (h : b - a = 1 ∨ b - a = 2) : False := by
  obtain h | h := h
  · have h' : ((b - a : ℤ) : ZMod 3) = 1 := by rw [h]; norm_cast
    simp [ha, hb] at h'
  · have h' : ((b - a : ℤ) : ZMod 3) = 2 := by rw [h]; norm_cast
    simp [ha, hb] at h'
    contradiction

/-! ## 2. The run-cap and signature theorems (the mod-5 rigidity) -/

/-- RUN CAP (target, decidable): no four consecutive states of the +3
flow are all admissible mod 5 — four steps of +3 visit four distinct
mod-5 classes, but only three classes {1,2,4} are admissible. Hence
every admissible run has length ≤ 3, at every wheel level. -/
