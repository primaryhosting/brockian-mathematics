/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 does not allow a `/-! ... -/` module docstring to precede `import`, so the
-- required header comment is reproduced verbatim immediately after the import below.)

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

/-!
## Overview

We prove the **quantum Singleton bound** (Knill–Laflamme–Rains): an `[[n, k, d]]_q`
quantum error-correcting code satisfies `k + 2 * (d - 1) ≤ n`, i.e. `n - k ≥ 2 (d - 1)`.

The proof given here is a purely linear-algebraic ("Rényi-0"/rank) version of the usual
entropic no-cloning argument.  Writing the code space as a tensor `T` with a reference
index `R` (of size `q ^ k`) and three groups of sites `A`, `B`, `C`, the Knill–Laflamme
conditions for the two disjoint site sets `A` and `B` say that the Gram matrices of the
code vectors, partially traced onto `A` (resp. `B`), are proportional to the identity in
the reference index.  Passing to ranks:

* `rank ρ_{RA} = |R| · rank ρ_A` and `rank ρ_{RB} = |R| · rank ρ_B`  (Kronecker structure);
* `rank ρ_{BC} ≤ rank ρ_B · rank ρ_C`  (rank submultiplicativity across a tensor cut);
* `rank ρ_{RA} = rank ρ_{BC}` and `rank ρ_{RB} = rank ρ_{AC}` (purity).

Multiplying the two resulting inequalities `|R| · a ≤ b · c` and `|R| · b ≤ a · c` and
cancelling `a·b > 0` gives `|R| ≤ c ≤ q ^ |C|`, which is the bound.

No Mathlib lemma proves this statement (Mathlib contains no quantum coding theory), so the
required linear algebra — in particular a rank factorization of a matrix with one-sided
inverses, the rank of `1 ⊗ₖ S`, and submultiplicativity of the rank across a tensor cut —
is developed here from scratch.
-/

open Matrix Module Kronecker
open scoped ComplexOrder

namespace QI

/-! ### General linear algebra: rank tools -/

/-- **Rank factorization.**  Any matrix `N` factors as `N = F * G` where `F` has `rank N`
columns and a left inverse, and `G` has `rank N` rows and a right inverse. -/

theorem rank_le_mul_rank {K D B C : Type} [Field K] [Fintype D] [Fintype B] [Fintype C]
    [DecidableEq D] [DecidableEq B] [DecidableEq C] (T : D → B → C → K) :
    (Matrix.of fun (p : B × C) (d : D) => T d p.1 p.2).rank
      ≤ (Matrix.of fun (b : B) (p : D × C) => T p.1 b p.2).rank
        * (Matrix.of fun (c : C) (p : D × B) => T p.1 p.2 c).rank := by
  classical
  set NB : Matrix B (D × C) K := Matrix.of fun (b : B) (p : D × C) => T p.1 b p.2 with hNB
  set NC : Matrix C (D × B) K := Matrix.of fun (c : C) (p : D × B) => T p.1 p.2 c with hNC
  set MBC : Matrix (B × C) D K := Matrix.of fun (p : B × C) (d : D) => T d p.1 p.2 with hMBC
  obtain ⟨rB, F, G, L, M, hrB, hFG, hLF, -⟩ := exists_rank_factorization NB
  obtain ⟨rC, H, J, M', -, hrC, hHJ, hMH, -⟩ := exists_rank_factorization NC
  have hP : (F * L) * NB = NB := by
    rw [hFG, Matrix.mul_assoc, ← Matrix.mul_assoc L F G, hLF, Matrix.one_mul]
  have hQ : (H * M') * NC = NC := by
    rw [hHJ, Matrix.mul_assoc, ← Matrix.mul_assoc M' H J, hMH, Matrix.one_mul]
  have keyB : ∀ (d : D) (b : B) (c : C), ∑ b', (F * L) b b' * T d b' c = T d b c := by
    intro d b c
    have := congrFun (congrFun hP b) (d, c)
    simpa [Matrix.mul_apply, hNB] using this
  have keyC : ∀ (d : D) (b : B) (c : C), ∑ c', (H * M') c c' * T d b c' = T d b c := by
    intro d b c
    have := congrFun (congrFun hQ c) (d, b)
    simpa [Matrix.mul_apply, hNC] using this
  have main : ((F * L) ⊗ₖ (H * M')) * MBC = MBC := by
    ext p d
    obtain ⟨b, c⟩ := p
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have h : ∀ b', ∑ c', ((F * L) ⊗ₖ (H * M')) (b, c) (b', c') * MBC (b', c') d
        = (F * L) b b' * T d b' c := by
      intro b'
      simp only [Matrix.kroneckerMap_apply, hMBC, Matrix.of_apply]
      rw [← keyC d b' c, Finset.mul_sum]
      congr 1
      ext c'
      ring
    rw [Finset.sum_congr rfl (fun b' _ => h b')]
    exact keyB d b c
  have hfact : ((F * L) ⊗ₖ (H * M')) = (F ⊗ₖ H) * (L ⊗ₖ M') := by
    rw [← Matrix.mul_kronecker_mul]
  calc MBC.rank = ((F ⊗ₖ H) * ((L ⊗ₖ M') * MBC)).rank := by
        rw [← Matrix.mul_assoc, ← hfact, main]
    _ ≤ (F ⊗ₖ H).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin rB × Fin rC) := Matrix.rank_le_card_width _
    _ = NB.rank * NC.rank := by simp [hrB, hrC]

/-- A nonzero matrix has positive rank. -/
