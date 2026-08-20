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

theorem tripleAdmissibleCount_mul_of_coprime (m n : ℕ) (h : m.Coprime n) :
    tripleAdmissibleCount (m * n) =
      tripleAdmissibleCount m * tripleAdmissibleCount n := by
  unfold tripleAdmissibleCount
  -- Build equivalence using Chinese Remainder Theorem
  let cred := ZMod.chineseRemainder h
  have equiv : {a : ZMod (m * n) // TripleAdmissible (m * n) a} ≃
      {a : ZMod m // TripleAdmissible m a} × {b : ZMod n // TripleAdmissible n b} := by
    refine Equiv.mk ?toFun ?fromFun ?left_inv ?right_inv
    case toFun =>
      intro x
      have hx := tripleAdmissible_chineseRemainder_iff m n h x.1 |>.mp x.2
      exact Prod.mk (⟨(cred x.1).1, hx.1⟩ : {a : ZMod m // TripleAdmissible m a})
                    (⟨(cred x.1).2, hx.2⟩ : {b : ZMod n // TripleAdmissible n b})
    case fromFun =>
      intro p
      have hx : TripleAdmissible m p.1.1 := p.1.2
      have hy : TripleAdmissible n p.2.1 := p.2.2
      have hcred : cred (cred.symm (p.1.1, p.2.1)) = (p.1.1, p.2.1) := RingEquiv.apply_symm_apply cred (p.1.1, p.2.1)
      refine ⟨cred.symm (p.1.1, p.2.1), by
        rw [tripleAdmissible_chineseRemainder_iff m n h]
        rw [hcred]
        exact ⟨hx, hy⟩⟩
    case left_inv =>
      intro x
      have hcred : cred.symm (cred x.1) = x.1 := RingEquiv.symm_apply_apply cred x.1
      apply Subtype.ext
      simp only
      exact hcred
    case right_inv =>
      intro p
      have hcred : cred (cred.symm (p.1.1, p.2.1)) = (p.1.1, p.2.1) := RingEquiv.apply_symm_apply cred (p.1.1, p.2.1)
      apply Prod.ext <;> apply Subtype.ext <;> simp [hcred]
  rw [Nat.card_congr equiv, Nat.card_prod]

/-- The local count at an odd prime: one choice at 3 and 5, and six
forbidden residue classes at every prime at least 7. -/
