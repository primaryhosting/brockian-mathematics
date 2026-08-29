import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix Kronecker

namespace Frontier

variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n]

/-- The reduced state ("partial trace") of a bipartite density matrix on the `m`-factor
(Alice's system), obtained by tracing out the `n`-factor (Bob's system). -/

private lemma sum_reorder (T : n → ι → n → n → ℂ) :
    ∑ k, ∑ a, ∑ b, ∑ d, T k a b d = ∑ b, ∑ d, ∑ a, ∑ k, T k a b d := by
  rw [show (∑ k, ∑ a, ∑ b, ∑ d, T k a b d)
        = ∑ p : n × ι × n × n, T p.1 p.2.1 p.2.2.1 p.2.2.2 from by simp [Fintype.sum_prod_type],
      show (∑ b, ∑ d, ∑ a, ∑ k, T k a b d)
        = ∑ q : n × n × ι × n, T q.2.2.2 q.2.2.1 q.1 q.2.1 from by simp [Fintype.sum_prod_type]]
  exact Fintype.sum_equiv
    ⟨fun p => (p.2.2.1, p.2.2.2, p.2.1, p.1), fun q => (q.2.2.2, q.2.2.1, q.1, q.2.1),
      by rintro ⟨k, a, b, d⟩; rfl, by rintro ⟨b, d, a, k⟩; rfl⟩ _ _ (fun _ => rfl)

omit [DecidableEq n] in
/-- Entrywise form of a local operation conjugating a bipartite matrix. -/
