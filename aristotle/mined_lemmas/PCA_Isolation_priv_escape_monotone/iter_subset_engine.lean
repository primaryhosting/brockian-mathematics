import PCA.Isolation

/-
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Isolation

/-! ## The abstract isolation model

A *privilege policy* on a type of privileges `P` is a relation `grants`, where
`grants a b` means "a principal holding privilege `a` may directly acquire
privilege `b`".  Privilege *escalation* is the reflexive–transitive closure of
this relation, and the *escape set* of a set `S` of initially held privileges is
the set of privileges reachable by escalation from `S`. -/

/-- A privilege policy: `grants a b` means privilege `a` directly confers `b`. -/
structure Policy (P : Type*) where
  /-- The direct-grant relation of the policy. -/
  grants : P → P → Prop

variable {P : Type*}

/-- `Escalates pol a b` : privilege `b` is reachable from privilege `a` by a
finite chain of direct grants of the policy `pol`. -/

theorem iter_subset_engine [Fintype P] (pol : FinPolicy P) (S : Finset P) (n : ℕ) :
    iter pol S n ⊆ engineEscape pol S := by
  by_cases hstall : ∀ k < Fintype.card P + 1, iter pol S (k + 1) ≠ iter pol S k
  · exfalso
    have h1 : Fintype.card P + 1 ≤ (iter pol S (Fintype.card P + 1)).card :=
      card_iter_ge pol S _ hstall
    have h2 : (iter pol S (Fintype.card P + 1)).card ≤ Fintype.card P :=
      Finset.card_le_univ _
    omega
  · push_neg at hstall
    obtain ⟨k, hkN, hk⟩ := hstall
    have hstab := iter_stabilizes pol S hk
    have hNk : iter pol S (Fintype.card P + 1) = iter pol S k := hstab _ (Nat.le_of_lt hkN)
    rcases Nat.lt_or_ge n k with hn | hn
    · rw [engineEscape, hNk]
      exact iter_mono pol S (Nat.le_of_lt hn)
    · rw [engineEscape, hNk, hstab n hn]

/-- **Soundness and completeness of the isolation engine.**  The computed escape
set is exactly the set of privileges reachable by escalation. -/
