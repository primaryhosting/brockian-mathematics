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

theorem card_iter_ge (pol : FinPolicy P) (S : Finset P) (n : ℕ)
    (h : ∀ k < n, iter pol S (k + 1) ≠ iter pol S k) :
    n ≤ (iter pol S n).card := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ (iter pol S k).card := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hne : iter pol S (k + 1) ≠ iter pol S k := h k (Nat.lt_succ_self k)
    have hsub : iter pol S k ⊆ iter pol S (k + 1) := iter_subset_succ pol S k
    have hssub : iter pol S k ⊂ iter pol S (k + 1) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun hcontra => hne hcontra.symm⟩
    have hcard := Finset.card_lt_card hssub
    omega

/-- Saturation is complete after `Fintype.card P + 1` rounds. -/
