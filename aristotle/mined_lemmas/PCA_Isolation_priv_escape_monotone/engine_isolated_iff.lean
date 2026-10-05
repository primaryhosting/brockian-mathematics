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

theorem engine_isolated_iff [Fintype P] (pol : FinPolicy P) (S T : Finset P) :
    engineEscape pol S ∩ T = ∅ ↔ Isolated pol.toPolicy (S : Set P) (T : Set P) := by
  rw [Isolated, ← engineEscape_eq]
  constructor
  · intro h
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro q ⟨hq, hqT⟩
    have hmem : q ∈ engineEscape pol S ∩ T :=
      Finset.mem_inter.mpr ⟨by exact_mod_cast hq, by exact_mod_cast hqT⟩
    rw [h] at hmem
    exact Finset.notMem_empty q hmem
  · intro h
    refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro q hq
    rw [Finset.mem_inter] at hq
    have hmem : q ∈ (engineEscape pol S : Set P) ∩ (T : Set P) :=
      ⟨by exact_mod_cast hq.1, by exact_mod_cast hq.2⟩
    rw [h] at hmem
    exact hmem

/-- Monotonicity of the engine, matching `priv_escape_monotone`. -/
