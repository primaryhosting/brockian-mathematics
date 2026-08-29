import Mathlib

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
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module doc-comment, so the header
-- above is repeated as the module documentation just after the import.)
import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Phys

/-! ## Shannon entropy of a finite distribution (in nats) -/

/-- Shannon entropy (in nats) of a distribution `p` on a finite type,
using the standard convention `0 * log 0 = 0`. -/

lemma entropy_eq_zero_of_deterministic {S : Type*} [Fintype S] [DecidableEq S] (p : S → ℝ)
    (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {t : S} (ht : p t = 1) :
    entropy p = 0 := by
  have hzero : ∀ s, s ≠ t → p s = 0 := by
    have hsplit : ∑ s ∈ Finset.univ.erase t, p s = 0 := by
      have hadd := Finset.add_sum_erase Finset.univ p (Finset.mem_univ t)
      rw [ht] at hadd
      linarith [hp1, hadd]
    intro s hst
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp0 x)).1 hsplit s
      (Finset.mem_erase.2 ⟨hst, Finset.mem_univ s⟩)
  rw [entropy]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  by_cases hst : s = t
  · rw [hst, ht]; simp [Real.negMulLog]
  · rw [hzero s hst]; simp

/-! ## The general Landauer bound -/

/-- **Landauer's bound.**  A memory `S` with state distribution `pS` is coupled to a reservoir
`R` in the Gibbs state at inverse temperature `β`, so that the initial joint distribution is the
product `pS ⊗ gibbs β E`.  The composite system evolves to a joint distribution `q` whose Shannon
entropy is at least that of the initial state (the second law for a closed system; an invertible
Hamiltonian evolution even preserves the entropy, cf. `entropy_comp_equiv`, and any bistochastic
evolution can only increase it).  Writing `qS` for the final memory marginal, the entropy lost by
the memory is then at most `β` times the heat delivered to the reservoir. -/
