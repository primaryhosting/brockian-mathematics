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

lemma entropy_two_point {S : Type*} [Fintype S] [DecidableEq S] {s₀ s₁ : S} (hs : s₀ ≠ s₁)
    (p : S → ℝ) (hp : ∀ s, p s = if s = s₀ ∨ s = s₁ then 1 / 2 else 0) :
    entropy p = Real.log 2 := by
  have h : ∀ s : S, Real.negMulLog (p s)
      = if s ∈ ({s₀, s₁} : Finset S) then Real.negMulLog (1 / 2) else 0 := by
    intro s
    rw [hp s]
    by_cases hmem : s = s₀ ∨ s = s₁ <;> simp [hmem, Finset.mem_insert]
  rw [entropy, Finset.sum_congr rfl (fun s _ => h s), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, Finset.card_pair hs, Real.negMulLog,
    show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
  ring

/-- A two-state distribution `(1/2, 1/2)` is normalised. -/
