/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Model

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-! ## A calculus for reasoning about program execution -/

/-- `Exec O S n f` says: started with registers `σ`, the statement `S` terminates
after exactly `n σ` steps, leaving the registers in state `f σ` (and the rest of
the control stack untouched). -/

theorem diagLang_mem_NP (O : Oracle) : diagLang O ∈ NPLang O := by
  refine ⟨verifier, 3, fun x => ?_⟩
  have hT : 7 * x.length + 3 ≤ (x.length + 2) ^ 3 := by
    have h : (x.length + 2) ^ 3 = x.length ^ 3 + 6 * x.length ^ 2 + 12 * x.length + 8 := by ring
    omega
  have hlen : x.length ≤ (x.length + 2) ^ 3 :=
    le_trans (by omega) (Nat.le_self_pow (by norm_num) (x.length + 2))
  constructor
  · rintro ⟨z, hz, hOz⟩
    refine ⟨z.reverse, by simpa [hz] using hlen, ?_⟩
    rw [verifier_accepts O x z.reverse hT]
    have : padTake x.length z.reverse = z.reverse := by
      rw [show x.length = z.reverse.length from by simp [hz]]
      exact padTake_self _
    rw [this]
    simpa using hOz
  · rintro ⟨w, _, hacc⟩
    rw [verifier_accepts O x w hT] at hacc
    exact ⟨(padTake x.length w).reverse, by simp [padTake_length], hacc⟩

/-! ## The diagonal language for `B` is not in `P^B` -/

