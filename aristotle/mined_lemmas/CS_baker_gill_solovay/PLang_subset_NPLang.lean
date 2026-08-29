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

theorem PLang_subset_NPLang (O : Oracle) : PLang O ⊆ NPLang O := by
  rintro L ⟨M, k, hH, hMk⟩
  refine ⟨ignoreWitness M, k + 2, fun x => ?_⟩
  have h1 : 1 ≤ (x.length + 2) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : (x.length + 2) ^ k * 4 ≤ (x.length + 2) ^ (k + 2) := by
    rw [show k + 2 = k + 2 from rfl, pow_add]
    exact Nat.mul_le_mul_left _ (by
      have : (x.length + 2) ^ 2 = (x.length + 2) * (x.length + 2) := by ring
      nlinarith)
  have hTB : (x.length + 2) ^ k + 2 ≤ (x.length + 2) ^ (k + 2) := by omega
  constructor
  · intro hx
    refine ⟨[], by simp, ?_⟩
    have hacc : AcceptsIn O M x [] ((x.length + 2) ^ (k + 2) - 2) :=
      ((hMk x).1 hx).mono (by omega)
    have hiw := (ignoreWitness_accepts_iff O M x [] ((x.length + 2) ^ (k + 2) - 2)).2 hacc
    have heq : (x.length + 2) ^ (k + 2) - 2 + (2 * ([] : Str).length + 2)
        = (x.length + 2) ^ (k + 2) := by simp; omega
    rwa [heq] at hiw
  · rintro ⟨w, _, hacc⟩
    have h3 := AcceptsIn_ignoreWitness_imp O M x w _ hacc
    exact (hMk x).2 (AcceptsIn_of_halts (hH x) (by omega) h3)

end CS

/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Machines

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-! ## Polynomials are eventually dominated by `2 ^ n` -/

