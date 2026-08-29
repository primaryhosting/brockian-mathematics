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

theorem Stmt.toNat_injective : Function.Injective Stmt.toNat := by
  intro a
  induction a with
  | skip => intro b h; cases b <;> simp_all [Stmt.toNat, Nat.pair_eq_pair]
  | push r c =>
      intro b h
      cases b <;> simp [Stmt.toNat, Nat.pair_eq_pair] at h
      rename_i r' c'
      obtain ⟨h1, h2⟩ := h
      subst h1
      cases c <;> cases c' <;> simp_all
  | pop r => intro b h; cases b <;> simp_all [Stmt.toNat, Nat.pair_eq_pair]
  | query s r => intro b h; cases b <;> simp_all [Stmt.toNat, Nat.pair_eq_pair]
  | seq p q ihp ihq =>
      intro b h
      cases b <;> simp [Stmt.toNat, Nat.pair_eq_pair] at h
      rw [ihp h.1, ihq h.2]
  | ite r p q ihp ihq =>
      intro b h
      cases b <;> simp [Stmt.toNat, Nat.pair_eq_pair] at h
      rw [h.1, ihp h.2.1, ihq h.2.2]
  | wh r p ihp =>
      intro b h
      cases b <;> simp [Stmt.toNat, Nat.pair_eq_pair] at h
      rw [h.1, ihp h.2]
  | padAux m r => intro b h; cases b <;> simp_all [Stmt.toNat, Nat.pair_eq_pair]
  | pad k s r => intro b h; cases b <;> simp_all [Stmt.toNat, Nat.pair_eq_pair]

instance : Countable Stmt := Stmt.toNat_injective.countable

instance : Nonempty Stmt := ⟨.skip⟩

/-- An enumeration of all pairs (machine, exponent). -/
