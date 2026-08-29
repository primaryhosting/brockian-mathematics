/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Cert

/-! ## Arithmetic: an injective pairing function on `Nat` -/

/-- Szudzik-style pairing function. -/

theorem Instr.enc_injective : Function.Injective Instr.enc := by
  intro i j h
  cases i with
  | nop =>
      cases j with
      | nop => rfl
      | read a => simp only [Instr.enc] at h; omega
      | write a v => simp only [Instr.enc] at h; omega
      | call c => simp only [Instr.enc] at h; omega
  | read x =>
      cases j with
      | nop => simp only [Instr.enc] at h; omega
      | read a => simp only [Instr.enc] at h; rw [show x = a by omega]
      | write a v => simp only [Instr.enc] at h; omega
      | call c => simp only [Instr.enc] at h; omega
  | write x y =>
      cases j with
      | nop => simp only [Instr.enc] at h; omega
      | read a => simp only [Instr.enc] at h; omega
      | write a v =>
          simp only [Instr.enc] at h
          obtain ⟨h1, h2⟩ := pairNat_inj (show pairNat x y = pairNat a v by omega)
          rw [h1, h2]
      | call c => simp only [Instr.enc] at h; omega
  | call z =>
      cases j with
      | nop => simp only [Instr.enc] at h; omega
      | read a => simp only [Instr.enc] at h; omega
      | write a v => simp only [Instr.enc] at h; omega
      | call c => simp only [Instr.enc] at h; rw [show z = c by omega]

/-- Injective encoding of a policy. -/
