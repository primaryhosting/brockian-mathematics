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

theorem step_no_fault (p : Policy) (m : Machine) (i : Instr)
    (hi : Instr.allowed p i = true) (hm : m.fault = false) : (step p m i).fault = false := by
  cases i with
  | nop => exact hm
  | read a => simp only [Instr.allowed, decide_eq_true_eq] at hi; simp [step, hi, hm]
  | write a v => simp only [Instr.allowed, decide_eq_true_eq] at hi; simp [step, hi, hm]
  | call c => simp only [Instr.allowed, decide_eq_true_eq] at hi; simp [step, hi, hm]

/-- A certified artifact never traps: a positive verdict on the certificate is a
genuine guarantee about every execution of the app. -/
