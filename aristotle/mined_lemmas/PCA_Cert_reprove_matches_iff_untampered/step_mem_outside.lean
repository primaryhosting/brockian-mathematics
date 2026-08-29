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

theorem step_mem_outside (p : Policy) (m : Machine) (i : Instr) (x : Nat)
    (hx : p.maxAddr ≤ x) : (step p m i).mem x = m.mem x := by
  cases i with
  | nop => rfl
  | read a => by_cases h : a < p.maxAddr <;> simp [step, h]
  | write a v =>
      by_cases h : a < p.maxAddr <;> simp [step, h, setMem] <;> omega
  | call c => by_cases h : c ∈ p.caps <;> simp [step, h]

/-- Memory outside the policy window is never modified, whatever the app does. -/
