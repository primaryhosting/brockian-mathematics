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

theorem run_trace_allowed (a : Artifact) (m : Machine) (c : Nat)
    (hc : c ∈ (run a m).trace) : c ∈ a.policy.caps ∨ c ∈ m.trace := by
  unfold run at hc
  generalize a.code = l at hc
  induction l generalizing m with
  | nil => exact Or.inr hc
  | cons i is ih =>
      rw [List.foldl_cons] at hc
      rcases ih (step a.policy m i) hc with h | h
      · exact Or.inl h
      · cases i with
        | nop => exact Or.inr h
        | read x => by_cases hx : x < a.policy.maxAddr <;> simp [step, hx] at h <;> exact Or.inr h
        | write x v =>
            by_cases hx : x < a.policy.maxAddr <;> simp [step, hx] at h <;> exact Or.inr h
        | call x =>
            by_cases hx : x ∈ a.policy.caps
            · simp only [step, hx, if_pos, if_true, List.mem_cons] at h
              rcases h with h | h
              · exact Or.inl (h ▸ hx)
              · exact Or.inr h
            · simp [step, hx] at h
              exact Or.inr h

