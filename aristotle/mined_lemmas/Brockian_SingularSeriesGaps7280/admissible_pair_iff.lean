/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- `IsPrime p` : `p` is at least `2` and has no divisor `d` with `2 ≤ d < p`. -/

theorem admissible_pair_iff (g : Nat) : Admissible [0, (g : Int)] ↔ g % 2 = 0 := by
  constructor
  · intro h
    obtain ⟨r, hr0, hr2, hres⟩ := h 2 isPrime_two
    have h0 : (0 : Int) % 2 ≠ r := hres 0 (by simp)
    have hg : (g : Int) % 2 ≠ r := hres (g : Int) (by simp)
    omega
  · intro hg p hp
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨1, by omega, by omega, ?_⟩
      intro h hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl
      · omega
      · omega
    · have hp3 : 3 ≤ p := by have := hp.1; omega
      have hpz : (3 : Int) ≤ (p : Int) := by exact_mod_cast hp3
      rcases pick_of_one ((g : Int) % (p : Int)) with h1 | h2
      · refine ⟨1, by omega, by omega, ?_⟩
        intro h hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl | rfl
        · simp
        · exact fun hc => h1 hc.symm
      · refine ⟨2, by omega, by omega, ?_⟩
        intro h hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl | rfl
        · simp
        · exact fun hc => h2 hc.symm

/-- **Triple criterion.** The gap tuple `{0, a, b}` is admissible exactly when `a` and `b`
are both even and the three entries do not cover all residues modulo `3`. -/
