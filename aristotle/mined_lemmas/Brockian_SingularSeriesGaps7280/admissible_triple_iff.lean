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

theorem admissible_triple_iff (a b : Int) :
    Admissible [0, a, b] ↔
      ((a % 2 = 0 ∧ b % 2 = 0) ∧ (a % 3 = 0 ∨ b % 3 = 0 ∨ a % 3 = b % 3)) := by
  constructor
  · intro h
    obtain ⟨r, hr0, hr2, hres⟩ := h 2 isPrime_two
    have e0 : (0 : Int) % 2 ≠ r := hres 0 (by simp)
    have ea : a % 2 ≠ r := hres a (by simp)
    have eb : b % 2 ≠ r := hres b (by simp)
    obtain ⟨s, hs0, hs3, hres3⟩ := h 3 isPrime_three
    have f0 : (0 : Int) % 3 ≠ s := hres3 0 (by simp)
    have fa : a % 3 ≠ s := hres3 a (by simp)
    have fb : b % 3 ≠ s := hres3 b (by simp)
    refine ⟨⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨⟨ha2, hb2⟩, h3⟩ p hp
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨1, by omega, by omega, ?_⟩
      intro h hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl <;> omega
    · by_cases hp3 : p = 3
      · subst hp3
        rcases (by omega : ((1 : Int) ≠ a % 3 ∧ (1 : Int) ≠ b % 3) ∨
            ((2 : Int) ≠ a % 3 ∧ (2 : Int) ≠ b % 3)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine ⟨1, by omega, by omega, ?_⟩
          intro h hh
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          rcases hh with rfl | rfl | rfl
          · simp
          · exact fun hc => h1 hc.symm
          · exact fun hc => h2 hc.symm
        · refine ⟨2, by omega, by omega, ?_⟩
          intro h hh
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          rcases hh with rfl | rfl | rfl
          · simp
          · exact fun hc => h1 hc.symm
          · exact fun hc => h2 hc.symm
      · have hp5 : 5 ≤ p := five_le_of_isPrime hp hp2 hp3
        have hpz : (5 : Int) ≤ (p : Int) := by exact_mod_cast hp5
        rcases pick_of_two (a % (p : Int)) (b % (p : Int)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine ⟨1, by omega, by omega, ?_⟩
          intro h hh
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          rcases hh with rfl | rfl | rfl
          · simp
          · exact fun hc => h1 hc.symm
          · exact fun hc => h2 hc.symm
        · refine ⟨2, by omega, by omega, ?_⟩
          intro h hh
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          rcases hh with rfl | rfl | rfl
          · simp
          · exact fun hc => h1 hc.symm
          · exact fun hc => h2 hc.symm
        · refine ⟨3, by omega, by omega, ?_⟩
          intro h hh
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          rcases hh with rfl | rfl | rfl
          · simp
          · exact fun hc => h1 hc.symm
          · exact fun hc => h2 hc.symm

/-- Exactly `m` of any `2 * m` consecutive natural numbers are even. -/
