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
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d < p → 2 ≤ d → ¬ (d ∣ p)

instance (p : Nat) : Decidable (IsPrime p) := by
  unfold IsPrime; infer_instance

/-- A finite tuple of integers `H` is *admissible* when for every prime `p` it omits at
least one residue class modulo `p`; equivalently, every local factor
`(1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` of the Hardy–Littlewood singular series is nonzero, so
that the singular series itself does not vanish. -/
def Admissible (H : List Int) : Prop :=
  ∀ p : Nat, IsPrime p → ∃ r : Int, 0 ≤ r ∧ r < (p : Int) ∧ ∀ h ∈ H, h % (p : Int) ≠ r

/-- Two candidate residues suffice to avoid one forbidden value. -/
theorem pick_of_one (A : Int) : (1 : Int) ≠ A ∨ (2 : Int) ≠ A := by omega

/-- Three candidate residues suffice to avoid two forbidden values. -/
theorem pick_of_two (A B : Int) :
    ((1 : Int) ≠ A ∧ (1 : Int) ≠ B) ∨ ((2 : Int) ≠ A ∧ (2 : Int) ≠ B) ∨
      ((3 : Int) ≠ A ∧ (3 : Int) ≠ B) := by omega

theorem isPrime_two : IsPrime 2 := by decide

theorem isPrime_three : IsPrime 3 := by decide

/-- A prime other than `2` and `3` is at least `5`. -/
theorem five_le_of_isPrime {p : Nat} (hp : IsPrime p) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  rcases hp with ⟨hp2, hdvd⟩
  if h : 5 ≤ p then
    exact h
  else
    have hp4 : p = 4 := by omega
    exact absurd (show (2 : Nat) ∣ p by omega) (hdvd 2 (by omega) (by omega))

/-- **Pair criterion.** The gap tuple `{0, g}` is admissible exactly when `g` is even. -/
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
theorem length_filter_even_range' (m : Nat) :
    ∀ n : Nat, ((List.range' n (2 * m)).filter (fun g => g % 2 == 0)).length = m := by
  induction m with
  | zero => intro n; simp
  | succ m ih =>
      intro n
      have hstep : 2 * (m + 1) = (2 * m) + 1 + 1 := by omega
      rw [hstep, List.range'_succ, List.range'_succ, List.filter_cons, List.filter_cons]
      have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hn with h | h
      · have h1 : ((n + 1) % 2 == 0) = false := by simp; omega
        have h2 : (n % 2 == 0) = true := by simp [h]
        rw [h1, h2]
        simpa using ih (n + 1 + 1)
      · have h1 : ((n + 1) % 2 == 0) = true := by simp; omega
        have h2 : (n % 2 == 0) = false := by simp; omega
        rw [h1, h2]
        simpa using ih (n + 1 + 1)

/-- **Singular Series Gaps 7280.**

A package of admissibility results for gap tuples, and the resulting count of admissible
gaps in every window of length `7280`:

* the pair `{0, g}` is admissible exactly when the gap `g` is even;
* the triple `{0, a, b}` is admissible exactly when `a, b` are even and `0, a, b` fail to
  cover all residues modulo `3`;
* every window `[n, n + 7280)` of gap values contains exactly `3640` admissible gaps,
  the members of the window that are picked out being precisely the admissible ones.
-/
theorem SingularSeriesGaps7280 :
    (∀ g : Nat, Admissible [0, (g : Int)] ↔ g % 2 = 0) ∧
    (∀ a b : Int, Admissible [0, a, b] ↔
      ((a % 2 = 0 ∧ b % 2 = 0) ∧ (a % 3 = 0 ∨ b % 3 = 0 ∨ a % 3 = b % 3))) ∧
    (∀ n : Nat, ((List.range' n 7280).filter (fun g => g % 2 == 0)).length = 3640) ∧
    (∀ n g : Nat, g ∈ (List.range' n 7280).filter (fun g => g % 2 == 0) ↔
      (g ∈ List.range' n 7280 ∧ Admissible [0, (g : Int)])) := by
  refine ⟨admissible_pair_iff, admissible_triple_iff, ?_, ?_⟩
  · intro n
    have h : (7280 : Nat) = 2 * 3640 := by omega
    rw [h]
    exact length_filter_even_range' 3640 n
  · intro n g
    rw [List.mem_filter]
    constructor
    · rintro ⟨hmem, hpar⟩
      exact ⟨hmem, (admissible_pair_iff g).mpr (by simpa using hpar)⟩
    · rintro ⟨hmem, hadm⟩
      exact ⟨hmem, by simpa using (admissible_pair_iff g).mp hadm⟩

end Brockian

