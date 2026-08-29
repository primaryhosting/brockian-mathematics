import Mathlib

/-- Landau's problem: there are infinitely many `n` with `n ^ 2 + 1` prime. -/

theorem landau_iff_even_infinite :
    LandauNSqPlusOne ↔ {n : ℕ | Even n ∧ (n ^ 2 + 1).Prime}.Infinite := by
  constructor
  · intro h
    have hsub : {n : ℕ | (n ^ 2 + 1).Prime} ⊆
        {n : ℕ | Even n ∧ (n ^ 2 + 1).Prime} ∪ {1} := by
      intro n hn
      simp only [Set.mem_setOf_eq] at hn
      rcases Nat.even_or_odd n with he | ho
      · exact Or.inl ⟨he, hn⟩
      · right
        obtain ⟨k, hk⟩ := ho
        have h2 : (2 : ℕ) ∣ n ^ 2 + 1 := ⟨2 * k ^ 2 + 2 * k + 1, by subst hk; ring⟩
        have h3 : n ^ 2 + 1 = 2 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hn).mp h2).symm
        have : n = 1 := by nlinarith
        simpa using this
    have hu : ({n : ℕ | Even n ∧ (n ^ 2 + 1).Prime} ∪ {1}).Infinite := h.mono hsub
    by_contra hfin
    exact hu (Set.not_infinite.mp hfin |>.union (Set.finite_singleton 1))
  · intro h
    exact h.mono (fun n hn => hn.2)

