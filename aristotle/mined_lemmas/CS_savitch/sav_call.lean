/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ## Machine model

We work with a *non-uniform* space-bounded machine model.  A machine works on inputs of one
fixed length; a language belongs to a space class if for every input length there is a machine
of the appropriate size deciding the language on inputs of that length.

A machine is described by its set of configurations `Cfg` (which is the whole memory of the
machine: the space used is `log₂ (card Cfg)`), a designated start configuration, a function
`head` telling which position of the (read-only) input is currently scanned, and a transition
which may depend on the current configuration and on the single input bit that is being read.
Note that the machine has *no* other access to the input, which is what makes the space measure
meaningful. -/

/-- The `i`-th bit of an input word; `false` beyond the end of the word. -/

lemma sav_call (k : ℕ) : ∀ (a b : Option M.Cfg) (rest : List (Frame M)) (c : SavCfg M d),
    c.1.val = ((a, b, 0, 0) : Frame M) :: rest → d + 1 - (rest.length + 1) = k →
    ∃ t, valOf (((savDSM M d).trans x)^[t] c) = (rest, RkB (M.E' x) k a b) := by
  induction k with
  | zero =>
      intro a b rest c hc hk
      refine ⟨1, ?_⟩
      have h := step_pop0 x c a b 0 0 rest hc hk
      simpa [Function.iterate_one, RkB, NSM.E'] using h
  | succ k ih =>
      have loop : ∀ (j : ℕ) (a b : Option M.Cfg) (i : Fin (NN M + 1)) (rest : List (Frame M))
          (c : SavCfg M d), c.1.val = ((a, b, i, 0) : Frame M) :: rest →
          d + 1 - (rest.length + 1) = k + 1 → NN M - (i : ℕ) ≤ j →
          ∃ t, (valOf (((savDSM M d).trans x)^[t] c)).1 = rest ∧
            ((valOf (((savDSM M d).trans x)^[t] c)).2 = true ↔
              ∃ z, (i : ℕ) ≤ z ∧ z < NN M ∧ RkB (M.E' x) k a (cand M z) = true ∧
                RkB (M.E' x) k (cand M z) b = true) := by
        intro j
        induction j with
        | zero =>
            intro a b i rest c hc hk hj
            refine ⟨1, ?_⟩
            have h := step_exhaust x c a b i rest hc (by omega) (by omega)
            rw [Function.iterate_one, h]
            refine ⟨rfl, ?_⟩
            simp only [Bool.false_eq_true, false_iff, not_exists]
            rintro z ⟨hz1, hz2, -, -⟩
            omega
        | succ j ihj =>
            intro a b i rest c hc hk hj
            by_cases hi : (i : ℕ) < NN M
            · -- start the recursive calls for the candidate midpoint `cand M i`
              have hlen2 : rest.length + 2 ≤ d + 1 := by omega
              set f := (savDSM M d).trans x with hf
              have h1 := step_push0 x c a b i rest hc hlen2 hi
              rw [← hf] at h1
              obtain ⟨t2, ht2⟩ := ih a (cand M (i : ℕ)) (((a, b, i, 1) : Frame M) :: rest) (f c)
                (valOf_fst h1) (by simp only [List.length_cons]; omega)
              by_cases hv1 : RkB (M.E' x) k a (cand M (i : ℕ)) = true
              · have h3 := step_ph1_true x (f^[t2] (f c)) a b i rest (valOf_fst ht2) hlen2
                  (by rw [valOf_snd ht2]; exact hv1)
                rw [← hf] at h3
                obtain ⟨t4, ht4⟩ := ih (cand M (i : ℕ)) b (((a, b, i, 2) : Frame M) :: rest)
                  (f (f^[t2] (f c))) (valOf_fst h3) (by simp only [List.length_cons]; omega)
                by_cases hv2 : RkB (M.E' x) k (cand M (i : ℕ)) b = true
                · have h5 := step_ph2_true x (f^[t4] (f (f^[t2] (f c)))) a b i rest
                    (valOf_fst ht4) (by omega) (by rw [valOf_snd ht4]; exact hv2)
                  rw [← hf] at h5
                  refine ⟨1 + (t4 + (1 + (t2 + 1))), ?_⟩
                  rw [Function.iterate_add_apply f 1, Function.iterate_add_apply f t4,
                    Function.iterate_add_apply f 1, Function.iterate_add_apply f t2 1]
                  simp only [Function.iterate_one]
                  rw [h5]
                  exact ⟨rfl, iff_of_true rfl ⟨(i : ℕ), le_rfl, hi, hv1, hv2⟩⟩
                · have hv2' : RkB (M.E' x) k (cand M (i : ℕ)) b = false := by simpa using hv2
                  have h5 := step_ph2_false x (f^[t4] (f (f^[t2] (f c)))) a b i rest
                    (valOf_fst ht4) (by omega) (by rw [valOf_snd ht4]; exact hv2')
                  rw [← hf] at h5
                  obtain ⟨t6, ht6⟩ := ihj a b (incF M i) rest (f (f^[t4] (f (f^[t2] (f c)))))
                    (valOf_fst h5) hk (by rw [incF_val hi]; omega)
                  refine ⟨t6 + (1 + (t4 + (1 + (t2 + 1)))), ?_⟩
                  rw [Function.iterate_add_apply f t6, Function.iterate_add_apply f 1,
                    Function.iterate_add_apply f t4, Function.iterate_add_apply f 1,
                    Function.iterate_add_apply f t2 1]
                  simp only [Function.iterate_one]
                  refine ⟨ht6.1, ?_⟩
                  rw [ht6.2, incF_val hi]
                  constructor
                  · rintro ⟨z, hz1, hz2, hz3, hz4⟩
                    exact ⟨z, by omega, hz2, hz3, hz4⟩
                  · rintro ⟨z, hz1, hz2, hz3, hz4⟩
                    rcases Nat.eq_or_lt_of_le hz1 with h | h
                    · rw [← h] at hz4; rw [hv2'] at hz4; exact absurd hz4 (by simp)
                    · exact ⟨z, by omega, hz2, hz3, hz4⟩
              · have hv1' : RkB (M.E' x) k a (cand M (i : ℕ)) = false := by simpa using hv1
                have h3 := step_ph1_false x (f^[t2] (f c)) a b i rest (valOf_fst ht2) (by omega)
                  (by rw [valOf_snd ht2]; exact hv1')
                rw [← hf] at h3
                obtain ⟨t4, ht4⟩ := ihj a b (incF M i) rest (f (f^[t2] (f c)))
                  (valOf_fst h3) hk (by rw [incF_val hi]; omega)
                refine ⟨t4 + (1 + (t2 + 1)), ?_⟩
                rw [Function.iterate_add_apply f t4, Function.iterate_add_apply f 1,
                  Function.iterate_add_apply f t2 1]
                simp only [Function.iterate_one]
                refine ⟨ht4.1, ?_⟩
                rw [ht4.2, incF_val hi]
                constructor
                · rintro ⟨z, hz1, hz2, hz3, hz4⟩
                  exact ⟨z, by omega, hz2, hz3, hz4⟩
                · rintro ⟨z, hz1, hz2, hz3, hz4⟩
                  rcases Nat.eq_or_lt_of_le hz1 with h | h
                  · rw [← h] at hz3; rw [hv1'] at hz3; exact absurd hz3 (by simp)
                  · exact ⟨z, by omega, hz2, hz3, hz4⟩
            · refine ⟨1, ?_⟩
              have h := step_exhaust x c a b i rest hc (by omega) hi
              rw [Function.iterate_one, h]
              refine ⟨rfl, ?_⟩
              simp only [Bool.false_eq_true, false_iff, not_exists]
              rintro z ⟨hz1, hz2, -, -⟩
              omega
      intro a b rest c hc hk
      obtain ⟨t, ht1, ht2⟩ := loop (NN M) a b 0 rest c hc hk (by simp)
      refine ⟨t, ?_⟩
      refine Prod.ext ht1 (bool_eq_of_iff ?_)
      rw [ht2]
      constructor
      · rintro ⟨z, -, -, hz3, hz4⟩
        simpa [RkB] using ⟨cand M z, hz3, hz4⟩
      · intro h
        simp only [RkB, decide_eq_true_eq] at h
        obtain ⟨m, hm1, hm2⟩ := h
        obtain ⟨z, hz, hzm⟩ := cand_surj M m
        exact ⟨z, by simp, hz, by rw [hzm]; exact hm1, by rw [hzm]; exact hm2⟩

end SavitchCorrect

end CS

namespace CS

section SavitchMain

/-- The Savitch machine halts with the value of the middle-first predicate at depth `d`. -/
