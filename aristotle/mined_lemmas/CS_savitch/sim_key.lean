/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring: Lean 4 requires `import` lines to come
first, so the very first comment of the file cannot be a module docstring.)

This file develops space bounded machines, proves Savitch's theorem
`NSPACE f ⊆ DSPACE (f ^ 2)` and deduces `PSPACE = NPSPACE`.
-/

set_option autoImplicit false

namespace CS

/-! ## Languages -/

/-- A language is a predicate on binary strings. -/
abbrev Language := List Bool → Prop

/-- The bit of `x` at position `i` (`false` beyond the end of `x`). -/

theorem sim_key (hE : ∀ u v, edgeOf edge epos bitf u v → u ≤ N ∧ v ≤ N) :
    ∀ (k u v : ℕ) (rest : List Frame), u ≤ N → v ≤ N →
      ∃ t, (srun N edge epos bitf)^[t] (none, ⟨u, v, k, 0, false⟩ :: rest)
        = (some (decide (Steps (edgeOf edge epos bitf) (2 ^ k) u v)), rest) := by
  have hdec : ∀ (P Q : Prop) (i1 : Decidable P) (i2 : Decidable Q) (rest : List Frame), (P ↔ Q) →
      ((some (@decide P i1), rest) : SState) = (some (@decide Q i2), rest) := by
    intro P Q i1 i2 rest h
    rw [(@decide_eq_decide P Q i1 i2).2 h]
  intro k
  induction k with
  | zero =>
    intro u v rest hu hv
    refine ⟨1, ?_⟩
    rw [Function.iterate_one, srun_none_zero' rfl]
    refine hdec _ _ _ _ _ ?_
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨u, rfl, h⟩
    · rintro (h | ⟨w, hw, hwv⟩)
      · exact Or.inl h
      · exact Or.inr (hw ▸ hwv)
  | succ k ih =>
    have hshift : ∀ (m u v : ℕ),
        ¬ (Steps (edgeOf edge epos bitf) (2 ^ k) u m ∧ Steps (edgeOf edge epos bitf) (2 ^ k) m v) →
        ((∃ w, m + 1 ≤ w ∧ w ≤ N ∧ Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
            Steps (edgeOf edge epos bitf) (2 ^ k) w v) ↔
          (∃ w, m ≤ w ∧ w ≤ N ∧ Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
            Steps (edgeOf edge epos bitf) (2 ^ k) w v)) := by
      intro m u v hbad
      constructor
      · rintro ⟨w, h1, h2, h3, h4⟩
        exact ⟨w, by omega, h2, h3, h4⟩
      · rintro ⟨w, h1, h2, h3, h4⟩
        rcases eq_or_lt_of_le h1 with heq | hlt
        · exact absurd ⟨heq ▸ h3, heq ▸ h4⟩ hbad
        · exact ⟨w, hlt, h2, h3, h4⟩
    have loop : ∀ (d m u v : ℕ) (rest : List Frame), N + 1 ≤ m + d → u ≤ N → v ≤ N →
        ∃ t, (srun N edge epos bitf)^[t] (none, ⟨u, v, k + 1, m, false⟩ :: rest)
          = (some (decide (∃ w, m ≤ w ∧ w ≤ N ∧
              Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
              Steps (edgeOf edge epos bitf) (2 ^ k) w v)), rest) := by
      intro d
      induction d with
      | zero =>
        intro m u v rest hd hu hv
        have hno : ¬ ∃ w, m ≤ w ∧ w ≤ N ∧ Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
            Steps (edgeOf edge epos bitf) (2 ^ k) w v := by
          rintro ⟨w, h1, h2, -, -⟩
          omega
        refine ⟨1, ?_⟩
        rw [Function.iterate_one, decide_eq_false hno]
        exact srun_none_fail' (by show k + 1 ≠ 0; omega) (by show ¬ m ≤ N; omega)
      | succ d ihd =>
        intro m u v rest hd hu hv
        by_cases hm : m ≤ N
        · have e1 : srun N edge epos bitf (none, (⟨u, v, k + 1, m, false⟩ : Frame) :: rest)
              = (none, (⟨u, m, k, 0, false⟩ : Frame) ::
                  (⟨u, v, k + 1, m, false⟩ : Frame) :: rest) :=
            srun_none_push' (by show k + 1 ≠ 0; omega) (show m ≤ N from hm)
          refine srun_trans (srun_step_reach e1) ?_
          refine srun_trans (ih u m ((⟨u, v, k + 1, m, false⟩ : Frame) :: rest) hu hm) ?_
          by_cases hum : Steps (edgeOf edge epos bitf) (2 ^ k) u m
          · rw [decide_eq_true hum]
            have e2 : srun N edge epos bitf
                (some true, (⟨u, v, k + 1, m, false⟩ : Frame) :: rest)
                = (none, (⟨m, v, k, 0, false⟩ : Frame) ::
                    (⟨u, v, k + 1, m, true⟩ : Frame) :: rest) :=
              srun_some_false_true' (by show k + 1 ≠ 0; omega) (by show ¬ N < m; omega) rfl rfl
            refine srun_trans (srun_step_reach e2) ?_
            refine srun_trans (ih m v ((⟨u, v, k + 1, m, true⟩ : Frame) :: rest) hm hv) ?_
            by_cases hmv : Steps (edgeOf edge epos bitf) (2 ^ k) m v
            · rw [decide_eq_true hmv]
              have hP : ∃ w, m ≤ w ∧ w ≤ N ∧ Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
                  Steps (edgeOf edge epos bitf) (2 ^ k) w v := ⟨m, le_rfl, hm, hum, hmv⟩
              rw [decide_eq_true hP]
              refine ⟨1, ?_⟩
              rw [Function.iterate_one]
              exact srun_some_true_true' (by show k + 1 ≠ 0; omega) (by show ¬ N < m; omega)
                rfl rfl
            · rw [decide_eq_false hmv]
              have e3 : srun N edge epos bitf
                  (some false, (⟨u, v, k + 1, m, true⟩ : Frame) :: rest)
                  = (none, (⟨u, v, k + 1, m + 1, false⟩ : Frame) :: rest) :=
                srun_some_true_false' (by show k + 1 ≠ 0; omega) (by show ¬ N < m; omega) rfl rfl
              refine srun_trans (srun_step_reach e3) ?_
              refine srun_trans (ihd (m + 1) u v rest (by omega) hu hv) ?_
              exact ⟨0, hdec _ _ _ _ _ (hshift m u v (fun h => hmv h.2))⟩
          · rw [decide_eq_false hum]
            have e3 : srun N edge epos bitf
                (some false, (⟨u, v, k + 1, m, false⟩ : Frame) :: rest)
                = (none, (⟨u, v, k + 1, m + 1, false⟩ : Frame) :: rest) :=
              srun_some_false_false' (by show k + 1 ≠ 0; omega) (by show ¬ N < m; omega) rfl rfl
            refine srun_trans (srun_step_reach e3) ?_
            refine srun_trans (ihd (m + 1) u v rest (by omega) hu hv) ?_
            exact ⟨0, hdec _ _ _ _ _ (hshift m u v (fun h => hum h.1))⟩
        · have hno : ¬ ∃ w, m ≤ w ∧ w ≤ N ∧ Steps (edgeOf edge epos bitf) (2 ^ k) u w ∧
              Steps (edgeOf edge epos bitf) (2 ^ k) w v := by
            rintro ⟨w, h1, h2, -, -⟩
            omega
          refine ⟨1, ?_⟩
          rw [Function.iterate_one, decide_eq_false hno]
          exact srun_none_fail' (by show k + 1 ≠ 0; omega) (by show ¬ m ≤ N; omega)
    intro u v rest hu hv
    obtain ⟨t, ht⟩ := loop (N + 1) 0 u v rest (by omega) hu hv
    refine ⟨t, ?_⟩
    rw [ht]
    refine hdec _ _ _ _ _ ?_
    constructor
    · rintro ⟨w, -, -, h1, h2⟩
      have : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      rw [this]
      exact Steps_add.2 ⟨w, h1, h2⟩
    · intro h
      have hpow : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      rw [hpow] at h
      obtain ⟨w, h1, h2⟩ := Steps_add.1 h
      have hwN : w ≤ N := Steps_le_of_edge (fun a b hab => (hE a b hab).2) hu h1
      exact ⟨w, Nat.zero_le _, hwN, h1, h2⟩

/-- The simulator, started on the top level call `REACH(u, tgt, K)`, accepts iff `tgt` is
reachable from `u` in at most `2 ^ K` steps. -/
