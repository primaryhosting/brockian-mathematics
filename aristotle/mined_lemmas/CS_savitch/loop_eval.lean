/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede every declaration, including module
docstrings, so the header above is a plain block comment.)
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk
import RequestProject.Savitch.Sim
import RequestProject.Savitch.Semantics
import RequestProject.Savitch.Space

/-!
The space-bounded machine model, the classes `CS.NSPACE`, `CS.DSPACE`,
`CS.PSPACE` and `CS.NPSPACE`, and the simulator used in the proof are defined in
the files `RequestProject/Savitch/*.lean`.

A machine reads its input through a head whose position is determined by its
memory value, and it works in space `g` if on inputs of length `n` all reachable
memory values lie in a set of at most `2 ^ g n` values depending only on `n`
(the standard correspondence between `s` tape cells and `2 ^ O(s)`
configurations).  The classes `NSPACE g` and `DSPACE g` are closed under
constant factors by definition, as usual for space classes.

Savitch's theorem is proved for space bounds `f` with `n + 1 ≤ 2 ^ f n`
(i.e. `f n ≥ log₂ (n+1)`), the standard hypothesis `f (n) ≥ log n`.
-/

namespace CS

/-- **Savitch's theorem**: a language recognized by a nondeterministic machine in
space `f` (with `f n ≥ log₂ (n + 1)`) is recognized by a deterministic machine in
space `O(f²)`, i.e. `NSPACE f ⊆ DSPACE (f²)`. -/

theorem loop_eval {n k : ℕ}
    (ih : ∀ (todo : List N.Mem) (a b : N.Mem) (st : List (Frame N.Mem)),
      SReach N S g x (.call n todo a b k st) (.ret n todo (decide (CY N S x n k a b)) st)) :
    ∀ (ms : List N.Mem) (todo : List N.Mem) (a b m : N.Mem) (st : List (Frame N.Mem)),
      SReach N S g x (.call n todo a m k (⟨a, b, k, m, ms, false⟩ :: st))
        (.ret n todo (decide (∃ mm ∈ m :: ms, CY N S x n k a mm ∧ CY N S x n k mm b)) st) := by
  intro ms
  induction ms with
  | nil =>
    intro todo a b m st
    by_cases hP : CY N S x n k a m
    · have s1 : SReach N S g x (.call n todo a m k (⟨a, b, k, m, [], false⟩ :: st))
          (.ret n todo true (⟨a, b, k, m, [], false⟩ :: st)) := by
        have h := ih todo a m (⟨a, b, k, m, [], false⟩ :: st)
        rwa [decide_eq_true hP] at h
      have s2 : SReach N S g x (.ret n todo true ((⟨a, b, k, m, [], false⟩ : Frame N.Mem) :: st))
          (.call n todo m b k (⟨a, b, k, m, [], true⟩ :: st)) :=
        SReach.one' (dstep_ret_true_first rfl)
      by_cases hQ : CY N S x n k m b
      · have s3 : SReach N S g x (.call n todo m b k (⟨a, b, k, m, [], true⟩ :: st))
            (.ret n todo true (⟨a, b, k, m, [], true⟩ :: st)) := by
          have h := ih todo m b (⟨a, b, k, m, [], true⟩ :: st)
          rwa [decide_eq_true hQ] at h
        have s4 : SReach N S g x (.ret n todo true ((⟨a, b, k, m, [], true⟩ : Frame N.Mem) :: st))
            (.ret n todo true st) := SReach.one' (dstep_ret_true_second rfl)
        have hval : (decide (∃ mm ∈ [m], CY N S x n k a mm ∧ CY N S x n k mm b)) = true :=
          decide_eq_true ⟨m, by simp, hP, hQ⟩
        rw [hval]
        exact s1.trans' (s2.trans' (s3.trans' s4))
      · have s3 : SReach N S g x (.call n todo m b k (⟨a, b, k, m, [], true⟩ :: st))
            (.ret n todo false (⟨a, b, k, m, [], true⟩ :: st)) := by
          have h := ih todo m b (⟨a, b, k, m, [], true⟩ :: st)
          rwa [decide_eq_false hQ] at h
        have s4 : SReach N S g x (.ret n todo false ((⟨a, b, k, m, [], true⟩ : Frame N.Mem) :: st))
            (.ret n todo false st) := SReach.one' (dstep_ret_false_nil rfl)
        have hval : (decide (∃ mm ∈ [m], CY N S x n k a mm ∧ CY N S x n k mm b)) = false := by
          refine decide_eq_false ?_
          rintro ⟨mm, hmm, -, h2⟩
          rw [List.mem_singleton] at hmm
          subst hmm
          exact hQ h2
        rw [hval]
        exact s1.trans' (s2.trans' (s3.trans' s4))
    · have s1 : SReach N S g x (.call n todo a m k (⟨a, b, k, m, [], false⟩ :: st))
          (.ret n todo false (⟨a, b, k, m, [], false⟩ :: st)) := by
        have h := ih todo a m (⟨a, b, k, m, [], false⟩ :: st)
        rwa [decide_eq_false hP] at h
      have s2 : SReach N S g x (.ret n todo false ((⟨a, b, k, m, [], false⟩ : Frame N.Mem) :: st))
          (.ret n todo false st) := SReach.one' (dstep_ret_false_nil rfl)
      have hval : (decide (∃ mm ∈ [m], CY N S x n k a mm ∧ CY N S x n k mm b)) = false := by
        refine decide_eq_false ?_
        rintro ⟨mm, hmm, h1, -⟩
        rw [List.mem_singleton] at hmm
        subst hmm
        exact hP h1
      rw [hval]
      exact s1.trans' s2
  | cons m2 ms2 ihms =>
    intro todo a b m st
    by_cases hP : CY N S x n k a m
    · have s1 : SReach N S g x (.call n todo a m k (⟨a, b, k, m, m2 :: ms2, false⟩ :: st))
          (.ret n todo true (⟨a, b, k, m, m2 :: ms2, false⟩ :: st)) := by
        have h := ih todo a m (⟨a, b, k, m, m2 :: ms2, false⟩ :: st)
        rwa [decide_eq_true hP] at h
      have s2 : SReach N S g x
          (.ret n todo true ((⟨a, b, k, m, m2 :: ms2, false⟩ : Frame N.Mem) :: st))
          (.call n todo m b k (⟨a, b, k, m, m2 :: ms2, true⟩ :: st)) :=
        SReach.one' (dstep_ret_true_first rfl)
      by_cases hQ : CY N S x n k m b
      · have s3 : SReach N S g x (.call n todo m b k (⟨a, b, k, m, m2 :: ms2, true⟩ :: st))
            (.ret n todo true (⟨a, b, k, m, m2 :: ms2, true⟩ :: st)) := by
          have h := ih todo m b (⟨a, b, k, m, m2 :: ms2, true⟩ :: st)
          rwa [decide_eq_true hQ] at h
        have s4 : SReach N S g x
            (.ret n todo true ((⟨a, b, k, m, m2 :: ms2, true⟩ : Frame N.Mem) :: st))
            (.ret n todo true st) := SReach.one' (dstep_ret_true_second rfl)
        have hval :
            (decide (∃ mm ∈ m :: m2 :: ms2, CY N S x n k a mm ∧ CY N S x n k mm b)) = true :=
          decide_eq_true ⟨m, by simp, hP, hQ⟩
        rw [hval]
        exact s1.trans' (s2.trans' (s3.trans' s4))
      · have s3 : SReach N S g x (.call n todo m b k (⟨a, b, k, m, m2 :: ms2, true⟩ :: st))
            (.ret n todo false (⟨a, b, k, m, m2 :: ms2, true⟩ :: st)) := by
          have h := ih todo m b (⟨a, b, k, m, m2 :: ms2, true⟩ :: st)
          rwa [decide_eq_false hQ] at h
        have s4 : SReach N S g x
            (.ret n todo false ((⟨a, b, k, m, m2 :: ms2, true⟩ : Frame N.Mem) :: st))
            (.call n todo a m2 k (⟨a, b, k, m2, ms2, false⟩ :: st)) :=
          SReach.one' (dstep_ret_false_cons rfl)
        have hiff : (∃ mm ∈ m :: m2 :: ms2, CY N S x n k a mm ∧ CY N S x n k mm b) ↔
            (∃ mm ∈ m2 :: ms2, CY N S x n k a mm ∧ CY N S x n k mm b) := by
          constructor
          · rintro ⟨mm, hmm, h1, h2⟩
            rcases List.mem_cons.mp hmm with rfl | hmm'
            · exact absurd h2 hQ
            · exact ⟨mm, hmm', h1, h2⟩
          · rintro ⟨mm, hmm, h1, h2⟩
            exact ⟨mm, List.mem_cons_of_mem _ hmm, h1, h2⟩
        rw [decide_eq_decide.mpr hiff]
        exact s1.trans' (s2.trans' (s3.trans' (s4.trans' (ihms todo a b m2 st))))
    · have s1 : SReach N S g x (.call n todo a m k (⟨a, b, k, m, m2 :: ms2, false⟩ :: st))
          (.ret n todo false (⟨a, b, k, m, m2 :: ms2, false⟩ :: st)) := by
        have h := ih todo a m (⟨a, b, k, m, m2 :: ms2, false⟩ :: st)
        rwa [decide_eq_false hP] at h
      have s2 : SReach N S g x
          (.ret n todo false ((⟨a, b, k, m, m2 :: ms2, false⟩ : Frame N.Mem) :: st))
          (.call n todo a m2 k (⟨a, b, k, m2, ms2, false⟩ :: st)) :=
        SReach.one' (dstep_ret_false_cons rfl)
      have hiff : (∃ mm ∈ m :: m2 :: ms2, CY N S x n k a mm ∧ CY N S x n k mm b) ↔
          (∃ mm ∈ m2 :: ms2, CY N S x n k a mm ∧ CY N S x n k mm b) := by
        constructor
        · rintro ⟨mm, hmm, h1, h2⟩
          rcases List.mem_cons.mp hmm with rfl | hmm'
          · exact absurd h1 hP
          · exact ⟨mm, hmm', h1, h2⟩
        · rintro ⟨mm, hmm, h1, h2⟩
          exact ⟨mm, List.mem_cons_of_mem _ hmm, h1, h2⟩
      rw [decide_eq_decide.mpr hiff]
      exact s1.trans' (s2.trans' (ihms todo a b m2 st))

/-- Correctness of the recursive procedure: a call at level `k` returns the
truth value of `CY n k a b`. -/
