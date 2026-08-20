/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module documentation, so the header above is
-- written as a plain comment; it is repeated as the module docstring below.)
import RequestProject.Savitch.Final

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The machine model is the standard off-line random-access model of space bounded computation
(see `RequestProject/Savitch/Model.lean`): the memory of a machine is a bit string, one step
rewrites the memory using the memory content and a single input bit, read at a position which
is determined by the memory, and the space used on an input is the maximal length of a memory
string occurring in the computation.

`NSPACE f` and `DSPACE g` are the classes of languages accepted by nondeterministic,
respectively deterministic, machines running in space `O (f n)`, respectively `O (g n)`.

The proof is Savitch's: for a nondeterministic machine `M` running in space `S` on the input
`x`, deciding whether `M` accepts amounts to deciding reachability in the configuration graph
of `M` on `x`, whose vertices are the words of length at most `S`.  Reachability by a path of
length at most `2 ^ k` is decided by the midpoint recursion `savR`, whose recursion depth is
`k`; taking `k = S + 1` suffices because there are only `2 ^ (S + 1) - 1` configurations.  The
simulator runs this recursion with an explicit stack of at most `S + 2` frames, each holding
three words of length at most `S`, so it uses `O (S ^ 2)` bits.  Since the simulator does not
know `S`, it runs the whole procedure for stages `s = 0, 1, 2, …`, and at each stage also
checks whether some reachable configuration has a successor of length more than `s`; the first
stage at which this check fails gives the correct answer, and this happens at the latest at
stage `S`.
-/

namespace CS

namespace Savitch

/-- A deterministic machine viewed as a nondeterministic machine. -/

theorem savR_iff (E : Word → Word → Bool) (s : ℕ) :
    ∀ (k : ℕ) {a b : Word}, a.length ≤ s → b.length ≤ s →
      (savR E s k a b = true ↔ ∃ n ≤ 2 ^ k, PathN E s n a b) := by
  intro k
  induction k with
  | zero =>
      intro a b ha _
      rw [savR_zero]
      constructor
      · intro h
        rw [Bool.or_eq_true] at h
        rcases h with h1 | h1
        · exact ⟨0, by norm_num, PathN.of_eq (by simpa using h1)⟩
        · exact ⟨1, by norm_num, PathN.single ha h1⟩
      · rintro ⟨n, hn, hp⟩
        have : n = 0 ∨ n = 1 := by simp at hn; omega
        rcases this with rfl | rfl
        · rw [PathN.zero_iff] at hp; simp [hp]
        · simp [hp.edge_of_one]
  | succ k ih =>
      intro a b ha hb
      rw [savR_succ]
      constructor
      · intro h
        rw [Bool.or_eq_true] at h
        rcases h with h1 | h1
        · exact ⟨0, by positivity, PathN.of_eq (by simpa using h1)⟩
        · obtain ⟨m, hm, hP⟩ := (anyMid_all _ s).1 h1
          rw [Bool.and_eq_true] at hP
          obtain ⟨n₁, hn₁, hp₁⟩ := (ih ha hm).1 hP.1
          obtain ⟨n₂, hn₂, hp₂⟩ := (ih hm hb).1 hP.2
          exact ⟨n₁ + n₂, by rw [pow_succ]; omega, hp₁.comp hp₂ hm⟩
      · rintro ⟨n, hn, hp⟩
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · rw [PathN.zero_iff] at hp; simp [hp]
        · have hle : min n (2 ^ k) ≤ n := min_le_left _ _
          obtain ⟨m, hpre, hsuf, hmem⟩ := hp.prefix (min n (2 ^ k)) hle
          have hmlen : m.length ≤ s := by
            rcases hmem with h | h
            · exact h
            · rw [h]; exact hb
          have h1 : min n (2 ^ k) ≤ 2 ^ k := min_le_right _ _
          have h2 : n - min n (2 ^ k) ≤ 2 ^ k := by
            rw [pow_succ] at hn
            rcases le_total n (2 ^ k) with h | h
            · simp [min_eq_left h]
            · simp [min_eq_right h]; omega
          have hA : savR E s k a m = true := (ih ha hmlen).2 ⟨_, h1, hpre⟩
          have hB : savR E s k m b = true := (ih hmlen hb).2 ⟨_, h2, hsuf⟩
          rw [Bool.or_eq_true]
          exact Or.inr ((anyMid_all _ s).2 ⟨m, hmlen, by simp [hA, hB]⟩)

/-- Reachability inside the words of length at most `s` is decided by `savR` at level `s + 1`. -/
