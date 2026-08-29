/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ### The `n`-fold power of a word -/

/-- `rep b n` is the `n`-fold concatenation `bⁿ` of the word `b` with itself. -/
def rep {α : Type*} (b : List α) (n : ℕ) : List α :=
  (List.replicate n b).flatten

@[simp] lemma rep_zero {α : Type*} (b : List α) : rep b 0 = [] := rfl

lemma rep_succ {α : Type*} (b : List α) (n : ℕ) : rep b (n + 1) = b ++ rep b n := by
  simp [rep, List.replicate_succ]

/-! ### Pumping for a fixed DFA

The pigeonhole step: among the `|σ| + 1` states reached after reading the prefixes of `x`
of lengths `0, 1, …, |σ|`, two must coincide, and the corresponding infix of `x` is a loop.
-/

variable {α σ : Type*} [Fintype σ] (M : DFA α σ)

omit [Fintype σ] in
/-- Reading a loop word `b` (i.e. `M.evalFrom q b = q`) any number of times stays at `q`. -/
lemma evalFrom_rep {q : σ} {b : List α} (hb : M.evalFrom q b = q) (n : ℕ) :
    M.evalFrom q (rep b n) = q := by
  induction n with
  | zero => simp [DFA.evalFrom]
  | succ n ih => rw [rep_succ, M.evalFrom_of_append, hb, ih]

/--
Pumping lemma for a DFA: every accepted word of length at least `Fintype.card σ`
splits as `a ++ b ++ c` with `|a| + |b| ≤ Fintype.card σ`, `b ≠ []`, and all pumped
words `a ++ bⁿ ++ c` accepted.
-/
theorem dfa_pumping {x : List α} (hx : x ∈ M.accepts) (hlen : Fintype.card σ ≤ x.length) :
    ∃ a b c : List α, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card σ ∧ b ≠ [] ∧
      ∀ n : ℕ, a ++ rep b n ++ c ∈ M.accepts := by
  obtain ⟨i, j, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card σ + 1) => M.evalFrom M.start (x.take i)) (by simp)
  -- We may assume `i < j`.
  wlog hlt : (i : ℕ) < (j : ℕ) generalizing i j
  · exact this j i hne.symm heq.symm
      (lt_of_le_of_ne (not_lt.1 hlt) (fun h => hne (Fin.ext h.symm)))
  have hprefix : (x.take j).take i = x.take i := by
    rw [List.take_take, min_eq_left hlt.le]
  have hab : x.take i ++ (x.take j).drop i = x.take j := by
    conv_lhs => rw [← hprefix]
    rw [List.take_append_drop]
  have hsplit : x = x.take i ++ (x.take j).drop i ++ x.drop j := by
    rw [hab, List.take_append_drop]
  -- the middle block is a loop at the state reached after reading the prefix `x.take i`
  have hloop : M.evalFrom (M.evalFrom M.start (x.take i)) ((x.take j).drop i)
      = M.evalFrom M.start (x.take i) := by
    rw [← M.evalFrom_of_append, hab, ← heq]
  refine ⟨x.take i, (x.take j).drop i, x.drop j, hsplit, ?_, ?_, ?_⟩
  · have hj : (j : ℕ) ≤ Fintype.card σ := Nat.lt_succ_iff.1 j.isLt
    simp only [List.length_take, List.length_drop]
    omega
  · have hjx : (j : ℕ) ≤ x.length := le_trans (Nat.lt_succ_iff.1 j.isLt) hlen
    intro h
    have hl := congrArg List.length h
    simp only [List.length_drop, List.length_take, List.length_nil] at hl
    omega
  · intro n
    have hfin : M.evalFrom (M.evalFrom M.start (x.take i)) (x.drop j)
        = M.evalFrom M.start x := by
      conv_rhs => rw [hsplit]
      rw [M.evalFrom_of_append, M.evalFrom_of_append, hloop]
    rw [DFA.mem_accepts, DFA.eval, M.evalFrom_of_append, M.evalFrom_of_append,
      evalFrom_rep M hloop, hfin]
    exact hx

/-! ### Pumping for regular languages -/

/--
**Pumping lemma for regular languages.**

Every regular language `L` admits a pumping length `p > 0` such that every word `x ∈ L`
of length at least `p` can be split as `x = a ++ b ++ c` with `|a| + |b| ≤ p`, `b ≠ []`,
and `a ++ bⁿ ++ c ∈ L` for every `n : ℕ`.
-/
theorem pumping_regular {α : Type*} {L : Language α} (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ x ∈ L, p ≤ x.length →
      ∃ a b c : List α, x = a ++ b ++ c ∧ a.length + b.length ≤ p ∧ b ≠ [] ∧
        ∀ n : ℕ, a ++ rep b n ++ c ∈ L := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  refine ⟨Fintype.card σ + 1, Nat.succ_pos _, ?_⟩
  intro x hx hlen
  obtain ⟨a, b, c, hsplit, hab, hbne, hpump⟩ := dfa_pumping M hx (by omega)
  exact ⟨a, b, c, hsplit, by omega, hbne, hpump⟩

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

