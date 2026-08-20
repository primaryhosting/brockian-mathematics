import RequestProject.Basic

/-!
# Unbounded fan-in Boolean circuits, the class `AC⁰`, and `PARITY`

A `Circuit n` is a Boolean circuit on `n` inputs built from constants, input
variables, negations, and *unbounded fan-in* `AND`/`OR` gates.

* `Circuit.depth` counts the maximal number of `AND`/`OR` gates on a root-to-leaf
  path (negations are free, as is standard for `AC⁰`).
* `Circuit.size` counts the number of `AND`/`OR` gates.

`InAC0 f` says that the family `f` is computed by circuits of some fixed depth and
polynomial size.  Making negations free and not counting them in the size only
makes the class larger, hence the lower bound proved later stronger.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`/`OR` gates. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | or : (m : ℕ) → (Fin m → Circuit n) → Circuit n
  | and : (m : ℕ) → (Fin m → Circuit n) → Circuit n

namespace Circuit

/-- The Boolean function computed by a circuit. -/

lemma two_mul_sum_range_choose_lt (m : ℕ) :
    2 * ∑ k ∈ Finset.range m, (2 * m).choose k + Nat.centralBinom m = 4 ^ m := by
  classical
  have hsplit : ∑ k ∈ Finset.range (2 * m + 1), (2 * m).choose k
      = (∑ k ∈ Finset.range m, (2 * m).choose k) + (2 * m).choose m
        + ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), (2 * m).choose k := by
    have h1 : Finset.range (2 * m + 1)
        = (Finset.range (m + 1)) ∪ Finset.Ico (m + 1) (2 * m + 1) := by
      ext k; simp [Finset.mem_range, Finset.mem_Ico]; omega
    have hd : Disjoint (Finset.range (m + 1)) (Finset.Ico (m + 1) (2 * m + 1)) := by
      simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [h1, Finset.sum_union hd, Finset.sum_range_succ]
  have hmirror : ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), (2 * m).choose k
      = ∑ k ∈ Finset.range m, (2 * m).choose k := by
    apply Finset.sum_nbij' (fun k => 2 * m - k) (fun k => 2 * m - k)
    · intro k hk; simp [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega
    · intro k hk; simp [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega
    · intro k hk; simp [Finset.mem_Ico] at hk; omega
    · intro k hk; simp [Finset.mem_range] at hk; omega
    · intro k hk
      simp [Finset.mem_Ico] at hk
      rw [Nat.choose_symm (by omega)]
  have htotal : ∑ k ∈ Finset.range (2 * m + 1), (2 * m).choose k = 4 ^ m := by
    rw [Nat.sum_range_choose (2 * m)]
    rw [pow_mul]
    norm_num
  have hCm : Nat.centralBinom m = (2 * m).choose m := rfl
  rw [hCm]
  omega

/-- The number of subsets of size at most `m + D` of a `2m`-element set. -/
