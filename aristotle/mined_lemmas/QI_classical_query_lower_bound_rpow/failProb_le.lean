import Mathlib
import RequestProject.Simon.Basic
import RequestProject.Simon.Classical
import RequestProject.Simon.Quantum
import RequestProject.Simon.Solve

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

set_option grind.warning false

/-!
# Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries

`QI.simon_algorithm` collects the two halves of the classical/quantum
separation for Simon's problem.  An instance is a function
`f : BV n → BV n` on `n`-bit strings satisfying Simon's promise
`IsSimon f s`: `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`.  The task is to
output the hidden shift `s`.

*Quantum upper bound.*  Each round of Simon's algorithm uses exactly **one**
query: it prepares `2 ^ (-n/2) ∑ₓ |x⟩|f x⟩`, applies the Hadamard transform to
the first register and measures.  The resulting distribution `prob f` is
uniform on the hyperplane `{y | ⟪y, s⟫ = 0}` orthogonal to `s`.  After
`2 * n` such rounds — i.e. `2 * n = O(n)` queries — the outcomes fail to pin
down `s` (as the unique nonzero solution of the linear system `⟪yᵢ, t⟫ = 0`)
only with probability at most `2 ^ (-n)`.

*Classical lower bound.*  A deterministic classical query algorithm that always
outputs the hidden shift after `q` queries must satisfy `2 ^ n ≤ (q + 2) ^ 2`,
i.e. `q ≥ 2 ^ (n / 2) - 2 = Ω(2 ^ (n / 2))`.
-/

namespace QI

/-- The classical lower bound in the form `2 ^ (n / 2) ≤ q + 2`. -/

theorem failProb_le {f : BV n → BV n} {s : BV n} (hf : IsSimon f s) (m : ℕ) :
    failProb f s m ≤ 2 ^ n / 2 ^ m := by
  classical
  have hpos : (0:ℝ) < (orth s).card := by exact_mod_cast card_orth_pos hf.1
  -- only tuples inside the hyperplane contribute
  have hsub : badTuples s m ⊆
      Finset.univ.filter (fun Y : Fin m → BV n => ¬ Determines Y s) := by
    intro Y hY
    rw [badTuples, Finset.mem_filter] at hY
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hY.2⟩
  have hzero : ∀ Y ∈ Finset.univ.filter (fun Y : Fin m → BV n => ¬ Determines Y s),
      Y ∉ badTuples s m → ∏ i, prob f (Y i) = 0 := by
    intro Y hY hYbad
    rw [badTuples, Finset.mem_filter] at hYbad
    have hnd : ¬ Determines Y s := (Finset.mem_filter.1 hY).2
    have : Y ∉ (Fintype.piFinset fun _ => orth s) := fun h => hYbad ⟨h, hnd⟩
    rw [Fintype.mem_piFinset] at this
    push_neg at this
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (prob_of_not_mem_orth hf hi)
  have hsum : failProb f s m = ∑ Y ∈ badTuples s m, ∏ i, prob f (Y i) := by
    rw [failProb]
    exact (Finset.sum_subset hsub hzero).symm
  have hval : ∀ Y ∈ badTuples s m, ∏ i, prob f (Y i) = (((orth s).card : ℝ)⁻¹) ^ m := by
    intro Y hY
    rw [badTuples, Finset.mem_filter, Fintype.mem_piFinset] at hY
    rw [Finset.prod_congr rfl fun i _ => prob_of_mem_orth hf (hY.1 i)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hsum, Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  -- now a purely numerical estimate
  have hcount : (2:ℝ) ^ m * (badTuples s m).card ≤ 2 ^ n * ((orth s).card : ℝ) ^ m := by
    have h2 : ((2 ^ m * (badTuples s m).card : ℕ) : ℝ) ≤ ((2 ^ n * (orth s).card ^ m : ℕ) : ℝ) :=
      Nat.cast_le.2 (card_badTuples_le s m)
    push_cast at h2
    exact h2
  have h2pos : (0:ℝ) < (2:ℝ) ^ m := by positivity
  have hne : ((orth s).card : ℝ) ≠ 0 := ne_of_gt hpos
  have key : ((badTuples s m).card : ℝ) ≤ 2 ^ n * ((orth s).card : ℝ) ^ m / 2 ^ m := by
    rw [le_div_iff₀ h2pos]
    linarith [hcount]
  have hinv : (0:ℝ) ≤ (((orth s).card : ℝ)⁻¹) ^ m := by positivity
  calc ((badTuples s m).card : ℝ) * (((orth s).card : ℝ)⁻¹) ^ m
      ≤ (2 ^ n * ((orth s).card : ℝ) ^ m / 2 ^ m) * (((orth s).card : ℝ)⁻¹) ^ m :=
        mul_le_mul_of_nonneg_right key hinv
    _ = 2 ^ n / 2 ^ m := by
        field_simp
        rw [← mul_pow]
        field_simp
        exact one_pow m

/-- **Simon's algorithm with `2 * n` quantum queries.**  For any function
satisfying Simon's promise with hidden shift `s`, running the one-query quantum
subroutine `2 * n` times produces measurement outcomes which determine `s`,
except with probability at most `2 ^ (-n)`. -/
