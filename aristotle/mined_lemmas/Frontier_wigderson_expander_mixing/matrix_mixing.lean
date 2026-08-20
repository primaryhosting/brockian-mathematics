import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Frontier

section Aux

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Cauchy–Schwarz for finite sums, in absolute-value / square-root form. -/

theorem matrix_mixing (A : Matrix V V ℝ) (d : ℝ)
    (hrow : ∀ x, ∑ y, A x y = d) (hcol : ∀ y, ∑ x, A x y = d)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hspec : ∀ v : V → ℝ, ∑ i, v i = 0 →
      Real.sqrt (∑ i, (A.mulVec v i) ^ 2) ≤ lam * Real.sqrt (∑ i, (v i) ^ 2))
    (S T : Finset V) :
    |(∑ x ∈ S, ∑ y ∈ T, A x y) - d * S.card * T.card / (Fintype.card V)|
      ≤ lam * Real.sqrt (S.card * T.card) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · have hS : S = ∅ := Finset.eq_empty_of_isEmpty S
    have hT : T = ∅ := Finset.eq_empty_of_isEmpty T
    subst hS; subst hT
    simp
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hn : 0 < n := by
    rw [hn_def]
    exact_mod_cast Fintype.card_pos
  set a : ℝ := (S.card : ℝ) with ha_def
  set b : ℝ := (T.card : ℝ) with hb_def
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set iS : V → ℝ := fun x => if x ∈ S then 1 else 0 with hiS
  set iT : V → ℝ := fun y => if y ∈ T then 1 else 0 with hiT
  set u : V → ℝ := fun x => iS x - a / n with hu
  set w : V → ℝ := fun y => iT y - b / n with hw
  have hsumS : ∑ x, iS x = a := by
    simp [hiS, ha_def]
  have hsumT : ∑ y, iT y = b := by
    simp [hiT, hb_def]
  have hcard : ∑ _x : V, (1:ℝ) = n := by
    simp [hn_def]
  have hsum_u : ∑ x, u x = 0 := by
    have : ∑ x, u x = (∑ x, iS x) - (∑ _x : V, a / n) := by
      simp [hu, Finset.sum_sub_distrib]
    rw [this, hsumS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def]
    field_simp
    ring
  have hsum_w : ∑ y, w y = 0 := by
    have : ∑ y, w y = (∑ y, iT y) - (∑ _y : V, b / n) := by
      simp [hw, Finset.sum_sub_distrib]
    rw [this, hsumT, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def]
    field_simp
    ring
  -- the four basic double sums
  have T1 : ∑ x, ∑ y, iS x * A x y * iT y = ∑ x ∈ S, ∑ y ∈ T, A x y := by
    have h1 : ∀ x, ∑ y, iS x * A x y * iT y = iS x * ∑ y ∈ T, A x y := by
      intro x
      rw [← sum_mul_indicator T (fun y => A x y), Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl fun x _ => h1 x, sum_indicator_mul S]
  have T2 : ∑ x, ∑ y, iS x * A x y = a * d := by
    have h1 : ∀ x, ∑ y, iS x * A x y = iS x * d := by
      intro x; rw [← Finset.mul_sum, hrow]
    rw [Finset.sum_congr rfl fun x _ => h1 x, sum_indicator_mul S (fun _ => d),
      Finset.sum_const, nsmul_eq_mul, ← ha_def]
  have T3 : ∑ x, ∑ y, A x y * iT y = b * d := by
    rw [Finset.sum_comm]
    have h1 : ∀ y, ∑ x, A x y * iT y = d * iT y := by
      intro y; rw [← Finset.sum_mul, hcol]
    rw [Finset.sum_congr rfl fun y _ => h1 y, sum_mul_indicator T (fun _ => d),
      Finset.sum_const, nsmul_eq_mul, ← hb_def]
  have T4 : ∑ x : V, ∑ y, A x y = n * d := by
    rw [Finset.sum_congr rfl fun x _ => hrow x, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hn_def]
  have hkey : ∑ x, u x * A.mulVec w x
      = (∑ x ∈ S, ∑ y ∈ T, A x y) - d * a * b / n := by
    have e1 : ∀ x, u x * A.mulVec w x
        = ∑ y, ((iS x * A x y * iT y) - (b / n) * (iS x * A x y)
            - (a / n) * (A x y * iT y) + (a * b / n ^ 2) * A x y) := by
      intro x
      rw [show A.mulVec w x = ∑ y, A x y * w y from rfl, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [hu, hw]
      ring
    rw [Finset.sum_congr rfl fun x _ => e1 x]
    have esplit : ∑ x, ∑ y, ((iS x * A x y * iT y) - (b / n) * (iS x * A x y)
            - (a / n) * (A x y * iT y) + (a * b / n ^ 2) * A x y)
        = (∑ x, ∑ y, iS x * A x y * iT y) - (b / n) * (∑ x, ∑ y, iS x * A x y)
            - (a / n) * (∑ x, ∑ y, A x y * iT y) + (a * b / n ^ 2) * (∑ x : V, ∑ y, A x y) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [esplit, T1, T2, T3, T4]
    field_simp
    ring
  have hu2 : ∑ x, (u x) ^ 2 = a - a ^ 2 / n := by
    have h1 : ∀ x, (u x) ^ 2 = iS x * (1 - 2 * (a / n)) + (a / n) ^ 2 := by
      intro x
      simp only [hu, hiS]
      by_cases hx : x ∈ S <;> (simp [hx]; try ring)
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_add_distrib, ← Finset.sum_mul, hsumS,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def]
    field_simp
    ring
  have hw2 : ∑ y, (w y) ^ 2 = b - b ^ 2 / n := by
    have h1 : ∀ y, (w y) ^ 2 = iT y * (1 - 2 * (b / n)) + (b / n) ^ 2 := by
      intro y
      simp only [hw, hiT]
      by_cases hy : y ∈ T <;> (simp [hy]; try ring)
    rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_add_distrib, ← Finset.sum_mul, hsumT,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def]
    field_simp
    ring
  have hu2le : ∑ x, (u x) ^ 2 ≤ a := by
    rw [hu2]
    have : 0 ≤ a ^ 2 / n := by positivity
    linarith
  have hw2le : ∑ y, (w y) ^ 2 ≤ b := by
    rw [hw2]
    have : 0 ≤ b ^ 2 / n := by positivity
    linarith
  have hAw : Real.sqrt (∑ i, (A.mulVec w i) ^ 2) ≤ lam * Real.sqrt b :=
    le_trans (hspec w hsum_w)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hw2le) hlam)
  rw [← hkey]
  calc |∑ x, u x * A.mulVec w x|
      ≤ Real.sqrt (∑ x, (u x) ^ 2) * Real.sqrt (∑ x, (A.mulVec w x) ^ 2) :=
        abs_sum_mul_le_sqrt_mul_sqrt _ _
    _ ≤ Real.sqrt a * (lam * Real.sqrt b) :=
        mul_le_mul (Real.sqrt_le_sqrt hu2le) hAw (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = lam * Real.sqrt (a * b) := by
        rw [Real.sqrt_mul ha0]; ring

end Matrix

/-- **Wigderson's expander mixing lemma.**  For a `d`-regular graph `G` on `n` vertices whose
adjacency matrix contracts every vector orthogonal to the all-ones vector by a factor `lam`
(i.e. `lam` bounds the absolute values of all eigenvalues other than the trivial one `d`), and
for any two sets of vertices `S`, `T`, the number of ordered pairs `(x, y) ∈ S × T` with
`x ~ y` differs from `d * |S| * |T| / n` by at most `lam * √(|S| * |T|)`. -/
