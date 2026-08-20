import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim

/-!
# Weil–Petersson volume polynomials in low complexity

We record the Weil–Petersson volume polynomials `V_{0,3}`, `V_{0,4}` and `V_{0,5}`, the
right-hand sides of Mirzakhani's recursion in the cases `(g,n) = (0,4)` and `(0,5)`, and
verify the recursion in both cases, together with the fact that the recursion determines
the volume polynomial.
-/

open scoped BigOperators Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The volume polynomials -/

/-- `V_{0,3} ≡ 1`: the moduli space of pairs of pants is a point. -/

lemma mirzRHS05_eq (L : Fin 5 → ℝ) :
    mirzRHS05 L
      = 5 * (L 0) ^ 4 / 8
        + (3 * ((L 1)^2 + (L 2)^2 + (L 3)^2 + (L 4)^2) / 2 + 9 * π ^ 2) * (L 0) ^ 2
        + (3 * π ^ 2 * ((L 1)^2 + (L 2)^2 + (L 3)^2 + (L 4)^2)
            + ((L 1)^2 + (L 2)^2 + (L 3)^2 + (L 4)^2) ^ 2 / 4
            - ((L 1)^4 + (L 2)^4 + (L 3)^4 + (L 4)^4) / 8 + 10 * π ^ 4) := by
  have hB : ∀ j : Fin 5,
      (∫ x in Ioi (0:ℝ), x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V04 (Fin.cons x (fun m => L (rest05 j m))))
      = (2 * π ^ 2 + (∑ m, (L (rest05 j m)) ^ 2) / 2)
          * (F1 (L 0 + L j) + F1 (L 0 - L j)) + (F3 (L 0 + L j) + F3 (L 0 - L j)) / 2 := by
    intro j
    rw [← integral_B_term (L 0 + L j) (L 0 - L j)
      (2 * π ^ 2 + (∑ m, (L (rest05 j m)) ^ 2) / 2)]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    show x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V04 (Fin.cons x (fun m => L (rest05 j m)))
      = x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        ((2 * π ^ 2 + (∑ m, (L (rest05 j m)) ^ 2) / 2) + x ^ 2 / 2)
    rw [V04_cons]
  have hsumB : ∀ f : Fin 5 → ℝ,
      ∑ j ∈ ({1,2,3,4} : Finset (Fin 5)), f j = f 1 + f 2 + f 3 + f 4 := by
    intro f; simp [Finset.sum_insert, Finset.mem_insert]; ring
  have s1 : ∑ m, (L (rest05 1 m)) ^ 2 = (L 2)^2 + (L 3)^2 + (L 4)^2 := by
    rw [Fin.sum_univ_three, show rest05 1 0 = 2 from rfl, show rest05 1 1 = 3 from rfl,
      show rest05 1 2 = 4 from rfl]
  have s2 : ∑ m, (L (rest05 2 m)) ^ 2 = (L 1)^2 + (L 3)^2 + (L 4)^2 := by
    rw [Fin.sum_univ_three, show rest05 2 0 = 1 from rfl, show rest05 2 1 = 3 from rfl,
      show rest05 2 2 = 4 from rfl]
  have s3 : ∑ m, (L (rest05 3 m)) ^ 2 = (L 1)^2 + (L 2)^2 + (L 4)^2 := by
    rw [Fin.sum_univ_three, show rest05 3 0 = 1 from rfl, show rest05 3 1 = 2 from rfl,
      show rest05 3 2 = 4 from rfl]
  have s4 : ∑ m, (L (rest05 4 m)) ^ 2 = (L 1)^2 + (L 2)^2 + (L 3)^2 := by
    rw [Fin.sum_univ_three, show rest05 4 0 = 1 from rfl, show rest05 4 1 = 2 from rfl,
      show rest05 4 2 = 3 from rfl]
  rw [mirzRHS05, Finset.sum_congr rfl (fun k _ => mirzRHS05_sep L k),
    Finset.sum_congr rfl (fun j _ => hB j), hsumB, Finset.sum_const, s1, s2, s3, s4]
  rw [F1_eq, F1_eq, F1_eq, F1_eq, F1_eq, F1_eq, F1_eq, F1_eq,
    F3_eq, F3_eq, F3_eq, F3_eq, F3_eq, F3_eq, F3_eq, F3_eq, F3_eq]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

