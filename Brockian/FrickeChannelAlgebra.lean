import Mathlib

/-!
# The algebra of the two Fricke channels

The variable `x` represents `p ^ (-s)`. All identities below are algebraic;
the analytic Eisenstein constant-term formula is a named hypothesis in
`channels_of_constant_term`. Division identities have explicit denominator
hypotheses. The parity theorem concerns local denominators and numerators,
not orders of meromorphic poles or cancellation by the level-one factor.
-/

namespace Brockian.FrickeChannelAlgebra

variable {K : Type*} [Field K] [CharZero K]

def plusFactor (p x : K) : K := x * (1 + p * x) / (1 + x)
def minusFactor (p x : K) : K := x * (p * x - 1) / (1 - x)

def scattering (p a x : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a * (p - 1) * x ^ 2 / (1 - x ^ 2),
     a * x * (1 - p * x ^ 2) / (1 - x ^ 2);
     a * x * (1 - p * x ^ 2) / (1 - x ^ 2),
     a * (p - 1) * x ^ 2 / (1 - x ^ 2)]

def fricke : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]
def evenProjector : Matrix (Fin 2) (Fin 2) K := !![1/2, 1/2; 1/2, 1/2]
def oddProjector : Matrix (Fin 2) (Fin 2) K := !![1/2, -(1/2); -(1/2), 1/2]

theorem denominator_factorization (x : K) : 1 - x ^ 2 = (1 - x) * (1 + x) := by
  ring

theorem denominator_ne_zero {x : K} (hm : 1 - x ≠ 0) (hp : 1 + x ≠ 0) :
    1 - x ^ 2 ≠ 0 := by
  rw [denominator_factorization]
  exact mul_ne_zero hm hp

theorem channel_sum (p a x : K) (hm : 1 - x ≠ 0) (hp : 1 + x ≠ 0) :
    scattering p a x 0 0 + scattering p a x 0 1 = a * plusFactor p x := by
  have hd := denominator_ne_zero hm hp
  simp [scattering, plusFactor]
  field_simp
  <;> ring

theorem channel_difference (p a x : K) (hm : 1 - x ≠ 0) (hp : 1 + x ≠ 0) :
    scattering p a x 0 0 - scattering p a x 0 1 = a * minusFactor p x := by
  have hd := denominator_ne_zero hm hp
  simp [scattering, minusFactor]
  field_simp
  <;> ring

theorem determinant (p a x : K) (hm : 1 - x ≠ 0) (hp : 1 + x ≠ 0) :
    (scattering p a x).det = a ^ 2 * x ^ 2 * (p ^ 2 * x ^ 2 - 1) / (1 - x ^ 2) := by
  have hd := denominator_ne_zero hm hp
  simp [scattering, Matrix.det_fin_two]
  field_simp
  <;> ring

theorem channel_product (p a x : K) (hm : 1 - x ≠ 0) (hp : 1 + x ≠ 0) :
    (a * plusFactor p x) * (a * minusFactor p x) = (scattering p a x).det := by
  rw [determinant p a x hm hp]
  have hd := denominator_ne_zero hm hp
  dsimp [plusFactor, minusFactor]
  field_simp
  <;> ring

/-- The local factor of the functional equation, on its regular domain. -/
theorem plus_functional_equation (p x : K) (hp : p ≠ 0) (hx : x ≠ 0)
    (hplus : 1 + x ≠ 0) (htransformed : 1 + 1 / (p * x) ≠ 0) :
    plusFactor p (1 / (p * x)) * plusFactor p x = 1 := by
  dsimp [plusFactor]
  field_simp
  <;> ring

theorem minus_functional_equation (p x : K) (hp : p ≠ 0) (hx : x ≠ 0)
    (hminus : 1 - x ≠ 0) (htransformed : 1 - 1 / (p * x) ≠ 0) :
    minusFactor p (1 / (p * x)) * minusFactor p x = 1 := by
  dsimp [minusFactor]
  field_simp
  <;> ring

theorem projector_resolution :
    (evenProjector : Matrix (Fin 2) (Fin 2) K) + oddProjector = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [evenProjector, oddProjector, Matrix.one_apply]

theorem projector_algebra :
    (evenProjector : Matrix (Fin 2) (Fin 2) K) * evenProjector = evenProjector ∧
    (oddProjector : Matrix (Fin 2) (Fin 2) K) * oddProjector = oddProjector ∧
    (evenProjector : Matrix (Fin 2) (Fin 2) K) * oddProjector = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [evenProjector, oddProjector, Matrix.mul_apply, Fin.sum_univ_two]

theorem fricke_parity :
    (fricke : Matrix (Fin 2) (Fin 2) K) * evenProjector = evenProjector ∧
    (fricke : Matrix (Fin 2) (Fin 2) K) * oddProjector = -oddProjector := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [fricke, evenProjector, oddProjector, Matrix.mul_apply, Fin.sum_univ_two]

theorem channel_decomposition (p a x : K) (hm : 1 - x ≠ 0) (hp : 1 + x ≠ 0) :
    scattering p a x =
      (a * plusFactor p x) • evenProjector + (a * minusFactor p x) • oddProjector := by
  have hd := denominator_ne_zero hm hp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scattering, plusFactor, minusFactor, evenProjector, oddProjector] <;>
    field_simp <;> ring

/-- The level-five determinant, in the coordinate `x = 5 ^ (-s)`. -/
theorem determinant_five (a x : K) (hm : 1 - x ≠ 0) (hp : 1 + x ≠ 0) :
    (scattering 5 a x).det = a ^ 2 * x ^ 2 * (25 * x ^ 2 - 1) / (1 - x ^ 2) := by
  rw [determinant (5 : K) a x hm hp]
  norm_num

/-- At the two local boundary points only one channel denominator vanishes,
and that channel's numerator equals four. No analytic pole is asserted here. -/
theorem local_channel_parity_five :
    ((1 + (1 : K)) = 2 ∧ (1 - (1 : K)) = 0 ∧ (1 : K) * (5 * 1 - 1) = 4) ∧
    ((1 + (-1 : K)) = 0 ∧ (1 - (-1 : K)) = 2 ∧ (-1 : K) * (1 + 5 * (-1)) = 4) := by
  norm_num

theorem even_channel_denominator_parity (k : ℕ) :
    1 + (-1 : K) ^ k = 0 ↔ Odd k := by
  have h : 1 + (-1 : K) ^ k = 0 ↔ (-1 : K) ^ k = -1 := by
    constructor <;> intro h <;> linear_combination h
  rw [h]
  exact neg_one_pow_eq_neg_one_iff_odd (by norm_num)

theorem odd_channel_denominator_parity (k : ℕ) :
    1 - (-1 : K) ^ k = 0 ↔ Even k := by
  rw [sub_eq_zero, eq_comm]
  exact neg_one_pow_eq_one_iff_even (by norm_num)

/-- Analytic input is supplied explicitly, without adding an axiom. -/
theorem channels_of_constant_term {S : Type*}
    (Phi : S → Matrix (Fin 2) (Fin 2) K) (phi0 x : S → K)
    (hEisensteinConstantTerm : ∀ s, Phi s = scattering 5 (phi0 s) (x s))
    (s : S) (hm : 1 - x s ≠ 0) (hp : 1 + x s ≠ 0) :
    Phi s = (phi0 s * plusFactor 5 (x s)) • evenProjector +
      (phi0 s * minusFactor 5 (x s)) • oddProjector := by
  rw [hEisensteinConstantTerm s]
  exact channel_decomposition 5 (phi0 s) (x s) hm hp

end Brockian.FrickeChannelAlgebra
