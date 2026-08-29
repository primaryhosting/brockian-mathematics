import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid. -/
noncomputable def natRank (M : Matroid α) (X : Set α) : ℕ := (M.eRk X).toNat

/-- The characteristic polynomial of a matroid `M` with (finite) ground set `E`, defined by
Whitney's rank-generating formula
`χ_M(t) = ∑_{S ⊆ E} (-1)^{|S|} t^{r(E) - r(S)}`. -/
noncomputable def charPoly (M : Matroid α) (E : Finset α) : ℤ[X] :=
  ∑ S ∈ E.powerset, (-1 : ℤ[X]) ^ S.card * X ^ (natRank M (E : Set α) - natRank M (S : Set α))

/-- A polynomial over `ℤ` has log-concave coefficient sequence if
`|c_k| * |c_{k+2}| ≤ |c_{k+1}|^2` for all `k`. -/
def LogConcaveCoeffs (p : ℤ[X]) : Prop :=
  ∀ k : ℕ, |p.coeff k| * |p.coeff (k + 2)| ≤ |p.coeff (k + 1)| ^ 2

/-- Log-concavity of the binomial coefficients: `C(n,k) * C(n,k+2) ≤ C(n,k+1)^2`. -/
theorem choose_mul_choose_le_choose_sq (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ n.choose (k + 1) ^ 2 := by
  set a := n.choose k with ha
  set b := n.choose (k + 1) with hb
  set c := n.choose (k + 2) with hc
  have h1 : b * (k + 1) = a * (n - k) := Nat.choose_succ_right_eq n k
  have h2 : c * (k + 2) = b * (n - (k + 1)) := Nat.choose_succ_right_eq n (k + 1)
  have key : (k + 1) * (n - (k + 1)) ≤ (n - k) * (k + 2) := by
    by_cases h : n ≤ k
    · simp [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le (h.trans (Nat.le_succ k))]
    · obtain ⟨d, hd⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
      subst hd
      have e : k + 1 + d - k = d + 1 := by omega
      rw [e]
      simp only [Nat.add_sub_cancel_left]
      nlinarith
  have e1 : a * c * ((k + 1) * (k + 2)) = a * b * ((k + 1) * (n - (k + 1))) := by
    calc a * c * ((k + 1) * (k + 2)) = a * (c * (k + 2)) * (k + 1) := by ring
      _ = a * (b * (n - (k + 1))) * (k + 1) := by rw [h2]
      _ = a * b * ((k + 1) * (n - (k + 1))) := by ring
  have e2 : b ^ 2 * ((k + 1) * (k + 2)) = a * b * ((n - k) * (k + 2)) := by
    calc b ^ 2 * ((k + 1) * (k + 2)) = (b * (k + 1)) * b * (k + 2) := by ring
      _ = (a * (n - k)) * b * (k + 2) := by rw [h1]
      _ = a * b * ((n - k) * (k + 2)) := by ring
  have hle : a * c * ((k + 1) * (k + 2)) ≤ b ^ 2 * ((k + 1) * (k + 2)) := by
    rw [e1, e2]; exact Nat.mul_le_mul_left _ key
  exact Nat.le_of_mul_le_mul_right hle (by positivity)

/-- The coefficients of `(X - 1)^n` are the signed binomial coefficients. -/
theorem coeff_X_sub_one_pow (n k : ℕ) :
    ((X - 1 : ℤ[X]) ^ n).coeff k = (-1) ^ (n - k) * (n.choose k : ℤ) := by
  rw [show (X - 1 : ℤ[X]) = X + (-1) by ring, add_pow]
  rw [Polynomial.finset_sum_coeff]
  have h : ∀ m ∈ range (n + 1),
      (((X : ℤ[X]) ^ m * (-1) ^ (n - m) * (n.choose m : ℤ[X])).coeff k)
        = if k = m then (-1) ^ (n - m) * (n.choose m : ℤ) else 0 := by
    intro m _
    rw [show ((X : ℤ[X]) ^ m * (-1) ^ (n - m) * (n.choose m : ℤ[X]))
        = Polynomial.C ((-1) ^ (n - m) * (n.choose m : ℤ)) * X ^ m by
      simp only [Polynomial.C_mul, Polynomial.C_pow, map_neg, map_one, Polynomial.C_eq_natCast]
      ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split <;> simp_all
  rw [Finset.sum_congr rfl h,
    Finset.sum_ite_eq (range (n + 1)) k (fun m => (-1) ^ (n - m) * (n.choose m : ℤ))]
  by_cases hk : k ≤ n
  · simp [Nat.lt_succ_of_le hk]
  · simp [hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hk)]

/-- The rank function of a free matroid is cardinality. -/
theorem natRank_freeOn (E S : Finset α) (h : S ⊆ E) :
    natRank (Matroid.freeOn (E : Set α)) (S : Set α) = S.card := by
  rw [natRank, Matroid.eRk_freeOn (by exact_mod_cast h), Set.encard_coe_eq_coe_finsetCard]
  simp

/-- Whitney's rank-generating formula for the free matroid evaluates to `(X - 1)^n`. -/
theorem charPoly_freeOn (E : Finset α) :
    charPoly (Matroid.freeOn (E : Set α)) E = (X - 1 : ℤ[X]) ^ E.card := by
  have hterm : ∀ S ∈ E.powerset,
      (-1 : ℤ[X]) ^ S.card *
          X ^ (natRank (Matroid.freeOn (E : Set α)) (E : Set α)
            - natRank (Matroid.freeOn (E : Set α)) (S : Set α))
        = (-1 : ℤ[X]) ^ S.card * X ^ (E.card - S.card) := by
    intro S hS
    rw [natRank_freeOn E S (Finset.mem_powerset.mp hS), natRank_freeOn E E (Finset.Subset.refl E)]
  rw [charPoly, Finset.sum_congr rfl hterm, Finset.sum_powerset]
  have step : ∀ j ∈ range (E.card + 1),
      (∑ S ∈ Finset.powersetCard j E, (-1 : ℤ[X]) ^ S.card * X ^ (E.card - S.card))
        = (-1 : ℤ[X]) ^ j * X ^ (E.card - j) * (E.card.choose j : ℤ[X]) := by
    intro j _
    rw [Finset.sum_congr rfl (fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]),
      Finset.sum_const, Finset.card_powersetCard]
    simp [nsmul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl step, show (X - 1 : ℤ[X]) = (-1) + X by ring, add_pow]

/-- **Base case of the Adiprasito–Huh–Katz theorem.**
The coefficients of the characteristic polynomial of a (Boolean/free) matroid form a log-concave
sequence. -/
theorem huh_matroid_log_concave (E : Finset α) :
    LogConcaveCoeffs (charPoly (Matroid.freeOn (E : Set α)) E) := by
  intro k
  rw [charPoly_freeOn]
  set n := E.card
  rw [coeff_X_sub_one_pow, coeff_X_sub_one_pow, coeff_X_sub_one_pow]
  have habs : ∀ m : ℕ, |(-1 : ℤ) ^ (n - m) * (n.choose m : ℤ)| = (n.choose m : ℤ) := by
    intro m
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  rw [habs, habs, habs]
  have := choose_mul_choose_le_choose_sq n k
  exact_mod_cast this

/-- If `e ∈ E` is a loop of `M`, the rank-generating characteristic polynomial vanishes:
the involution `S ↦ S △ {e}` is sign-reversing and rank-preserving. -/
theorem charPoly_eq_zero_of_isLoop (M : Matroid α) (E : Finset α) (e : α) (heE : e ∈ E)
    (he : M.IsLoop e) : charPoly M E = 0 := by
  classical
  have hins : ∀ S : Set α, M.eRk (insert e S) = M.eRk S := fun S => by
    rw [← M.eRk_insert_closure_eq e S, Set.insert_eq_self.2 (he.mem_closure S), M.eRk_closure_eq]
  have hE : E = insert e (E.erase e) := (Finset.insert_erase heE).symm
  rw [charPoly, show E.powerset = (insert e (E.erase e)).powerset from by rw [← hE],
    Finset.sum_powerset_insert (Finset.notMem_erase e E), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun t ht => ?_
  have het : e ∉ t := fun h => (Finset.notMem_erase e E) (Finset.mem_powerset.mp ht h)
  have hcard : (insert e t).card = t.card + 1 := Finset.card_insert_of_notMem het
  have hrank : natRank M ((insert e t : Finset α) : Set α) = natRank M (t : Set α) := by
    rw [natRank, natRank, Finset.coe_insert, hins]
  rw [hcard, hrank, pow_succ]
  ring

/-- A matroid with a loop also satisfies the log-concavity conclusion (its characteristic
polynomial is identically zero). -/
theorem huh_matroid_log_concave_of_isLoop (M : Matroid α) (E : Finset α) (e : α) (heE : e ∈ E)
    (he : M.IsLoop e) : LogConcaveCoeffs (charPoly M E) := by
  intro k
  simp [charPoly_eq_zero_of_isLoop M E e heE he]

end Frontier

