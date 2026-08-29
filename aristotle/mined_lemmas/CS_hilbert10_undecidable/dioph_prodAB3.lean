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

import Mathlib
import RequestProject.H10.Factorial

/-!
# The product `∏_{k=1}^{y} (a + b*k)` is Diophantine

This is the last of the classical auxiliary Diophantine functions needed for the
Davis–Putnam–Robinson elimination of bounded universal quantifiers.

The idea is that modulo a large `N` coprime to `b`, one has
`∏_{k=1}^{y} (a + b k) ≡ b^y ∏_{k=1}^{y} (m + k) = b^y y! binom(m+y, y)`
where `m` is the residue `a * b⁻¹ mod N`.
-/

namespace H10

open Nat Finset Dioph

/-- `prodAB a b y = (a + b) * (a + 2b) * ⋯ * (a + y b)`. -/

theorem dioph_prodAB3 : DiophFn fun v : Vector3 ℕ 3 => prodAB (v &0) (v &1) (v &2) := by
  have dN : DiophFn fun v : Vector3 ℕ 5 => v &3 * ((v &2 + v &3 * v &4 + 1) ^ (v &4) + 1) + 1 :=
    ((D&3) D* ((pow_dioph (((D&2) D+ ((D&3) D* (D&4))) D+ (D.1)) (D&4)) D+ (D.1))) D+ (D.1)
  have inner : Dioph {v : Vector3 ℕ 5 |
      (v &3 * v &0 ≡ v &2 [MOD (v &3 * ((v &2 + v &3 * v &4 + 1) ^ (v &4) + 1) + 1)]) ∧
      v &1 = (v &3 ^ v &4 * ((v &4)! * (v &0 + v &4).choose (v &4)))
        % (v &3 * ((v &2 + v &3 * v &4 + 1) ^ (v &4) + 1) + 1) } :=
    (D≡ ((D&3) D* (D&0)) (D&2) dN) D∧
      ((D&1) D= ((pow_dioph (D&3) (D&4) D* (dioph_factorial (D&4) D*
        dioph_choose ((D&0) D+ (D&4)) (D&4))) D% dN))
  have big : Dioph {v : Vector3 ℕ 4 |
      (v &2 = 0 ∧ v &0 = v &1 ^ v &3) ∨ (0 < v &2 ∧ ∃ m : ℕ,
        (v &2 * m ≡ v &1 [MOD (v &2 * ((v &1 + v &2 * v &3 + 1) ^ (v &3) + 1) + 1)]) ∧
        v &0 = (v &2 ^ v &3 * ((v &3)! * (m + v &3).choose (v &3)))
          % (v &2 * ((v &1 + v &2 * v &3 + 1) ^ (v &3) + 1) + 1)) } :=
    (((D&2) D= (D.0)) D∧ ((D&0) D= (pow_dioph (D&1) (D&3)))) D∨
      (((D.0) D< (D&2)) D∧ ((D∃) 4 inner))
  refine (diophFn_vec _).2 <| Dioph.ext big <| (vectorAll_iff_forall _).1 fun P a b y => ?_
  show ((b = 0 ∧ P = a ^ y) ∨ (0 < b ∧ ∃ m : ℕ,
      (b * m ≡ a [MOD (b * ((a + b * y + 1) ^ y + 1) + 1)]) ∧
      P = (b ^ y * (y ! * (m + y).choose y)) % (b * ((a + b * y + 1) ^ y + 1) + 1)))
    ↔ prodAB a b y = P
  set N := b * ((a + b * y + 1) ^ y + 1) + 1 with hNdef
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hb, m, hm, rfl⟩)
    · exact prodAB_zero a y
    · refine prodAB_eq a b y m N ?_ hm
      have : 1 ≤ b := hb
      nlinarith [Nat.one_le_iff_ne_zero.mpr (pow_ne_zero y (show a + b * y + 1 ≠ 0 by omega))]
  · rintro rfl
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact Or.inl ⟨rfl, prodAB_zero a y⟩
    · refine Or.inr ⟨hb, ?_⟩
      have hNlt : (a + b * y + 1) ^ y < N := by
        have : 1 ≤ b := hb
        nlinarith [Nat.one_le_iff_ne_zero.mpr (pow_ne_zero y (show a + b * y + 1 ≠ 0 by omega))]
      have hN1 : 1 < N := by
        have : 1 ≤ (a + b * y + 1) ^ y := Nat.one_le_pow _ _ (by omega)
        omega
      have hcop : Nat.Coprime b N := by
        rw [hNdef]; simp [Nat.coprime_mul_left_add_right]
      obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hN1
      refine ⟨m' * a, ?_, prodAB_eq a b y (m' * a) N hNlt ?_⟩ <;>
      · have : b * (m' * a) = (b * m') * a := by ring
        rw [this]
        calc (b * m') * a ≡ 1 * a [MOD N] :=
              Nat.ModEq.mul_right a (by unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hN1]; exact hm')
          _ = a := one_mul a

end H10

import Mathlib

/-!
# Base-`B` digits

Extraction of the `k`-th base-`B` digit of a number, and the fact that the digits of
`∑ i ∈ range n, c i * B ^ i` are the `c i`, provided `c i < B`.

This is used both for the Diophantine definition of binomial coefficients and for coding
finite sequences (traces of primitive recursive computations) by a single number.
-/

namespace H10

open Finset

/-- The `k`-th digit of `S` in base `B`. -/
