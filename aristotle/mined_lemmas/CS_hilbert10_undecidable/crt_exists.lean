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

/-
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem crt_exists {q n : ℕ} (hq : (n + 1).factorial ∣ q) (a : ℕ → ℕ) (b : ℕ) :
    ∃ U, b ≤ U ∧ ∀ i ≤ n, U ≡ a i [MOD modAt q i] := by
  have main : ∀ m : ℕ, m ≤ n → ∃ U, ∀ i ≤ m, U ≡ a i [MOD modAt q i] := by
    intro m
    induction m with
    | zero =>
        intro _
        exact ⟨a 0, fun i hi => by
          have : i = 0 := by omega
          subst this
          rfl⟩
    | succ m ih =>
        intro hm
        obtain ⟨U, hU⟩ := ih (by omega)
        have hcop : Nat.Coprime (∏ i ∈ Finset.range (m+1), modAt q i) (modAt q (m+1)) := by
          refine Nat.Coprime.prod_left (fun i hi => ?_)
          simp only [Finset.mem_range] at hi
          exact coprime_modAt hq (by omega) (by omega) (by omega)
        obtain ⟨V, hV1, hV2⟩ := Nat.chineseRemainder hcop U (a (m+1))
        refine ⟨V, fun i hi => ?_⟩
        rcases Nat.lt_or_ge i (m+1) with h | h
        · refine Nat.ModEq.trans ?_ (hU i (by omega))
          exact Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))) hV1
        · have : i = m + 1 := by omega
          subst this
          exact hV2
  obtain ⟨U, hU⟩ := main n le_rfl
  refine ⟨U + (b + 1) * modProd q n, ?_, ?_⟩
  · have h1 : 1 ≤ modProd q n := modProd_pos q n
    calc b ≤ (b+1) * 1 := by omega
      _ ≤ (b+1) * modProd q n := Nat.mul_le_mul_left _ h1
      _ ≤ U + (b+1) * modProd q n := by omega
  · intro i hi
    have hdvd : modAt q i ∣ (b+1) * modProd q n := Dvd.dvd.mul_left (modAt_dvd_modProd hi) _
    have hmod : U ≡ U + (b+1) * modProd q n [MOD modAt q i] :=
      (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2 (by simpa using hdvd)
    exact hmod.symm.trans (hU i hi)

end H10

/-
Binomial coefficients, factorials and products of arithmetic progressions are Diophantine.
-/
import RequestProject.H10.Poly

open Dioph Finset

namespace H10

variable {α : Type}

/-! ### Binomial coefficients -/

