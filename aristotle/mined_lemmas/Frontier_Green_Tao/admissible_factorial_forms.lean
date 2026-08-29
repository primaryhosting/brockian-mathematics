/-
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier

/-! ## Formalizing the statement -/

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with nonzero common difference `d`. -/

theorem admissible_factorial_forms (k p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, ∀ i < k, ¬ (p ∣ (i * k ! + 1 * n)) := by
  rcases le_or_gt p k with hpk | hpk
  · refine ⟨1, fun i hi hdvd => ?_⟩
    have hfac : p ∣ k ! := Nat.dvd_factorial hp.pos hpk
    have h1 : p ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_left hfac i)).mp (by simpa using hdvd)
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  · haveI : NeZero p := ⟨hp.pos.ne'⟩
    classical
    set S : Finset (ZMod p) := (Finset.range k).image (fun i => -((i * k ! : ℕ) : ZMod p)) with hS
    have hcard : S.card < Fintype.card (ZMod p) := by
      have h1 : S.card ≤ k := le_trans Finset.card_image_le (by simp)
      have h2 : Fintype.card (ZMod p) = p := ZMod.card p
      omega
    have hne : Sᶜ.Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl]; omega
    obtain ⟨n, hn⟩ := hne
    rw [Finset.mem_compl] at hn
    refine ⟨n.val, fun i hi hdvd => hn ?_⟩
    rw [one_mul] at hdvd
    have h0 : ((i * k ! + n.val : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    simp only [hS, Finset.mem_image, Finset.mem_range]
    refine ⟨i, hi, ?_⟩
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id] at h0 ⊢
    linear_combination -h0

/-- Reduction 2: Dickson's conjecture implies the Green–Tao statement. Applying Dickson to the
admissible family `n ↦ i * k ! + n` (`i < k`) produces a `k`-term arithmetic progression of
primes with common difference `k !`. -/
