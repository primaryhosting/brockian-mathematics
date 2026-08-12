/-
# Van Der Waerden
Category: Frontier Math
Target: Math2.van_der_waerden
Statement: Any finite coloring of ℕ has arbitrarily long monochromatic APs (van der Waerden).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math2

/-- `HasAP c m N` says the coloring `c` admits a monochromatic arithmetic progression of
length `m` with positive common difference, contained (together with a little slack) in
`[0, N]`. -/
@[reducible] def HasAP {K : Type*} (c : ℕ → K) (m N : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a + m * d ≤ N ∧ ∀ i < m, c (a + i * d) = c a

/-- `FanFamily c k s N` says there are `s` monochromatic arithmetic progressions of length `k`,
pairwise of different colors, all "focused" at a common point `f ≤ N`. -/
@[reducible] def FanFamily {K : Type*} (c : ℕ → K) (k s N : ℕ) : Prop :=
  ∃ (f : ℕ) (a d : ℕ → ℕ), f ≤ N ∧ (∀ j < s, 0 < d j) ∧
    (∀ j < s, a j + k * d j = f) ∧
    (∀ j < s, ∀ i < k, c (a j + i * d j) = c (a j)) ∧
    (∀ i < s, ∀ j < s, c (a i) = c (a j) → i = j)

/-- The finitary van der Waerden statement for progressions of length `k`. -/
def VDW (k : ℕ) : Prop :=
  ∀ (L : Type) [Finite L], ∃ N : ℕ, ∀ c : ℕ → L, HasAP c k N

theorem vdw_one : VDW 1 := by
  intro L _
  refine ⟨1, fun c => ⟨0, 1, one_pos, by omega, ?_⟩⟩
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

/-- The color-focusing induction: assuming van der Waerden for length `k`, for every `s` there
is a bound `N` such that every coloring either has a monochromatic AP of length `k+1` or
`s` focused monochromatic APs of length `k` with distinct colors. -/
theorem fan_induction {K : Type} [Finite K] {k : ℕ} (hk : 1 ≤ k) (Wk : VDW k) (s : ℕ) :
    ∃ N : ℕ, ∀ c : ℕ → K, HasAP c (k + 1) N ∨ FanFamily c k s N := by
  induction s with
  | zero =>
    refine ⟨0, fun c => Or.inr ⟨0, fun _ => 0, fun _ => 0, le_rfl, ?_, ?_, ?_, ?_⟩⟩ <;> simp
  | succ s ih =>
    obtain ⟨Ns, hNs⟩ := ih
    set B := Ns + 1 with hBdef
    have hBpos : 0 < B := by omega
    obtain ⟨M, hM⟩ := Wk (Fin B → K)
    refine ⟨(M + 2) * B, fun c => ?_⟩
    obtain ⟨b, e, he, hbM, hblocks⟩ := hM (fun t i => c (t * B + i))
    have hb : b ≤ M := by omega
    have hbB : b * B ≤ M * B := Nat.mul_le_mul_right B hb
    have hMB : (M + 2) * B = M * B + 2 * B := by ring
    -- transfer of colors between blocks with the same pattern
    have key : ∀ i, i < k → ∀ x, x < B → c ((b + i * e) * B + x) = c (b * B + x) := by
      intro i hi x hx
      have h := congrFun (hblocks i hi) (⟨x, hx⟩ : Fin B)
      simpa using h
    rcases hNs (fun x => c (b * B + x)) with hAP | hFan
    · -- a monochromatic AP of length `k+1` inside the block, translated back
      obtain ⟨a, d, hd, hbound, hmono⟩ := hAP
      refine Or.inl ⟨b * B + a, d, hd, ?_, ?_⟩
      · omega
      · intro i hi
        have h1 : b * B + a + i * d = b * B + (a + i * d) := by ring
        rw [h1]
        exact hmono i hi
    · obtain ⟨f, a, d, hfN, hdpos, hfocus, hmonof, hinj⟩ := hFan
      by_cases hcol : ∃ j < s, c (b * B + f) = c (b * B + a j)
      · -- the focus has the color of one of the fans: extend that fan
        obtain ⟨j, hj, hcj⟩ := hcol
        have hfj : a j + k * d j = f := hfocus j hj
        have hdle : d j ≤ k * d j := Nat.le_mul_of_pos_left _ hk
        have hexp : (k + 1) * d j = k * d j + d j := by ring
        refine Or.inl ⟨b * B + a j, d j, hdpos j hj, by omega, ?_⟩
        intro i hi
        rcases Nat.lt_or_ge i k with hik | hik
        · have h1 : b * B + a j + i * d j = b * B + (a j + i * d j) := by ring
          rw [h1]
          exact hmonof j hj i hik
        · have hik' : i = k := by omega
          subst hik'
          have h1 : b * B + a j + i * d j = b * B + f := by rw [← hfj]; ring
          rw [h1]
          exact hcj
      · -- otherwise we get one more fan, focused at the same point
        push_neg at hcol
        refine Or.inr ⟨b * B + f + k * (e * B),
          fun j => if j = s then b * B + f else b * B + a j,
          fun j => if j = s then e * B else d j + e * B, ?_, ?_, ?_, ?_, ?_⟩
        · have hexp : b * B + f + k * (e * B) = (b + k * e) * B + f := by ring
          have hle : (b + k * e) * B ≤ M * B := Nat.mul_le_mul_right B hbM
          omega
        · intro j hj
          by_cases hjs : j = s
          · simp only [hjs, if_true]
            exact Nat.mul_pos he hBpos
          · simp only [if_neg hjs]
            have := hdpos j (by omega)
            omega
        · intro j hj
          by_cases hjs : j = s
          · simp only [hjs, if_true]
          · simp only [if_neg hjs]
            have h1 : b * B + a j + k * (d j + e * B)
                = b * B + (a j + k * d j) + k * (e * B) := by ring
            rw [h1, hfocus j (by omega)]
        · intro j hj i hi
          by_cases hjs : j = s
          · simp only [hjs, if_true]
            have h1 : b * B + f + i * (e * B) = (b + i * e) * B + f := by ring
            rw [h1]
            exact key i hi f (by omega)
          · simp only [if_neg hjs]
            have hjs' : j < s := by omega
            have hfj : a j + k * d j = f := hfocus j hjs'
            have hlt : a j + i * d j < B := by
              have : i * d j ≤ k * d j := Nat.mul_le_mul_right _ (le_of_lt hi)
              omega
            have h1 : b * B + a j + i * (d j + e * B)
                = (b + i * e) * B + (a j + i * d j) := by ring
            rw [h1, key i hi (a j + i * d j) hlt]
            exact hmonof j hjs' i hi
        · intro i hi j hj hij
          by_cases his : i = s <;> by_cases hjs : j = s
          · omega
          · simp only [his, if_true, if_neg hjs] at hij
            exact absurd hij (hcol j (by omega))
          · simp only [hjs, if_true, if_neg his] at hij
            exact absurd hij.symm (hcol i (by omega))
          · simp only [if_neg his, if_neg hjs] at hij
            exact hinj i (by omega) j (by omega) hij

theorem vdw_step {k : ℕ} (hk : 1 ≤ k) (Wk : VDW k) : VDW (k + 1) := by
  intro K _
  obtain ⟨N, hN⟩ := fan_induction (K := K) hk Wk (Nat.card K + 1)
  refine ⟨N, fun c => ?_⟩
  rcases hN c with h | ⟨f, a, d, _, _, _, _, hinj⟩
  · exact h
  · exfalso
    have hginj : Function.Injective (fun j : Fin (Nat.card K + 1) => c (a j)) := by
      intro i j hij
      have := hinj i i.isLt j j.isLt hij
      exact Fin.ext this
    have := Nat.card_le_card_of_injective _ hginj
    simp at this

theorem vdw_all (k : ℕ) : VDW k := by
  induction k with
  | zero =>
    intro L _
    exact ⟨1, fun c => ⟨0, 1, one_pos, by omega, fun i hi => absurd hi (by omega)⟩⟩
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact vdw_one
    · exact vdw_step hk ih

/-- **Van der Waerden's theorem.**  For any coloring of `ℕ` by finitely many colors and any
`k`, there is a monochromatic arithmetic progression of length `k` with positive common
difference. -/
theorem van_der_waerden {K : Type*} [Finite K] (c : ℕ → K) (k : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, c (a + i * d) = c a := by
  classical
  let e := Finite.equivFin K
  obtain ⟨N, hN⟩ := vdw_all k (Fin (Nat.card K))
  obtain ⟨a, d, hd, -, hmono⟩ := hN (fun x => e (c x))
  exact ⟨a, d, hd, fun i hi => e.injective (hmono i hi)⟩

end Math2

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

