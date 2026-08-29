import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-!
## Setting

We work with the standard `m`-fold dilated `n`-dimensional simplex

  `Δ = { v : ℕ^{n+1} | v 0 + ... + v n = m }`

described in *partial sum coordinates*: a vertex is encoded by the function
`s : ℕ → ℕ` with `s j = v 0 + ... + v (j-1)`, so that `s 0 = 0`, `s` is monotone,
and `s j = m` for `j > n`.  The barycentric coordinate `v i` is `s (i+1) - s i`.

The triangulation is the classical Freudenthal–Kuhn triangulation: a maximal cell
is given by a base vertex `s` together with an ordering of the `n` coordinates
`1, …, n`; the ordering is encoded by the function `p : ℕ → ℕ` sending a coordinate
`j ∈ [1,n]` to the step `p j ∈ [0,n-1]` at which it is incremented.  The `k`-th
vertex of the cell is then `wv n s p k`.
-/

/-- `Reg n m s` says that `s` encodes a vertex of the `m`-fold dilated standard
`n`-simplex, in partial sum coordinates. -/

lemma isCell_iff {n m : ℕ} {s p : ℕ → ℕ} (hs : Reg n m s) (hp : IsPos n p) :
    IsCell n m s p ↔ ∀ j, 1 ≤ j → j ≤ n → s j = s (j+1) → (j < n ∧ p (j+1) < p j) := by
  constructor
  · rintro ⟨-, -, hcell⟩ j hj1 hj2 hsj
    have hjn : j < n := by
      by_contra hcon
      have hjn : j = n := by omega
      have hk : p j + 1 ≤ n := hp.1 j hj1 hj2
      have := (hcell (p j + 1) hk).2.1 j hj2
      rw [wv_in hj1 hj2, wv_out (Or.inr (show n < j + 1 by omega))] at this
      rw [if_pos (by omega)] at this
      omega
    refine ⟨hjn, ?_⟩
    by_contra hcon
    have hne : p (j+1) ≠ p j := fun hh => by
      have := hp.2.1 (j+1) j (by omega) (by omega) hj1 hj2 hh; omega
    have hlt : p j < p (j+1) := by omega
    have hk : p j + 1 ≤ n := by have := hp.1 (j+1) (by omega) (by omega); omega
    have := (hcell (p j + 1) hk).2.1 j hj2
    rw [wv_in hj1 hj2, wv_in (by omega) (by omega)] at this
    rw [if_pos (by omega), if_neg (by omega)] at this
    omega
  · intro hcrit
    refine ⟨hs, hp, fun k hk => ⟨?_, ?_, ?_⟩⟩
    · rw [wv_out (Or.inl rfl)]; exact hs.1
    · intro j hj
      rcases (by omega : j = 0 ∨ 1 ≤ j) with rfl | hj1
      · rw [wv_out (Or.inl rfl), hs.1]; omega
      · rw [wv_in hj1 hj]
        rcases (by omega : j = n ∨ j + 1 ≤ n) with hjn | hj2
        · rw [wv_out (Or.inr (show n < j + 1 by omega))]
          have hmono := hs.2.1 j hj
          have : s j ≠ s (j+1) := by
            intro hh; have := (hcrit j hj1 hj hh).1; omega
          split <;> omega
        · rw [wv_in (by omega) hj2]
          have hmono := hs.2.1 j hj
          by_cases h1 : p j < k
          · by_cases h2 : p (j+1) < k
            · simp [h1, h2]; omega
            · have : s j ≠ s (j+1) := by
                intro hh; have := (hcrit j hj1 hj hh).2; omega
              simp [h1, h2]; omega
          · simp [h1]; split <;> omega
    · intro j hj
      rw [wv_out (Or.inr hj)]; exact hs.2.2 j hj

end Math

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

