import Mathlib
/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`
(there are `2 ^ k` of them). -/
abbrev Cube (k : ℕ) : Type := Fin k → ZMod 2

theorem cube_add_self {k : ℕ} (x : Cube k) : x + x = 0 := by
  ext j; simp [CharTwo.add_self_eq_zero]

theorem cube_add_eq_zero_iff {k : ℕ} (x y : Cube k) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have : x + y + y = 0 + y := by rw [h]
    rwa [add_assoc, cube_add_self, add_zero, zero_add] at this
  · rintro rfl
    exact cube_add_self x

/-- The unit vector in direction `i`, i.e. the bit string that is `1` exactly at `i`. -/
def unit {k : ℕ} (i : Fin k) : Cube k := Pi.single i 1

theorem unit_apply_self {k : ℕ} (i : Fin k) : unit i i = 1 := by simp [unit]

theorem unit_apply_ne {k : ℕ} {i j : Fin k} (h : j ≠ i) : unit i j = 0 := by
  simp [unit, h]

theorem unit_injective {k : ℕ} : Function.Injective (unit (k := k)) := by
  intro i j h
  by_contra hne
  have := congrFun h i
  simp [unit, hne] at this

/-- The hypercube graph `Q k`: two bit strings are adjacent when one is obtained from the
other by flipping a single bit (equivalently, when they differ in exactly one coordinate;
see `hypercube_adj_iff`). -/
def hypercube (k : ℕ) : SimpleGraph (Cube k) where
  Adj x y := ∃ i : Fin k, y = x + unit i
  symm := by
    rintro x y ⟨i, rfl⟩
    exact ⟨i, by rw [add_assoc, cube_add_self, add_zero]⟩
  loopless := by
    constructor
    rintro x ⟨i, h⟩
    have h2 : x + unit i = x + 0 := by rw [← h, add_zero]
    have h3 := congrFun (add_left_cancel h2) i
    simp [unit] at h3

instance (k : ℕ) : DecidableRel (hypercube k).Adj := fun x y =>
  decidable_of_iff (∃ i : Fin k, y = x + unit i) Iff.rfl

/-- Faithfulness of the definition: adjacency in `hypercube k` means differing in exactly one
coordinate. -/
theorem hypercube_adj_iff {k : ℕ} (x y : Cube k) :
    (hypercube k).Adj x y ↔ ∃! i : Fin k, x i ≠ y i := by
  have hne : ∀ a : ZMod 2, a ≠ a + 1 := by decide
  have hflip : ∀ a b : ZMod 2, a ≠ b → b = a + 1 := by decide
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_, ?_⟩
    · show x i ≠ (x + unit i) i
      rw [Pi.add_apply, unit_apply_self]
      exact hne (x i)
    · intro j hj
      by_contra hji
      exact hj (by rw [Pi.add_apply, unit_apply_ne hji, add_zero])
  · rintro ⟨i, hi, huniq⟩
    refine ⟨i, ?_⟩
    ext j
    rcases eq_or_ne j i with rfl | hji
    · rw [Pi.add_apply, unit_apply_self]
      exact hflip _ _ hi
    · have hxy : x j = y j := by
        by_contra hc
        exact hji (huniq j hc)
      rw [Pi.add_apply, unit_apply_ne hji, add_zero, hxy]

theorem hypercube_neighborFinset {k : ℕ} (x : Cube k) :
    (hypercube k).neighborFinset x = Finset.image (fun i : Fin k => x + unit i) Finset.univ := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, hypercube, eq_comm]

theorem sum_over_neighbors {k : ℕ} (x : Cube k) (v : Cube k → ℝ) :
    ∑ u ∈ (hypercube k).neighborFinset x, v u = ∑ i : Fin k, v (x + unit i) := by
  rw [hypercube_neighborFinset, Finset.sum_image]
  intro i _ j _ h
  exact unit_injective (add_right_injective x h)

/-- The hypercube is `k`-regular. -/
theorem hypercube_degree {k : ℕ} (x : Cube k) : (hypercube k).degree x = k := by
  rw [SimpleGraph.degree, hypercube_neighborFinset, Finset.card_image_of_injective _
    (fun i j h => unit_injective (add_right_injective x h))]
  simp

/-- The sign character of a bit. -/
def eps (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

theorem eps_zero : eps 0 = 1 := by simp [eps]

theorem eps_one : eps 1 = -1 := by
  simp [eps, show (1 : ZMod 2) ≠ 0 from by decide]

theorem eps_add (a b : ZMod 2) : eps (a + b) = eps a * eps b := by
  have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h a with rfl | rfl <;> rcases h b with rfl | rfl <;>
    simp [eps_zero, eps_one, show (1 : ZMod 2) + 1 = 0 from by decide]

theorem eps_ne_zero (z : ZMod 2) : eps z ≠ 0 := by
  have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h z with rfl | rfl <;> simp [eps_zero, eps_one]

/-- The Fourier character attached to a set `S` of coordinates. -/
def chi {k : ℕ} (S : Finset (Fin k)) (x : Cube k) : ℝ := ∏ i ∈ S, eps (x i)

theorem chi_add {k : ℕ} (S : Finset (Fin k)) (x y : Cube k) :
    chi S (x + y) = chi S x * chi S y := by
  simp [chi, eps_add, Finset.prod_mul_distrib]

theorem chi_ne_zero {k : ℕ} (S : Finset (Fin k)) (x : Cube k) : chi S x ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => eps_ne_zero _

theorem chi_fun_ne_zero {k : ℕ} (S : Finset (Fin k)) : chi S ≠ (0 : Cube k → ℝ) := by
  intro h
  exact chi_ne_zero S 0 (by rw [h]; rfl)

theorem chi_unit {k : ℕ} (S : Finset (Fin k)) (i : Fin k) :
    chi S (unit i) = if i ∈ S then -1 else 1 := by
  unfold chi
  by_cases hi : i ∈ S
  · rw [if_pos hi, ← Finset.prod_erase_mul _ _ hi, unit_apply_self, eps_one,
      Finset.prod_eq_one (fun j hj => ?_), one_mul]
    rw [unit_apply_ne (Finset.ne_of_mem_erase hj), eps_zero]
  · rw [if_neg hi]
    refine Finset.prod_eq_one fun j hj => ?_
    rw [unit_apply_ne (by rintro rfl; exact hi hj), eps_zero]

theorem sum_chi_unit {k : ℕ} (S : Finset (Fin k)) :
    ∑ i : Fin k, chi S (unit i) = (k : ℝ) - 2 * S.card := by
  have h : ∀ i : Fin k, chi S (unit i) = 1 - 2 * (if i ∈ S then (1 : ℝ) else 0) := by
    intro i; rw [chi_unit]; split <;> ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i), Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp

/-- The Laplacian acts on functions by `L v x = k * v x - ∑ i, v (x + e i)`. -/
theorem lap_apply {k : ℕ} (v : Cube k → ℝ) (x : Cube k) :
    ((hypercube k).lapMatrix ℝ).mulVec v x = k * v x - ∑ i : Fin k, v (x + unit i) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, hypercube_degree, sum_over_neighbors]

/-- Characters are eigenvectors: `L χ_S = 2 |S| χ_S`. -/
theorem lap_chi {k : ℕ} (S : Finset (Fin k)) :
    ((hypercube k).lapMatrix ℝ).mulVec (chi S) = (2 * S.card : ℝ) • chi S := by
  funext x
  rw [lap_apply]
  have h : ∀ i : Fin k, chi S (x + unit i) = chi S x * chi S (unit i) :=
    fun i => chi_add S x (unit i)
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum, sum_chi_unit]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Summing all characters at a point: `∑_S χ_S z = 2^k` if `z = 0` and `0` otherwise. -/
theorem sum_chi {k : ℕ} (z : Cube k) :
    ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, chi S z = if z = 0 then (2 ^ k : ℝ) else 0 := by
  have key : ∏ i : Fin k, (eps (z i) + 1)
      = ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, chi S z := by
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl fun S _ => by simp [chi]
  rw [← key]
  by_cases hz : z = 0
  · subst hz
    simp only [Pi.zero_apply, eps_zero]
    norm_num
  · rw [if_neg hz]
    obtain ⟨i, hi⟩ : ∃ i : Fin k, z i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hz (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have hzi : z i = 1 := by
      have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases h (z i) with h' | h'
      · exact absurd h' hi
      · exact h'
    rw [hzi, eps_one]; ring

/-- The Laplacian is symmetric for the standard inner product. -/
theorem lap_symm {k : ℕ} (v w : Cube k → ℝ) :
    ∑ x : Cube k, ((hypercube k).lapMatrix ℝ).mulVec v x * w x
      = ∑ x : Cube k, v x * ((hypercube k).lapMatrix ℝ).mulVec w x := by
  have shift : ∀ u : Cube k, ∑ x : Cube k, v (x + u) * w x
      = ∑ x : Cube k, v x * w (x + u) := by
    intro u
    refine Fintype.sum_equiv (Equiv.addRight u) _ _ ?_
    intro x
    simp only [Equiv.coe_addRight]
    rw [add_assoc, cube_add_self, add_zero]
  have expand : ∑ x : Cube k, ((hypercube k).lapMatrix ℝ).mulVec v x * w x
      = (k : ℝ) * (∑ x : Cube k, v x * w x)
        - ∑ i : Fin k, ∑ x : Cube k, v (x + unit i) * w x := by
    have hx : ∀ x : Cube k, ((hypercube k).lapMatrix ℝ).mulVec v x * w x
        = (k : ℝ) * (v x * w x) - ∑ i : Fin k, v (x + unit i) * w x := by
      intro x
      rw [lap_apply, sub_mul, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
  have expand2 : ∑ x : Cube k, v x * ((hypercube k).lapMatrix ℝ).mulVec w x
      = (k : ℝ) * (∑ x : Cube k, v x * w x)
        - ∑ i : Fin k, ∑ x : Cube k, v x * w (x + unit i) := by
    have hx : ∀ x : Cube k, v x * ((hypercube k).lapMatrix ℝ).mulVec w x
        = (k : ℝ) * (v x * w x) - ∑ i : Fin k, v x * w (x + unit i) := by
      intro x
      rw [lap_apply, mul_sub, Finset.mul_sum]
      ring_nf
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
  rw [expand, expand2]
  congr 1
  exact Finset.sum_congr rfl fun i _ => shift (unit i)

/-- Fourier inversion on the hypercube. -/
theorem fourier_inversion {k : ℕ} (v : Cube k → ℝ) (x : Cube k) :
    ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (∑ y : Cube k, v y * chi S y) * chi S x = (2 ^ k : ℝ) * v x := by
  have step : ∀ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      (∑ y : Cube k, v y * chi S y) * chi S x = ∑ y : Cube k, v y * chi S (y + x) := by
    intro S _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by rw [chi_add]; ring
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  have step2 : ∀ y : Cube k,
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, v y * chi S (y + x)
        = if y = x then (2 ^ k : ℝ) * v y else 0 := by
    intro y
    rw [← Finset.mul_sum, sum_chi]
    rcases eq_or_ne y x with rfl | hne
    · rw [if_pos (cube_add_self y), if_pos rfl]; ring
    · rw [if_neg (fun h => hne ((cube_add_eq_zero_iff y x).mp h)), if_neg hne]; ring
  rw [Finset.sum_congr rfl fun y _ => step2 y]
  simp

/-- Every eigenvalue of the hypercube Laplacian is of the form `2 |S|`. -/
theorem eigenvalue_form {k : ℕ} (mu : ℝ) (v : Cube k → ℝ) (hv : v ≠ 0)
    (hL : ((hypercube k).lapMatrix ℝ).mulVec v = mu • v) :
    ∃ S : Finset (Fin k), mu = 2 * S.card := by
  set c : Finset (Fin k) → ℝ := fun S => ∑ y : Cube k, v y * chi S y with hc
  have key : ∀ S : Finset (Fin k), mu * c S = 2 * S.card * c S := by
    intro S
    have h1 : ∑ x : Cube k, ((hypercube k).lapMatrix ℝ).mulVec v x * chi S x = mu * c S := by
      rw [hc]
      simp only [hL, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    have h2 : ∑ x : Cube k, v x * ((hypercube k).lapMatrix ℝ).mulVec (chi S) x
        = 2 * S.card * c S := by
      simp only [lap_chi, Pi.smul_apply, smul_eq_mul, hc]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [← h1, ← h2]
    exact lap_symm v (chi S)
  obtain ⟨x, hx⟩ : ∃ x : Cube k, v x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  have hsum : ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, c S * chi S x ≠ 0 := by
    rw [fourier_inversion v x]
    exact mul_ne_zero (by positivity) hx
  obtain ⟨S, _, hS⟩ : ∃ S ∈ (Finset.univ : Finset (Fin k)).powerset, c S * chi S x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hsum (Finset.sum_eq_zero hcon)
  have hcS : c S ≠ 0 := fun h => hS (by rw [h]; ring)
  exact ⟨S, mul_right_cancel₀ hcS (key S)⟩

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian of the hypercube graph
`Q k` (which has `2 ^ k` vertices) equals `2`.  In particular the family `(Q k)` has a
spectral gap bounded below by `2`, uniformly in `k`. -/
theorem expander_uniform_gap_witness :
    ∀ k : ℕ, 1 ≤ k →
      IsLeast {mu : ℝ | mu ≠ 0 ∧ ∃ v : Cube k → ℝ, v ≠ 0 ∧
        ((hypercube k).lapMatrix ℝ).mulVec v = mu • v} 2 := by
  intro k hk
  constructor
  · refine ⟨two_ne_zero, chi {(⟨0, hk⟩ : Fin k)}, chi_fun_ne_zero _, ?_⟩
    rw [lap_chi]
    norm_num
  · rintro mu ⟨hmu, v, hv, hL⟩
    obtain ⟨S, rfl⟩ := eigenvalue_form mu v hv hL
    have hScard : S.card ≠ 0 := by
      intro h
      rw [h] at hmu
      simp at hmu
    have h1 : (1 : ℝ) ≤ S.card := by
      have : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr hScard
      exact_mod_cast this
    linarith

/-- The hypercube `Q k` has `2 ^ k` vertices. -/
theorem hypercube_card_vertices (k : ℕ) : Fintype.card (Cube k) = 2 ^ k := by
  simp [Cube]

/-- The uniform gap, spelled out: for every `k ≥ 1` every nonzero Laplacian eigenvalue of the
hypercube `Q k` is at least `2`, with the bound `2` independent of `k` and attained. -/
theorem hypercube_uniform_gap (k : ℕ) (hk : 1 ≤ k) (mu : ℝ) (hmu : mu ≠ 0)
    (v : Cube k → ℝ) (hv : v ≠ 0)
    (hL : ((hypercube k).lapMatrix ℝ).mulVec v = mu • v) : 2 ≤ mu :=
  (expander_uniform_gap_witness k hk).2 ⟨hmu, v, hv, hL⟩

end Frontier.Spectral

