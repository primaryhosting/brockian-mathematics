import Mathlib
import RequestProject.Pentagonal

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

/-!
# Euler's pentagonal number theorem

`Math.euler_pentagonal` states the identity of formal power series over `ℤ`
$$\prod_{n = 1}^{\infty} (1 - X^n) = \sum_{k \in \mathbb Z} (-1)^k X^{k(3k-1)/2},$$
where the product and the sum are taken in the `X`-adic (product) topology on `ℤ⟦X⟧`.

`Math.euler_pentagonal_partition` states the corresponding statement for the generating
function of the partition function: the pentagonal series is the multiplicative inverse of
$\sum_{n} p(n) X^n$.

The combinatorial heart of the proof (Franklin's involution) is in
`RequestProject.Pentagonal`.
-/

namespace Math

open PowerSeries Finset Filter
open scoped PowerSeries.WithPiTopology

/-- The pentagonal exponent `k(3k-1)/2`. -/
abbrev pentExp : ℤ → ℕ := Franklin.pentExp

/-- The sign `(-1)^k`. -/
abbrev pentSign : ℤ → ℤ := Franklin.pentSign

/-- The pentagonal series `∑_{k ∈ ℤ} (-1)^k X^{k(3k-1)/2}` as a formal power series over `ℤ`. -/

theorem sum_powerset_filter_eq_sum_parts (d : ℕ) (s : Finset ℕ) (hs : Finset.range d ⊆ s) :
    ∑ t ∈ s.powerset.filter (fun t => ∑ i ∈ t, (i + 1) = d), (-1 : ℤ) ^ (#t)
      = ∑ S ∈ Franklin.parts d, (-1 : ℤ) ^ (#S) := by
  have hinj1 : ∀ (t : Finset ℕ), ∀ x ∈ t, ∀ y ∈ t, x + 1 = y + 1 → x = y := by
    intro t x _ y _ h; omega
  refine Finset.sum_nbij' (fun t => t.image (· + 1)) (fun S => S.image (· - 1)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    refine Franklin.mem_parts.2 ⟨by simp, ?_⟩
    rw [Finset.sum_image (fun x hx y hy h => hinj1 t x hx y hy (by simpa using h))]
    exact ht.2
  · intro S hS
    obtain ⟨h0, hsum⟩ := Franklin.mem_parts.1 hS
    have hpos : ∀ x ∈ S, 1 ≤ x := by
      intro x hx
      rcases Nat.eq_zero_or_pos x with rfl | h
      · exact absurd hx h0
      · exact h
    have hle : ∀ x ∈ S, x ≤ d := by
      intro x hx
      have h2 : x ≤ ∑ i ∈ S, i := by
        simpa using Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
      omega
    have hinj2 : ∀ x ∈ S, ∀ y ∈ S, x - 1 = y - 1 → x = y := by
      intro x hx y hy h
      have := hpos x hx
      have := hpos y hy
      simp only at h
      omega
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      refine hs ?_
      simp only [Finset.mem_range]
      have := hpos x hx
      have := hle x hx
      omega
    · rw [Finset.sum_image (fun x hx y hy h => hinj2 x hx y hy (by simpa using h)), ← hsum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have := hpos x hx
      omega
  · intro t _
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨x + 1, ⟨x, hx, rfl⟩, by omega⟩
  · intro S hS
    obtain ⟨h0, -⟩ := Franklin.mem_parts.1 hS
    have hpos : ∀ x ∈ S, 1 ≤ x := by
      intro x hx
      rcases Nat.eq_zero_or_pos x with rfl | h
      · exact absurd hx h0
      · exact h
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      have h1 := hpos z hz
      show z - 1 + 1 ∈ S
      rwa [Nat.sub_add_cancel h1]
    · intro hx
      exact ⟨x - 1, ⟨x, hx, rfl⟩, by have := hpos x hx; omega⟩
  · intro t _
    congr 1
    rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h)]

/-! ### The two sides as explicit power series -/

/-- The infinite product `∏_{n ≥ 1} (1 - X^n)` has the pentagonal coefficients. -/
