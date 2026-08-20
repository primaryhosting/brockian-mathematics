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

theorem sum_parts_eq_sum_exc {n : ℕ} (hn : 0 < n) :
    ∑ S ∈ parts n, (-1 : ℤ) ^ #S = ∑ S ∈ (parts n).filter Exc, (-1 : ℤ) ^ #S := by
  rw [← Finset.sum_filter_add_sum_filter_not (parts n) Exc]
  have hmemiff : ∀ S, S ∈ (parts n).filter (fun S => ¬ Exc S) ↔ S ∈ parts n ∧ ¬ Exc S := by
    intro S; simp [Finset.mem_filter]
  have hzero : ∑ S ∈ (parts n).filter (fun S => ¬ Exc S), (-1 : ℤ) ^ #S = 0 := by
    refine Finset.sum_involution (fun S _ => franklin S) ?_ ?_ ?_ ?_
    · intro S hSmem
      obtain ⟨hS, hexc⟩ := (hmemiff S).1 hSmem
      exact (franklin_props hS (nonempty_of_mem_parts hn hS) hexc).2.2.2.1
    · intro S hSmem _
      obtain ⟨hS, hexc⟩ := (hmemiff S).1 hSmem
      intro hcon
      have hcon' : franklin S = S := hcon
      have hsign := (franklin_props hS (nonempty_of_mem_parts hn hS) hexc).2.2.2.1
      rw [hcon'] at hsign
      have hne0 : ((-1 : ℤ)) ^ #S ≠ 0 := by positivity
      omega
    · intro S hSmem
      obtain ⟨hS, hexc⟩ := (hmemiff S).1 hSmem
      obtain ⟨h1, h2, h3, h4, h5⟩ := franklin_props hS (nonempty_of_mem_parts hn hS) hexc
      exact (hmemiff _).2 ⟨h1, h3⟩
    · intro S hSmem
      obtain ⟨hS, hexc⟩ := (hmemiff S).1 hSmem
      exact (franklin_props hS (nonempty_of_mem_parts hn hS) hexc).2.2.2.2
  rw [hzero, add_zero]

/-! ### The exceptional configurations are the pentagonal ones -/

