import Mathlib

/-!
# Kraft's inequality

This file proves the Kraft inequality for finite prefix-free binary codes.
It is part of the development of `CS.huffman_optimal`.
-/

namespace CS

open List

/-- A list of binary codewords is prefix-free when no codeword is a prefix of another. -/

theorem kraftL_le_one : ∀ (L : List (List Bool)), PrefixFreeList L → kraftL L ≤ 1 := by
  intro L
  induction hn : lenSum L using Nat.strong_induction_on generalizing L with
  | _ n ih =>
  intro hpf
  subst hn
  by_cases hemp : [] ∈ L
  · -- the empty codeword forces `L = [[]]`
    have hsingle : L = [[]] := by
      rcases List.mem_iff_append.1 hemp with ⟨A, B, rfl⟩
      have hA : A = [] := by
        rcases A with _ | ⟨a, A'⟩
        · rfl
        · exfalso
          rw [PrefixFreeList, List.pairwise_append] at hpf
          have := hpf.2.2 a (List.mem_cons_self ..) [] (List.mem_cons_self ..)
          exact this.2 (List.nil_prefix)
      have hB : B = [] := by
        rcases B with _ | ⟨b, B'⟩
        · rfl
        · exfalso
          subst hA
          simp only [List.nil_append, PrefixFreeList, List.pairwise_cons] at hpf
          exact (hpf.1 b (List.mem_cons_self ..)).1 List.nil_prefix
      subst hA; subst hB; rfl
    rw [hsingle]; simp [kraftL]
  · have hne : ∀ s ∈ L, s ≠ [] := by
      intro s hs hcon; exact hemp (hcon ▸ hs)
    rcases L with _ | ⟨s, L'⟩
    · simp [kraftL]
    · set L := s :: L' with hLdef
      have hlen : 0 < L.length := by simp [hLdef]
      have hsplit := lenSum_split hne
      have h0 : lenSum (child false L) < lenSum L := by omega
      have h1 : lenSum (child true L) < lenSum L := by omega
      have k0 := ih _ h0 (child false L) rfl (prefixFree_child false hpf)
      have k1 := ih _ h1 (child true L) rfl (prefixFree_child true hpf)
      rw [kraftL_split hne]
      linarith

end CS

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

