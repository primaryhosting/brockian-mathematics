import Mathlib

set_option maxHeartbeats 1000000

/-!
# Common machinery for the Kochen–Specker theorem

A *noncontextual hidden-variable assignment* for a quantum system with Hilbert space `E`
assigns to every unit vector (equivalently, to every rank-one projection, i.e. to every
"yes/no question" about the system) a definite truth value, in a way that does not depend on
the context in which the corresponding measurement is performed, and which respects the
quantum-mechanical sum rule: in every complete family of mutually orthogonal rank-one
projections — that is, in every orthonormal basis — exactly one projection is assigned the
value `true`.

We model such an assignment by a function `f : E → Bool`, the sum rule being the hypothesis
`∀ b : Fin n → E, Orthonormal ℝ b → ∃! i, f (b i) = true` (in an `n`-dimensional space an
orthonormal family indexed by `Fin n` is exactly an orthonormal basis).

This file collects the pieces used in dimensions three and four.
-/

namespace Frontier

open scoped RealInnerProductSpace

/-- "Exactly one `true`" in a triple, expressed as a count. -/

theorem kochen_specker_three (f : E3 → Bool)
    (h : ∀ b : Fin 3 → E3, Orthonormal ℝ b → ∃! i, f (b i) = true) : False := by
  have c0 := ks_ctx3 f h r0 r4 r20 nz0 nz4 nz20 o0_4 o0_20 o4_20
  have c1 := ks_ctx3 f h r0 r12 r25 nz0 nz12 nz25 o0_12 o0_25 o12_25
  have c2 := ks_ctx3 f h r0 r15 r28 nz0 nz15 nz28 o0_15 o0_28 o15_28
  have c3 := ks_ctx3 f h r1 r14 r26 nz1 nz14 nz26 o1_14 o1_26 o14_26
  have c4 := ks_ctx3 f h r2 r5 r20 nz2 nz5 nz20 o2_5 o2_20 o5_20
  have c5 := ks_ctx3 f h r3 r6 r20 nz3 nz6 nz20 o3_6 o3_20 o6_20
  have c6 := ks_ctx3 f h r4 r18 r21 nz4 nz18 nz21 o4_18 o4_21 o18_21
  have c7 := ks_ctx3 f h r4 r19 r22 nz4 nz19 nz22 o4_19 o4_22 o19_22
  have c8 := ks_ctx3 f h r7 r16 r24 nz7 nz16 nz24 o7_16 o7_24 o16_24
  have c9 := ks_ctx3 f h r8 r10 r31 nz8 nz10 nz31 o8_10 o8_31 o10_31
  have c10 := ks_ctx3 f h r9 r30 r32 nz9 nz30 nz32 o9_30 o9_32 o30_32
  have c11 := ks_ctx3 f h r11 r23 r27 nz11 nz23 nz27 o11_23 o11_27 o23_27
  have c12 := ks_ctx3 f h r13 r17 r29 nz13 nz17 nz29 o13_17 o13_29 o17_29
  have d0 := ks_pair3 f h r0 r9 nz0 nz9 o0_9
  have d1 := ks_pair3 f h r0 r31 nz0 nz31 o0_31
  have d2 := ks_pair3 f h r1 r7 nz1 nz7 o1_7
  have d3 := ks_pair3 f h r1 r20 nz1 nz20 o1_20
  have d4 := ks_pair3 f h r2 r11 nz2 nz11 o2_11
  have d5 := ks_pair3 f h r2 r29 nz2 nz29 o2_29
  have d6 := ks_pair3 f h r3 r8 nz3 nz8 o3_8
  have d7 := ks_pair3 f h r3 r32 nz3 nz32 o3_32
  have d8 := ks_pair3 f h r4 r17 nz4 nz17 o4_17
  have d9 := ks_pair3 f h r4 r23 nz4 nz23 o4_23
  have d10 := ks_pair3 f h r5 r10 nz5 nz10 o5_10
  have d11 := ks_pair3 f h r5 r30 nz5 nz30 o5_30
  have d12 := ks_pair3 f h r6 r13 nz6 nz13 o6_13
  have d13 := ks_pair3 f h r6 r27 nz6 nz27 o6_27
  have d14 := ks_pair3 f h r7 r20 nz7 nz20 o7_20
  have d15 := ks_pair3 f h r8 r21 nz8 nz21 o8_21
  have d16 := ks_pair3 f h r9 r31 nz9 nz31 o9_31
  have d17 := ks_pair3 f h r10 r19 nz10 nz19 o10_19
  have d18 := ks_pair3 f h r11 r25 nz11 nz25 o11_25
  have d19 := ks_pair3 f h r12 r24 nz12 nz24 o12_24
  have d20 := ks_pair3 f h r12 r26 nz12 nz26 o12_26
  have d21 := ks_pair3 f h r13 r25 nz13 nz25 o13_25
  have d22 := ks_pair3 f h r14 r22 nz14 nz22 o14_22
  have d23 := ks_pair3 f h r14 r28 nz14 nz28 o14_28
  have d24 := ks_pair3 f h r15 r27 nz15 nz27 o15_27
  have d25 := ks_pair3 f h r15 r29 nz15 nz29 o15_29
  have d26 := ks_pair3 f h r16 r18 nz16 nz18 o16_18
  have d27 := ks_pair3 f h r16 r28 nz16 nz28 o16_28
  have d28 := ks_pair3 f h r17 r23 nz17 nz23 o17_23
  have d29 := ks_pair3 f h r18 r26 nz18 nz26 o18_26
  have d30 := ks_pair3 f h r19 r32 nz19 nz32 o19_32
  have d31 := ks_pair3 f h r21 r30 nz21 nz30 o21_30
  have d32 := ks_pair3 f h r22 r24 nz22 nz24 o22_24
  exact ks3_arith c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 d32

end Frontier

import RequestProject.KS3

/-!
# From dimension `n ≥ 3` down to dimension three

Given a noncontextual assignment `f` on `ℝⁿ` with `3 ≤ n`, we produce one on `ℝ³`.

The point to check is that the sum rule survives the restriction.  Apply the sum rule to the
standard basis: exactly one standard basis vector, say `e k`, gets the value `true`.  Choose an
injection `φ : Fin 3 ↪ Fin n` whose image contains `k`, and embed `ℝ³` isometrically into `ℝⁿ`
along `φ`.  Any orthonormal basis of the image, completed by the standard basis vectors `e j`
with `j ∉ range φ` (all of which are `false`, since `k ∈ range φ`), is an orthonormal basis of
`ℝⁿ`; hence exactly one vector of the original basis of `ℝ³` gets the value `true`.
-/

namespace Frontier

open scoped RealInnerProductSpace

/-- The real inner product on `EuclideanSpace ℝ (Fin n)`, in coordinates. -/
