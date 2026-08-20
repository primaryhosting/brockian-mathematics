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

private lemma ks3_arith {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 : ℕ}
    (h0 : x0 + x4 + x20 = 1) (h1 : x0 + x12 + x25 = 1) (h2 : x0 + x15 + x28 = 1)
    (h3 : x1 + x14 + x26 = 1) (h4 : x2 + x5 + x20 = 1) (h5 : x3 + x6 + x20 = 1)
    (h6 : x4 + x18 + x21 = 1) (h7 : x4 + x19 + x22 = 1) (h8 : x7 + x16 + x24 = 1)
    (h9 : x8 + x10 + x31 = 1) (h10 : x9 + x30 + x32 = 1) (h11 : x11 + x23 + x27 = 1)
    (h12 : x13 + x17 + x29 = 1) (h13 : x0 + x9 ≤ 1) (h14 : x0 + x31 ≤ 1)
    (h15 : x1 + x7 ≤ 1) (h16 : x1 + x20 ≤ 1) (h17 : x2 + x11 ≤ 1)
    (h18 : x2 + x29 ≤ 1) (h19 : x3 + x8 ≤ 1) (h20 : x3 + x32 ≤ 1)
    (h21 : x4 + x17 ≤ 1) (h22 : x4 + x23 ≤ 1) (h23 : x5 + x10 ≤ 1)
    (h24 : x5 + x30 ≤ 1) (h25 : x6 + x13 ≤ 1) (h26 : x6 + x27 ≤ 1)
    (h27 : x7 + x20 ≤ 1) (h28 : x8 + x21 ≤ 1) (h29 : x9 + x31 ≤ 1)
    (h30 : x10 + x19 ≤ 1) (h31 : x11 + x25 ≤ 1) (h32 : x12 + x24 ≤ 1)
    (h33 : x12 + x26 ≤ 1) (h34 : x13 + x25 ≤ 1) (h35 : x14 + x22 ≤ 1)
    (h36 : x14 + x28 ≤ 1) (h37 : x15 + x27 ≤ 1) (h38 : x15 + x29 ≤ 1)
    (h39 : x16 + x18 ≤ 1) (h40 : x16 + x28 ≤ 1) (h41 : x17 + x23 ≤ 1)
    (h42 : x18 + x26 ≤ 1) (h43 : x19 + x32 ≤ 1) (h44 : x21 + x30 ≤ 1)
    (h45 : x22 + x24 ≤ 1)
    : False := by
  rcases t3_cases_a h0 with e0 | e0
  ·
    rcases t3_cases_b h0 with e4 | e4
    ·
      have e20 : x20 = 1 := t3_last_c h0 e0 e4
      have ph4_c := t3_one_c h4 e20
      have e2 : x2 = 0 := ph4_c.1
      have e5 : x5 = 0 := ph4_c.2
      have ph5_c := t3_one_c h5 e20
      have e3 : x3 = 0 := ph5_c.1
      have e6 : x6 = 0 := ph5_c.2
      have e1 : x1 = 0 := p2_b h16 e20
      have e7 : x7 = 0 := p2_b h27 e20
      rcases t3_cases_a h9 with e8 | e8
      ·
        rcases t3_cases_a h10 with e9 | e9
        ·
          rcases t3_cases_b h9 with e10 | e10
          ·
            have e31 : x31 = 1 := t3_last_c h9 e8 e10
            rcases t3_cases_a h11 with e11 | e11
            ·
              rcases t3_cases_b h1 with e12 | e12
              ·
                have e25 : x25 = 1 := t3_last_c h1 e0 e12
                have e13 : x13 = 0 := p2_b h34 e25
                rcases t3_cases_b h3 with e14 | e14
                ·
                  have e26 : x26 = 1 := t3_last_c h3 e1 e14
                  have e18 : x18 = 0 := p2_b h42 e26
                  have e21 : x21 = 1 := t3_last_c h6 e4 e18
                  have e30 : x30 = 0 := p2_a h44 e21
                  have e32 : x32 = 1 := t3_last_c h10 e9 e30
                  have e19 : x19 = 0 := p2_b h43 e32
                  have e22 : x22 = 1 := t3_last_c h7 e4 e19
                  have e24 : x24 = 0 := p2_a h45 e22
                  have e16 : x16 = 1 := t3_last_b h8 e7 e24
                  have e28 : x28 = 0 := p2_a h40 e16
                  have e15 : x15 = 1 := t3_last_b h2 e0 e28
                  have e27 : x27 = 0 := p2_a h37 e15
                  have e29 : x29 = 0 := p2_a h38 e15
                  have e23 : x23 = 1 := t3_last_b h11 e11 e27
                  have e17 : x17 = 1 := t3_last_b h12 e13 e29
                  exact p2_false h41 e17 e23
                ·
                  have ph3_b := t3_one_b h3 e14
                  have e26 : x26 = 0 := ph3_b.2
                  have e22 : x22 = 0 := p2_a h35 e14
                  have e28 : x28 = 0 := p2_a h36 e14
                  have e15 : x15 = 1 := t3_last_b h2 e0 e28
                  have e19 : x19 = 1 := t3_last_b h7 e4 e22
                  have e27 : x27 = 0 := p2_a h37 e15
                  have e29 : x29 = 0 := p2_a h38 e15
                  have e32 : x32 = 0 := p2_a h43 e19
                  have e30 : x30 = 1 := t3_last_b h10 e9 e32
                  have e23 : x23 = 1 := t3_last_b h11 e11 e27
                  have e17 : x17 = 1 := t3_last_b h12 e13 e29
                  exact p2_false h41 e17 e23
              ·
                have ph1_b := t3_one_b h1 e12
                have e25 : x25 = 0 := ph1_b.2
                have e24 : x24 = 0 := p2_a h32 e12
                have e26 : x26 = 0 := p2_a h33 e12
                have e14 : x14 = 1 := t3_last_b h3 e1 e26
                have e16 : x16 = 1 := t3_last_b h8 e7 e24
                have e22 : x22 = 0 := p2_a h35 e14
                have e28 : x28 = 0 := p2_a h36 e14
                have e18 : x18 = 0 := p2_a h39 e16
                have e15 : x15 = 1 := t3_last_b h2 e0 e28
                have e21 : x21 = 1 := t3_last_c h6 e4 e18
                have e19 : x19 = 1 := t3_last_b h7 e4 e22
                have e27 : x27 = 0 := p2_a h37 e15
                have e29 : x29 = 0 := p2_a h38 e15
                have e32 : x32 = 0 := p2_a h43 e19
                have e30 : x30 = 0 := p2_a h44 e21
                exact t3_false h10 e9 e30 e32
            ·
              have ph11_a := t3_one_a h11 e11
              have e23 : x23 = 0 := ph11_a.1
              have e27 : x27 = 0 := ph11_a.2
              have e25 : x25 = 0 := p2_a h31 e11
              have e12 : x12 = 1 := t3_last_b h1 e0 e25
              have e24 : x24 = 0 := p2_a h32 e12
              have e26 : x26 = 0 := p2_a h33 e12
              have e14 : x14 = 1 := t3_last_b h3 e1 e26
              have e16 : x16 = 1 := t3_last_b h8 e7 e24
              have e22 : x22 = 0 := p2_a h35 e14
              have e28 : x28 = 0 := p2_a h36 e14
              have e18 : x18 = 0 := p2_a h39 e16
              have e15 : x15 = 1 := t3_last_b h2 e0 e28
              have e21 : x21 = 1 := t3_last_c h6 e4 e18
              have e19 : x19 = 1 := t3_last_b h7 e4 e22
              have e29 : x29 = 0 := p2_a h38 e15
              have e32 : x32 = 0 := p2_a h43 e19
              have e30 : x30 = 0 := p2_a h44 e21
              exact t3_false h10 e9 e30 e32
          ·
            have ph9_b := t3_one_b h9 e10
            have e31 : x31 = 0 := ph9_b.2
            have e19 : x19 = 0 := p2_a h30 e10
            have e22 : x22 = 1 := t3_last_c h7 e4 e19
            have e14 : x14 = 0 := p2_b h35 e22
            have e24 : x24 = 0 := p2_a h45 e22
            have e26 : x26 = 1 := t3_last_c h3 e1 e14
            have e16 : x16 = 1 := t3_last_b h8 e7 e24
            have e12 : x12 = 0 := p2_b h33 e26
            have e18 : x18 = 0 := p2_a h39 e16
            have e28 : x28 = 0 := p2_a h40 e16
            have e25 : x25 = 1 := t3_last_c h1 e0 e12
            have e15 : x15 = 1 := t3_last_b h2 e0 e28
            have e21 : x21 = 1 := t3_last_c h6 e4 e18
            have e11 : x11 = 0 := p2_b h31 e25
            have e13 : x13 = 0 := p2_b h34 e25
            have e27 : x27 = 0 := p2_a h37 e15
            have e29 : x29 = 0 := p2_a h38 e15
            have e30 : x30 = 0 := p2_a h44 e21
            have e32 : x32 = 1 := t3_last_c h10 e9 e30
            have e23 : x23 = 1 := t3_last_b h11 e11 e27
            have e17 : x17 = 1 := t3_last_b h12 e13 e29
            exact p2_false h41 e17 e23
        ·
          have ph10_a := t3_one_a h10 e9
          have e30 : x30 = 0 := ph10_a.1
          have e32 : x32 = 0 := ph10_a.2
          have e31 : x31 = 0 := p2_a h29 e9
          have e10 : x10 = 1 := t3_last_b h9 e8 e31
          have e19 : x19 = 0 := p2_a h30 e10
          have e22 : x22 = 1 := t3_last_c h7 e4 e19
          have e14 : x14 = 0 := p2_b h35 e22
          have e24 : x24 = 0 := p2_a h45 e22
          have e26 : x26 = 1 := t3_last_c h3 e1 e14
          have e16 : x16 = 1 := t3_last_b h8 e7 e24
          have e12 : x12 = 0 := p2_b h33 e26
          have e18 : x18 = 0 := p2_a h39 e16
          have e28 : x28 = 0 := p2_a h40 e16
          have e25 : x25 = 1 := t3_last_c h1 e0 e12
          have e15 : x15 = 1 := t3_last_b h2 e0 e28
          have e21 : x21 = 1 := t3_last_c h6 e4 e18
          have e11 : x11 = 0 := p2_b h31 e25
          have e13 : x13 = 0 := p2_b h34 e25
          have e27 : x27 = 0 := p2_a h37 e15
          have e29 : x29 = 0 := p2_a h38 e15
          have e23 : x23 = 1 := t3_last_b h11 e11 e27
          have e17 : x17 = 1 := t3_last_b h12 e13 e29
          exact p2_false h41 e17 e23
      ·
        have ph9_a := t3_one_a h9 e8
        have e10 : x10 = 0 := ph9_a.1
        have e31 : x31 = 0 := ph9_a.2
        have e21 : x21 = 0 := p2_a h28 e8
        have e18 : x18 = 1 := t3_last_b h6 e4 e21
        have e16 : x16 = 0 := p2_b h39 e18
        have e26 : x26 = 0 := p2_a h42 e18
        have e14 : x14 = 1 := t3_last_b h3 e1 e26
        have e24 : x24 = 1 := t3_last_c h8 e7 e16
        have e12 : x12 = 0 := p2_b h32 e24
        have e22 : x22 = 0 := p2_a h35 e14
        have e28 : x28 = 0 := p2_a h36 e14
        have e25 : x25 = 1 := t3_last_c h1 e0 e12
        have e15 : x15 = 1 := t3_last_b h2 e0 e28
        have e19 : x19 = 1 := t3_last_b h7 e4 e22
        have e11 : x11 = 0 := p2_b h31 e25
        have e13 : x13 = 0 := p2_b h34 e25
        have e27 : x27 = 0 := p2_a h37 e15
        have e29 : x29 = 0 := p2_a h38 e15
        have e32 : x32 = 0 := p2_a h43 e19
        have e23 : x23 = 1 := t3_last_b h11 e11 e27
        have e17 : x17 = 1 := t3_last_b h12 e13 e29
        exact p2_false h41 e17 e23
    ·
      have ph0_b := t3_one_b h0 e4
      have e20 : x20 = 0 := ph0_b.2
      have ph6_a := t3_one_a h6 e4
      have e18 : x18 = 0 := ph6_a.1
      have e21 : x21 = 0 := ph6_a.2
      have ph7_a := t3_one_a h7 e4
      have e19 : x19 = 0 := ph7_a.1
      have e22 : x22 = 0 := ph7_a.2
      have e17 : x17 = 0 := p2_a h21 e4
      have e23 : x23 = 0 := p2_a h22 e4
      rcases t3_cases_a h3 with e1 | e1
      ·
        rcases t3_cases_a h4 with e2 | e2
        ·
          have e5 : x5 = 1 := t3_last_b h4 e2 e20
          have e10 : x10 = 0 := p2_a h23 e5
          have e30 : x30 = 0 := p2_a h24 e5
          rcases t3_cases_a h5 with e3 | e3
          ·
            have e6 : x6 = 1 := t3_last_b h5 e3 e20
            have e13 : x13 = 0 := p2_a h25 e6
            have e27 : x27 = 0 := p2_a h26 e6
            have e11 : x11 = 1 := t3_last_a h11 e23 e27
            have e29 : x29 = 1 := t3_last_c h12 e13 e17
            have e25 : x25 = 0 := p2_a h31 e11
            have e15 : x15 = 0 := p2_b h38 e29
            have e12 : x12 = 1 := t3_last_b h1 e0 e25
            have e28 : x28 = 1 := t3_last_c h2 e0 e15
            have e24 : x24 = 0 := p2_a h32 e12
            have e26 : x26 = 0 := p2_a h33 e12
            have e14 : x14 = 0 := p2_b h36 e28
            have e16 : x16 = 0 := p2_b h40 e28
            exact t3_false h3 e1 e14 e26
          ·
            have ph5_a := t3_one_a h5 e3
            have e6 : x6 = 0 := ph5_a.1
            have e8 : x8 = 0 := p2_a h19 e3
            have e32 : x32 = 0 := p2_a h20 e3
            have e31 : x31 = 1 := t3_last_c h9 e8 e10
            have e9 : x9 = 1 := t3_last_a h10 e30 e32
            exact p2_false h29 e9 e31
        ·
          have ph4_a := t3_one_a h4 e2
          have e5 : x5 = 0 := ph4_a.1
          have e11 : x11 = 0 := p2_a h17 e2
          have e29 : x29 = 0 := p2_a h18 e2
          have e27 : x27 = 1 := t3_last_c h11 e11 e23
          have e13 : x13 = 1 := t3_last_a h12 e17 e29
          have e6 : x6 = 0 := p2_b h25 e13
          have e25 : x25 = 0 := p2_a h34 e13
          have e15 : x15 = 0 := p2_b h37 e27
          have e12 : x12 = 1 := t3_last_b h1 e0 e25
          have e28 : x28 = 1 := t3_last_c h2 e0 e15
          have e3 : x3 = 1 := t3_last_a h5 e6 e20
          have e8 : x8 = 0 := p2_a h19 e3
          have e32 : x32 = 0 := p2_a h20 e3
          have e24 : x24 = 0 := p2_a h32 e12
          have e26 : x26 = 0 := p2_a h33 e12
          have e14 : x14 = 0 := p2_b h36 e28
          have e16 : x16 = 0 := p2_b h40 e28
          exact t3_false h3 e1 e14 e26
      ·
        have ph3_a := t3_one_a h3 e1
        have e14 : x14 = 0 := ph3_a.1
        have e26 : x26 = 0 := ph3_a.2
        have e7 : x7 = 0 := p2_a h15 e1
        rcases t3_cases_a h4 with e2 | e2
        ·
          have e5 : x5 = 1 := t3_last_b h4 e2 e20
          have e10 : x10 = 0 := p2_a h23 e5
          have e30 : x30 = 0 := p2_a h24 e5
          rcases t3_cases_a h5 with e3 | e3
          ·
            have e6 : x6 = 1 := t3_last_b h5 e3 e20
            have e13 : x13 = 0 := p2_a h25 e6
            have e27 : x27 = 0 := p2_a h26 e6
            have e11 : x11 = 1 := t3_last_a h11 e23 e27
            have e29 : x29 = 1 := t3_last_c h12 e13 e17
            have e25 : x25 = 0 := p2_a h31 e11
            have e15 : x15 = 0 := p2_b h38 e29
            have e12 : x12 = 1 := t3_last_b h1 e0 e25
            have e28 : x28 = 1 := t3_last_c h2 e0 e15
            have e24 : x24 = 0 := p2_a h32 e12
            have e16 : x16 = 0 := p2_b h40 e28
            exact t3_false h8 e7 e16 e24
          ·
            have ph5_a := t3_one_a h5 e3
            have e6 : x6 = 0 := ph5_a.1
            have e8 : x8 = 0 := p2_a h19 e3
            have e32 : x32 = 0 := p2_a h20 e3
            have e31 : x31 = 1 := t3_last_c h9 e8 e10
            have e9 : x9 = 1 := t3_last_a h10 e30 e32
            exact p2_false h29 e9 e31
        ·
          have ph4_a := t3_one_a h4 e2
          have e5 : x5 = 0 := ph4_a.1
          have e11 : x11 = 0 := p2_a h17 e2
          have e29 : x29 = 0 := p2_a h18 e2
          have e27 : x27 = 1 := t3_last_c h11 e11 e23
          have e13 : x13 = 1 := t3_last_a h12 e17 e29
          have e6 : x6 = 0 := p2_b h25 e13
          have e25 : x25 = 0 := p2_a h34 e13
          have e15 : x15 = 0 := p2_b h37 e27
          have e12 : x12 = 1 := t3_last_b h1 e0 e25
          have e28 : x28 = 1 := t3_last_c h2 e0 e15
          have e3 : x3 = 1 := t3_last_a h5 e6 e20
          have e8 : x8 = 0 := p2_a h19 e3
          have e32 : x32 = 0 := p2_a h20 e3
          have e24 : x24 = 0 := p2_a h32 e12
          have e16 : x16 = 0 := p2_b h40 e28
          exact t3_false h8 e7 e16 e24
  ·
    have ph0_a := t3_one_a h0 e0
    have e4 : x4 = 0 := ph0_a.1
    have e20 : x20 = 0 := ph0_a.2
    have ph1_a := t3_one_a h1 e0
    have e12 : x12 = 0 := ph1_a.1
    have e25 : x25 = 0 := ph1_a.2
    have ph2_a := t3_one_a h2 e0
    have e15 : x15 = 0 := ph2_a.1
    have e28 : x28 = 0 := ph2_a.2
    have e9 : x9 = 0 := p2_a h13 e0
    have e31 : x31 = 0 := p2_a h14 e0
    rcases t3_cases_a h3 with e1 | e1
    ·
      rcases t3_cases_a h4 with e2 | e2
      ·
        have e5 : x5 = 1 := t3_last_b h4 e2 e20
        have e10 : x10 = 0 := p2_a h23 e5
        have e30 : x30 = 0 := p2_a h24 e5
        have e8 : x8 = 1 := t3_last_a h9 e10 e31
        have e32 : x32 = 1 := t3_last_c h10 e9 e30
        have e3 : x3 = 0 := p2_b h19 e8
        have e21 : x21 = 0 := p2_a h28 e8
        have e19 : x19 = 0 := p2_b h43 e32
        have e6 : x6 = 1 := t3_last_b h5 e3 e20
        have e18 : x18 = 1 := t3_last_b h6 e4 e21
        have e22 : x22 = 1 := t3_last_c h7 e4 e19
        have e13 : x13 = 0 := p2_a h25 e6
        have e27 : x27 = 0 := p2_a h26 e6
        have e14 : x14 = 0 := p2_b h35 e22
        have e16 : x16 = 0 := p2_b h39 e18
        have e26 : x26 = 0 := p2_a h42 e18
        have e24 : x24 = 0 := p2_a h45 e22
        exact t3_false h3 e1 e14 e26
      ·
        have ph4_a := t3_one_a h4 e2
        have e5 : x5 = 0 := ph4_a.1
        have e11 : x11 = 0 := p2_a h17 e2
        have e29 : x29 = 0 := p2_a h18 e2
        rcases t3_cases_a h5 with e3 | e3
        ·
          have e6 : x6 = 1 := t3_last_b h5 e3 e20
          have e13 : x13 = 0 := p2_a h25 e6
          have e27 : x27 = 0 := p2_a h26 e6
          have e23 : x23 = 1 := t3_last_b h11 e11 e27
          have e17 : x17 = 1 := t3_last_b h12 e13 e29
          exact p2_false h41 e17 e23
        ·
          have ph5_a := t3_one_a h5 e3
          have e6 : x6 = 0 := ph5_a.1
          have e8 : x8 = 0 := p2_a h19 e3
          have e32 : x32 = 0 := p2_a h20 e3
          have e10 : x10 = 1 := t3_last_b h9 e8 e31
          have e30 : x30 = 1 := t3_last_b h10 e9 e32
          have e19 : x19 = 0 := p2_a h30 e10
          have e21 : x21 = 0 := p2_b h44 e30
          have e18 : x18 = 1 := t3_last_b h6 e4 e21
          have e22 : x22 = 1 := t3_last_c h7 e4 e19
          have e14 : x14 = 0 := p2_b h35 e22
          have e16 : x16 = 0 := p2_b h39 e18
          have e26 : x26 = 0 := p2_a h42 e18
          have e24 : x24 = 0 := p2_a h45 e22
          exact t3_false h3 e1 e14 e26
    ·
      have ph3_a := t3_one_a h3 e1
      have e14 : x14 = 0 := ph3_a.1
      have e26 : x26 = 0 := ph3_a.2
      have e7 : x7 = 0 := p2_a h15 e1
      rcases t3_cases_a h4 with e2 | e2
      ·
        have e5 : x5 = 1 := t3_last_b h4 e2 e20
        have e10 : x10 = 0 := p2_a h23 e5
        have e30 : x30 = 0 := p2_a h24 e5
        have e8 : x8 = 1 := t3_last_a h9 e10 e31
        have e32 : x32 = 1 := t3_last_c h10 e9 e30
        have e3 : x3 = 0 := p2_b h19 e8
        have e21 : x21 = 0 := p2_a h28 e8
        have e19 : x19 = 0 := p2_b h43 e32
        have e6 : x6 = 1 := t3_last_b h5 e3 e20
        have e18 : x18 = 1 := t3_last_b h6 e4 e21
        have e22 : x22 = 1 := t3_last_c h7 e4 e19
        have e13 : x13 = 0 := p2_a h25 e6
        have e27 : x27 = 0 := p2_a h26 e6
        have e16 : x16 = 0 := p2_b h39 e18
        have e24 : x24 = 0 := p2_a h45 e22
        exact t3_false h8 e7 e16 e24
      ·
        have ph4_a := t3_one_a h4 e2
        have e5 : x5 = 0 := ph4_a.1
        have e11 : x11 = 0 := p2_a h17 e2
        have e29 : x29 = 0 := p2_a h18 e2
        rcases t3_cases_a h5 with e3 | e3
        ·
          have e6 : x6 = 1 := t3_last_b h5 e3 e20
          have e13 : x13 = 0 := p2_a h25 e6
          have e27 : x27 = 0 := p2_a h26 e6
          have e23 : x23 = 1 := t3_last_b h11 e11 e27
          have e17 : x17 = 1 := t3_last_b h12 e13 e29
          exact p2_false h41 e17 e23
        ·
          have ph5_a := t3_one_a h5 e3
          have e6 : x6 = 0 := ph5_a.1
          have e8 : x8 = 0 := p2_a h19 e3
          have e32 : x32 = 0 := p2_a h20 e3
          have e10 : x10 = 1 := t3_last_b h9 e8 e31
          have e30 : x30 = 1 := t3_last_b h10 e9 e32
          have e19 : x19 = 0 := p2_a h30 e10
          have e21 : x21 = 0 := p2_b h44 e30
          have e18 : x18 = 1 := t3_last_b h6 e4 e21
          have e22 : x22 = 1 := t3_last_c h7 e4 e19
          have e16 : x16 = 0 := p2_b h39 e18
          have e24 : x24 = 0 := p2_a h45 e22
          exact t3_false h8 e7 e16 e24

/-- **Kochen–Specker theorem**, dimension three: there is no assignment of truth values to
the unit vectors of `ℝ³` giving exactly one `true` in every orthonormal basis. -/
