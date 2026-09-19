# General seam holonomy: proof and formalization boundary

Let q,m≥1, h∈Z/m, g=gcd(m,h) (using any integer representative), and
L=q(m/g). On Z/q × Z/m define

P_h(j,d)=(j+1,d+h·[j=−1]).

This is a permutation: decrement j and subtract h exactly if the incoming
residue is 0 to obtain its inverse. During q steps each residue crosses the
seam exactly once. Consequently P_h^q(j,d)=(j,d+h). More generally, writing
j in {0,...,q−1},

\[
P_h^n(j,d)=\left(j+n\pmod q,
 d+\left\lfloor\frac{j+n}{q}\right\rfloor h\pmod m\right).
\]

For a return, the first coordinate forces q|n. Write n=qr. The second
coordinate then forces rh=0 mod m, equivalent to (m/g)|r. The least positive
return time of every state is therefore L. There are qm states, hence g cycles.
This includes h=0: g=m and all m cycles have length q. It also includes q=1.

Let P_h also denote the permutation matrix in the basis of states. Reordering
the basis by its cycles conjugates it to g identical L-cycle blocks. For one
cycle block C_L,

\[
\det(I-zC_L)=1-z^L.
\]

For L≥2 the only nonzero determinant terms are the all-diagonal term 1 and
the full cycle term: (−z)^L times the sign (−1)^(L−1), giving −z^L.
For L=1 the 1×1 matrix is [1−z], so the same formula holds without separating
two entries at the same position. Multiplying the block determinants gives

\[
\boxed{\det(I-zP_h)=(1-z^{qm/g})^g.}
\]

For fixed q,m, this polynomial determines g: its least positive exponent is
qm/g with nonzero coefficient −g. It does not determine the labelled h.

The **residue-only** process j↦j+1 detects no h at all. The **full permutation
up to relabelling**, or its determinant, detects g. A labelled depth observer
π:Z/m→A detects π(h), since π(d+h)=π(d)+π(h). Two holonomies have the same
observed loop translation iff h−k lies in ker π. Quotient observers therefore
form a lattice ordered by factorization. These observer classes must not be
conflated: a determinant observation is richer than the residue marginal.

For m=8, reduction modulo 4 identifies h=1 and h=5 but separates h=1 and
h=3. All three are coprime to 8 and have the same cycle determinant. The
modulo-4 observer adds information that the determinant alone cannot supply,
but by itself does not refine gcd globally (0 and 4 illustrate the issue).
The combined observer O(h)=(gcd(h,8),h mod 4) is strictly more informative than
gcd and strictly less informative than labelled h. This is the precise
counterexample to the earlier dichotomy.

`Brockian.HolonomyObservers` formalizes the general quotient-observer theorem,
translations through arbitrarily many loops, and the order m/gcd(m,h).
`Brockian.HolonomySeam` connects the actual one-step map to the translations:
`one_loop` gives the q-step shift, `completed_loops` gives all multiples of q,
and `seam_return_iff` gives the exact divisibility criterion for a return.
The final kernel receipt is indexed in REVIEW.md.
`SeamDeterminantStatement` records the full one-step determinant target as a
Prop. Its proof still requires the uniform cycle decomposition and a
cycle-block determinant lemma in Lean. Neither the definition nor the finite
(5,6), (3,8), (4,12) pilots closes that formalization gap. The proof above is
the written mathematical result; it has no claim of novelty.
