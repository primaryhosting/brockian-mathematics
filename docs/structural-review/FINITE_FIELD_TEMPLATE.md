# The finite-field sign template and the arithmetic gate

16 September 2026. Written proof with named classical inputs. The Lean module
`Brockian.HodgeGramAlgebra` covers only the elementary implication **after** the
sign has been supplied. It does not formalize the surface or Hodge index.

## 1. The object and the primitive space

Fix a smooth projective geometrically connected curve C of genus g over F_q,
where q is a prime power. Form S = C × C over an algebraic closure. Work in the
real vector space of divisor classes modulo numerical equivalence; this quotient
is essential when using the word definite. Choose a geometric point P and put
H = C × {P}, V = {P} × C. The intersection pairing satisfies

\[
H^2=V^2=0,\qquad H\cdot V=1.
\]

The matrix on span(H,V) is [[0,1],[1,0]], with signature (1,1) in the
positive/negative convention. The primitive space for this calculation is

\[
E=\{D:D\cdot H=D\cdot V=0\}.
\]

For every divisor class D define

\[
D'=D-(D\cdot V)H-(D\cdot H)V.
\]

**Projection lemma.** D' lies in E. Expanding the bilinear form gives, for D,F,

\[
D'\cdot F'=D\cdot F
 -(D\cdot H)(F\cdot V)-(D\cdot V)(F\cdot H).
\tag{P}
\]

For example D'·H = D·H − 0 − D·H = 0. In (P), the two positive cross terms
arising from the corrections cancel two of the four negative ones. This is
an algebraic identity and supplies no sign.

## 2. The one step that produces the sign

**Ample-class input.** H+V is ample on C × C: its associated line bundle is the
tensor product of the pullbacks of positive-degree line bundles from the factors.

**Hodge-index input.** The intersection form is negative definite on the
orthogonal complement of an ample class, after numerical equivalence.

Every D in E is perpendicular to H+V. Consequently

\[
B(D,F):=-D\cdot F
\]

is positive definite on E. For any finite list D_0,...,D_n, its Gram matrix is
positive semidefinite, because

\[
\sum_{i,j}c_ic_j B(D_i,D_j)
 = B\left(\sum_i c_iD_i,\sum_i c_iD_i\right)\ge0.
\tag{S}
\]

The matrix need not be positive definite: the listed classes can be dependent.
All principal minors are nonnegative; zero minors are permitted. The sign in
(S) comes from Hodge index, not from point counts or the explicit formula.

This is the geometric setup of Hallouin–Perret, Theorem 1, Definition 2 and
Lemma 3 in [*From Hodge Index Theorem to the number of points of curves over
finite fields*](https://arxiv.org/pdf/1409.2357). Their treatment develops the
higher Gram determinants as well as the two-class bound. The expansion and
worked examples below spell out the normalization used in this review.

## 3. Frobenius intersections, including the diagonal

Let F be q-power Frobenius and Γ_i the graph of F^i, with Γ_0 = Δ. Put
N_r = #C(F_{q^r}) for r ≥ 1. Then

\[
\Gamma_i\cdot H=q^i,\quad \Gamma_i\cdot V=1,\quad
\Gamma_i^2=(2-2g)q^i.
\tag{I1}
\]

The first two equalities are degrees of the projections. The normal bundle of
the graph is (F^i)^*T_C, whose degree is q^i(2−2g); this gives the third.
In particular Δ² = 2−2g, whereas its **primitive projection** has square −2g.

For i<j the projection formula for F^i × id gives

\[
\Gamma_i\cdot\Gamma_j=q^i(\Delta\cdot\Gamma_{j-i})=q^iN_{j-i}.
\tag{I2}
\]

The fixed points of positive Frobenius powers have multiplicity one here:
their differential is zero, so the diagonal and graph meet transversely.
Thus the fixed-point intersection is the actual point count.

Now set D_i = Γ_i − H − q^iV. Applying (P) gives

\[
G_{ij}=D_i\cdot D_j=
\begin{cases}
-2gq^i,&i=j,\\
q^{\min(i,j)}N_{|i-j|}-q^i-q^j,&i\ne j.
\end{cases}
\tag{G}
\]

One may use the off-diagonal expression for every i,j **only after defining
the formal value N_0 := 2−2g**. This value is an Euler characteristic, not
the cardinality of C over a field F_1. The positive Gram matrix is −G.

## 4. From the sign to the Weil bound

Restrict to D_0 and D_r, r≥1. Their positive Gram matrix is

\[
\begin{pmatrix}
2g & q^r+1-N_r\\
q^r+1-N_r & 2gq^r
\end{pmatrix}.
\]

By (S), its determinant is nonnegative. Therefore

\[
(N_r-q^r-1)^2\le4g^2q^r,
\qquad |N_r-q^r-1|\le2gq^{r/2}.
\tag{W}
\]

For g=0, D_0 has zero B-norm and hence is zero in the numerical space, so the
off-diagonal pairing vanishes and N_r=q^r+1. For g>0, the displayed determinant
argument applies directly. Taking square roots uses only q^r>0 and g≥0.
These are the complete sign steps: ample class → Hodge negativity → positive
primitive pairing → Gram minor → absolute-value inequality.

If the target is the absolute values of the reciprocal roots of the curve's
zeta numerator, also name the independent rationality and functional-equation
inputs: Z_C(T)=P_C(T)/((1−T)(1−qT)), deg(P_C)=2g, and roots paired by α↦q/α.
The bounds (W) for every r bound the power sums Σα_j^r by 2gq^{r/2}.
If some |α_j|>√q, the generating series of these power sums has a noncanceling
pole at 1/α_j inside |T|<q^(−1/2), contradicting those coefficient bounds.
Multiplicity is a positive integer and cannot remove this pole. Thus all
|α_j|≤√q; pairing gives equality. A single point count alone would not prove this.

## 5. Two completely specified curves

These exact, hand-checkable examples illustrate (G); they are not evidence for
the number-field RH and do not constitute new numerical pilots.

**Genus 1:** E/F_5, y²=x³−x, with its smooth projective completion. The cubic
has three distinct roots, and the characteristic is neither 2 nor 3. At
x=0,1,2,3,4 the right-hand sides are 0,0,1,4,0, giving 1,1,2,2,1 affine
points respectively. Adding the point at infinity gives N_1=8 and a_1=−2.

\[
-G_1=\begin{pmatrix}2&-2\\-2&10\end{pmatrix},\quad
\det(-G_1)=16,\quad |8-6|\le2\sqrt5.
\]

**Genus 2:** C/F_5, y²=x⁵−x+1, again with smooth projective completion.
The polynomial has derivative −1, so it is square-free. Its odd degree 5
gives genus 2 and one rational point at infinity. For each x in F_5 the
right-hand side is 1, giving ten affine points and N_1=11. Hence

\[
-G_1=\begin{pmatrix}4&-5\\-5&20\end{pmatrix},\quad
\det(-G_1)=55.
\]

The positive determinant proves that these two primitive classes are independent.
This example makes the primitive span nontrivial without importing unidentified
curve data.

## 6. Interpreting the reported v5 witnesses

The v5 archive has not been available in this review. Its reported q=101,
genus-1 determinant 368 is consistent with a_1²=36. Its reported genus-2
data q=31, N_1=45, N_2=987 give, using N_0=−2,

\[
-G_2=\begin{pmatrix}4&-13&-25\\-13&124&-403\\-25&-403&3844\end{pmatrix}.
\]

The 1×1 principal minors are 4,124,3844; the 2×2 minors are
327,14751,314247; the determinant is 267902. These are algebraic consequences
of the supplied counts. They do not verify those counts or identify the curve.

The total first Frobenius trace is **−13**. If t_1,t_2 denote the two
conjugate-pair traces, Newton identities give t_1+t_2=−13 and
t_1²+t_2²=99. Thus t_i=(−13±√29)/2. Each lies in [−2√31,2√31]: the larger
absolute value has square (99+13√29)/2 < 124, since
13√29<149 follows from 169·29<149². The interval applies to each pair trace;
the total trace has the genus-2 bound [−4√31,4√31]. The two traces alone do not
replace the surface sign theorem.

## 7. Six-role gate for the arithmetic route

The following is a comparison test, not a construction of an arithmetic surface.

| Required role | Finite-field object | Obligation for a proposed Spec Z construction |
|---|---|---|
| Space and equivalence | Numerical divisor classes on C×C | Define the arithmetic space of classes, its equivalence relation, and a usable topology |
| Primitive part | Orthogonal complement of H,V | Define the two trivial directions and a genuine projection/quotient removing them |
| Arithmetic action | Graphs of Frobenius powers | Construct correspondences or a flow whose periods and local terms encode the primes |
| Pairing | Symmetric intersection form on numerical classes | Define a real/Hermitian pairing with a domain on which all expressions make sense |
| Sign theorem | Hodge index for the ample class H+V | Prove the needed sign from independently established structure |
| Trace and limiting bridge | Intersection counts and zeta rationality | Prove the exact explicit-formula identity and the global limit without assuming the desired sign |

**Reading of Connes–Consani.** In [*On the Jacobian of Spec Z*](https://alainconnes.org/wp-content/uploads/JNcG2026-1.pdf),
Theorem 1.1 models the Riemann sector by an arithmetic Picard monoid. Theorem
8.15 gives its framed/rooted adelic uniformization. Sections 9.1–9.2 identify
local fixed-point contributions; §9.3, equation (9.5), gives the semilocal
cutoff trace formula. Section 9.4, Theorem 9.1, supplies the sheaf framework.
The introduction suggests relative cohomology of the Picard space and the
generic-point contribution. This does not exhibit the analogue of E together
with its required signed intersection pairing. A Hilbert space used for the
semilocal cutoff is not, by itself, that primitive pairing.

**Decision:** the manuscript provides concrete objects for roles 1 and 3 and
a semilocal contribution to role 6. In this review, roles 2, 4 and 5, and the
global passage needed in role 6, remain unfilled. This is a scope assessment
of the cited manuscript, not a claim that no such construction can exist.

Keep the RH-directed route at **SIGN_GATE_UNMET**. A sign inserted as a
hypothesis makes a conditional reformulation. To open the route, require a
construction filling the six roles and a sign theorem independent of RH or
an equivalent positivity criterion. The next proposal must identify that
specific missing object; analogy or additional cutoff numerics do not pass the gate.

## 8. Formalization boundary

`HodgeGramAlgebra.gram_minor_nonnegative` proves the elementary 2×2 Gram step.
`weil_squared_of_gram_sign` substitutes the Frobenius intersection data, with
`hHodgeGramSign` visible in the theorem statement. `gram_diagonal` checks the
N_0 normalization. The geometric inputs above remain literature inputs;
none has been introduced as a new Lean axiom or advertised as formalized here.
