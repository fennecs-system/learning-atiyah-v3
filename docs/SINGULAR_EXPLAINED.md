# What the singular-family verification checks

The reported construction does not give a convenient list of 84 decimal
coordinates with an exactly zero determinant. Instead it gives a continuous
motion of 84 points and proves that a singular configuration occurs somewhere
strictly inside that motion.

There are four groups: 52 points on an axis, two points off the axis, and
30 further points on the axis. For a parameter t between 0 and 1, the points
are

- ((j−51)t(1−t), 0), for j=0,…,51;
- (31,t);
- (32,32t);
- (33−t+j t(1−t),0), for j=0,…,29.

For every strictly intermediate t, their first coordinates are strictly
ordered, so none of the points collide. They all lie in one plane in ordinary
three-dimensional space.

Each point determines a polynomial formed from its directions toward the
other points. The question is whether these 84 polynomials are linearly
independent. Write their coefficients as a square matrix. Dependence means
that its determinant is zero.

At the two ends of the motion some points collide. We do not call those
endpoints configurations. The chosen *normalized polynomial coefficients*,
however, have well-defined continuous limits there. At the first end the
polynomials are 1,T,…,T^83, giving determinant 1. At the other end a special
algebraic calculation gives a negative determinant. A continuous real
function cannot go from positive to negative without passing through zero.
That crossing lies strictly between the endpoints, where all 84 points are
still distinct.

Why the large calculation is manageable: 82 rows have a very simple form.
Eliminating them leaves a two-by-two determinant. Its entries involve only
sqrt(2) and sqrt(962), so exact integer arithmetic with four coefficients can
check its sign. The Lean argument must also prove that this small calculation
is the same determinant as the original matrix; checking a negative number
alone would not establish a counterexample.

In algebraic-geometric language, the path of polynomial coefficients meets
the determinant divisor. The geometric map uses real lengths and Hopf lifts,
so this statement is about a real geometric incidence construction, not an
unrestricted holomorphic map of complex configuration spaces. The existing
cell interpretation then says that the singular coefficient vectors have a
nonzero common annihilator: the associated signed cones share a line.

This is compatible with the distant-point theorem. That theorem starts with
an independent core and proves independence sufficiently far out along a ray.
It does not say every finite arrangement is independent, nor that any
arbitrary motion to a separated configuration preserves independence.

See [the proof ledger](proofs/SINGULAR_FAMILY.md) for the current checked
status and [the arithmetic certificate](proofs/SINGULAR_CERTIFICATE.md) for
the exact computation. The construction being formalized here is the
84-point specialization, not the full arbitrary-size family in the preprint.
