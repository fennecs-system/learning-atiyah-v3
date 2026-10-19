# Independent geometric attack and boundary reproduction

Status: paper calculations, exploratory numerics, and an exact integer-arithmetic
boundary sign certificate; none are Lean theorems. This
investigation initially used neither the repository strategy nor the other
agents' approaches. The later Eickhoff check was requested explicitly.

## IG1. An exact three-point sum-of-squares identity

Rotate a physical triangle into the equatorial plane of the direction sphere.
Let its three cyclic directed edge roots be `a,b,c`, of modulus one. Rescaling
the individual factors does not affect independence. The polynomials are

```
p1 = (z-a)(z+c), p2 = (z+a)(z-b), p3 = (z+b)(z-c).
```

With rows in coefficient order `z²,z,1`, expansion gives

```
det = (a+b+c)(ab+bc+ca) - 9abc
    = abc (|a+b+c|² - 9)
    = -abc (|a-b|² + |b-c|² + |c-a|²).
```

Thus dependence occurs precisely when `a=b=c`. Actual edges have positive
lengths `r,s,t` satisfying `ra+sb+tc=0`. This excludes that equality, including
collinear configurations: a positive multiple of a nonzero unit vector cannot
be zero. This is a complete paper proof for three points in these conventions.

Exact checks: an equilateral directed triangle has roots `1,ω,ω²` and
determinant `-9`; collinear cyclic roots `1,1,-1` give `8`. The non-geometric
array `a=b=c=1` gives three identical polynomials `z²-1` and determinant zero.
Antipodal reversal alone therefore cannot prove general C1.

## IG2. Why root-count and stability shortcuts are insufficient

Sorting points by a projection gives distinct counts of roots in a hemisphere,
or in the corresponding disk. Distinct counts do not force independence,
even if all roots are real and simple. Exactly,

```
q0 = (z-2)(z-3),
q2 = z²-1/4,
q1 = q0-3q2 = -2z²-5z+27/4.
```

The roots of `q0` are `2,3`, those of `q2` are `±1/2`, and those of `q1` are
`(-5±√79)/4`. Consequently the open unit disk contains respectively zero,
two, and one roots. No root lies on the circle, yet the displayed relation is
an exact dependence. This is a counterexample to the proposed sufficient
root-count criterion, not a geometric counterexample to C1.

## IG3. A valid interpolation/gluing lemma

Let two fixed configurations have sizes `a,b` and independent point forms.
Translate the second cluster to infinity in a fixed direction with linear form
`l`; write `m=Jl`. After continuous nonzero lift choices, the limit forms span

```
l^b Sym^(a-1)(C²)  and  m^a Sym^(b-1)(C²).
```

These subspaces have zero intersection. An element in the intersection would
be divisible by `l^b m^a`, of degree `a+b`, but has degree `a+b-1`; the
independent linear forms `l,m` are relatively prime. Their dimensions sum to
`a+b`. The union of the two limiting bases is therefore a basis. Openness of
independence gives independence for sufficiently separated physical clusters.

The proposed next lemma is the homogeneous direct-sum statement above,
followed by coefficient convergence and openness. The parent has assigned
its formalization separately. This proves hierarchical separated families,
not arbitrary configurations. Claiming nonvanishing throughout a deformation
from that region would reintroduce precisely the missing global assertion.

## IG4. Independent reproduction of the new m=1 boundary calculation

The supplied September 2026 Eickhoff manuscript `singular.txt` was examined
after IG1–IG3. The following is independent numerical support for its boundary
mechanism, not a certification of its full theorem or an interior singular
configuration.

Set `u=d=1`, `v=0`, `b=N`, `R=N+2`,
`x=y=√2-1`, `a=ceil((1+x)N/(2x))`,
`α=√(1+(R-1)²)-(R-1)`, and
`τ=(√(1+(R-1)²)-1)/(R-1)`. At the boundary `t=1`, define

```
L(T) = (1-αT)(1-xT),
A(T) = (T+α)^a (1+yT)^b (1-τT),
B(T) = (T+x)^a (1+T)^b (T+τ).
```

For a polynomial `C`, let `D_C` be the truncation of `C/L` to degrees below
`a`, and set `W_C=(C-LD_C)/T^a`. The boundary determinant is

```
[W_A(y)W_B(1)-W_A(1)W_B(y)]/(1-y).
```

The formulas for individual physical forward and reverse edge factors were
also checked directly against the manuscript's m=1 coordinates; no sign
discrepancy was found in that check.

Using Python's Decimal arithmetic at 100 digits, direct polynomial products,
and the coefficient recurrence below gave:

| N | a | W_A(1)/W_A(y) | W_B(1)/W_B(y) | determinant sign |
|---:|---:|---:|---:|:---:|
| 5 | 9 | 0.3458621558 | 1.858191179 | + |
| 10 | 18 | 0.4625820437 | 2.113360619 | + |
| 20 | 35 | 1.398373783 | 2.599047663 | + |
| 50 | 86 | 126.5146533 | 3.617722707 | − |
| 100 | 171 | 761792.4263 | 4.810594042 | − |
| 200 | 342 | 5.692407562e13 | 6.420710696 | − |

For reproducibility, if `C=Σ c_j T^j` and `C/L=Σ d_j T^j`, use

```
d_j = c_j + (α+x)d_(j-1) - αx d_(j-2),
d_(-1)=d_(-2)=0,
W_C(T)=d_a+(c_(a+1)-αx d_(a-1))T+Σ_(k≥2)c_(a+k)T^k.
```

This avoids subtracting the two nearly equal evaluations `C(s)` and
`L(s)D_C(s)` directly. All four evaluations were positive in the computations.

### Exact boundary certificate implemented

`python scripts/check_boundary_certificate.py` now certifies the case
`N=30,a=52,b=30,n=84,R=32` using 2048-bit dyadic intervals. All arithmetic is
integer arithmetic with outward rounding; `math.isqrt` encloses the radicals.
No floating-point values or external libraries enter the certificate. The
four eliminated evaluations and `1-y` have strictly positive lower endpoints.
After multiplying each coupling factor by `k=31`, the numerator is certified
to lie in the exact interval

```
[-30666146689591218473741, -30666146689591218473740].
```

The original numerator differs by the positive factor `31²`, so its sign is
also strictly negative. The interval multiplication implementation was
independently cross-checked against Python `Fraction` endpoint products on
4,356 interval pairs including positive, negative, and zero-crossing intervals.
The implementation contains the coefficient recurrence above and explicitly
asserts every needed sign. This certificate establishes only the specified
boundary-polynomial sign, not the full geometric counterexample theorem.
An independent agent reviewed the interval operations, the determination of
`a`, the elimination recurrence, and the positive scaling factor and found
them correct. That review is conditional on the input polynomial formulas
and their determinant orientation; it did not independently certify those
geometric bridges.

### Alternative exact number-field certificate

For `N=50`, `a=86,b=50,n=138`, all coefficients lie in
`Q(√2,√2602)`. In particular `α=√2602-51` and
`τ=(√2602-1)/51`. Replace the last factor of A by
`51-(√2602-1)T`, and that of B by `51T+(√2602-1)`.
This positive scaling makes all arithmetic integral in
`Z[√2,√2602]`. Represent elements by four integer coefficients and certify
the final sign using rational enclosures of the radicals. This is a concrete
way to replace numerical evidence by an exact negative endpoint certificate.
One must still verify the continuous family, positive initial determinant,
and endpoint-to-interior sign argument. The clustered boundary itself is not
an admissible distinct-point counterexample.

## Correspondence ledger

| Step | Evidence | Formal status |
|---|---|---|
| IG1 | Explicit determinant expansion and equality analysis | Paper only |
| IG2 | Rational polynomial identity and exact radical root bounds | Paper only |
| IG3 | Divisibility and finite-dimensional openness | Assigned separately |
| IG4 | Decimal exploration; integer dyadic sign certificate for n=84 | Exact executable boundary audit, not Lean |

No general C1 theorem follows from this report. In light of IG4, proving a
global positivity bridge should not be attempted without resolving the new
counterexample claim first.
