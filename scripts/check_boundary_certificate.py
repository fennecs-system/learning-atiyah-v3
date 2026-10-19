#!/usr/bin/env python3
"""Exact interval audit of Eickhoff's m=1 *boundary* determinant.

No third-party dependencies; no floating-point arithmetic. This is not a
Lean proof and does not by itself certify an interior singular configuration.
Every interval endpoint is an integer divided by 2**bits. Multiplication is
rounded outward with integer floor/ceiling. Radical bounds use integer sqrt.
"""

import argparse
from dataclasses import dataclass
from math import isqrt


SCALE = 1


def ceil_div(a, b):
    assert b > 0
    return -((-a) // b)


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self):
        assert self.lo <= self.hi

    @staticmethod
    def integer(n):
        return Interval(n * SCALE, n * SCALE)

    @staticmethod
    def sqrt_integer(n):
        assert n >= 0
        radicand = n * SCALE * SCALE
        lower = isqrt(radicand)
        upper = lower if lower * lower == radicand else lower + 1
        assert lower * lower <= radicand <= upper * upper
        return Interval(lower, upper)

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        products = (self.lo * other.lo, self.lo * other.hi,
                    self.hi * other.lo, self.hi * other.hi)
        return Interval(min(products) // SCALE,
                        ceil_div(max(products), SCALE))

    def divide_integer(self, denominator):
        assert denominator > 0
        return Interval(self.lo // denominator,
                        ceil_div(self.hi, denominator))


def multiply_linear(poly, constant, linear):
    result = [Interval.integer(0) for _ in range(len(poly) + 1)]
    for index, coefficient in enumerate(poly):
        result[index] = result[index] + coefficient * constant
        result[index + 1] = result[index + 1] + coefficient * linear
    return result


def eliminated_coefficients(poly, a, alpha, x):
    """Coefficients of W=(C-L trunc_<a(C/L))/T^a, L=(1-alpha T)(1-x T)."""
    previous2 = previous1 = Interval.integer(0)
    for j in range(a + 1):
        current = poly[j] + (alpha + x) * previous1 - (alpha * x) * previous2
        previous2, previous1 = previous1, current
    return [previous1, poly[a + 1] - (alpha * x) * previous2] + poly[a + 2:]


def evaluate(poly, at):
    result = Interval.integer(0)
    for coefficient in reversed(poly):
        result = result * at + coefficient
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--N', type=int, default=30)
    parser.add_argument('--bits', type=int, default=2048)
    args = parser.parse_args()
    assert args.N >= 1 and args.bits >= 32
    global SCALE
    SCALE = 1 << args.bits
    one = Interval.integer(1)
    sqrt2 = Interval.sqrt_integer(2)
    x = y = sqrt2 - one
    # (1+x)/(2x) = 1 + sqrt(2)/2, exactly.
    a_bound = (one + sqrt2.divide_integer(2)) * Interval.integer(args.N)
    a = ceil_div(a_bound.lo, SCALE)
    assert a == ceil_div(a_bound.hi, SCALE), 'Increase --bits to fix a'
    b = args.N
    k = args.N + 1  # R=N+2; k=R-1.
    radical = Interval.sqrt_integer(k * k + 1)
    alpha = radical - Interval.integer(k)
    # Scale both coupling factors by k>0 to avoid division by k:
    # A coupling = k-(sqrt(k²+1)-1)T, B coupling=kT+sqrt(k²+1)-1.
    coupling = radical - one
    A = [one]
    B = [one]
    for _ in range(a):
        A = multiply_linear(A, alpha, one)
        B = multiply_linear(B, x, one)
    for _ in range(b):
        A = multiply_linear(A, one, y)
        B = multiply_linear(B, one, one)
    A = multiply_linear(A, Interval.integer(k), -coupling)
    B = multiply_linear(B, coupling, Interval.integer(k))
    WA = eliminated_coefficients(A, a, alpha, x)
    WB = eliminated_coefficients(B, a, alpha, x)
    Ay, A1, By, B1 = (evaluate(WA, y), evaluate(WA, one),
                       evaluate(WB, y), evaluate(WB, one))
    numerator = Ay * B1 - A1 * By
    denominator = one - y
    checks = {'W_A(y)>0': Ay.lo > 0, 'W_A(1)>0': A1.lo > 0,
              'W_B(y)>0': By.lo > 0, 'W_B(1)>0': B1.lo > 0,
              '1-y>0': denominator.lo > 0,
              'boundary numerator<0': numerator.hi < 0}
    print(f'N={args.N}, a={a}, b={b}, n={a+b+2}, R={k+1}, bits={args.bits}')
    for name, success in checks.items():
        print(f'{name}: {"CERTIFIED" if success else "NOT CERTIFIED"}')
    # Exact outward enclosure of the scaled numerator by integral endpoints.
    print('Scaled boundary numerator integral enclosure:')
    print(f'[{numerator.lo // SCALE}, {ceil_div(numerator.hi, SCALE)}]')
    assert all(checks.values()), 'Sign certificate failed; no negative sign certified'
    print('PASS: exact negative sign; the unscaled boundary expression has the same sign.')
    print('The coupling scaling contributes k²>0.')
    print('Geometric matrix identification relies on the paper formulas.')
    print('This is not an interior counterexample.')


if __name__ == '__main__':
    main()
