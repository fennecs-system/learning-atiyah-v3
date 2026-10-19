#!/usr/bin/env python3
"""Regenerate the four integer coefficients in SingularCertificate.boundaryQuad.

Exploratory generator only: Lean rechecks the entire computation using
`decide +kernel` and proves real-evaluation compatibility independently.
Coordinates are 1, sqrt(2), sqrt(962), sqrt(2)*sqrt(962).
"""
from math import isqrt
z=(0,0,0,0); one=(1,0,0,0)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def neg(a):return tuple(-x for x in a)
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 r=[0]*4
 for i in range(4):
  for j in range(4):r[i^j]+=a[i]*b[j]*(2 if i&j&1 else 1)*(962 if i&j&2 else 1)
 return tuple(r)
def lin(p,c,l):return [add(mul(p[i],c) if i<len(p) else z,mul(p[i-1],l) if i else z) for i in range(len(p)+1)]
def elim(p):
 p2=p1=z
 for j in range(53):p2,p1=p1,sub(add(p[j],mul(add(al,x),p1)),mul(mul(al,x),p2))
 return [p1,sub(p[53],mul(mul(al,x),p2))]+p[54:]
def ev(p,t):
 r=z
 for c in reversed(p):r=add(mul(r,t),c)
 return r
x=(-1,1,0,0);al=(-31,0,1,0);c=(-1,0,1,0);k=(31,0,0,0)
a=b=[one]
for _ in range(52):a=lin(a,al,one);b=lin(b,x,one)
for _ in range(30):a=lin(a,one,x);b=lin(b,one,one)
a=lin(a,k,neg(c));b=lin(b,c,k)
a=elim(a);b=elim(b)
r=sub(mul(ev(a,x),ev(b,one)),mul(ev(a,one),ev(b,x)))
print(r)
print([len(str(abs(v))) for v in r])
