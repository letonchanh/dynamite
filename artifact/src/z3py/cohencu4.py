from z3 import *

x0, y0, z0, c0, k0 = Ints('x0 y0 z0 c0 k0')
x1, y1, z1, c1, k1 = Ints('x1 y1 z1 c1 k1')

t = And(x1==x0+y0, y1==y0+z0, z1==z0+6, c1==c0, k1==k0)
r0 = y0*z0 - 18*x0 - 12*y0 + 2*z0 -6 + c0 <= k0
r1 = y1*z1 - 18*x1 - 12*y1 + 2*z1 -6 + c1 <= k1
i0 = y0*z0 - 18*x0 - 12*y0 + 2*z0 -6 == 0
i1 = y1*z1 - 18*x1 - 12*y1 + 2*z1 -6 == 0

s = Solver()
s.add(t)
s.add(r0)
s.add(i0)
s.add(i1)
s.add(Not(r1))
print(s.check())
print(s.model())