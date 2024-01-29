#!/usr/bin/env sage
proof.all(False)

idl_f = open(sys.argv[1])
d = ZZ(next(idl_f).removeprefix('d '))
f = ZZ(next(idl_f).removeprefix('f '))

disc = d * f^2
K = QuadraticField(disc)
O = K.order_of_conductor(f)
assert O.discriminant() == disc

################################################################

C = 99  #TODO

emax = ceil((C * log(disc.abs(),2) * disc.abs()).log(2)) - 2

################################################################

assert disc < 0
assert disc % 8 == 5

for e in range(ceil(log(-disc,2)), emax+1):
    for z in range(ceil(sqrt(-2^(e+2)/disc - 1))):
        M = 2^(e+2) + disc*(z^2+1)
        assert M >= 0
        if (M.is_prime() and M%4==1) or (M/2 in ZZ and ZZ(M/2).is_prime() and (M/2)%4==1):
            X,Y = two_squares(M)
            if X % 2 == 0:
                X,Y = Y,X
            if X % 2 == 0:
                continue
            x = (X-disc)/2
            y = (Y-z*disc)/2
            if x and y:
                break
    else:
        continue
    break
else:
    raise NotImplementedError

################################################################

assert K.gen()^2 == disc
gen = (disc + K.gen())/2
assert gen in O
ω = x + gen
β = y + z*gen

assert ω in O and β in O
assert ω.minpoly().discriminant() == disc
assert gcd(ω.norm(), β.norm()) == 1
assert ω.norm() + β.norm() == 2^e

print(e, file=sys.stderr)
print(list(ω))
print(list(β))

import re
orient_f = re.sub(r'(.*)/ideals-([0-9]+)-[0-9]+', r'\1/oriented-\2', sys.argv[1])
with open(orient_f,'w') as outf:
    print(f'ω {list(ω*ω.denominator())}, {ω.denominator()}', file=outf)
    print(f'β {list(β*β.denominator())}, {β.denominator()}', file=outf)
