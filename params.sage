#!/usr/bin/env sage
proof.all(False)
set_random_seed(0)

bits = ZZ(sys.argv[1])
numgens = ZZ(sys.argv[2])
disc = -11

################################################################

def allfs():
    f2 = 2^floor((sqrt(abs(2^bits/disc))-1).log(2))
    while True:
        bnd = ceil((sqrt(abs(2^bits/disc))-1) / f2)
        for s in reversed(range(1,bnd,2)):
            f = s*f2 + 1
            yield f
        if f2 <= 1:
            break
        f2 //= 2

for f in allfs():
    inert = kronecker(disc, f) == -1
    if not inert and f.is_prime():
        break
else:
    assert False

print(f'{f = :#x}')
print(f'f-1 = {factor(f-1)}')
print(f'log(disc) ≈ {abs(disc*f^2).log(2).n()}')

################################################################

K.<sqrtdisc> = QuadraticField(disc)
assert K.discriminant() == disc

ls = []
for l in Primes():
    if len(K(l).factor()) == 2:
        ls.append(l)
    if len(ls) >= numgens:
        break

################################################################

# if l is split, returns a generator of a prime ideal of K above l
def ideal_above_K(l):
    assert l in ZZ and is_prime(l)
    if 0:
        ll, _ = K.primes_above(l, 1)
    else:
        evs = K.defining_polynomial().change_ring(GF(l)).roots(multiplicities=False)
        m = min(map(ZZ, evs))
        ll = K.ideal([l, sqrtdisc-m])
    assert ll.norm() == l
    g, = ll.gens_reduced()  # h(K) = 1
    return g

O = K.order_of_conductor(f)
assert O.discriminant() == f^2 * K.discriminant()

# if l is split, returns a generator of a prime ideal of O above l
def ideal_above_O(l):
    h = (f*sqrtdisc).minpoly().change_ring(GF(l))

    try:
        m = min(map(ZZ, h.roots(multiplicities=False)))
    except ValueError:
        return

    Igens = (l, f*sqrtdisc-m)

    assert Igens[0] == l
    return Igens[1]

assert not inert
F = GF(f)
b,a = ideal_above_K(f).polynomial().padded_list(2)

def map_to_ff(l, τ):
    assert l in ZZ and is_prime(l) and τ in K

    α, = K.ideal((l, τ)).gens_reduced()     # h(K) = 1
    assert K.ideal(α) == K.ideal((l, τ))

    y,x = (α / α.conjugate()).polynomial().padded_list(2)
    return F(y - x*b/a)

################################################################

assert not inert
h = f-1
fac = factor(h)

τs = [ideal_above_O(l) for l in ls]
els = [map_to_ff(l,τ) for l,τ in zip(ls,τs)]

from sage.groups.generic import order_from_multiple
ords = [order_from_multiple(el, h, factorization=fac, operation='*') for el in els]
idx = ords.index(h)

from sage.groups.generic import discrete_log

logs = []
for l,τ,el in zip(ls,τs,els):
    assert τ[1] == f
    lg = discrete_log(el, els[idx], ord=h)
    logs.append(lg)
    print(l, -τ[0], logs[-1])

################################################################

lat = []
for i in range(len(els)):
    row = [0]*len(els)
    if i == idx:
        row[i] = h
    else:
        row[i] = -logs[idx]
        row[idx] = logs[i]
    lat.append(row)
lat = matrix(ZZ, lat)
assert lat.det().abs() == h

lat = lat.LLL()
print(lat)

with open(f'data/ideals-{abs(disc*f^2).bit_length()}-{numgens}.txt','w') as outf:
    print(f'd {disc}', file=outf)
    print(f'f {f}', file=outf)
    for l,τ,lg in zip(ls,τs,logs):
        print(l, -τ[0], lg, file=outf)

for bsz in range(40,101,5):
    lat = lat.BKZ(block_size=bsz, fp='rr', precision=200)
    print(lat)
    with open(f'data/reduced-{abs(disc*f^2).bit_length()}-{numgens}-{bsz}.txt','w') as outf:
        for row in lat:
            print(list(row), file=outf)

