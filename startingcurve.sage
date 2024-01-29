#!/usr/bin/env sage
proof.all(False)
import ast

idl_f = open(sys.argv[1])
ort_f = open(sys.argv[2])
d = ZZ(next(idl_f).removeprefix('d '))
f = ZZ(next(idl_f).removeprefix('f '))
ls = []
for line in idl_f:
    l,_,_ = map(ZZ, line.strip().split())
    ls.append(l)

disc = d * f^2
K = QuadraticField(disc)

ω = ast.literal_eval(next(ort_f).removeprefix('ω ')); ω = K(ω[0]) / ω[1]
β = ast.literal_eval(next(ort_f).removeprefix('β ')); β = K(β[0]) / β[1]
e = ZZ(log(ω.norm() + β.norm(), 2))

################################################################

forced_torsion = prod(ls) << e+2
p = forced_torsion - 1
assert p.parent() is ZZ
while True:
    p += forced_torsion
    if K.ideal(p).is_prime():
        break

print(f'log2(p) = {p.log(2).n()}')
print(f'{p = }')

################################################################

q = abs(d); assert q.is_prime()

from deuring.broker import torsion

F2.<i> = GF((p,2), modulus=[1,0,1])


j0, = hilbert_class_polynomial(d).roots(ring=GF(p), multiplicities=False)
E0 = EllipticCurve(j=F2(j0))
E0.set_order((p+1)^2)
frob = E0.frobenius_isogeny(); assert frob.is_endomorphism()
ιmap = next(iso*psi for psi in E0.isogenies_prime_degree(q)
                    for iso in psi.codomain().isomorphisms(E0)
                    if (iso*psi).scaling_factor().trace() == 0)
R = E0.random_point(); assert (ιmap^2)(R) == -q*R  # check


Quat.<ii,jj,kk> = QuaternionAlgebra(-q, -p)
assert Quat.discriminant() == p

surface = len(E0.change_ring(GF(p)).abelian_group().invariants()) == 2
c = min(map(ZZ, Mod(-p,q).sqrt(all=True)))
P,Q = torsion(E0,q)
if surface:
    raise NotImplementedError
elif not any(c*ιmap._eval(T) + ιmap._eval(frob._eval(T)) for T in (P,Q)):
    O0 = Quat.quaternion_order([Quat.one(), (1+ii)/2, (jj+kk)/2, (c*ii+kk)/q])
else:
    assert not any(c*ιmap._eval(T) - ιmap._eval(frob._eval(T)) for T in (P,Q))
    O0 = Quat.quaternion_order([Quat.one(), (1+ii)/2, (jj+kk)/2, (c*ii-kk)/q])
assert surface == ((1+jj)/2 in O0)

# check
assert O0.discriminant() == Quat.discriminant()
if 0:   # slow
    for el in O0.basis():
        d = el.denominator()
        t,u,v,w = el * d
        P,Q = torsion(E0, d)
        for T in torsion(E0,d):
            assert not t*T + u*ιmap._eval(T) + v*frob._eval(T) + w*ιmap._eval(frob._eval(T))

################################################################

from deuring.correspondence import Deuring_Context as DCTX
from deuring.cost import choose_torsion                                 , cost_model

C = ceil(p^.07)  # kind of arbitrary

twopow = 1  #XXX 2^(e//2)
T,facToExt = choose_torsion(p, q, 2, floor(C*p/f/twopow))
print(f'T = {T.factor()}')
##for tup in sorted(facToExt.items(), key = lambda t: cost_model(p)(t[0], t[1])):
##    print(*tup)
##exit()
assert T % 2
T *= twopow
for i in range(e+1):
    assert (2^i).divides(p+1)
    facToExt[2^i] = 1

ctx = DCTX(O0, E0, ιmap, facToExt, T, None, None)

# RepresentInteger
R.<x,y> = ZZ[]
if q % 4 == 3:
    subO = Quat.quaternion_order([Quat.one(), (1+ii)/2, jj, (jj+kk)/2])
    assert subO.free_module() <= O0.free_module()
    nf1 = x^2 + x*y + (1+q)//4*y^2
else:
    raise NotImplementedError
nf = lambda v,w,rhs: nf1(x,y) + p*nf1(v,w) - rhs

normγ = f*T
assert normγ > C*p

import itertools
vbnd = floor(sqrt(normγ/p))
for v in range(-vbnd, vbnd+1):
    wbnd = floor(sqrt((normγ-p*v^2)/p/q))
    for w in range(-wbnd, wbnd+1):
        eqn = nf(v,w, normγ)
        rhs = -eqn.monomial_coefficient(R.one())
        if rhs <= 0:
            #FIXME should probably be able to avoid this entirely?
#            print(rhs)
            continue
        fac = rhs.factor(limit=2^10)
        if len(fac) > 5 or not fac[-1][0].is_pseudoprime():
            continue  # not easily factorable, or too many prime factors
        lhs = eqn + rhs
        assert eqn == lhs - rhs
        qf = BinaryQF(lhs)
#        print(qf, rhs)
        sol = qf.solve_integer(rhs)
        if sol is not None:
            γ = sum(c*g for c,g in zip(subO.basis(), sol+(v,w)))
            assert γ.reduced_norm() == normγ
            break
    else:
        continue
    break
else:
    raise NotImplementedError('cannot γ')

if (O0*γ + O0*f) * ii == ii * (O0*γ + O0*f):  # ii is ω₀
    raise NotImplementedError('γ commutes')

def γmap(pt):
    fld = pt.base_ring()
    cs = vector(list(γ))
    assert cs.denominator() in (1,2)
    if cs.denominator() == 2:
        try:
            pt = next(filter(bool, pt.division_points(2)))
        except StopIteration:
            pt = pt.change_ring(fld.extension(2,'u'))
            pt = next(filter(bool, pt.division_points(2)))
        cs *= 2
    cs = cs.change_ring(ZZ)

    jpt = frob._eval(pt)
    γpt = cs[0]*pt + ιmap._eval(cs[1]*pt + cs[3]*jpt) + cs[2]*jpt
    return γpt.change_ring(fld)

################################################################

I = O0*γ + O0*(normγ//f)
assert I.norm() == normγ//f

set_verbose(1)

ψmap = ctx.IdealToIsogeny(I)
E = ψmap.codomain()
print(E.a_invariants())

set_verbose(0)

################################################################

ι = K['x']([q,0,1]).any_root()
u,v = (f*ι).coordinates_in_terms_of_powers()(ω)
assert ω == u + v*f*ι
w = lcm(u.denominator(), v.denominator())
assert w in (1, 2)

P0,Q0 = torsion(E0, 2^(e+2)*w)
P1,Q1 = torsion(E, 2^(e+2)*w)

G0 = AdditiveAbelianGroupWrapper(P0.parent(), [P0,Q0], [P0.order(),Q0.order()])
G1 = AdditiveAbelianGroupWrapper(P1.parent(), [P1,Q1], [P1.order(),Q1.order()])
matι = matrix(Zmod(w<<e+2), [G0.discrete_log(ιmap._eval(pt)) for pt in (P0,Q0)])
matγ = matrix(Zmod(w<<e+2), [G0.discrete_log(γmap(pt)) for pt in (P0,Q0)])
matψ = matrix(Zmod(w<<e+2), [G1.discrete_log(ψmap._eval(pt)) for pt in (P0,Q0)])
matφ = ~matψ * matγ
matfι = f * matφ * matι * ~matφ
assert matfι^2 == disc

P = (w*P1).change_ring(F2)
Q = (w*Q1).change_ring(F2)
print(list(P))
print(list(Q))
assert P.order() == 2^(e+2)
assert Q.order() == 2^(e+2)

matwω = (ZZ(u*w) + ZZ(v*w)*matfι).change_ring(ZZ)
assert matwω.change_ring(Zmod(2^(e+2))).charpoly() == (w*ω).charpoly().change_ring(Zmod(2^(e+2)))

ωP = (matwω[0][0]*P1 + matwω[0][1]*Q1).change_ring(F2)
ωQ = (matwω[1][0]*P1 + matwω[1][1]*Q1).change_ring(F2)
print(list(ωP))
print(list(ωQ))
assert ωP.order() == 2^(e+2)
assert ωQ.order() == 2^(e+2)

assert ωP.weil_pairing(ωQ, 2^(e+2)) == P.weil_pairing(Q, 2^(e+2))^abs(ω.norm())

################################################################

if 0:   # _very_ slow!!

    for f in E0.isogenies_prime_degree(f):
        for iso in f.codomain().isomorphisms(E):
            myφmap = iso * f
            myγmap = myφmap.dual() * ψmap
            if myγmap.trace() == γ.reduced_trace():
                myfιmap = myφmap * ιmap * myφmap.dual()
                mymatfι = matrix(Zmod(w<<e+2), (G1.discrete_log(myfιmap._eval(pt)) for pt in (P1,Q1)))
                print(mymatfι)
                if mymatfι == matfι:
                    break
        else:
            continue
        break
    else:
        assert False

    mymatfι = matrix(Zmod(w<<e+2), (G1.discrete_log(myfιmap._eval(pt)) for pt in (P1,Q1)))
    assert mymatfι == matfι

    mywωmap = E.scalar_multiplication(u*w) + E.scalar_multiplication(v*w)*myfιmap
    assert mywωmap.degree() == w^2*ω.norm()
    assert mywωmap.trace() == w*ω.trace()
    assert P == (w*P1).change_ring(F2)
    assert Q == (w*Q1).change_ring(F2)
    assert ωP == mywωmap._eval(P1).change_ring(F2)
    assert ωQ == mywωmap._eval(Q1).change_ring(F2)

    mymatwω = matrix(Zmod(w<<e+2), (G1.discrete_log(mywωmap._eval(pt)) for pt in (P1,Q1)))
    assert mymatwω == matwω

################################################################

load('canonical.sage')

E, P, Q, ωP, ωQ = canonicalize_orientation(E, P, Q, ωP, ωQ)

################################################################

curve_f = sys.argv[1].replace('ideals-','curve-')
with open(curve_f,'w') as outf:
    assert is_montgomery(E)
    print('p', p, file=outf)
    print('E', list(E.a2()), file=outf)
    print('P', list(map(list, P.xy())), file=outf)
    print('Q', list(map(list, Q.xy())), file=outf)
    print('ωP', list(map(list, ωP.xy())), file=outf)
    print('ωQ', list(map(list, ωQ.xy())), file=outf)

