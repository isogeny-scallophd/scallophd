
from sage.schemes.elliptic_curves.weierstrass_morphism import identity_morphism
from sage.schemes.elliptic_curves.weierstrass_morphism import WeierstrassIsomorphism as WI
def is_montgomery(E):
    a1,a2,a3,a4,a6 = E.a_invariants()
    return a1 == a3 == a6 == 0 and a4 == 1
def montgomerize(E, P):
    assert 2*P and not 4*P
    r = (2*P).xy()[0]
    iso = WI(E, (1,r,0,0))
    a1,a2,a3,a4,a6 = iso.codomain().a_invariants()
    P = iso(P)
    assert a1 == a3 == a6 == 0
    u = P.xy()[0].sqrt()
    iso = WI(iso.codomain(), (u,0,0,0)) * iso
    assert is_montgomery(iso.codomain())
    return iso

def canonical_two_power_basis(E, k0):
    p = E.base_field().characteristic()
    assert (2^k0).divides(p+1)
    cof = (p+1)//2^k0
    u = E.base_field().gen()
    for i in range(1,9999):
        try:
            P = E.lift_x(u + i) * cof
        except ValueError:
            continue
        if 2^(k0-1)*P:
            break
    else:
        assert False
    for j in range(1,9999):
        try:
            Q = E.lift_x(u - j) * cof
        except ValueError:
            continue
        w = P.weil_pairing(Q, 2^k0)
        if w^(2^(k0-1)) != 1:
            break
    else:
        assert False
    return P, Q

def mylogfun(P, Q, k0):
    v = P.weil_pairing(Q, 2^k0)
    vs = Sequence([v])
    while len(vs) < k0:
        vs.append(vs[-1]^2)
    assert vs[-1] == -1
    vs.append(1)
    vs.reverse()

    def _dlog(w, k):
        assert k >= 0
#        assert w^(2^k) == 1
        if k == 0:
            assert w.is_one()
            return 0
        w2 = w^2
        r = _dlog(w2, k-1)
#        assert vs[k-1]^r == w2
#        assert vs[k]^r == w or vs[k]^r == -w
        if vs[k]^r != w:
            r += 2^(k-1)
        assert vs[k]^r == w
        return r

    def _solve(T):
        wa = T.weil_pairing(Q, 2^k0)
        wb = P.weil_pairing(T, 2^k0)
        a = _dlog(wa, k0)
        b = _dlog(wb, k0)
        assert a*P + b*Q == T
        return (a, b)
    return _solve

def canonicalize_orientation(E, P, Q, ωP, ωQ):
    assert P.order() == Q.order()
    o = P.order().is_prime_power(get_data=True)
    assert o[0] == 2
    e = o[1] - 2
    P4 = 2^e*P
    Q4 = 2^e*Q
    PQ4, P2, Q2 = P4+Q4, 2*P4, 2*Q4
    iso = identity_morphism(E)
    for pt in (P4, Q4, PQ4, PQ4-P2, P4+Q2, Q4+P2):
        iso2 = montgomerize(E, pt)
        if not is_montgomery(iso.codomain()) or iso2.codomain().a2() < iso.codomain().a2():
            iso = iso2
    E = iso.codomain()
    P, Q, ωP, ωQ = map(iso, (P, Q, ωP, ωQ))

    (R,S) = canonical_two_power_basis(E, e+2)
    mylog = mylogfun(P, Q, e+2)
    PQRS = matrix(Zmod(2^(e+2)), (mylog(R), mylog(S)))
    Ω_PQ = matrix((mylog(ωP), mylog(ωQ)))
    Ω_RS = (PQRS * Ω_PQ * ~PQRS).change_ring(ZZ)
    ωR,ωS = (row[0]*R + row[1]*S for row in Ω_RS)
    return E, R, S, ωR, ωS

