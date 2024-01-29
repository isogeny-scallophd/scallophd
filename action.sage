#!/usr/bin/env sage
proof.all(False)

sys.path.insert(0, './two-isogenies/Theta-SageMath/')

from theta_structures.couple_point import CouplePoint
from theta_isogenies.product_isogeny import EllipticProductIsogeny

sys.setrecursionlimit(9999)

class SCALLOPHD_Context:

    def __init__(self, ω, β, idls):
        self.ω = ω
        self.β = β
        self.e = ZZ(log(ω.norm() + β.norm(), 2))

        K = self.ω.parent()
        d = K.discriminant()
        f = K.order(ω).conductor()
        fι = K.gen()
        assert list(fι.minpoly()) == [-d*f^2, 0, 1]
        r,s = ω.coordinates_in_terms_of_powers()(fι)
        assert fι == r + s*ω
        self.idls = [(l, (v-r)/s%l) for l,v in idls]  # eigenvalues of ω, not fι!

#        # debug
#        O = K.order_of_conductor(f)
#        for (l1,v1),(l2,v2) in zip(idls, self.idls):
#            print(O.ideal([l1, fι-v1]) == O.ideal([l2, ω-v2]), O.ideal([l2, ω-v2]).norm())

        tω = ZZ(ω.trace())
        self.ambiguous = {l for l,v in self.idls if v == (tω-v)%l or v == (v-tω)%l}
        self.disambiguator = next((l,v) for l,v in sorted(self.idls)[::-1] if l not in self.ambiguous)

class Isogeny_2dim:

    H2 = lambda tup: (tup[0]+tup[1], tup[0]-tup[1])

    def __init__(self, ker, e, iopair, *, Hcnt_post=None):

        ker0 = deepcopy(ker)

        Hcnt_pre = 0
        while not 2^(e+1) * (ker[0][0] - ker[0][1]):
            ker = tuple(map(Isogeny_2dim.H2, ker))
            e -= 1
            Hcnt_pre += 1

#        assert all(pt.order() == 2^(e+2) for pt2 in ker for pt in pt2)
        ker = tuple(CouplePoint(*pt) for pt in ker)

        if Hcnt_post is None:
            Hcnt_post = 0
        while Hcnt_post < 2:
            try:
                Phi = EllipticProductIsogeny(tuple(cpt*2^Hcnt_post for cpt in ker), e-Hcnt_post)  # this is where the magic happens!
            except ZeroDivisionError:
                Hcnt_post += 1
                continue
            break
        else:
            assert False, 'looks like somehow our isogeny splits too early?'
        self.Hcnt_post = Hcnt_post

        def _pre():
            def _aux(pt):
                pt = (pt[0], pt[1])  # workaround for theta code raising ValueError when it should be IndexError
                for _ in range(Hcnt_pre):
                    pt = Isogeny_2dim.H2(pt)
                return CouplePoint(*pt)
            return _aux
        pre = _pre()

#        assert not Phi(pre(((4<<Hcnt_post)*ker0[0][0], (4<<Hcnt_post)*ker0[0][1])))[0]
#        assert not Phi(pre(((4<<Hcnt_post)*ker0[0][0], (4<<Hcnt_post)*ker0[0][1])))[1]
#        assert not Phi(pre(((4<<Hcnt_post)*ker0[1][0], (4<<Hcnt_post)*ker0[1][1])))[0]
#        assert not Phi(pre(((4<<Hcnt_post)*ker0[1][0], (4<<Hcnt_post)*ker0[1][1])))[1]

        assert Phi.domain()[0] == Phi.domain()[1]
        if Phi.codomain()[0] == Phi.codomain()[1]:
            iso1 = iso2 = Phi.codomain()[0].isomorphism_to(Phi.domain()[0])
        else:
            iso1 = Phi.codomain()[0].isomorphism_to(Phi.domain()[0])
            iso2 = Phi.codomain()[1].isomorphism_to(Phi.domain()[1])
        if Hcnt_post == 0:
            post = lambda pt: CouplePoint(iso1(pt[0]), iso2(pt[1]))
        elif Hcnt_post == 1:
            post = lambda pt: CouplePoint(*Isogeny_2dim.H2((iso1(pt[0]), iso2(pt[1]))))
        else:
            assert False, "oops"

#        assert not post(Phi(pre((4*ker0[0][0], 4*ker0[0][1]))))[0]
#        assert not post(Phi(pre((4*ker0[0][0], 4*ker0[0][1]))))[1]
#        assert not post(Phi(pre((4*ker0[1][0], 4*ker0[1][1]))))[0]
#        assert not post(Phi(pre((4*ker0[1][0], 4*ker0[1][1]))))[1]

        import itertools
        def _ev():
            P,imP = iopair
            chk_pt = P.order()//4 * P
            chk_im = P.order()//4 * imP
            assert 2*chk_pt and not 4*chk_pt
            assert 2*chk_im and not 4*chk_im
            for i in range(2):
                im = post(Phi(pre(CouplePoint((1-i)*P, i*P))))
                for j in range(2):
                    if im[j] in (imP, -imP):
                        if Hcnt_post == 0:
                            def _fun(pt):
                                return post(Phi(pre(CouplePoint((1-i)*pt,i*pt))))[j]
                            return _fun
                        elif Hcnt_post == 1:
                            def _fun(pt):
                                n = pt.order()
                                assert n % 2
                                pt += chk_pt
                                r = post(Phi(pre(CouplePoint((1-i)*pt,i*pt))))
                                cim = chk_im * n
                                if r[0]*n in (cim,-cim):
                                    rpt = 4 * r[0]
                                else:
                                    assert r[1]*n in (cim,-cim)
                                    rpt = 4 * r[1]
                                rpt *= ZZ(~Mod(4, n))
                                return rpt
                            return _fun
                        else:
                            assert False
            assert False
        self.ev = _ev()

    def __call__(self, pt):
        return self.ev(pt)

def Isogeny_1dim(E, ker):
    ordr = ker.order()

    phi = E.automorphisms()[0]  # identity map
    while ordr > 1:
        l = max(ordr.prime_factors())

        import time; t0 = time.time()
        K = ordr//l * ker
#        print(l, 'smul:', time.time()-t0)
        assert K and not l*K
        K.set_order(l, check=False)

        import time; t0 = time.time()
        psi = E.isogeny(K, check=False)
#        print(l, 'isog:', time.time()-t0)

        phi = psi * phi

        import time; t0 = time.time()
        ker = psi(ker)
#        print(l, 'eval:', time.time()-t0)

        ordr //= l
        E = phi.codomain()
    return phi


load('canonical.sage')


t_pointwithorder = []
t_computeorientation = []
t_evalorientation = []
t_computeisogeny = []
t_pushorientation = []
t_montgomerize = []
t_canonicalrepr = []

class SCALLOPHD_PublicKey:

    def __init__(self, ctx, E, P, Q, ωP, ωQ, *, canonicalize=True, Hcnt_post=None):
        self.ctx = ctx

        self.p = E.base_field().characteristic()

        import time; t0 = time.time()

        if not is_montgomery(E):
            iso = montgomerize(E, 2^self.ctx.e*P)
            E = iso.codomain()
            P, Q, ωP, ωQ = map(iso, (P, Q, ωP, ωQ))

        t_montgomerize.append(time.time() - t0); t0 = time.time()

        if canonicalize:
            P.set_order(2^(self.ctx.e+2), check=False)
            Q.set_order(2^(self.ctx.e+2), check=False)
            E, P, Q, ωP, ωQ = canonicalize_orientation(E, P, Q, ωP, ωQ)

            t_canonicalrepr.append(time.time() - t0); t0 = time.time()

        self.E = E
        self.P, self.Q, self.ωP, self.ωQ = P, Q, ωP, ωQ

        E.set_order((self.p+1)^2, check=False)
        for pt in (self.P, self.Q, self.ωP, self.ωQ):
            pt.set_order(2^(self.ctx.e+2), check=False)

        u,v = Sequence(self.ctx.ω.coordinates_in_terms_of_powers()(self.ctx.β), ZZ)
        assert self.ctx.β == u + v*self.ctx.ω
        βP = u*self.P + v*self.ωP
        βQ = u*self.Q + v*self.ωQ

        ker = ((self.ωP, βP), (self.ωQ, βQ))
        import time; t0 = time.time()
        self.ω = Isogeny_2dim(ker, self.ctx.e, (self.P, self.ωP), Hcnt_post=Hcnt_post)
        t_computeorientation.append(time.time() - t0)

    def __repr__(self):
        A = self.E.a2()
        assert self.E == EllipticCurve([0,A,0,1,0])
        return f'SCALLOPHD<{A}, {self.ωP.xy()}, {self.ωQ.xy()}>'

    def act(self, vec):
        from sage.groups.generic import order_from_multiple

        if not any(vec):
            return self
        vec = list(vec)
        print(vec, file=sys.stderr)

        import time; t0 = time.time()

        tω = ZZ(self.ctx.ω.trace())
        vs = {l: v if e > 0 else (tω-v)%l for (l,v),e in zip(self.ctx.idls, vec) if e}

        # when the exponent vector is very sparse, we may not have enough
        # information in our points to disambiguate the signs lost in the
        # theta isogeny -- so we pretend we still had to evaluate at an l
        # with an unambiguous eigenvalue and throw away that part of the
        # order later.
        lfake = None
        if set(vs.keys()) <= self.ctx.ambiguous:
            lfake,v = self.ctx.disambiguator
            assert lfake not in vs
            vs[lfake] = v

        k = prod(vs.keys())
        P = (self.p+1)//k * self.E.random_point()
        P.set_order(multiple=k)
        k = P.order()
        vs = {l:v for l,v in vs.items() if l.divides(k)}
        t_pointwithorder.append(time.time() - t0); t0 = time.time()

        if set(vs.keys()) <= self.ctx.ambiguous:
            return self.act(vec)

        vv = CRT(*map(list, zip(*map(reversed, vs.items()))))

        ωP = self.ω(P)
        v1P = vv*P
        v2P = tω%k*P - v1P
        if __debug__:
            K1 = ωP - v2P
            K1.set_order(multiple=k)
            K2 = ωP + v2P
            K2.set_order(multiple=k)
            _c = sum(self.ω(T) + s*vv*T == 0 for s in (+1,-1) for T in (K1,K2))
            assert _c == 1, f'for some reason we have {_c} solutions, not 1'
        K = ωP - v2P
        K.set_order(multiple=k)
        ωK = self.ω(K)
        vK = vv*K
        if ωK not in (vK, -vK):
            K = ωP + v2P
            if __debug__:
                K.set_order(multiple=k)
                ωK = self.ω(K)
                vK = vv*K
                assert ωK in (vK, -vK)

        # now we don't want the extra part of the order anymore
        if lfake is not None:
            K *= lfake

        o = order_from_multiple(K, k)
        K.set_order(o, check=False)
        for l,_ in vs.items():
            if not l.divides(o):  # we accidentally guessed a kernel point of the dual -- happens to the best
                continue
            idx = next(i for i,(ll,_) in enumerate(self.ctx.idls) if ll==l)
            vec[idx] -= sign(vec[idx])
        t_evalorientation.append(time.time() - t0); t0 = time.time()

        phi = Isogeny_1dim(self.E, K)
#        print(phi)
        t_computeisogeny.append(time.time() - t0); t0 = time.time()

        imE = phi.codomain()
        imP = phi._eval(self.P)
        imQ = phi._eval(self.Q)
        imωP = phi._eval(self.ωP)
        imωQ = phi._eval(self.ωQ)

        t_pushorientation.append(time.time() - t0); t0 = time.time()

        if any(vec):
            return SCALLOPHD_PublicKey(self.ctx, imE, imP, imQ, imωP, imωQ, canonicalize=False, Hcnt_post=self.ω.Hcnt_post).act(vec)

        return SCALLOPHD_PublicKey(self.ctx, imE, imP, imQ, imωP, imωQ, Hcnt_post=self.ω.Hcnt_post)


def timers():
    print('time for random point and order computation:         ', sum(t_pointwithorder))
    print('time for computing the orientation (2-dim):          ', sum(t_computeorientation))
    print('time for evaluating the orientation (2-dim):         ', sum(t_evalorientation))
    print('time for computing the actual isogeny (1-dim):       ', sum(t_computeisogeny))
    print('time for pushing the orientation through (1-dim):    ', sum(t_pushorientation))
    print('time for converting to Montgomery form (1-dim):      ', sum(t_montgomerize))
    print('time for finding a canonical representation (1-dim): ', sum(t_canonicalrepr))

def reset_timers():
    global t_pointwithorder, t_computeorientation, t_evalorientation
    global t_computeisogeny, t_pushorientation, t_montgomerize, t_canonicalrepr
    t_pointwithorder, t_computeorientation, t_evalorientation = [], [], []
    t_computeisogeny, t_pushorientation, t_montgomerize, t_canonicalrepr = [], [], [], []

################################################################

discbits = ZZ(sys.argv[1])
numgens = ZZ(sys.argv[2])
####discbits, numgens = 510, 74
####discbits, numgens = 1020, 100

import ast

with open(f'data/ideals-{discbits}-{numgens}.txt') as ls:
    _d = ZZ(next(ls).removeprefix('d '))
    _f = ZZ(next(ls).removeprefix('f '))
    _K = QuadraticField(_d*_f^2)
    _idls = []
    for l,v,_ in map(str.split, ls):
        _idls.append(tuple(map(ZZ, (l,v))))

with open(f'data/oriented-{discbits}.txt') as ls:
    _ω = ast.literal_eval(next(ls).removeprefix('ω ')); _ω = _K(_ω[0]) / _ω[1]
    _β = ast.literal_eval(next(ls).removeprefix('β ')); _β = _K(_β[0]) / _β[1]

ctx = SCALLOPHD_Context(_ω, _β, _idls)

with open(f'data/curve-{discbits}-{numgens}.txt') as ls:
    _p = ZZ(next(ls).removeprefix('p '))
    _F2.<i> = GF((_p,2), modulus=[1,0,1])
    _E = EllipticCurve(_F2, [0, ast.literal_eval(next(ls).removeprefix('E ')), 0, 1, 0])
    _P = _E(Sequence(ast.literal_eval(next(ls).removeprefix('P ')), _F2))
    _Q = _E(Sequence(ast.literal_eval(next(ls).removeprefix('Q ')), _F2))
    _ωP = _E(Sequence(ast.literal_eval(next(ls).removeprefix('ωP ')), _F2))
    _ωQ = _E(Sequence(ast.literal_eval(next(ls).removeprefix('ωQ ')), _F2))

if __debug__:
    _E.set_order((_p+1)^2)
    _P.set_order(multiple=(_p+1).p_primary_part(2))
    _Q.set_order(multiple=(_p+1).p_primary_part(2))
    assert (_E,_P,_Q,_ωP,_ωQ) == canonicalize_orientation(_E,_P,_Q,_ωP,_ωQ)

import fpylll

for bsz in range(1, 101):
    try:
        f = open(f'data/reduced-{discbits}-{numgens}-{bsz}.txt')
    except FileNotFoundError:
        continue
    mat = []
    for l in f:
        mat.append(ast.literal_eval(l))
mat = matrix(ZZ, mat)
lat = fpylll.IntegerMatrix(mat.nrows(), mat.ncols())
for i,row in enumerate(mat):
    for j,ent in enumerate(row):
        lat[i,j] = ent
gso = fpylll.GSO.Mat(lat)
gso.update_gso()
def short_equivalent(vec):
    vec = vector(ZZ, vec)
    sol = vector(ZZ, gso.babai(list(vec)))
    return list(vec - sol * mat)

pk0 = SCALLOPHD_PublicKey(ctx, _E, _P, _Q, _ωP, _ωQ)
reset_timers()

################################################################

print(f'{pk0 = }')

sk1 = short_equivalent([randrange(999) for _ in _idls])
sk2 = short_equivalent([randrange(999) for _ in _idls])
pk1 = pk0.act(sk1)
print(f'{pk1 = }')
pk2 = pk0.act(sk2)
print(f'{pk2 = }')

ss1 = pk2.act(sk1)
print(f'{ss1 = }')
ss2 = pk1.act(sk2)
print(f'{ss2 = }')

print()
timers()
