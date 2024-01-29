#!/usr/bin/env sage

idl_f, lat_f = map(open, sys.argv[1:3])

idls, lgs = [], []

for l in idl_f:
    if l[0] == 'd':
        d = ZZ(l.strip().split()[1])
        K.<T> = QuadraticField(d)
    elif l[0] == 'f':
        f = ZZ(l.strip().split()[1])
        O = K.order_of_conductor(f)
    else:
        l,m,lg = map(ZZ, l.strip().split())
        I = O.ideal([l, f*T-m])
        assert I.norm() == l
        idls.append(I)
        lgs.append(lg)

import ast
lat = []
for l in lat_f:
    lat.append(ast.literal_eval(l))
lat = matrix(ZZ, lat)

################################################################

def fpow(form, e):
    if e < 0:
        return fpow(BinaryQF(form[0], -form[1], form[2]), -e)
    ret = BinaryQF.principal(f^2*d)
    if e % 2:
        ret *= form
    if e > 1:
        ret *= fpow((form * form).reduced_form(), e//2)
    return ret.reduced_form()

def checkrel(vec):
    form = BinaryQF.principal(f^2*d)
    for I,e in zip(idls,vec):
        form *= fpow(I.quadratic_form(), e)
        form = form.reduced_form()
    return form == BinaryQF.principal(f^2*d)

for i,row in enumerate(lat):
    print(f'\x1b[K  checking row #{i} of {lat.nrows()}...', end=' ', file=sys.stderr, flush=True)
    assert checkrel(row)
    print(f'ok', end='\r', file=sys.stderr, flush=True)
print('\x1b[K', end='', file=sys.stderr, flush=True)

