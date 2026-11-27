# a candidate true cycle of the pass loop by the %rec takeover (period 3): one formula f, root at
# tag 0, members T_i = (f, sigma_i) at tag 1 knowing only y_i; site 1 at s (all y known) takes the
# latest T_i by %rec, its product says which y T_i knew, site 2 rotates that into sigma_{i+1}
import sys
src = open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'passmeasure-repush.py')).read().split("if __name__")[0]
exec(src)
Y = L(1, 0)
def tsub(*ks): return tup([K(1)] + [K(Y) if k else None for k in ks])
def site_sub(tag, ys, unk):   # [[1 tag] [y1 [y2 y3]]] with y a formula
    return tup([K(tag)] + ys)
# ROOT on [P K]
S = tup([K(1), K(Y), K(Y), K(Y)])
SITE1 = L(2, L(S, A(3)), A(6))
yq = lambda rax: L(6, L(3, A(rax)), A(15), K(Y))
SIG = tup([K(1), yq(19), yq(8), yq(18)])            # y1' <- r3, y2' <- r1, y3' <- r2
SITE2 = L(2, L(SIG, A(7)), A(14))
RPROD = L(tup([K(0), A(31), A(31)]), tup([L(2, A(1), A(58)), L(2, A(1), A(118)), L(2, A(1), A(119))]))
RBASE = L(tup([K(0), A(7), A(7)]), tup([L(2, A(1), A(10)), L(2, A(1), A(22)), L(2, A(1), A(23))]))
ROOT = L(6, L(3, A(7)), RBASE, L(8, SITE1, L(8, SITE2, RPROD)))
RCALL = L(2, L(tup([K(0), K(Y), K(Y), K(Y)]), A(3)), A(6))
Q = L(6, L(3, A(15)), K(0), L(7, L(2, A(3), A(14)), L(A(3), K(0))))
TB = L(8, RCALL, L(tup([L(2, A(1), A(26)), L(2, A(1), A(54)), L(2, A(1), A(55))]), Q))
f = L(6, A(4), ROOT, TB)
bus = '[[& [& |]] [[0 [%Y [%Y %Y]]] [%F 0]]]'.replace('%Y', n2h(Y)).replace('%F', n2h(f))
driver([('cyc', bus, f)], sys.argv[1])
