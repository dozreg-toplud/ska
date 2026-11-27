"""Print the arms of the door of +comp (`door`) or of the core K (anything
else) that carry a %fast hint, with their battery axes and names.  Run from
formalization/ under tools/capped.sh."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
def cordname(v):
    b = v.to_bytes((v.bit_length()+7)//8,'little')
    try: return b.decode()
    except: return None
def fastname(f):
    f = norm(f)
    # [7 X [11 [%fast [1 [cord ...]]] [0 1]]]
    if f[0]=='C' and norm(f[1])==('A',7):
        r = norm(f[2]); y = norm(r[2])
        if y[0]=='C' and norm(y[1])==('A',11):
            h = norm(norm(y[2])[1])
            if h[0]=='C' and norm(h[1])==('A',0x74736166):
                c = norm(h[2])
                if c[0]=='C' and norm(c[1])==('A',1):
                    cc = norm(norm(c[2])[1])
                    if cc[0]=='A': return cordname(cc[1])
    return None
which = sys.argv[1]
if which == 'door':
    bat = ('R','comp.door')
else:
    K = ('C', ('R','nhe0b859c3d8aa'), ('C', ('R','nh15c74912d225'), ('C', ('A',0), ('R','ana'))))
    bat = norm(K)[1]
for ax, f in arms(bat):
    nm = fastname(f)
    if nm: print(ax, nm)
