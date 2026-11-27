# The noun parser of sccloop.py, for sccstress.py.
import re

def cord(n):
    s = b''
    while n:
        s += bytes([n & 255]); n >>= 8
    return s.decode('latin1')


def parse(t):
    """A raw noun as printed by ~& of a `*`: atoms in @ud with dots, cells in brackets."""
    toks = re.findall(r'\[|\]|[0-9.]+|~', t)
    pos = [0]

    def one():
        x = toks[pos[0]]; pos[0] += 1
        if x == '[':
            xs = []
            while toks[pos[0]] != ']':
                xs.append(one())
            pos[0] += 1
            r = xs[-1]
            for y in reversed(xs[:-1]):
                r = (y, r)
            return r
        if x == '~':
            return 0
        return int(x.replace('.', ''))
    return one()


def lst(n):
    out = []
    while n != 0:
        out.append(n[0]); n = n[1]
    return out


def need(n):
    """need-ordered as Lean."""
    h, t = n
    if isinstance(h, tuple):
        return '(.pair %s %s)' % (need(h), need(t))
    c = cord(h)
    if c == 'none': return '.none'
    if c == 'this': return '.this'
    if c == 'both': return '(.both %s %s)' % (need(t[0]), need(t[1]))
    raise Exception(c)


def cape(n):
    if isinstance(n, tuple):
        return '(.cell %s %s)' % (cape(n[0]), cape(n[1]))
    return '.yes' if n == 0 else '.no'


def loy(n): return 'true' if n == 0 else 'false'



def show(n):
    """need-ordered as Hoon text."""
    h, t = n
    if isinstance(h, tuple):
        return '[%s %s]' % (show(h), show(t))
    c = cord(h)
    if c in ('none', 'this'): return c
    return '[%%both %s %s]' % (show(t[0]), show(t[1]))
