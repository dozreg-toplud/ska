"""Hash-consed nouns, cue, jam and a plain Nock 4K interpreter.

Nouns are integers indexing NODES: an atom node is a Python int, a cell node
is a (head_id, tail_id) tuple.  Structurally equal nouns get the same id.
"""
import sys
sys.setrecursionlimit(1_000_000)

NODES = []          # id -> int | (h, t)
_ATOM = {}          # int -> id
_CELL = {}          # (h, t) -> id


def atom(n):
    i = _ATOM.get(n)
    if i is None:
        i = len(NODES)
        NODES.append(n)
        _ATOM[n] = i
    return i


def cell(h, t):
    k = (h, t)
    i = _CELL.get(k)
    if i is None:
        i = len(NODES)
        NODES.append(k)
        _CELL[k] = i
    return i


def is_atom(i):
    return type(NODES[i]) is int


def head(i):
    return NODES[i][0]


def tail(i):
    return NODES[i][1]


def val(i):
    n = NODES[i]
    assert type(n) is int
    return n


def cue(data):
    """data: little-endian bytes of the jammed atom."""
    n = int.from_bytes(data, 'little')
    bits = bin(n)[2:][::-1]          # bits[i] is bit i
    nb = len(bits)

    def rub(pos):
        # returns (bits consumed, value) of a mat-encoded atom at pos
        z = 0
        while bits[pos + z] == '0':
            z += 1
        if z == 0:
            return 1, 0
        lenbits = bits[pos + z + 1: pos + z + z]            # z-1 bits
        ln = (int(lenbits[::-1], 2) if lenbits else 0) | (1 << (z - 1))
        start = pos + z + z
        body = bits[start:start + ln]
        return z + z + ln, int(body[::-1], 2) if body else 0

    refs = {}
    # explicit stack to avoid deep recursion on long lists
    out = []            # value stack
    todo = [('cue', 0)]
    pos = 0
    while todo:
        op, arg = todo.pop()
        if op == 'cue':
            start = pos
            if bits[pos] == '0':
                used, v = rub(pos + 1)
                pos += 1 + used
                i = atom(v)
                refs[start] = i
                out.append(i)
            elif bits[pos + 1] == '0':
                pos += 2
                todo.append(('cons', start))
                todo.append(('cue', 0))
                todo.append(('cue', 0))
            else:
                used, v = rub(pos + 2)
                pos += 2 + used
                out.append(refs[v])
        else:
            t = out.pop()
            h = out.pop()
            i = cell(h, t)
            refs[arg] = i
            out.append(i)
    assert len(out) == 1
    return out[0]


def _mat(a):
    """(nbits, value) of the mat encoding of atom a."""
    if a == 0:
        return 1, 1
    b = a.bit_length()
    c = b.bit_length()
    # c zeros, a one, c-1 low bits of b, then a
    v = (1 << c) | ((b & ((1 << (c - 1)) - 1)) << (c + 1)) | (a << (c + c))
    return c + c + b, v


def jam(root):
    """Vere-compatible jam; returns the atom as a Python int."""
    chunks = []         # (nbits, value)
    pos = 0
    seen = {}
    todo = [root]
    while todo:
        i = todo.pop()
        n = NODES[i]
        if i in seen:
            rb, rv = _mat(seen[i])
            if type(n) is int:
                ab, av = _mat(n)
                if ab <= rb:
                    chunks.append((1 + ab, av << 1))
                    pos += 1 + ab
                    continue
            chunks.append((2 + rb, 3 | (rv << 2)))
            pos += 2 + rb
            continue
        seen[i] = pos
        if type(n) is int:
            ab, av = _mat(n)
            chunks.append((1 + ab, av << 1))
            pos += 1 + ab
        else:
            chunks.append((2, 1))
            pos += 2
            todo.append(n[1])
            todo.append(n[0])
    # assemble
    parts = []
    acc, accb = 0, 0
    for nb_, v in chunks:
        acc |= v << accb
        accb += nb_
        if accb >= 1 << 16:
            parts.append((accb, acc))
            acc, accb = 0, 0
    parts.append((accb, acc))
    res, sh = 0, 0
    for nb_, v in parts:
        res |= v << sh
        sh += nb_
    return res


def slot(axis, i):
    assert axis >= 1
    for b in bin(axis)[3:]:
        i = NODES[i][1] if b == '1' else NODES[i][0]
    return i


def edit(axis, new, i):
    if axis == 1:
        return new
    path = bin(axis)[3:]

    def go(k, i):
        if k == len(path):
            return new
        h, t = NODES[i]
        return cell(h, go(k + 1, t)) if path[k] == '1' else cell(go(k + 1, h), t)
    return go(0, i)


class Crash(Exception):
    pass


STEPS = 0


def nock(s, f):
    """*[s f] on ids."""
    global STEPS
    while True:
        STEPS += 1
        fn = NODES[f]
        if type(fn) is int:
            raise Crash('atom formula')
        op, arg = fn
        opn = NODES[op]
        if type(opn) is not int:
            return cell(nock(s, op), nock(s, arg))
        if opn == 0:
            try:
                return slot(val(arg), s)
            except Exception:
                raise Crash('slot %d' % val(arg))
        if opn == 1:
            return arg
        if opn == 2:
            b, c = NODES[arg]
            s, f = nock(s, b), nock(s, c)
            continue
        if opn == 3:
            return atom(1 if is_atom(nock(s, arg)) else 0)
        if opn == 4:
            return atom(val(nock(s, arg)) + 1)
        if opn == 5:
            b, c = NODES[arg]
            return atom(0 if nock(s, b) == nock(s, c) else 1)
        if opn == 6:
            b, cd = NODES[arg]
            c, d = NODES[cd]
            t = NODES[nock(s, b)]
            if t == 0:
                f = c
            elif t == 1:
                f = d
            else:
                raise Crash('bad test')
            continue
        if opn == 7:
            b, c = NODES[arg]
            s, f = nock(s, b), c
            continue
        if opn == 8:
            b, c = NODES[arg]
            s, f = cell(nock(s, b), s), c
            continue
        if opn == 9:
            b, c = NODES[arg]
            core = nock(s, c)
            s, f = core, slot(val(b), core)
            continue
        if opn == 10:
            bc, d = NODES[arg]
            b, c = NODES[bc]
            return edit(val(b), nock(s, c), nock(s, d))
        if opn == 11:
            b, c = NODES[arg]
            if not is_atom(b):
                nock(s, NODES[b][1])
            f = c
            continue
        raise Crash('op %r' % (opn,))


def tape(i):
    """cord atom -> str"""
    n = val(i)
    return n.to_bytes((n.bit_length() + 7) // 8, 'little').decode('latin1')


def cord(s):
    return int.from_bytes(s.encode(), 'little')


def size(root):
    """(#distinct cells, #distinct atoms, unshared tree size) below root."""
    seen = set()
    todo = [root]
    cells = atoms = 0
    while todo:
        i = todo.pop()
        if i in seen:
            continue
        seen.add(i)
        n = NODES[i]
        if type(n) is int:
            atoms += 1
        else:
            cells += 1
            todo.extend(n)
    return cells, atoms


def show(i, depth=4):
    n = NODES[i]
    if type(n) is int:
        return str(n) if n < 1 << 64 else '<atom %d bits>' % n.bit_length()
    if depth == 0:
        return '...'
    parts = []
    while type(NODES[i]) is not int and len(parts) < 8:
        parts.append(show(NODES[i][0], depth - 1))
        i = NODES[i][1]
    parts.append(show(i, depth - 1))
    return '[' + ' '.join(parts) + ']'
