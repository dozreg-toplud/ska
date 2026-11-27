"""The pieces of push 8 of `spRest` (`srSccs`, `+tarjan` under `%poke-tarjan`)
as Lean literals, for `lemmas/Compiler/CompTarjanPoke.lean` (track Q).
Run: python3 tools/gen/tarjanpoke.py"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nouns
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'lemmas', 'Compiler',
                        'PokeLinkRestCut.lean')).read()
t = nouns.parse(re.search(r'def srSccs : Noun :=\n  (.*)\n', src).group(1))

def pat(s):
    toks = re.findall(r'\[|\]|\?[a-zA-Z]+|0x[0-9a-f]+|[0-9]+', s)
    pos = [0]
    def item():
        tk = toks[pos[0]]; pos[0] += 1
        if tk == '[':
            xs = []
            while toks[pos[0]] != ']':
                xs.append(item())
            pos[0] += 1
            n = xs[-1]
            for x in reversed(xs[:-1]):
                n = ('C', x, n)
            return n
        if tk.startswith('?'):
            return ('V', tk[1:])
        return ('A', int(tk, 0))
    return item()

def match(n, p, env):
    if p[0] == 'V':
        env[p[1]] = n; return
    if p[0] == 'A':
        assert n == p, (n, p); return
    assert n[0] == 'C'
    match(n[1], p[1], env); match(n[2], p[2], env)

env = {}
match(t, pat('[6 [5 [1 0] 0 2] [1 0] 8 ?flopdoor 9 2 10 [6 7 [0 3] 7 [8 [1 ?trap] ?hint] 9 2 0 1] 0 2]'), env)
match(env['trap'], pat('[8 [9 2815 0 0x7fff] 9 2 10 [6 7 [0 3] ?jug] 0 2]'), env)
match(env['jug'], pat('[8 [8 [9 0x17d7 0 0x7ffffff] 9 767 10 [6 0 14] 0 2] 9 2 10 [6 7 [0 3] 8 [1 ?bunt] [1 ?gb] 0 1] 0 2]'), env)
match(env['gb'], pat('[8 [8 [9 0x17d7 0 0x1fffffff] 9 340 10 [6 0 29] 0 2] 9 2 10 [6 [0 56] 7 [0 3] ?silt] 0 2]'), env)
match(env['silt'], pat('[8 [9 767 0 0x1fffffff] 9 2 10 [6 7 [0 3] ?skim] 0 2]'), env)
match(env['skim'], pat('[8 [9 0x5f7bb 0 0x1fffffff] 9 2 10 [6 ?tap 7 [0 3] 8 [1 ?hbunt] [1 ?hb] 0 1] 0 2]'), env)
match(env['tap'], pat('[7 [0 3] 8 [9 0x17d6 0 0x1fffffff] 9 186 10 [6 0 230] 0 2]'), env)
match(env['hb'], pat('[8 [8 [9 0x17d7 0 0x7fffffff] 9 3061 10 [6 0 254] 0 2] 9 2 10 [6 0 14] 0 2]'), env)

def lean(p):
    if p[0] == 'V': return p[1]
    if p[0] == 'A': return '(A %s)' % (str(p[1]) if p[1] < 4096 else hex(p[1]))
    return '(C %s %s)' % (lean(p[1]), lean(p[2]))

# the pieces, innermost first; a `?name` is the Lean name of a piece
pieces = [
  ('tpHBunt', None, env['hbunt']),
  ('tpHB', None, env['hb']),
  ('tpTap', None, env['tap']),
  ('tpSkim', '[8 [9 0x5f7bb 0 0x1fffffff] 9 2 10 [6 ?tpTap 7 [0 3] 8 [1 ?tpHBunt] [1 ?tpHB] 0 1] 0 2]', None),
  ('tpSilt', '[8 [9 767 0 0x1fffffff] 9 2 10 [6 7 [0 3] ?tpSkim] 0 2]', None),
  ('tpPutDoor', '[8 [9 0x17d7 0 0x1fffffff] 9 340 10 [6 0 29] 0 2]', None),
  ('tpGB', '[8 ?tpPutDoor 9 2 10 [6 [0 56] 7 [0 3] ?tpSilt] 0 2]', None),
  ('tpBunt', None, env['bunt']),
  ('tpRepDoor', '[8 [9 0x17d7 0 0x7ffffff] 9 767 10 [6 0 14] 0 2]', None),
  ('tpJug', '[8 ?tpRepDoor 9 2 10 [6 7 [0 3] 8 [1 ?tpBunt] [1 ?tpGB] 0 1] 0 2]', None),
  ('tpTrap', '[8 [9 2815 0 0x7fff] 9 2 10 [6 7 [0 3] ?tpJug] 0 2]', None),
  ('tpHint', None, env['hint']),
  ('tpRun', '[7 [8 [1 ?tpTrap] ?tpHint] 9 2 0 1]', None),
  ('tpFlop', '[9 0x2fbd7f 0 0x3ffffff]', None),
]
for name, ps, n in pieces:
    body = nouns.lean(n) if n is not None else lean(pat(ps))
    print('def %s : Noun :=\n  %s\n' % (name, body))
print('theorem srSccs_eq : srSccs = %s := rfl' % lean(pat('[6 [5 [1 0] 0 2] [1 0] 8 ?tpFlop 9 2 10 [6 7 [0 3] ?tpRun] 0 2]')))
