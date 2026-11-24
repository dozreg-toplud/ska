#!/usr/bin/env python3
"""Generate walkLazy_okDI, walkForks_okDI, walkBonds_okDI (walkLazy_okD with an
invariant I of the states that the gate needs at its start) from the text of
the mutual block in lemmas/Ska/CompCollapseGate.lean.  Prints the Lean text;
each replacement asserts its match count."""
import sys
src = open(sys.argv[1]).read()
a = src.index('mutual\ntheorem walkLazy_okD')
b = src.index('\nend\n', a) + len('\nend\n')
t = src[a:b]
def rep(old, new, n):
    global t
    k = t.count(old)
    assert k == n, (old, k, n)
    t = t.replace(old, new)
rep('_okD ', '_okDI ', 10)
rep('_okD\n', '_okDI\n', 0)
rep("(cb : ∀ a b : Gen Map, C a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k)",
    "(cb : ∀ a b : Gen Map, C a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k)\n    {I : Gen Map → Prop} (ci : ∀ a b : Gen Map, C a b → I a → I b)", 3)
rep("(hf : GateOKD C P f)", "(hf : GateOKDI C I P f)", 3)
rep("    g.drop = false → (((o, l) :: entries l).map Prod.fst).Nodup → WalkOKD",
    "    g.drop = false → I g → (((o, l) :: entries l).map Prod.fst).Nodup → WalkOKD", 1)
rep("    g.drop = false → ((forkEntries fk).map Prod.fst).Nodup → WalkOKD",
    "    g.drop = false → I g → ((forkEntries fk).map Prod.fst).Nodup → WalkOKD", 1)
rep("    g.drop = false → ((bondEntries bd).map Prod.fst).Nodup → WalkOKD",
    "    g.drop = false → I g → ((bondEntries bd).map Prod.fst).Nodup → WalkOKD", 1)
rep("  | o, mk s fk bd, g, g', h, hd, hn => by", "  | o, mk s fk bd, g, g', h, hd, hI, hn => by", 1)
rep("    have W1 := hf o (mk s fk bd) g g1 h1 hd\n",
    "    have W1 := hf o (mk s fk bd) g g1 h1 hd hI\n    have hI1 := ci _ _ W1.cnd hI\n", 1)
rep("walkForks_okDI cr ct cb pm hf fk g1 g2 h2 d1 (", "walkForks_okDI cr ct cb ci pm hf fk g1 g2 h2 d1 hI1 (", 1)
rep("walkBonds_okDI cr ct cb pm hf bd g2 g' h3 (WF.drop.trans d1) (",
    "walkBonds_okDI cr ct cb ci pm hf bd g2 g' h3 (WF.drop.trans d1) (ci _ _ WF.cnd hI1) (", 1)
rep("  | [], g, g', h, _, _ => by", "  | [], g, g', h, _, _, _ => by", 2)
rep("  | ((oy, y), (on, n)) :: rest, g, g', h, hd, hn => by", "  | ((oy, y), (on, n)) :: rest, g, g', h, hd, hI, hn => by", 1)
rep("walkLazy_okDI cr ct cb pm hf oy y g g1 h1 hd hn2.1", "walkLazy_okDI cr ct cb ci pm hf oy y g g1 h1 hd hI hn2.1", 1)
rep("walkLazy_okDI cr ct cb pm hf on n g1 g2 h2 (Wy.drop.trans hd) hn2.2.1",
    "walkLazy_okDI cr ct cb ci pm hf on n g1 g2 h2 (Wy.drop.trans hd) (ci _ _ Wy.cnd hI) hn2.2.1", 1)
rep("walkForks_okDI cr ct cb pm hf rest g2 g' h3 (Wn.drop.trans (Wy.drop.trans hd)) hn1.2.1",
    "walkForks_okDI cr ct cb ci pm hf rest g2 g' h3 (Wn.drop.trans (Wy.drop.trans hd)) (ci _ _ Wn.cnd (ci _ _ Wy.cnd hI)) hn1.2.1", 1)
rep("  | (o, l) :: rest, g, g', h, hd, hn => by", "  | (o, l) :: rest, g, g', h, hd, hI, hn => by", 1)
rep("walkLazy_okDI cr ct cb pm hf o l g g1 h1 hd hn1.1", "walkLazy_okDI cr ct cb ci pm hf o l g g1 h1 hd hI hn1.1", 1)
rep("walkBonds_okDI cr ct cb pm hf rest g1 g' h2 (Wl.drop.trans hd) hn1.2.1",
    "walkBonds_okDI cr ct cb ci pm hf rest g1 g' h2 (Wl.drop.trans hd) (ci _ _ Wl.cnd hI) hn1.2.1", 1)
assert t.rstrip().endswith('Wl.trans ct cb pm Wr (nodup_disj hn)\nend'), t[-200:]
print(t, end='')
