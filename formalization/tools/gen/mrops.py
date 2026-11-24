"""Writes the 25 lemmas `mr_op_<tag>` of Compiler/CompMapRegs.lean (the op
gate of `+map-regs` on one op of each tag) from one template, between the
lines `-- BEGIN mrops` and `-- END mrops`, and the case split `mr_op`.
Run from formalization/."""
import re
OPS = [
    ('imm', '(n : Noun) (d : Nat)', 'n d'), ('mov', '(s d : Nat)', 's d'),
    ('inc', '(s d : Nat)', 's d'), ('con', '(h t d : Nat)', 'h t d'),
    ('hed', '(s d : Nat)', 's d'), ('tal', '(s d : Nat)', 's d'),
    ('cel', '(p : Nat)', 'p'), ('lob', '(p : Nat)', 'p'), ('equ', '(l r : Nat)', 'l r'),
    ('hsp', '(n : Nat) (f : Noun)', 'n f'), ('hse', '(n : Nat) (f : Noun)', 'n f'),
    ('hdp', '(n p : Nat) (f : Noun)', 'n p f'), ('hde', '(n p : Nat) (f : Noun)', 'n p f'),
    ('hmp', '(a : Bell) (v : List Nat) (f : Noun)', 'a v f'),
    ('hme', '(a : Bell) (v : List Nat) (f : Noun)', 'a v f'),
    ('hcp', '(n f : Noun)', 'n f'), ('hce', '(n f : Noun)', 'n f'),
    ('spy', '(e p d : Nat)', 'e p d'), ('nok', '(u f d : Nat)', 'u f d'),
    ('cal', '(a : Bell) (v : List Nat) (d : Nat)', 'a v d'),
    ('caf', '(a : Bell) (v : List Nat) (d : Nat) (n : Ring)', 'a v d n'),
    ('cam', '(a : Bell) (v : List Nat) (d : Nat) (k : Noun)', 'a v d k'),
    ('csl', '(a : Bell) (s d : Nat)', 'a s d'),
    ('csf', '(a : Bell) (s d : Nat) (n : Ring)', 'a s d n'),
    ('csm', '(a : Bell) (s d : Nat) (k : Noun)', 'a s d k'),
]
TURN = {'hmp', 'hme', 'cal', 'caf', 'cam'}
out = []
for tag, binders, args in OPS:
    ht = '\n  have ht := mr_turn_ren RB RS RC ren hren v' if tag in TURN else ''
    extra = ', hT, turn.arm_at, ht' if tag in TURN else ''
    out.append(f'''theorem mr_op_{tag} (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) {binders} :
    nock (C X (C (Pole.toNoun (Pole.{tag} {args})) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.{tag} {args}))) := by{ht}
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.{tag}, hren{extra}]
''')
cases = '\n'.join(f'  | {tag} {args} => exact mr_op_{tag} X RJ I bN MB RB RS RC T ren hren hT {args}'
                  for tag, _, args in OPS)
out.append(f'''/-- **The op gate of `+map-regs`** on any op: `renPole ren op`. -/
theorem mr_op (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (op : Pole) :
    nock (C X (C (Pole.toNoun op) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren op)) := by
  cases op with
{cases}
''')
path = 'lemmas/Compiler/CompMapRegs.lean'
text = open(path).read()
pat = re.compile(r'(-- BEGIN mrops\n).*?(-- END mrops\n)', re.S)
assert len(pat.findall(text)) == 1
text = pat.sub(lambda m: m.group(1) + '\n'.join(out) + m.group(2), text)
open(path, 'w').write(text)
