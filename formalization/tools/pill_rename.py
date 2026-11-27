#!/usr/bin/env python3
"""usage: pill_rename.py NOTE.md ROOT [--apply]
Lists (and with --apply rewrites) whole-word uses of the OLD hash names of a
pill switch in ROOT/lemmas outside lemmas/Pill, and in ROOT/tools."""
import re, sys, os
note, root = sys.argv[1], sys.argv[2]; apply = '--apply' in sys.argv
pairs = dict(m.groups() for m in re.finditer(r'^(?:\*\s*)?((?:comp\.h|nh)[0-9a-f]{12})\s+((?:comp\.h|nh)[0-9a-f]{12})\b', open(note).read(), re.M))
print(len(pairs), 'pairs')
rx = re.compile(r'(?<![\w.])(' + '|'.join(re.escape(k) for k in pairs) + r')(?!\w)')
hits = 0
for base in ('lemmas', 'tools'):
    for d, _, fs in os.walk(os.path.join(root, base)):
        if '/lemmas/Pill' in d + '/': continue
        for f in fs:
            if not f.endswith(('.lean', '.py')): continue
            p = os.path.join(d, f); s = open(p).read()
            n = len(rx.findall(s))
            if n:
                hits += n; print(n, p)
                if apply: open(p, 'w').write(rx.sub(lambda m: pairs[m.group(1)], s))
print('uses of old names:', hits)
