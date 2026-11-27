:: hintdump.hoon: hints through +comp (README Gaps 24, lemmas/Ska/CompHintCheck.lean).
:: For each formula, for a subject sock that knows nothing: the nomm after the analysis and the
:: raw blocks (before +optimize) of the whole-subject version (+compiled-mono) and of the n-ary
:: version, as one @ux jam of [nomm [mono-need mono-nargs mono-blocks] [nary-need nary-nargs
:: nary-blocks] fol] with the blocks sorted by label; then, for each subject, +mink's tone and the
:: tone of the raw whole-subject code under +eval-blob (traces raw: the frames of %hcp/%hmp are
:: %meac/%meaf), with no scry gate and with the gate |=(^ ``[%v +<]).
=/  r=*  [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]
=/  ss=(list *)  ~[[1 2] [1 [2 3]] [[1 2] 3] [0 1] [[0 1] 0]]
=/  cases=(list [nam=@tas fol=*])
  :~  [%s01 [11 %bout [0 3]]]
      [%s02 [11 %spot [0 3]]]
      [%s03 [11 %foo [4 [0 3]]]]
      [%s04 [[11 %bout [0 2]] [0 3]]]
      [%s05 [4 [11 %xray [0 3]]]]
      [%s06 [11 %bout [7 [0 3] [4 [0 1]]]]]
      [%s07 [7 [11 %bout [0 3]] [4 [0 2]]]]
      [%d01 [11 [%spot [1 [1 2] 3]] [0 3]]]
      [%d02 [11 [%spot [0 2]] [4 [0 3]]]]
      [%d03 [11 [%slog [1 0 %foo]] [0 3]]]
      [%d04 [11 [%memo [0 2]] [4 [0 3]]]]
      [%d05 [11 [%foo [0 2]] [4 [0 3]]]]
      [%d06 [11 [%foo [1 7]] [4 [0 3]]]]
      [%d07 [11 [[1 2] [0 2]] [4 [0 3]]]]
      [%d08 [11 [%hunk [0 2]] [4 [0 3]]]]
      [%d09 [11 [%xray [0 2]] [4 [0 3]]]]
      [%d10 [11 [%spot [1 0]] [11 [%spot [1 1]] [4 [0 3]]]]]
      [%d11 [[11 [%spot [1 0]] [4 [0 2]]] [11 [%spot [1 1]] [4 [0 3]]]]]
      [%d12 [7 [11 [%spot [1 0]] [0 3]] [4 [0 2]]]]
      [%d13 [7 [11 [%spot [1 0]] [[0 2] [0 3]]] [4 [0 2]]]]
      [%d14 [7 [0 3] [11 [%spot [0 1]] [4 [0 1]]]]]
      [%d15 [5 [11 [%spot [1 0]] [0 2]] [0 3]]]
      [%d16 [6 [11 [%spot [0 2]] [5 [0 2] [0 3]]] [1 0] [1 1]]]
      [%d17 [6 [3 [0 2]] [11 [%spot [1 0]] [4 [0 2]]] [11 [%spot [1 1]] [4 [0 3]]]]]
      [%d18 [11 [%spot [0 2]] [6 [0 3] [1 1] [1 2]]]]
      [%d19 [4 [11 [%spot [1 0]] [4 [0 3]]]]]
      [%d20 [10 [2 [11 [%spot [1 0]] [4 [0 3]]]] [0 1]]]
      [%d21 [11 [%spot [1 0]] [2 [0 3] [0 2]]]]
      [%d22 [11 [%spot [1 0]] [8 [1 r] [9 2 [0 1]]]]]
      [%d23 [11 [%spot [0 6]] [0 3]]]
      [%m01 [11 [%mean [1 [1 %leaf 120]]] [4 [0 3]]]]
      [%m02 [11 [%mean [[1 [1 %leaf 120]] [0 1]]] [4 [0 3]]]]
      [%m03 [11 [%mean [[1 [0 3]] [0 1]]] [4 [0 3]]]]
      [%m04 [7 [11 [%mean [[1 [1 %leaf 120]] [0 1]]] [0 3]] [4 [0 2]]]]
      [%c01 [12 [1 %ref] [1 %path]]]
      [%c02 [12 [0 2] [0 3]]]
      [%c03 [[12 [1 1] [0 2]] [0 3]]]
      [%c04 [12 [1 0] [11 [%spot [1 0]] [0 3]]]]
      [%c05 [4 [12 [0 2] [0 3]]]]
  ==
=/  gul  |=(a=^ ``[%v a])
|-  ^-  @
?~  cases  0
=.  nary.cache.state  ~
=.  mono.cache.state  ~
=^  [func=bell new=(list [pax=path tem=sock clue=*])]  long-ska.state
  (ska-poke [[| ~] ?>(?=(^ fol.i.cases) fol.i.cases)] long-ska.state ~(key by jets-hot.state))
=^  scc=(set bell)  sccs.cache.state
  (scc-of func calls.long-ska.state sccs.cache.state)
=^  raw=straight  cache.state  (compiled-mono func scc)
=/  nar=straight  (~(gut by nary.cache.state) func *straight)
=/  bl  (sort ~(tap by blocks.raw) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
=/  nb  (sort ~(tap by blocks.nar) |=([a=[k=@ *] b=[k=@ *]] (lth k.a k.b)))
=/  nom  nomm:(~(got by code.long-ska.state) func)
~&  [%case nam.i.cases less=less.func mono=[need.raw n-args.raw (lent bl)] nary=[need.nar n-args.nar (lent nb)]]
~&  [%nomm nam.i.cases nom]
~&  [%jam nam.i.cases `@ux`(jam [nom [need.raw n-args.raw bl] [need.nar n-args.nar nb] fol.i.cases])]
=/  s  ss
|-
?~  s  ^$(cases t.cases)
=/  a=tone  (mink [i.s fol.i.cases] ~)
=/  b
  %-  mule  |.
  -:(eval-blob [[[`@`0 `i.s] ~ ~] ~] (~(got by blocks.raw) 0w0) raw ~ ~)
=/  a2=tone  (mink [i.s fol.i.cases] gul)
=/  b2
  %-  mule  |.
  -:(eval-blob [[[`@`0 `i.s] ~ ~] ~] (~(got by blocks.raw) 0w0) raw ~ gul)
~&  :*  %run  nam.i.cases  `*`i.s
        mink=`*`a
        ir=?:(?=(%| -.b) %interpreter-crashed `*`p.b)
        mink-g=`*`a2
        ir-g=?:(?=(%| -.b2) %interpreter-crashed `*`p.b2)
    ==
$(s t.s)
