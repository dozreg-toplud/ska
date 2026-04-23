/*  sock  %hoon  /sur/sock/hoon
/*  noir  %hoon  /sur/noir/hoon
/*  gene  %hoon  /sur/gene/hoon
/*  soak  %hoon  /lib/soak/hoon
/*  skan  %hoon  /lib/smol/skan/hoon
/*  line  %hoon  /lib/line/hoon
::
/*  vere-interface  %hoon  /lib/vere-interface/hoon
::
=<
  =/  test
    =/  zus  !>(..zuse)
    =/  sock-hoon  hoon:(p sock)
    =/  soak-hoon  hoon:(p soak)
    =/  noir-hoon  hoon:(p noir)
    =/  skan-hoon  hoon:(p skan)
    =/  gene-hoon  hoon:(p gene)
    =/  line-hoon  hoon:(p line)
    =/  vere-hoon  hoon:(p vere-interface)
    =/  sock-vase  (slap zus sock-hoon)
    =/  soak-vase  (slap (slop sock-vase zus) soak-hoon)
    =/  noir-vase  (slap (slop soak-vase zus) noir-hoon)
    =/  gene-vase  (slap (slop noir-vase zus) gene-hoon)
    =/  skan-vase  (slap :(slop (with-face %gene gene-vase) noir-vase zus) skan-hoon)
    =/  line-vase  (slap :(slop skan-vase (with-face %gene gene-vase) zus) line-hoon)
    =/  vere-vase  (slap :(slop (with-face %line-dor line-vase) (with-face %skan skan-vase) zus) vere-hoon)
    %+  slap  vere-vase
    !,  *hoon
    =<  -
    (compile 0 [4 0 1])
  ::
  ~&  test
  =/  fol
    !.
    =>  [sock-hoon=*hoon soak-hoon=*hoon noir-hoon=*hoon skan-hoon=*hoon gene-hoon=*hoon line-hoon=*hoon vere-hoon=*hoon ..zuse]
    !=
    =/  zus  !>(..zuse)
    =/  with-face  |=([face=@tas =vase] vase(p [%face face p.vase]))
    =/  sock-vase  (slap zus sock-hoon)
    =/  soak-vase  (slap (slop sock-vase zus) soak-hoon)
    =/  noir-vase  (slap (slop soak-vase zus) noir-hoon)
    =/  gene-vase  (slap (slop noir-vase zus) gene-hoon)
    =/  skan-vase  (slap :(slop (with-face %gene gene-vase) noir-vase zus) skan-hoon)
    =/  line-vase  (slap :(slop skan-vase (with-face %gene gene-vase) zus) line-hoon)
    =/  vere-vase  (slap :(slop (with-face %line-dor line-vase) (with-face %skan skan-vase) zus) vere-hoon)
    vere-vase
  ::
  (jam fol hoon:(p sock) hoon:(p soak) hoon:(p noir) hoon:(p skan) hoon:(p gene) hoon:(p line) hoon:(p vere-interface))
::
|%
++  with-face  |=([face=@tas =vase] vase(p [%face face p.vase]))
++  p  (cork trip (cury parse-pile ~))
++  parse-pile
  |=  [pax=path tex=tape]
  ^-  pile:clay
  =/  [=hair res=(unit [=pile:clay =nail])]
    ((pile-rule pax) [1 1] tex)
  ::
  ?^  res  pile.u.res
  %-  mean
  =/  lyn  p.hair
  =/  col  q.hair
  ^-  (list tank)
  :~  leaf+"syntax error at [{<lyn>} {<col>}] in {<pax>}"
    ::
      =/  =wain  (to-wain:format (crip tex))
      ?:  (gth lyn (lent wain))
        '<<end of file>>'
      (snag (dec lyn) wain)
    ::
      leaf+(runt [(dec col) '-'] "^")
  ==
::
++  pile-rule
  |=  pax=path
  %-  full
  %+  ifix
    :_  gay
    ::  parse optional /? and ignore
    ::
    ;~(plug gay (punt ;~(plug fas wut gap dem gap)))
  |^
  ;~  plug
    %+  cook  (bake zing (list (list taut:clay)))
    %+  rune  hep
    (most ;~(plug com gaw) taut-rule)
  ::
    %+  cook  (bake zing (list (list taut:clay)))
    %+  rune  lus
    (most ;~(plug com gaw) taut-rule)
  ::
    %+  rune  tis
    ;~(plug sym ;~(pfix gap stap))
  ::
    %+  rune  sig
    ;~((glue gap) sym wyde:vast stap)
  ::
    %+  rune  cen
    ;~(plug sym ;~(pfix gap ;~(pfix cen sym)))
  ::
    %+  rune  buc
    ;~  (glue gap)
      sym
      ;~(pfix cen sym)
      ;~(pfix cen sym)
    ==
  ::
    %+  rune  tar
    ;~  (glue gap)
      sym
      ;~(pfix cen sym)
      ;~(pfix stap)
    ==
  ::
    %+  stag  %tssg
    (most gap tall:(vang & pax))
  ==
  ::
  ++  pant
    |*  fel=rule
    ;~(pose fel (easy ~))
  ::
  ++  mast
    |*  [bus=rule fel=rule]
    ;~(sfix (more bus fel) bus)
  ::
  ++  rune
    |*  [bus=rule fel=rule]
    %-  pant
    %+  mast  gap
    ;~(pfix fas bus gap fel)
  --
::
++  taut-rule
  %+  cook  |=(taut:clay +<)
  ;~  pose
    (stag ~ ;~(pfix tar sym))
    ;~(plug (stag ~ sym) ;~(pfix tis sym))
    (cook |=(a=term [`a a]) sym)
  ==
--
