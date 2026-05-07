/*  sock  %hoon  /lib/smol/sock/hoon
/*  noir  %hoon  /lib/smol/noir/hoon
/*  gene  %hoon  /lib/smol/gene/hoon
/*  soak  %hoon  /lib/smol/soak/hoon
/*  skan  %hoon  /lib/smol/skan/hoon
/*  line  %hoon  /lib/smol/line/hoon
::
/*  vere-interface  %hoon  /lib/smol/vere-interface/hoon
::
=/  fol
  !:
  =>  [[sock-hoon=*@t soak-hoon=*@t noir-hoon=*@t skan-hoon=*@t gene-hoon=*@t line-hoon=*@t vere-hoon=*@t] zus=*vase ..zuse]
  !=
  ?>  =(hoon-version 135)
  ?>  =(zuse 408)
  =/  with-face  |=([face=@tas =vase] vase(p [%face face p.vase]))
  =/  sock-hoon  (ream sock-hoon)
  =/  soak-hoon  (ream soak-hoon)
  =/  noir-hoon  (ream noir-hoon)
  =/  gene-hoon  (ream gene-hoon)
  =/  skan-hoon  (ream skan-hoon)
  =/  line-hoon  (ream line-hoon)
  =/  vere-hoon  (ream vere-hoon)
  ::
  =/  sock-vase  ~>  %bout  (slap zus sock-hoon)
  =/  soak-vase  ~>  %bout  (slap (slop sock-vase zus) soak-hoon)
  =/  noir-vase  ~>  %bout  (slap (slop soak-vase zus) noir-hoon)
  =/  gene-vase  ~>  %bout  (slap (slop noir-vase zus) gene-hoon)
  =/  skan-vase  ~>  %bout  (slap :(slop (with-face %gene gene-vase) noir-vase zus) skan-hoon)
  =/  line-vase  ~>  %bout  (slap :(slop skan-vase (with-face %gene gene-vase) zus) line-hoon)
  =/  vere-vase  ~>  %bout  (slap :(slop (with-face %line-dor line-vase) (with-face %skan skan-vase) zus) vere-hoon)
  vere-vase
::
=/  out  [fol sock+sock soak+soak noir+noir skan+`@t`skan gene+gene line+line vere+vere-interface]
=-  out
~>  %bout
.*([[+.&2.out +.&3.out +.&4.out +.&5.out +.&6.out +.&7.out +.|7.out] !>(..zuse) ..zuse] &1.out)