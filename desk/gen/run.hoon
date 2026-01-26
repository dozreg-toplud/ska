/-  *noir
/+  skan
/+  playpen
/+  hoot
::
:-  %say  |=  *  :-  %noun
::
:: =/  cor
::   !.
::   ..scow:hoot
::   :: =>  ~
::   :: |.
::   :: =/  once  |=(@ +(+<))
::   :: =/  dabl  =>  +  |=(@ +(+(+<)))
::   :: =/  slam  |=(g=$-(@ @) |=(n=@ (g n)))
::   :: [((slam once) 1) ((slam dabl) 1)]
::   :: %.  3
::   :: |=  n=@
::   :: ^-  @
::   :: ?<  =(0 n)
::   :: =/  c  0
::   :: |-  ^-  @
::   :: ?:  =(+(c) n)  c
::   :: $(c +(c))
:: ::
:: =/  fol
::   !.  =>  cor
::   !.  !=
::   (scow %ud 5)
  :: [9 2 0 1]
=/  cor
  !.
  =>  ..ride:hoot
  |%
  ++  test  (expr-parse "3+3+4+1+2")
  ++  expr-parse
    |=  math=tape
    (scan math expr)
    ::
  ++  expr
    %+  knee  *@ud
    |.  ~+
    ;~  pose
      ((slug add) lus ;~(pose dem expr))
      dem
    ==
  --
::
=/  fol
  !.  =>  cor
  !.  !=
  test
::
~>  %bout
(run-nomm:skan cor fol)