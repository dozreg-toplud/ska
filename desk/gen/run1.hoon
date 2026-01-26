/+  *skan
::
:-  %say  |=  *  :-  %noun
::
=/  cor
  =>  ~
  =/  c=@  0
  |%
  ++  bump  .(c +(c))
  ++  jump
    =*  this  .
    |-  ^+  this
    ?:  =(c 10)
      this
    $(this bump)
  ::
  ++  post  bump:jump
  --
::
=/  fol
  =>  cor  !=
  post
::
~>  %bout
(run-nomm cor fol)