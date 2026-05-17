/+  v=vere-interface
/+  hoot-zpdt-fol
/+  hoot-zpdt
::
=/  memo-call
  =>  ..ride
  |*  [g=gate v=*]
  %-  need  %-  ~(mole vi |)
  |.  =>  [g=g v=v]
  !.  ~>  %memo./user
  (g v)  
::
=/  print-noun
  |=  n=*
  ^-  tape
  =/  n-tape=tape  <n>
  ?:  (lth (lent n-tape) 100)  n-tape
  (weld (scag 100 n-tape) "...")
::
=/  print-bell
  |=  b=bell:line-dor:v
  ^-  tape
  "bell={<`@ux`(mug b)>}"
::
=/  print-vere-op
  |=  op=vere-op:line-dor:v
  ^-  tape
  =*  this-gate  .
  ?+  -.op  <op>
    %imm  <op(n (print-noun n.op))>
    %his  <op(f (print-noun f.op))>
    %hys  <op(f (print-noun f.op))>
    %hos  <op(f (print-noun f.op))>
    %hid  <op(f (print-noun f.op))>
    %hyd  <op(f (print-noun f.op))>
    %hod  <op(f (print-noun f.op))>
    %mem  <op(f (print-noun f.op))>
    %cal  <op(a (print-bell a.op))>
    %caf  <op(a (print-bell a.op))>
    %clq  <op(z `tape`(zing (join " " (turn z.op this-gate))), o `tape`(zing (join " " (turn o.op this-gate))))>
    %eqq  <op(z `tape`(zing (join " " (turn z.op this-gate))), o `tape`(zing (join " " (turn o.op this-gate))))>
    %brn  <op(z `tape`(zing (join " " (turn z.op this-gate))), o `tape`(zing (join " " (turn o.op this-gate))))>
    %mim  <op(z `tape`(zing (join " " (turn z.op this-gate))), o `tape`(zing (join " " (turn o.op this-gate))), f (print-noun f.op))>
    %jmp  <op(a (print-bell a.op))>
    %jmf  <op(a (print-bell a.op))>
    %dom  <op(r (print-noun r.op))>
  ==
::
=/  print-vere-ops
  |=  ops=(list vere-op:line-dor:v)
  ^-  tape
  %+  murn  `tape`(zing (join " " (turn ops print-vere-op)))
  |=  c=char
  ^-  (unit char)
  ?:  =('"' c)   ~
  ?:  =('\\' c)  ~
  `c
::
=/  invert
  |*  m=(map)
  ?:  =(~ m)  ~
  %-  ~(gas by *(map _,.->.m _,.-<.m))
  (turn ~(tap by m) |=([a=_,.-<.m b=_,.->.m] [b a]))
::
|=  *
^-  tape
=.  v  +:(memo-call compile:v ~ hoot-zpdt-fol)
=/  sub
  =;  fol  .*(..dec:hoot-zpdt fol)
  !.  =>  ..dec:hoot-zpdt  !=
  |=  [m=@ n=@]
  ^-  @
  ?:  =(0 m)  +(n)
  ?:  =(0 n)  $(m (dec m), n 1)
  $(m (dec m), n $(n (dec n)))
::
=/  fol
  !.
  =>  sub  !=
  :: (. 3 8)
  .*([. 3 8] [9 2 10 [6 0 3] 0 2])
::
=^  sock  v  (compile:v sub fol)
~&  .*(sub fol)
(print-vere-ops -:(vere-straighten:v [sock fol] &))