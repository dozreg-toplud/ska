/-  *noir
|%
++  void  |=(* !!)
::  @uvre: register index 
::  @uwoo: basic block index
::
+$  need
  $^  [p=need q=need]
  ::  c: does the downstream code crash if this is not a cell?
  ::
  ::  if c, then head and tail are safe to access, but we must not crash
  ::  immediately when satisfying that need with an atom, we must defer
  ::  the crash till %cell check
  ::
  ::  else, we can crash immediately just fine, but we can't access the root
  ::  noun without a cell check
  ::
  $%  [%both r=@uvre c=? h=need t=need]
      [%this r=@uvre]
      [%none ~]
  ==
::    linear control flow
::
::  a label for code for some nock, and the shape of its subject
+$  next  $>(%next goal)
::
::    destination
::
::  codegen destination
::
::  %pick: result will be used as a loobean for Nock 6
::  %done: nock is in tail position, return result
::  %next: jump to given label with result in given $need
+$  goal
  $%  [%pick zero=@uwoo once=@uwoo]
      [%done ~]
      [%next what=need then=@uwoo]
  ==
::    instructions in a block
::
::  faces:
::  n - noun
::  d - destination
::  f - formula
::  h - head
::  k - key
::  l - label
::  r - result
::  s - source
::  t - tail
::  u - subject
::
::  cases:
::  %imm - write immediate n to d
::  %mov - copy s to d
::  %inc - increment s and write to d
::  %con - cons h and t into d
::  %hed - write head of s to d. Writes 0 if s is an atom
::  %tal - write tail of s to d. Writes 0 if s is an atom
::  %cel - crash if p is an atom
::  %spy - scry with ref in e, path in p, put in d
::  hint ops (except for %memo):
::
::  %his - static hint prologue
::  %hys - static hint epilogue, product of hinted formula in p
::  %hos - static hint epilogue, no product of hinted formula
::  %hid - arbitrary dynamic hint prologue, product of hint-formula in p
::  %hyd - arbitrary dynamic hint epilogue, product of hint-formula in p,
::         product of hinted formula in q
::  %hod - arbitrary dynamic hint epilogue, product of hint-formula in p (no
::         product of hinted formula)
::  memo instructions:
::    %mem - save noun `r` with key [k s f]
::
::  mute: product of the hinted formula not needed
::  prod: it is needed
::  stop: crash relocation boundary
::  safe: safe to relocate crashes
::
+$  hint-static-mute-safe  ?(%bout %xray)
+$  hint-static-mute-stop  void
+$  hint-static-mute  ?(hint-static-mute-safe hint-static-mute-stop)
+$  hint-static-prod  void
+$  hint-static-stop  ?(hint-static-mute-stop)
+$  hint-static  ?(hint-static-prod hint-static-mute)
::
+$  hint-dynamic-mute-stop  ?(%mean %spot)
+$  hint-dynamic-mute-safe  ?(%bout %xray %spin %loop %jinx %live %slog)
+$  hint-dynamic-mute  ?(hint-dynamic-mute-stop hint-dynamic-mute-safe)
+$  hint-dynamic-prod  void
+$  hint-dynamic-stop  ?(hint-dynamic-mute-stop)
+$  hint-dynamic  ?(hint-dynamic-mute hint-dynamic-prod)
::
+$  pole
  $%  [%imm n=* d=@uvre]
      [%mov s=@uvre d=@uvre]
      [%inc s=@uvre d=@uvre]
      [%con h=@uvre t=@uvre d=@uvre]
      [%hed s=@uvre d=@uvre]
      [%tal s=@uvre d=@uvre]
      [%cel p=@uvre]
      [%his n=hint-static f=*]
      [%hys n=hint-static-prod p=@uvre f=*]  ::  do we need formulas in non-memo stuff?
      [%hos n=hint-static-mute f=*]
  ::
      [%hid n=hint-dynamic p=@uvre f=*]
      [%hyd n=hint-dynamic-prod p=@uvre q=@uvre f=*]
      [%hod n=hint-dynamic-mute p=@uvre f=*]
      [%spy e=@uvre p=@uvre d=@uvre]
      [%mem k=@uvre s=@uvre f=* r=@uvre]  ::  memo slot [k f]?
  ==
::
::    control flow instructions
::
::  faces:
::  a - target arm
::  c - come-from block
::  d - destination
::  e - scry ref
::  f - formula
::  i - in cache
::  k - key
::  l - left source
::  m - cache miss
::  n - fast label and axis into battery
::  o - "one" / false case
::  p - scry path
::  r - right source
::  s - source
::  t - target block
::  u - subject
::  v - subject but registerized
::  z - "zero" / true case
::
::  cases:
::  %clq - if s is a cell goto z else goto o
::  %eqq - if l and r equal goto z else goto o
::  %brn - if s is 0 goto z, if 1 goto o, else crash
::  %hop - unconditionally go to t
::  %hip - set comefrom label to c and goto t
::  %lnk - evaluate f against u and put the result in d, then goto t
::  %cal - call the arm a with subject in registers v,
::         put result in d, and then goto t
::  %caf - like call but with fast label
::  %lnt - evaluate f against u in tail position
::  %jmp - call the arm a with subject in registers v, in
::         tail position
::  %jmf - like jmp but with fast label
::  %don - return value in s from current arm
::  %dom - return immediate value r
::  %bom - crash
::
::  %memo instructions:
::  %mim: check triple [k s f], write product to d if available and goto z,
::        else goto o
+$  site
  $%  [%clq s=@uvre z=@uwoo o=@uwoo]
      [%eqq l=@uvre r=@uvre z=@uwoo o=@uwoo]
      [%brn s=@uvre z=@uwoo o=@uwoo]
      [%hop t=@uwoo]
      [%hip c=@uwoo t=@uwoo]
      [%jmp a=bell v=(list @uvre)]
      [%jmf a=bell v=(list @uvre) n=ring]
      [%lnt u=@uvre f=@uvre]
      [%don s=@uvre]
      [%dom r=*]
      [%bom ~]
      [%mim k=@uvre s=@uvre f=* d=@uvre z=@uwoo o=@uwoo]
      ::
      ::  XX  these should be just poles
      [%lnk u=@uvre f=@uvre d=@uvre t=@uwoo]
      [%cal a=bell v=(list @uvre) d=@uvre t=@uwoo]
      [%caf a=bell v=(list @uvre) d=@uvre t=@uwoo n=ring]
  ==
::
++  get-regs-site
  |=  s=site
  ^-  (list @uvre)
  ?-  -.s
    %clq  ~[s.s]
    %eqq  ~[l.s r.s]
    %brn  ~[s.s]
    %hop  ~
    %hip  ~
    %lnk  ~[u.s f.s d.s]
    %cal  [d.s v.s]
    %caf  [d.s v.s]
    %lnt  ~[u.s f.s]
    %jmp  v.s
    %jmf  v.s
    %don  ~[s.s]
    %dom  ~
    %bom  ~
    %mim  ~[k s d]:s
  ==
::
++  get-regs-pole
  |=  p=pole
  ^-  (list @uvre)
  ?-  -.p
    %imm  ~[d]:p
    %mov  ~[s d]:p
    %inc  ~[s d]:p
    %con  ~[h t d]:p
    %hed  ~[s d]:p
    %tal  ~[s d]:p
    %cel  ~[p]:p
    %his  ~
    %hos  ~
    %hid  ~[p]:p
    %hod  ~[p]:p
    %spy  ~[e p d]:p
    %mem  ~[k s r]:p
    %hyd  ~[p q]:p
    %hys  ~[p]:p
  ==
::    basic block
::
::  phi: which registers are set according to the comefrom label to values from
::    which registers
::  body: list of data-flow instructions
::  bend: final control-flow instruction
::
+$  blob  [phi=(map @uvre (map @uwoo @uvre)) body=(list pole) bend=site]
::
::  XX want to know the shape of the control flow: what is the join
::  block of branches that are entered from a given block, if it exists
::  (map @uwoo @uwoo)
::
+$  straight
  $:  =need
      ::  these are hardcoded
      ::
      :: entry=@uwoo 0w1
      :: args=(list @uvre)  ~[0v0 0v1 ... 0v(n-args - 1)]
      n-args=@ud
      blocks=(map @uwoo blob)
      =bell
  ==
::
+$  line-long
  $:  code=(map bell straight)
      arity=(map bell meme-args)
      =boil
      jet-args=(map ring shape-final)
  ==
::
+$  line-short
  $:  line-long
      re-gen=@uvre
      bo-gen=_`@uwoo`2
      $=  here
      $:  blocks=(map @uwoo blob)
  ==  ==
--