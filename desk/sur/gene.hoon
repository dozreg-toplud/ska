/-  *noir
|%
::  @uvre: register index 
::  @uwoo: basic block index
::  @uxor: function index
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
::  static hints that do not need the result of the hinted formula
::
+$  hint-static-mute  ?(%bout %xray)
::  static hints that need the result of the hinted formula
::
::  there are none, and I don't know how to express void type w/o mint-vain...
::
:: +$  hint-static-prod  _!!
::
+$  hint-dynamic-mute-stop  ?(%mean %spot)
+$  hint-dynamic-mute-safe  ?(%bout %xray %spin %loop %jinx %live)
+$  hint-dynamic-mute  ?(hint-dynamic-mute-stop hint-dynamic-mute-safe)
+$  hint-dynamic-prod-safe  ?(%slog)
+$  hint-dynamic  ?(hint-dynamic-prod-safe hint-dynamic-mute)
::
+$  pole
  $%  [%imm n=* d=@uvre]
      [%mov s=@uvre d=@uvre]
      [%inc s=@uvre d=@uvre]
      [%con h=@uvre t=@uvre d=@uvre]
      [%hed s=@uvre d=@uvre]
      [%tal s=@uvre d=@uvre]
      [%cel p=@uvre]
      ::  XX save original hinted formulas?
      ::
      [%his n=hint-static-mute f=nomm-1]
      :: [%hys n=hint-static-prod p=@uvre f=nomm-1]
      [%hos n=hint-static-mute f=nomm-1]
  ::
      [%hid n=hint-dynamic p=@uvre f=nomm-1]
      [%hyd n=hint-dynamic-prod-safe p=@uvre q=@uvre f=nomm-1]
      [%hod n=hint-dynamic-mute p=@uvre f=nomm-1]
      [%spy e=@uvre p=@uvre d=@uvre]
      [%mem k=@uvre s=@uvre f=nomm-1 r=@uvre]
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
      [%lnk u=@uvre f=@uvre d=@uvre t=@uwoo]
      [%cal a=@uxor v=(list @uvre) d=@uvre t=@uwoo]
      [%caf a=@uxor v=(list @uvre) d=@uvre t=@uwoo u=@uvre n=[path @]]
      [%lnt u=@uvre f=@uvre]
      [%jmp a=@uxor v=(list @uvre)]
      [%jmf a=@uxor v=(list @uvre) u=@uvre n=[path @]]
      [%don s=@uvre]
      [%bom ~]
      [%mim k=@uvre s=@uvre f=nomm-1 d=@uvre z=@uwoo o=@uwoo]
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
+$  straight
  $:  entry=@uwoo
      =need
      args=(list @uvre)
      blocks=(map @uwoo blob)
      =bell
  ==
::
+$  line-long
  $:  code=(map @uxor straight)
      ax-gen=@uxor
      bells=(map bell @uxor)
      arity=args-locations
  ==
::
+$  line-short
  $:  line-long
      re-gen=@uvre
      bo-gen=@uwoo
      $=  here
      $:  blocks=(map @uwoo blob)
  ==  ==
--