/-  *noir
|%
::  @uvre: register index 
::  @uwoo: basic block index
::  @uxor: function index
::
+$  need
  $^  [p=need q=need]
  ::  c: does the downstream code crash if this is not a cell?
  ::  this flag is used to avoid crash relocation:
  ::  if upstream code produces an atom that is supposed to fulfill
  ::  a need [%both @uvre & * *], the crash is deferred by producing an atom
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
::  hint ops:     XX massive overkill as we always require the entire product
::                   of the hinted formula which is not needed in general
::
::  %his - arbitrary static hint prologue
::  %hes - arbitrary static hint epilogue, product of hinted formula in p
::  %hid - arbitrary dynamic hint prologue, product of hint-formula in p
::  %hed - arbitrary dynamic hint prologue, product of hint-formula in p,
::         product of formula-formula in q
::
+$  pole
  $%  [%imm n=* d=@uvre]
      [%mov s=@uvre d=@uvre]
      [%inc s=@uvre d=@uvre]
      [%con h=@uvre t=@uvre d=@uvre]
      [%hed s=@uvre d=@uvre]
      [%tal s=@uvre d=@uvre]
      [%cel p=@uvre]
      [%his n=@]
      [%hes n=@ p=@uvre]
      [%hid n=@ p=@uvre]
      [%hed n=@ p=@uvre q=@uvre]
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