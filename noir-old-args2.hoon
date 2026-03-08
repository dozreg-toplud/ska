::  %hole - the sub-noun is not needed (but its descendants might be needed)
::  %look - test shape for presence, do not include in the args
::  %arg  - one of the arguments
::
+$  args  (tree ?(%hole %look %arg))
+$  args-locations  (map bell args)
+$  meme-args
  $:  =args                         ::  argument usage of the function's subject
      branch-args=(map @axis args)  ::  argument usage of the branches's subject
  ==
::  for printing
::
+$  arg-treeless
  $~  ~
  $@  ?(~ %arg %hole %look)
  [arg-treeless arg-treeless]
::
++  blind
  |=  [l=args r=args]
  ^-  args
  ?:  &(?=(~ l) ?=(~ r))  ~
  ?:  &(?=(^ r) ?=(%look n.r) ?=(^ l))
    [%hole l ~]
  ?:  &(?=(^ l) ?=(%look n.l) ?=(^ r))
    [%hole ~ r]
  [%hole l r]
::
++  max-args
  |=  [a=args b=args]
  ^-  (unit ?(%arg %look))
  ~+
  ?~  a
    ?~  b  ~
    ?.  ?=(%hole n.b)  `n.b
    (max-args l.b r.b)
  ?~  b
    ?.  ?=(%hole n.a)  `n.a
    (max-args l.a r.a)
  ?:  |(?=(%arg n.a) ?=(%arg n.b))    `%arg
  ?:  &(?=(%look n.a) ?=(%look n.b))  `%look
  ?:  ?=(%look n.a)  (max-args l.b r.b)
  ?:  ?=(%look n.b)  (max-args l.a r.a)
  =/  from-a  (need (max-args l.a r.a))
  =/  from-b  (need (max-args l.b r.b))
  ?:  |(?=(%arg from-a) ?=(%arg from-b))  `%arg
  `%look
::
:: ++  subtract-cape-args-final
::   |=  [a=args c=cape]
::   ^-  args
::   =-  ?:  =(- (normalize-args -))  -
::       ~|  `*`-
::       ~|  `*`(normalize-args -)
::       !!
::   ^-  args
::   ?@  c
::     ?:  c  ~
::     ?~  a  ~
::     ?:  ?=(?(%arg %look) n.a)  a
::     ~&  [%max l.a r.a]
::     ~&  (max-args l.a r.a)
::     [(need (max-args l.a r.a)) ~ ~]
::   ?~  a  ~
::   ?-    n.a
::       %hole
::     =-  ?:  =(- (normalize-args -))  -
::         ~|  `*`-
::         ~|  `*`(normalize-args -)
::         !!
::     =/  l=args  $(a l.a, c -.c)
::     =/  r=args  $(a r.a, c +.c)
::     (blind l r)
::   ::
::       %arg  [%arg ~ ~]
::   ::
::       %look  ~
::   ==
:: ::
:: ++  subtract-cape-args
::   |=  [a=args c=cape]
::   ^-  args
::   =-  ?:  =(- (normalize-args -))  -
::       ~|  `*`-
::       ~|  `*`(normalize-args -)
::       !!
::   ^-  args
::   ?@  c
::     ?:  c  ~
::     a
::   ?~  a  ~
::   ?-    n.a
::       %hole
::     =-  ?:  =(- (normalize-args -))  -
::         ~|  `*`-
::         ~|  `*`(normalize-args -)
::         !!
::     =/  l=args  $(a l.a, c -.c)
::     =/  r=args  $(a r.a, c +.c)
::     (blind l r)
::   ::
::       %arg  [%arg ~ ~]
::   ::
::       %look  ~
::   ==
::
++  normalize-args
  |=  =args
  ^+  args
  :: args
  ?~  args  ~
  =.  l.args  $(args l.args)
  =.  r.args  $(args r.args)
  ?:  ?=(%arg n.args)
    ?:  =([~ ~] +.args)  args
    ~&  [%norm args]
    [n.args ~ ~]
  ?:  ?=(%look n.args)
    ?:  =([~ ~] +.args)  args
    ~&  [%norm args]
    [%hole +.args]
  ::  n.args == %hole
  ::
  ?:  =([~ ~] +.args)
    ~&  [%norm args]
    ~
  (blind l.args r.args)
::
::  union of data needs, used to compute a data need of
::  a sequential computation
::
::  note that if one need is more "refined" than the other
::  (e.g. [%arg ~ ~] is less refined than [%hole arg+~+~ ~])
::  then we weaken the need of the more refined computation,
::  as we do not want to have both a noun and its child to avoid
::  having to recons things
::
++  uni-args
  |=  [a=args b=args]
  ^-  args
  =-  ?:  =(- (normalize-args -))  -
      ~|  `*`a
      ~|  `*`b
      ~|  `*`-
      ~|  `*`(normalize-args -)
      !!
  ?:  =(a b)  a
  ?~  a  b
  ?~  b  a
  ?:  |(?=(%arg n.a) ?=(%arg n.b))  [%arg ~ ~]
  ?:  &(?=(%look n.a) ?=(%look n.b))  [%look ~ ~]
  ?:  ?=(%look n.a)  b
  ?:  ?=(%look n.b)  a
  ::  both are %hole, cons unions of head and tail
  ::
  ~+
  (blind (uni-args l.a l.b) (uni-args r.a r.b))
::
++  uni-args-loc
  |=  [a=args-locations b=args-locations]
  ^-  args-locations
  %-  (~(uno by a) b)
  |=  [bell a=args b=args]
  (uni-args a b)
::  data that is required by both branches
::
::  %arg and %look are intersected to %arg because we are going to merge
::  the residuals and unify the merged result with the intersection anyway
::
::  similar to union, we pessimize a computation with a more detailed arg
::  requirement
::
++  int-args
  |=  [a=args b=args]
  ^-  args
  =-  ?:  =(- (normalize-args -))  -
      ~|  `*`a
      ~|  `*`b
      ~|  `*`-
      ~|  `*`(normalize-args -)
      !!
  ?:  =(a b)  a
  ?~  a  ~
  ?~  b  ~
  ?:  |(?=(%arg n.a) ?=(%arg n.b))  [%arg ~ ~]
  ?:  &(?=(%look n.a) ?=(%look n.b))  [%look ~ ~]
  ?:  ?=(%look n.a)  b
  ?:  ?=(%look n.b)  a
  ~+
  (blind (int-args l.a l.b) (int-args r.a r.b))
::  (a - b), i.e. args in a that are not in b
::
::  residual arg requirement. used to calculate what locations
::  are required by only one branch. `b` is the requirement by previous code
::  plus the conditional formula plus the intersection of requirements
::
::  thus `b` includes the intersection of `a` with the arg requirement
::  from the other branch, so `a` and `b` are correlated, which we can leverage
::
++  dis-args
  |=  [a=args b=args]
  ^-  args
  =-  ?:  =(- (normalize-args -))  -
      ~|  `*`a
      ~|  `*`b
      ~|  `*`-
      ~|  `*`(normalize-args -)
      !!
  ?:  =(a b)  ~
  ?~  a  ~
  ?~  b  a
  ?:  ?=(%arg n.b)  ~
  ?:  ?=(%look n.b)
    ::  since `a` is not empty then it has to be %look
    ::  otherwise this %look would not be present in `b`
    ::  due to intersection rules
    ::
    ?>  ?=(%look n.a)
    ~
  ::  `b` is %hole, so `a` also has to be %hole or %look, otherwise
  ::  `b` would be %arg here or above
  ::
  ?<  ?=(%arg n.a)
  ?:  ?=(%look n.a)  ~
  ~+
  (blind (dis-args l.a l.b) (dis-args r.a r.b))
::  get greatest common ancestor of `a` and `b`
::
::  once we calculated what data is required by only first and only second
::  branches, we merge these requirements into one
::
::  `a` and `b` are disjoint: if `a` is %arg then `b` is ~ etc.
::
++  join-args
  |=  [a=args b=args]
  ^-  args
  =-  ?:  =(- (normalize-args -))  -
      ~|  `*`a
      ~|  `*`b
      ~|  `*`-
      ~|  `*`(normalize-args -)
      !!
  ?:  &(?=(~ a) ?=(~ b))  ~
  ::  XX this should take %look into account but I ignore it elsewhere so it's
  ::  fine...
  :::
  ?:  |(?=(~ a) ?=(~ b))  [%arg ~ ~]
  ::  XX this works when a and b describe argument usage exclusive to these
  ::  branches, but since we don't do that for now we still need to check
  ::
  :: ::  assert disjointness
  :: ::
  :: ?>  ?=(%hole n.a)
  :: ?>  ?=(%hole n.b)
  ::
  ?.  &(?=(%hole n.a) ?=(%hole n.b))  [%arg ~ ~]
  ?:  &(?=(~ l.a) ?=(~ l.b))  [%hole ~ $(a r.a, b r.b)]
  ?:  &(?=(~ r.a) ?=(~ r.b))  [%hole $(a l.a, b l.b) ~]
  ::  condition: a and b require from head and tail only, respectively,
  ::  or vice versa
  ::
  ?.  |(&(?=(~ l.a) ?=(~ r.b)) &(?=(~ r.a) ?=(~ l.b)))
    ::  reconcilable requirements: cons
    ::
    [%hole $(a l.a, b l.b) $(a r.a, b r.b)]
  ::  require the common ancestor
  ::
  :_  [~ ~]
  %-  need
  %+  max-args  [(need (max-args l.a r.a)) ~ ~]
  [(need (max-args l.b r.b)) ~ ~]
::
++  args-branches
  |=  [old=args-locations y=args-locations n=args-locations]
  ^-  args-locations
  =/  keys  (~(uni in ~(key by y)) ~(key by n))
  %-  ~(rep in keys)
  |=  [key=bell acc=_old]
  ^+  acc
  ::  XX here the idea is that we want to know which parts of the subject
  ::  are used exclusively by the yes/no branches, and join these exclusive
  ::  usages into one usage under which both would nest. This does not play well
  ::  with the linearizer, which does not currently do that, so it pessimizes
  ::  registerization of branches, making the linearizer greedier than the
  ::  prepass. As a result, the subject registerization by the linearizer no
  ::  longer nests under the prepass' estimate, resulting in a crash in +coerce
  ::  (which could technically be an arity rewrite + recompilation of the whole
  ::  call graph... the crash is to prevent that from happening while I am
  ::  writing this thing).
  ::
  ::  The problem is that the arity prepass walks the code forward, so it only
  ::  knows which parts of the subject are used by the previous code, and the
  ::  linearizer could only know which parts of the subject are required by the
  ::  code after the control flow merge + the conditional itself -- in short,
  ::  by the following code. 
  ::
  ::  Ideally we want to know which parts of the subject are used by code before
  ::  and after the branch. It is currently not clear how to do that.
  ::
  ::  XX per-function stacks of branches to finalize?
  ::
  :: =/  args-y=args    (~(gut by y) key ~)
  :: =/  args-n=args    (~(gut by n) key ~)
  :: =/  args-old=args  (~(gut by acc) key ~)
  :: =/  args-sure  (uni-args args-old (int-args args-y args-n))
  :: =/  only-y=args  (dis-args args-y args-sure)
  :: =/  only-n=args  (dis-args args-n args-sure)
  :: =/  join  (join-args only-y only-n)
  :: (~(put by acc) key (uni-args args-sure join))
  ::
  =/  args-y=args    (~(gut by y) key ~)
  =/  args-n=args    (~(gut by n) key ~)
  =/  join  (join-args args-y args-n)
  =/  args-old=args  (~(gut by acc) key ~)
  (~(put by acc) key (uni-args args-old join))
::
++  push-args
  |=  [a=args ax=@]
  ^-  args
  ?:  =(1 ax)  a
  ~+
  ?-  (cap ax)
    %2  [%hole $(ax (mas ax)) ~]
    %3  [%hole ~ $(ax (mas ax))]
  ==
::
++  hed-args
  |=  a=args
  ^-  args
  ?~  a  ~
  ?:  ?=(%hole n.a)  l.a
  a
::
++  tel-args
  |=  a=args
  ^-  args
  ?~  a  ~
  ?:  ?=(%hole n.a)  r.a
  a
::
++  urge-args
  |=  [src=source tak=(lest bell) =args]
  ^-  args-locations
  ?:  =([~ ~] i.src)  ~
  =^  comps=(lest (lest spring:source))  tak
    =/  hed  i.src
    =/  tel  t.src
    |-  ^-  [(lest (lest spring:source)) (lest bell)]
    ?~  tel  [~[hed] tak]
    =.  hed  (turn-spring:source hed (mask-spring-cut-args:source args) %args)
    ?:  ?=([~ ~] hed)  [~[hed] ~[i.tak]]
    =/  site  i.tak
    =^  r=(list (lest spring:source))  tak
      =/  comp  (compose:source hed i.tel)
      $(hed comp, tel t.tel, tak ?~(t.tak !! t.tak))
    ::
    [[hed r] [site tak]]
  ::
  =|  out=args-locations
  |-  ^+  out
  ?:  ?=([~ ~] i.comps)  out
  =/  a=^args
    %+  roll  `(list spring:source)`i.comps
    |=  [pin=spring:source acc=^args]
    ?~  pin  acc
    %+  uni-args  acc
    =>  .(pin `spring:source`pin)
    =-  ?:  =(- (normalize-args -))  -
        ~|  `*`-
        ~|  `*`(normalize-args -)
        !!
    |-  ^-  ^args
    ?~  pin         ~
    ?:  =(~ args)   ~
    ?@  pin  (push-args args pin)
    %+  uni-args
      $(pin -.pin, args (hed-args args))
    $(pin +.pin, args (tel-args args))
  ::
  =.  out  (jib out i.tak _a |=(b=^args (uni-args a b)))
  ?~  t.comps  out
  ?~  t.tak  !!
  $(tak t.tak, comps t.comps)
::
++  update-args-loc
  |=  [old=args-locations src=source tak=(lest bell) =args]
  ^-  args-locations
  (uni-args-loc old (urge-args +<+))
::
++  mask-spring-cut-args
    |=  =args
    =.  args  (normalize-args args)
    |=  pin=spring
    ^-  spring
    ?~  pin  ~
    ?~  args  ~
    ?:  ?=(?(%arg %look) n.args)  pin
    ?@  pin  pin
    %+  cons-spring  $(args l.args, pin -.pin)
    $(args r.args, pin +.pin)
  ::