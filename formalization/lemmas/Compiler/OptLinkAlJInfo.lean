import lemmas.Compiler.OptLinkAlPInfo

/-!
# `+alias`: `join-info` (phase 4 of the plan, README Gaps 13)

```hoon
  ++  join-info
    |=  [a=(map @uvre info-reg) b=(map @uvre info-reg)]
    ^-  (map @uvre info-reg)
    |-  ^-  (map @uvre info-reg)
    ?~  b  ~
    ?~  a  ~
    ?:  =(a b)  a
    ?:  (mor p.n.a p.n.b)
      ?:  =(p.n.b p.n.a)
        %=  b
          n  [p.n.b (join-reg q.n.a q.n.b)]
          l  $(a l.a, b l.b)
          r  $(a r.a, b r.b)
        ==
      ?:  (gor p.n.b p.n.a)
        (~(uni by $(a l.a, r.b ~)) $(b r.b))
      (~(uni by $(a r.a, l.b ~)) $(b l.b))
    ?:  (gor p.n.a p.n.b)
      (~(uni by $(b l.b, r.a ~)) $(a r.a))
    (~(uni by $(b r.b, l.a ~)) $(a l.a))
```

* `JIR jr a b out`: the loop (the trap `alJITrap`), one constructor per
  branch, where `jr va vb v` says that `join-reg` of `va` and `vb` is `v`
  and the four last branches unite the products of two inner calls with
  `+uni:by` (`UniByR`); `ji_loop` runs the Nock on every derivation.
* `jiP_of_maps`: on two maps whose values `join-reg` takes (`jr` defined on
  them), a derivation to a map holding exactly the keys of both, the value
  at each the `jr` of the two or, from an equal subtree, the value itself.
* `al_jinfo`: **`join-info` of two related maps is related to `joinInfoA`**
  (`InfoMapRel`: a map of atoms to related `info-reg` nouns, the same keys).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The loop of `join-info`, one constructor per branch. -/
inductive JIR (jr : Noun → Noun → Noun → Prop) : Noun → Noun → Noun → Prop where
  | nilB (a : Noun) : JIR jr a (A 0) (A 0)
  | nilA (b : Noun) : b ≠ A 0 → JIR jr (A 0) b (A 0)
  | eq {a : Noun} : a ≠ A 0 → JIR jr a a a
  | same {k va la ra vb lb rb v l r : Noun} : C (C k va) (C la ra) ≠ C (C k vb) (C lb rb) →
      jr va vb v → JIR jr la lb l → JIR jr ra rb r →
      JIR jr (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) (C (C k v) (C l r))
  | mg {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      kb ≠ ka → morF mugF ka kb = true → gorF mugF kb ka = true →
      JIR jr la (C (C kb vb) (C lb (A 0))) x → JIR jr (C (C ka va) (C la ra)) rb y → UniByR mugF x y u →
      JIR jr (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u
  | mn {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      kb ≠ ka → morF mugF ka kb = true → gorF mugF kb ka = false →
      JIR jr ra (C (C kb vb) (C (A 0) rb)) x → JIR jr (C (C ka va) (C la ra)) lb y → UniByR mugF x y u →
      JIR jr (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u
  | ng {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      morF mugF ka kb = false → gorF mugF ka kb = true →
      JIR jr (C (C ka va) (C la (A 0))) lb x → JIR jr ra (C (C kb vb) (C lb rb)) y → UniByR mugF x y u →
      JIR jr (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u
  | nn {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      morF mugF ka kb = false → gorF mugF ka kb = false →
      JIR jr (C (C ka va) (C (A 0) ra)) rb x → JIR jr la (C (C kb vb) (C lb rb)) y → UniByR mugF x y u →
      JIR jr (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u

/-- The arm `join-reg` at the head of the battery of the `|^` core. -/
def alJRArm : Noun := C (A 8) (C (C (A 1) alJRegBunt) (C (C (A 1) alJRegB) (C (A 0) (A 1))))

/-- `join-reg` in the core `K`. -/
def jrK (K va vb v : Noun) : Prop := nock (C alJRegB (C (C va vb) K)) alJRegB = some v

/-- **The loop of `join-info`** on a derivation, in a core whose battery has
`join-reg` at its head and whose context holds `optC`. -/
theorem ji_loop (R G Y Z OC P : Noun) (hL2 : slot? 0x1ffff OC = some layer2) :
    ∀ {a b out : Noun}, JIR (jrK (C (C alJRArm R) (C G (C Y (C Z OC))))) a b out →
      nock (C alJITrap (C P (C (C a b) (C (C alJRArm R) (C G (C Y (C Z OC))))))) alJITrap = some out := by
  have hc := gorIn_morIn_layer2
  have hgor := gor_gate (mug := mugF) layer2 hc.1.2
  have hmor := mor_gate (mug := mugF) layer2 hc.2.2
  have hg := hc.1.1
  have hm := hc.2.1
  intro a b out h
  induction h with
  | nilB a =>
    nock_open alJITrap
    simp [nock_exec]
  | nilA b hb =>
    nock_open alJITrap
    simp [nock_exec, eqCode, Ne.symm hb]
  | eq ha =>
    nock_open alJITrap
    simp [nock_exec, eqCode, ha, Ne.symm ha]
  | same hne hv _ _ ih1 ih2 =>
    unfold jrK at hv
    nock_open alJITrap
    unfold alJRArm at hv ih1 ih2 ⊢
    simp [nock_exec, eqCode, hne, hL2, hm, hmor, morF_refl, hv, ih1, ih2]
  | mg hne e m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJITrap
    simp [nock_exec, eqCode, hne, e, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]
  | mn hne e m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJITrap
    simp [nock_exec, eqCode, hne, e, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]
  | ng hne m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJITrap
    simp [nock_exec, eqCode, hne, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]
  | nn hne m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJITrap
    simp [nock_exec, eqCode, hne, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]

end Compiler
end Formalization
