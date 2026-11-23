import lemmas.Compiler.PiEdit
import lemmas.Compiler.Safe
import lemmas.Pill.Arm.Knit_anno
import lemmas.Pill.Arm.Patch_prod
import lemmas.Pill.Arm.Msg_sock
import lemmas.Pill.Arm.Msg_anno
import lemmas.Ska.CallGraph

/-!
The products of the analysis core `ana`: `+knit-anno`, `+patch-prod`,
`+msg-sock` and `+msg-anno` against `knitAnno`, `patchProd`, `msgSock` and
`msgAnno` of `lemmas/Ska/CallGraph.lean`.

```hoon
++  patch-prod
  |=  [pro=[=sock src=spring] new=sock]
  ^-  [=sock src=spring]
  ?:  =(~ src.pro)  pro
  ?:  ?=(%void sock.pro)  pro
  ?@  src.pro  [(pull:so new src.pro) src.pro]
  ~+
  %+  knit-anno
    $(pro [(hed:so sock.pro) (hed:pi src.pro)])
  $(pro [(tel:so sock.pro) (tel:pi src.pro)])
```

The arms read the library core `lib` at `knit_anno.lib.axis` of their
context `ana`, and through it the cores of `+so` and `+pi`; `+patch-prod` and
`+msg-anno` read `+knit-anno` of their context too.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel

/-! ## What the arms read from the library core -/

/-- The library core builds the core of `+so`, and that core holds `+knit`. -/
abbrev SoKnitOf (lib : Noun) : Prop :=
  ∃ f k, slot? so.lib.axis lib = some f ∧ nock lib f = some k ∧
    slot? so.knit.axis k = some so.knit.arm ∧ KnitIn k

/-- The library core builds the core of `+pi`, and that core holds `+cons`. -/
abbrev PiConsOf (lib : Noun) : Prop :=
  ∃ f k, slot? pi.lib.axis lib = some f ∧ nock lib f = some k ∧
    slot? pi.cons.axis k = some pi.cons.arm

/-- The library core builds the core of `+so`, and that core holds `+pull`. -/
abbrev SoPullOf (lib : Noun) : Prop :=
  ∃ f k, slot? so.lib.axis lib = some f ∧ nock lib f = some k ∧
    slot? so.pull.axis k = some so.pull.arm ∧ AxisIn k

theorem soKnitOf_of_soOf {lib : Noun} (h : SoOf lib) : SoKnitOf lib := by
  obtain ⟨f, k, hf, hk, hknit, _, _, hkc⟩ := h
  exact ⟨f, k, hf, hk, hknit, hkc⟩

theorem piConsOf_of_piOf {lib : Noun} (h : PiOf lib) : PiConsOf lib := by
  obtain ⟨f, k, hf, hk, _, _, hcons, _⟩ := h
  exact ⟨f, k, hf, hk, hcons⟩

/-! ## `+knit-anno` -/

/-- What `+knit-anno` reads from its context: `+knit:so` and `+cons:pi`
through the library core. -/
abbrev KnitAnnoIn (c : Noun) : Prop :=
  ∃ lib, slot? knit_anno.lib.axis c = some lib ∧ SoKnitOf lib ∧ PiConsOf lib

@[nock_exec] theorem knit_anno_arm (c : Noun) :
    nock c knit_anno.arm
      = some (C knit_anno.battery
          (C (C (C (C (A 1) (A 0)) (A 0)) (C (C (A 1) (A 0)) (A 0))) c)) := by
  nock_open knit_anno.arm; simp only [nock_exec]

theorem knit_anno_gate (ctx : Noun) (hc : KnitAnnoIn ctx) (h t : Anno) :
    nock (C knit_anno.battery (C (C h.toNoun t.toNoun) ctx)) knit_anno.battery
      = some (knitAnno h t).toNoun := by
  obtain ⟨lib, hlib, ⟨f, k, hf, hk, hknit, hkc⟩, ⟨g, p, hg, hp, hcons⟩⟩ := hc
  obtain ⟨sh, rh⟩ := h
  obtain ⟨st, rt⟩ := t
  nock_open knit_anno.battery
  simp [nock_exec, anno_mk_toNoun, knitAnno, hlib, hf, hk, hknit, hg, hp, hcons, so_knit_arm,
    pi_cons_arm, so_knit_gate k hkc, pi_cons_gate]

/-! ## `+patch-prod` -/

/-- What `+patch-prod` reads from its context: `+knit-anno`, and `hed`,
`tel`, `pull` of `+so` and `hed`, `tel`, `cons` of `+pi` through the library
core. -/
abbrev PatchProdIn (c : Noun) : Prop :=
  slot? knit_anno.axis c = some knit_anno.arm ∧
    ∃ lib, slot? knit_anno.lib.axis c = some lib ∧ SoOf lib ∧ PiOf lib ∧ SoPullOf lib

@[nock_exec] theorem patch_prod_arm (c : Noun) :
    nock c patch_prod.arm
      = some (C patch_prod.battery
          (C (C (C (C (A 1) (A 0)) (A 0)) (C (A 1) (A 0))) c)) := by
  nock_open patch_prod.arm; simp only [nock_exec]

theorem patchProd_zero (s new : Sock) : patchProd s (A 0) new = ⟨s, A 0⟩ := by
  unfold patchProd; simp

theorem patchProd_void (src : Noun) (new : Sock) :
    patchProd Sock.void src new = ⟨Sock.void, src⟩ := by
  unfold patchProd; simp

theorem patchProd_atom {a : Nat} (ha : a ≠ 0) (c : Cape) (d : Noun) (new : Sock) :
    patchProd (Sock.mk c d) (A a) new = ⟨(So.pull new a).getD Sock.void, A a⟩ := by
  unfold patchProd; simp [ha]

theorem patchProd_cell (c : Cape) (d h t : Noun) (new : Sock) :
    patchProd (Sock.mk c d) (C h t) new
      = knitAnno (patchProd (So.hed (Sock.mk c d)) h new)
          (patchProd (So.tel (Sock.mk c d)) t new) := by
  rw [patchProd.eq_def]; simp

theorem so_pull_some {a : Nat} (ha : a ≠ 0) (s : Sock) : ∃ p, So.pull s a = some p := by
  unfold So.pull; cases s <;> simp [ha]

theorem patch_prod_gate (ctx : Noun) (hc : PatchProdIn ctx) (new : Sock) :
    ∀ (src : Noun) (s : Sock),
    nock (C patch_prod.battery (C (C (C s.toNoun src) new.toNoun) ctx)) patch_prod.battery
      = some (patchProd s src new).toNoun := by
  obtain ⟨hka, lib, hlib, hso, hpi, f', k', hf', hk', hpull, hax⟩ := hc
  have hkn : KnitAnnoIn ctx := ⟨lib, hlib, soKnitOf_of_soOf hso, piConsOf_of_piOf hpi⟩
  obtain ⟨f, k, hf, hk, hknit, hshed, hstel, hkc⟩ := hso
  obtain ⟨g, p, hg, hp, hphed, hptel, hpcons, hpeg⟩ := hpi
  obtain rfl : f = f' := Option.some.inj (hf.symm.trans hf')
  obtain rfl : k = k' := Option.some.inj (hk.symm.trans hk')
  intro src
  induction src with
  | atom a =>
    intro s
    by_cases ha : a = 0
    · subst ha
      rw [patchProd_zero]
      nock_open patch_prod.battery
      simp [nock_exec, anno_mk_toNoun]
    cases s with
    | void =>
      rw [patchProd_void]
      nock_open patch_prod.battery
      simp [nock_exec, anno_mk_toNoun, sock_void_toNoun, Ne.symm ha, Tag.void]
    | mk c d =>
      rw [patchProd_atom ha]
      obtain ⟨q, hq⟩ := so_pull_some ha new
      nock_open patch_prod.battery
      simp [nock_exec, anno_mk_toNoun, sock_mk_toNoun, Ne.symm ha, hlib, hf, hk, hpull,
        so_pull_arm, so_pull_gate k hax, hq, Tag.void]
  | cell h t ihh iht =>
    intro s
    cases s with
    | void =>
      rw [patchProd_void]
      nock_open patch_prod.battery
      simp [nock_exec, anno_mk_toNoun, sock_void_toNoun, Tag.void]
    | mk c d =>
      rw [patchProd_cell]
      have h1 := so_hed_gate k (Sock.mk c d)
      have h2 := so_tel_gate k (Sock.mk c d)
      simp only [sock_mk_toNoun] at h1 h2
      nock_open patch_prod.battery
      simp [nock_exec, anno_mk_toNoun, sock_mk_toNoun, hlib, hf, hk, hg, hp, hshed, hstel, hphed,
        hptel, hka, so_hed_arm, so_tel_arm, pi_hed_arm, pi_tel_arm, knit_anno_arm, h1, h2,
        pi_hed_gate p hpeg, pi_tel_gate p hpeg, Pi.hed, Pi.tel, ihh, iht, knit_anno_gate ctx hkn,
        Tag.void]

/-! ## `+msg-sock` -/

/-- What `+msg-sock` reads from its context: `+knit:so` through the library
core. -/
abbrev MsgSockIn (c : Noun) : Prop := ∃ lib, slot? knit_anno.lib.axis c = some lib ∧ SoKnitOf lib

@[nock_exec] theorem msg_sock_arm (c : Noun) :
    nock c msg_sock.arm
      = some (C msg_sock.battery (C (C (C (A 1) (A 0)) (C (A 1) (A 0))) c)) := by
  nock_open msg_sock.arm; simp only [nock_exec]

theorem sock_toNoun_ne {a b : Sock} (h : a ≠ b) : ¬ (a.toNoun = b.toNoun) :=
  fun e => h (sock_toNoun_inj e)

theorem msgSock_self (a : Sock) : msgSock a a = some a := by
  rw [msgSock.eq_def]; simp

/-- One step of `msgSock` on two different socks. -/
macro "msg_unfold " h:ident : tactic => `(tactic|
  (first | rw [msgSock.eq_def, dif_neg $h] | rw [msgSock.eq_def, if_neg $h]))

/-- The cases of `+msg-sock` that do not recurse. -/
macro "msg_simp" : tactic => `(tactic|
  (nock_open msg_sock.battery
   simp [nock_exec, sock_mk_toNoun, sock_void_toNoun, cape_yes_toNoun, cape_no_toNoun,
     cape_cell_toNoun, Tag.void, Sock.dunno, msgSock_self, *]))

set_option maxHeartbeats 1000000 in
/-- Slamming `+msg-sock` on a sock that is not `%void` and any sock, by
induction on the data of the first. -/
theorem msg_sock_gate_mk (ctx : Noun) (hc : MsgSockIn ctx) :
    ∀ (da : Noun) (ca : Cape) (b : Sock),
    nock (C msg_sock.battery (C (C (C ca.toNoun da) b.toNoun) ctx)) msg_sock.battery
      = (msgSock (Sock.mk ca da) b).map Sock.toNoun := by
  obtain ⟨lib, hlib, f, k, hf, hk, hknit, hkc⟩ := hc
  intro da
  induction da with
  | atom n =>
    intro ca b
    by_cases hab : Sock.mk ca (A n) = b
    · subst hab; msg_simp
    have hne := sock_toNoun_ne hab
    msg_unfold hab
    cases b with
    | void => msg_simp
    | mk cb db =>
      simp only [sock_mk_toNoun, Noun.cell.injEq] at hne
      rcases ca with _ | _ | ⟨ah, aT⟩ <;> rcases cb with _ | _ | ⟨bh, bT⟩ <;>
        rcases db with _ | ⟨_, _⟩ <;>
        simp only [cape_yes_toNoun, cape_no_toNoun, cape_cell_toNoun, Noun.cell.injEq,
          Noun.atom.injEq, true_and] at hne <;> msg_simp
  | cell d1 d2 ih1 ih2 =>
    intro ca b
    by_cases hab : Sock.mk ca (C d1 d2) = b
    · subst hab; msg_simp
    have hne := sock_toNoun_ne hab
    msg_unfold hab
    cases b with
    | void => msg_simp
    | mk cb db =>
      simp only [sock_mk_toNoun, Noun.cell.injEq] at hne
      rcases ca with _ | _ | ⟨ah, aT⟩ <;> rcases cb with _ | _ | ⟨bh, bT⟩ <;>
        rcases db with _ | ⟨e1, e2⟩ <;>
        simp only [cape_yes_toNoun, cape_no_toNoun, cape_cell_toNoun, Noun.cell.injEq,
          Noun.atom.injEq, true_and] at hne
      all_goals try (msg_simp; done)
      -- both capes and both data are cells: the recursion
      have i1 := ih1 ah (Sock.mk bh e1)
      have i2 := ih2 aT (Sock.mk bT e2)
      simp only [sock_mk_toNoun] at i1 i2
      cases r1 : msgSock (Sock.mk ah d1) (Sock.mk bh e1) <;>
        cases r2 : msgSock (Sock.mk aT d2) (Sock.mk bT e2) <;>
        simp only [r1, r2, Option.map_none, Option.map_some] at i1 i2 <;>
        nock_open msg_sock.battery <;>
        simp [nock_exec, sock_mk_toNoun, cape_cell_toNoun, Tag.void, hne, hlib, hf, hk, hknit,
          so_knit_arm, i1, i2, r1, r2, so_knit_gate k hkc]

/-- Slamming `+msg-sock` on two socks. -/
theorem msg_sock_gate (ctx : Noun) (hc : MsgSockIn ctx) (a b : Sock) :
    nock (C msg_sock.battery (C (C a.toNoun b.toNoun) ctx)) msg_sock.battery
      = (msgSock a b).map Sock.toNoun := by
  cases a with
  | mk ca da => simpa only [sock_mk_toNoun] using msg_sock_gate_mk ctx hc da ca b
  | void =>
    by_cases hab : Sock.void = b
    · subst hab; msg_simp
    msg_unfold hab
    cases b with
    | void => exact absurd rfl hab
    | mk cb db => msg_simp

/-! ## `+msg-anno` -/

/-- What `+msg-anno` reads from its context: `+knit-anno`, and `hed`, `tel`
of `+so` and `hed`, `tel`, `cons` of `+pi` through the library core. -/
abbrev MsgAnnoIn (c : Noun) : Prop :=
  slot? knit_anno.axis c = some knit_anno.arm ∧
    ∃ lib, slot? knit_anno.lib.axis c = some lib ∧ SoOf lib ∧ PiOf lib

@[nock_exec] theorem msg_anno_arm (c : Noun) :
    nock c msg_anno.arm
      = some (C msg_anno.battery
          (C (C (C (C (A 1) (A 0)) (A 0)) (C (C (A 1) (A 0)) (A 0))) c)) := by
  nock_open msg_anno.arm; simp only [nock_exec]

theorem msgAnno_self (a : Anno) : msgAnno a a = a := by
  rw [msgAnno.eq_def]; simp

/-- One step of `msgAnno` on two different annotated socks. -/
macro "anno_unfold " h:ident : tactic => `(tactic|
  (first | rw [msgAnno.eq_def, dif_neg $h] | rw [msgAnno.eq_def, if_neg $h]))

/-- The cases of `+msg-anno` that do not recurse. -/
macro "anno_simp" : tactic => `(tactic|
  (nock_open msg_anno.battery
   simp [nock_exec, anno_mk_toNoun, sock_mk_toNoun, cape_yes_toNoun, cape_no_toNoun,
     cape_cell_toNoun, anno_dunno_toNoun, Tag.void, *]))

set_option maxHeartbeats 1000000 in
/-- Slamming `+msg-anno` on two annotated socks, by induction on the measure
of the model. -/
theorem msg_anno_gate (ctx : Noun) (hc : MsgAnnoIn ctx) : ∀ (n : Nat) (a b : Anno),
    Sock.msr a.sock + Sock.msr b.sock < n →
    nock (C msg_anno.battery (C (C a.toNoun b.toNoun) ctx)) msg_anno.battery
      = some (msgAnno a b).toNoun := by
  obtain ⟨hka, lib, hlib, hso, hpi⟩ := hc
  have hkn : KnitAnnoIn ctx := ⟨lib, hlib, soKnitOf_of_soOf hso, piConsOf_of_piOf hpi⟩
  obtain ⟨f, k, hf, hk, hknit, hshed, hstel, hkc⟩ := hso
  obtain ⟨g, p, hg, hp, hphed, hptel, hpcons, hpeg⟩ := hpi
  intro n
  induction n with
  | zero => intro a b h; omega
  | succ n ih =>
    intro a b hlt
    by_cases hab : a = b
    · subst hab
      nock_open msg_anno.battery
      simp [nock_exec, msgAnno_self]
    have hne := anno_toNoun_ne hab
    anno_unfold hab
    obtain ⟨sa, ra⟩ := a
    obtain ⟨sb, rb⟩ := b
    cases sa with
    | void =>
      simp only [anno_mk_toNoun, sock_void_toNoun, Noun.cell.injEq, Tag.void] at hne
      nock_open msg_anno.battery
      simp [nock_exec, anno_mk_toNoun, sock_void_toNoun, hne, Tag.void]
    | mk ca da =>
    cases sb with
    | void =>
      simp only [anno_mk_toNoun, sock_void_toNoun, sock_mk_toNoun, Noun.cell.injEq, Tag.void] at hne
      nock_open msg_anno.battery
      simp [nock_exec, anno_mk_toNoun, sock_void_toNoun, sock_mk_toNoun, hne, Tag.void]
    | mk cb db =>
    rcases ca with _ | _ | ⟨ah, aT⟩ <;> rcases cb with _ | _ | ⟨bh, bT⟩ <;>
      simp only [anno_mk_toNoun, sock_mk_toNoun, cape_yes_toNoun, cape_no_toNoun,
        cape_cell_toNoun, Noun.cell.injEq, Noun.atom.injEq, true_and] at hne
    all_goals try (anno_simp; done)
    simp only at hlt
    have m1 := msr_hed_lt (c := Cape.cell ah aT) (by simp) da
    have m2 := msr_hed_lt (c := Cape.cell bh bT) (by simp) db
    have m3 := msr_tel_lt (c := Cape.cell ah aT) (by simp) da
    have m4 := msr_tel_lt (c := Cape.cell bh bT) (by simp) db
    have hh := ih ⟨So.hed (Sock.mk (Cape.cell ah aT) da), Pi.hed ra⟩
      ⟨So.hed (Sock.mk (Cape.cell bh bT) db), Pi.hed rb⟩ (by simp only; omega)
    have ht := ih ⟨So.tel (Sock.mk (Cape.cell ah aT) da), Pi.tel ra⟩
      ⟨So.tel (Sock.mk (Cape.cell bh bT) db), Pi.tel rb⟩ (by simp only; omega)
    simp only [anno_mk_toNoun] at hh ht
    have h1 := so_hed_gate k (Sock.mk (Cape.cell ah aT) da)
    have h2 := so_hed_gate k (Sock.mk (Cape.cell bh bT) db)
    have h3 := so_tel_gate k (Sock.mk (Cape.cell ah aT) da)
    have h4 := so_tel_gate k (Sock.mk (Cape.cell bh bT) db)
    simp only [sock_mk_toNoun, cape_cell_toNoun] at h1 h2 h3 h4
    nock_open msg_anno.battery
    simp [nock_exec, anno_mk_toNoun, sock_mk_toNoun, cape_cell_toNoun, hne, Tag.void, hlib, hf, hk,
      hg, hp, hshed, hstel, hphed, hptel, hka, so_hed_arm, so_tel_arm, pi_hed_arm, pi_tel_arm,
      knit_anno_arm, h1, h2, h3, h4, pi_hed_gate p hpeg, pi_tel_gate p hpeg, hh, ht,
      knit_anno_gate ctx hkn]

/-- Slamming `+msg-anno` on two annotated socks. -/
theorem msg_anno_gate' (ctx : Noun) (hc : MsgAnnoIn ctx) (a b : Anno) :
    nock (C msg_anno.battery (C (C a.toNoun b.toNoun) ctx)) msg_anno.battery
      = some (msgAnno a b).toNoun :=
  msg_anno_gate ctx hc _ a b (Nat.lt_succ_self _)

/-! ## On the pill's analysis core, with no assumption -/

theorem soPullOf_lib : SoPullOf lib :=
  ⟨so.lib.arm, C so.battery lib, so.lib.arm_at, so_lib_arm, so.pull.arm_at lib, soIn_pill.2.2.1⟩

theorem knitAnnoIn_ana : KnitAnnoIn ana :=
  ⟨lib, knit_anno.lib.arm_at, soKnitOf_of_soOf soOf_lib, piConsOf_of_piOf piOf_lib⟩

theorem knit_anno_pill (h t : Anno) :
    nock (C knit_anno.battery (C (C h.toNoun t.toNoun) ana)) knit_anno.battery
      = some (knitAnno h t).toNoun :=
  knit_anno_gate ana knitAnnoIn_ana h t

theorem patch_prod_pill (s : Sock) (src : Noun) (new : Sock) :
    nock (C patch_prod.battery (C (C (C s.toNoun src) new.toNoun) ana)) patch_prod.battery
      = some (patchProd s src new).toNoun :=
  patch_prod_gate ana ⟨knit_anno.arm_at, lib, knit_anno.lib.arm_at, soOf_lib, piOf_lib,
    soPullOf_lib⟩ new src s

theorem msg_sock_pill (a b : Sock) :
    nock (C msg_sock.battery (C (C a.toNoun b.toNoun) ana)) msg_sock.battery
      = (msgSock a b).map Sock.toNoun :=
  msg_sock_gate ana ⟨lib, knit_anno.lib.arm_at, soKnitOf_of_soOf soOf_lib⟩ a b

theorem msg_anno_pill (a b : Anno) :
    nock (C msg_anno.battery (C (C a.toNoun b.toNoun) ana)) msg_anno.battery
      = some (msgAnno a b).toNoun :=
  msg_anno_gate' ana ⟨knit_anno.arm_at, lib, knit_anno.lib.arm_at, soOf_lib, piOf_lib⟩ a b

end Compiler
end Formalization
