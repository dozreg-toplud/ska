import lemmas.Compiler.Axes
import lemmas.Hoon.Layer1

/-!
The last two arms of `+ca` and `+so`, and the pill's own library core.

`dif` of `+ca` and `huge` of `+so` quote, in the `%mean` hint of a crash
message, a noun that holds the hoon core (`ca.dif.mean`, `so.huge.mean`).  So
the generator names them in the bulk chain, and this file imports the chain.
The proofs never look inside the quoted noun: the hint's product is dropped.

Then the library core `lib` of the pill, the core that holds the arms `+ca`
and `+so` at `ca.lib.axis` and `so.lib.axis`, satisfies `CaOf`, `SoOf`,
`AxisOf` and `YeaOf`, and every gate of `+ca` and `+so` computes its model on
the pill's core of `+ca` or `+so` with no assumption.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel

/-! ## `+dif:ca` -/

/-- What `+dif` reads from its context, the core of `+ca`: `+con:ca` through
the library core. -/
abbrev DifIn (c : Noun) : Prop := Hoon.Below CaOf c

@[nock_exec] theorem ca_dif_arm (c : Noun) :
    nock c ca.dif.arm = some (C ca.dif.battery (C (C (A 1) (A 1)) c)) := by
  unfold ca.dif.arm; simp only [nock_exec]

theorem ca_dif_gate (ctx : Noun) (hc : DifIn ctx) : ∀ (a b : Cape),
    nock (C ca.dif.battery (C (C a.toNoun b.toNoun) ctx)) ca.dif.battery
      = (Ca.dif a b).map Cape.toNoun := by
  obtain ⟨bat, lib, rfl, f, k, hf, hk, hcon⟩ := hc.elim
  intro a
  induction a with
  | yes =>
    intro b
    nock_open ca.dif.battery
    cases b <;> simp [nock_exec, Cape.toNoun, Ca.dif]
  | no =>
    intro b
    nock_open ca.dif.battery
    cases b <;> simp [nock_exec, Cape.toNoun, Ca.dif]
  | cell ah aT ih it =>
    intro b
    cases b with
    | yes => nock_open ca.dif.battery; simp [nock_exec, Cape.toNoun, Ca.dif]
    | no => nock_open ca.dif.battery; simp [nock_exec, Cape.toNoun, Ca.dif]
    | cell bh bT =>
      have i1 := ih bh
      have i2 := it bT
      by_cases e : Cape.cell ah aT = Cape.cell bh bT
      · rw [e]; nock_open ca.dif.battery; simp [nock_exec, Ca.dif, Cape.toNoun]
      have e' : ¬ (C ah.toNoun aT.toNoun = C bh.toNoun bT.toNoun) := fun h =>
        e (cape_toNoun_inj (show (Cape.cell ah aT).toNoun = (Cape.cell bh bT).toNoun from h))
      rw [Ca.dif, if_neg e]
      nock_open ca.dif.battery
      cases h1 : Ca.dif ah bh <;> cases h2 : Ca.dif aT bT <;> simp only [h1, h2] at i1 i2 <;>
        simp [nock_exec, Cape.toNoun, e', hf, hk, hcon, ca_con_arm, ca_con_gate, i1, i2]

/-! ## `+huge:so` -/

@[nock_exec] theorem so_huge_arm (c : Noun) :
    nock c so.huge.arm = some (C so.huge.battery (C (C (C (A 1) (A 0)) (C (A 1) (A 0))) c)) := by
  unfold so.huge.arm; simp only [nock_exec]

/-- `+huge` on two socks that are not `%void`. -/
theorem so_huge_mk (ctx : Noun) : ∀ (d1 : Noun) (c1 c2 : Cape) (d2 : Noun),
    nock (C so.huge.battery (C (C (C c1.toNoun d1) (C c2.toNoun d2)) ctx)) so.huge.battery
      = (So.hugeMk c1 d1 c2 d2).map Hoon.loob
  | Noun.atom k, c1, c2, d2 => by
    nock_open so.huge.battery
    rcases c1 with _ | _ | ⟨a, b⟩ <;> rcases c2 with _ | _ | ⟨a', b'⟩ <;>
      rcases d2 with _ | ⟨x, y⟩ <;>
      simp [nock_exec, nock_ite, Cape.toNoun, So.hugeMk, cape_toNoun_eq, Hoon.loob] <;>
      (repeat' split) <;> simp_all [Hoon.loob]
  | Noun.cell h t, c1, c2, d2 => by
    rcases d2 with k | ⟨x, y⟩
    · nock_open so.huge.battery
      rcases c1 with _ | _ | ⟨a, b⟩ <;> rcases c2 with _ | _ | ⟨a', b'⟩ <;>
        simp [nock_exec, Cape.toNoun, So.hugeMk, cape_toNoun_eq, Hoon.loob] <;>
        (repeat' split) <;> simp_all [eqCode]
    · have i1 := so_huge_mk ctx h (Ca.hed c1) (Ca.hed c2) x
      have i2 := so_huge_mk ctx t (Ca.tel c1) (Ca.tel c2) y
      generalize r1 : So.hugeMk (Ca.hed c1) h (Ca.hed c2) x = o1 at i1
      generalize r2 : So.hugeMk (Ca.tel c1) t (Ca.tel c2) y = o2 at i2
      nock_open so.huge.battery
      rcases c1 with _ | _ | ⟨a, b⟩ <;> rcases c2 with _ | _ | ⟨a', b'⟩ <;>
        simp only [Ca.hed, Ca.tel, Cape.toNoun] at i1 i2 r1 r2 <;>
        obtain _ | ⟨_ | _⟩ := o1 <;> obtain _ | ⟨_ | _⟩ := o2 <;>
        simp [nock_exec, nock_ite, Cape.toNoun, So.hugeMk, cape_toNoun_eq, Ca.hed, Ca.tel, i1, i2,
          r1, r2, Hoon.loob] <;>
        (repeat' split) <;> simp_all [Hoon.loob]

/-- Slamming `huge` of `+so` on two socks: does the second nest under the first? -/
theorem so_huge_gate (ctx : Noun) (s1 s2 : Sock) :
    nock (C so.huge.battery (C (C s1.toNoun s2.toNoun) ctx)) so.huge.battery
      = (So.huge s1 s2).map Hoon.loob := by
  rcases s1 with _ | ⟨c1, d1⟩ <;> rcases s2 with _ | ⟨c2, d2⟩
  · nock_open so.huge.battery; simp [nock_exec, Sock.toNoun, So.huge, Tag.void, Hoon.loob]
  · nock_open so.huge.battery; simp [nock_exec, Sock.toNoun, So.huge, Tag.void, Hoon.loob]
  · nock_open so.huge.battery; simp [nock_exec, Sock.toNoun, So.huge, Tag.void, Hoon.loob]
  · exact so_huge_mk ctx d1 c1 c2 d2

/-! ## The pill's library core -/

/-- The arm `+ca` of the library core builds the core of `+ca`. -/
theorem ca_lib_arm : nock lib ca.lib.arm = some (C ca.battery lib) := by
  unfold ca.lib.arm; simp only [nock_exec]

/-- The arm `+so` of the library core builds the core of `+so`. -/
theorem so_lib_arm : nock lib so.lib.arm = some (C so.battery lib) := by
  unfold so.lib.arm; simp only [nock_exec]

theorem caOf_lib : CaOf lib :=
  ⟨ca.lib.arm, C ca.battery lib, ca.lib.arm_at, ca_lib_arm, ca.con.arm_at lib⟩

theorem soOf_lib : SoOf lib :=
  ⟨so.lib.arm, C so.battery lib, so.lib.arm_at, so_lib_arm, so.knit.arm_at lib,
    so.hed.arm_at lib, so.tel.arm_at lib, Hoon.Below.cell caOf_lib⟩

theorem axisOf_lib : AxisOf lib := by
  obtain ⟨ha, _, hm, _, _, _, _, _, _, _, hdv, hmd⟩ := Hoon.arith_layer1
  exact ⟨layer1, ca.lib.layer1.arm_at, ⟨cap.arm_at, hdv⟩, ⟨mas.arm_at, ha, hmd, hm, hdv⟩⟩

theorem yeaOf_lib : YeaOf lib := by
  obtain ⟨ha, _, hm, _, _, _, _, _, _, _, hdv, hmd⟩ := Hoon.arith_layer1
  exact ⟨layer2, layer1, ca.lib.layer2.arm_at, weld.arm_at, ca.lib.layer1.arm_at,
    ⟨peg.arm_at, ha, hmd, hm, hdv⟩⟩

/-- The pill's core of `+ca` gives its gates all that they read. -/
theorem caIn_pill :
    CaConIn (C ca.battery lib) ∧ DifIn (C ca.battery lib) ∧ AppIn (C ca.battery lib) ∧
      AxisIn (C ca.battery lib) ∧ YeaIn (C ca.battery lib) :=
  ⟨ca.con.arm_at lib, Hoon.Below.cell caOf_lib, Hoon.Below.cell soOf_lib,
    Hoon.Below.cell axisOf_lib, Hoon.Below.cell yeaOf_lib⟩

/-- The pill's core of `+so` gives its gates all that they read. -/
theorem soIn_pill :
    KnitIn (C so.battery lib) ∧ PurrIn (C so.battery lib) ∧ AxisIn (C so.battery lib) ∧
      DarnIn (C so.battery lib) := by
  have hk : KnitIn (C so.battery lib) := Hoon.Below.cell caOf_lib
  have hp : PurrIn (C so.battery lib) :=
    ⟨so.knit.arm_at lib, so.hed.arm_at lib, so.tel.arm_at lib, hk⟩
  have hx : AxisIn (C so.battery lib) := Hoon.Below.cell axisOf_lib
  exact ⟨hk, hp, hx, hp, hx⟩

/-! ## The gates of `+ca` and `+so` on the pill, with no assumption

The gates `hed`, `tel`, `all`, `con` of `+ca` and `hed`, `tel`, `jibe`, `huge`
of `+so` read nothing from their context, and their theorems hold on every
context already. -/

theorem ca_int_pill (a b : Cape) :
    nock (C ca.int.battery (C (C a.toNoun b.toNoun) (C ca.battery lib))) ca.int.battery
      = some (Ca.int a b).toNoun :=
  ca_int_gate _ caIn_pill.1 a b

theorem ca_uni_pill (a b : Cape) :
    nock (C ca.uni.battery (C (C a.toNoun b.toNoun) (C ca.battery lib))) ca.uni.battery
      = some (Ca.uni a b).toNoun :=
  ca_uni_gate _ caIn_pill.1 a b

theorem ca_lack_pill (a b : Cape) :
    nock (C ca.lack.battery (C (C a.toNoun b.toNoun) (C ca.battery lib))) ca.lack.battery
      = some (Ca.lack a b).toNoun :=
  ca_lack_gate _ caIn_pill.1 a b

theorem ca_dif_pill (a b : Cape) :
    nock (C ca.dif.battery (C (C a.toNoun b.toNoun) (C ca.battery lib))) ca.dif.battery
      = (Ca.dif a b).map Cape.toNoun :=
  ca_dif_gate _ caIn_pill.2.1 a b

theorem ca_app_pill (c : Cape) (s : Sock) :
    nock (C ca.app.battery (C (C c.toNoun s.toNoun) (C ca.battery lib))) ca.app.battery
      = some (Ca.app c s).toNoun :=
  ca_app_gate _ caIn_pill.2.2.1 c s

theorem ca_pat_pill (c : Cape) (a : Nat) :
    nock (C ca.pat.battery (C (C c.toNoun (A a)) (C ca.battery lib))) ca.pat.battery
      = (Ca.pat c a).map Cape.toNoun :=
  ca_pat_gate _ caIn_pill.2.2.2.1 c a

theorem ca_lot_pill (c : Cape) (axe : Nat) :
    nock (C ca.lot.battery (C (C c.toNoun (A axe)) (C ca.battery lib))) ca.lot.battery
      = (Ca.lot c axe).map Cape.toNoun :=
  ca_lot_gate _ caIn_pill.2.2.2.1 c axe

theorem ca_yea_pill (c : Cape) :
    nock (C ca.yea.battery (C c.toNoun (C ca.battery lib))) ca.yea.battery
      = some (Hoon.listN ((Ca.yea c).map A)) :=
  ca_yea_gate _ caIn_pill.2.2.2.2 c

theorem so_knit_pill (s1 s2 : Sock) :
    nock (C so.knit.battery (C (C s1.toNoun s2.toNoun) (C so.battery lib))) so.knit.battery
      = some (So.knit s1 s2).toNoun :=
  so_knit_gate _ soIn_pill.1 s1 s2

theorem so_purr_pill (s1 s2 : Sock) :
    nock (C so.purr.battery (C (C s1.toNoun s2.toNoun) (C so.battery lib))) so.purr.battery
      = some (So.purr s1 s2).toNoun :=
  so_purr_gate _ soIn_pill.2.1 s1 s2

theorem so_pull_pill (s : Sock) (axe : Nat) :
    nock (C so.pull.battery (C (C s.toNoun (A axe)) (C so.battery lib))) so.pull.battery
      = (So.pull s axe).map Sock.toNoun :=
  so_pull_gate _ soIn_pill.2.2.1 s axe

theorem so_darn_pill (one : Sock) (axe : Nat) (two : Sock) :
    nock (C so.darn.battery (C (C one.toNoun (C (A axe) two.toNoun)) (C so.battery lib)))
        so.darn.battery
      = (So.darn one axe two).map Sock.toNoun :=
  so_darn_gate _ soIn_pill.2.2.2 one axe two

end Compiler
end Formalization
