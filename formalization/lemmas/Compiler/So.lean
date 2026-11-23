import lemmas.Compiler.Ca
import lemmas.Pill.Arm.So

/-!
The arms of the compiler's core `+so` (operations on socks) compute track B's
models in `lemmas/Ska/Sock.lean`, on the nouns `Sock.toNoun`.

Proved here: `hed`, `tel`, `jibe`, which read nothing from their context,
`knit`, which reads `+con:ca` through the library core, `purr`, which reads
`knit`, `hed`, `tel` from its own core, and `app` of `+ca`, which reads `+so`
through the library core.  Each agrees with B's model on every sock.

The predicates on contexts say what a library core `lib` gives at the named
axes (`Lib.lean` proves them of the pill's own library core): `CaOf lib` says that the arm at `ca.lib.axis` builds
a core that holds `+con:ca`, and `SoOf lib` that the arm at `so.lib.axis`
builds a core that holds `+knit`, `+hed`, `+tel` of `+so`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel

@[nock_exec] theorem so_hed_arm (c : Noun) :
    nock c so.hed.arm = some (C so.hed.battery (C (C (A 1) (A 0)) c)) := by
  nock_open so.hed.arm; simp only [nock_exec]

@[nock_exec] theorem so_tel_arm (c : Noun) :
    nock c so.tel.arm = some (C so.tel.battery (C (C (A 1) (A 0)) c)) := by
  nock_open so.tel.arm; simp only [nock_exec]

@[nock_exec] theorem so_jibe_arm (c : Noun) :
    nock c so.jibe.arm = some (C so.jibe.battery (C (C (C (A 1) (A 0)) (C (A 1) (A 0))) c)) := by
  nock_open so.jibe.arm; simp only [nock_exec]

theorem so_hed_gate (ctx : Noun) (s : Sock) :
    nock (C so.hed.battery (C s.toNoun ctx)) so.hed.battery = some (So.hed s).toNoun := by
  nock_open so.hed.battery
  rcases s with _ | ⟨c, d⟩
  · simp [nock_exec, Sock.toNoun, So.hed]
  · rcases c with _ | _ | ⟨ch, ct⟩ <;> rcases d with _ | ⟨dh, dt⟩ <;>
      simp [nock_exec, Sock.toNoun, Cape.toNoun, So.hed, Sock.dunno]

theorem so_tel_gate (ctx : Noun) (s : Sock) :
    nock (C so.tel.battery (C s.toNoun ctx)) so.tel.battery = some (So.tel s).toNoun := by
  nock_open so.tel.battery
  rcases s with _ | ⟨c, d⟩
  · simp [nock_exec, Sock.toNoun, So.tel]
  · rcases c with _ | _ | ⟨ch, ct⟩ <;> rcases d with _ | ⟨dh, dt⟩ <;>
      simp [nock_exec, Sock.toNoun, Cape.toNoun, So.tel, Sock.dunno]

theorem so_jibe_mk (ctx : Noun) : ∀ (d1 : Noun) (c1 c2 : Cape) (d2 : Noun),
    nock (C so.jibe.battery (C (C (C c1.toNoun d1) (C c2.toNoun d2)) ctx)) so.jibe.battery
      = some (Hoon.loob (So.jibeMk c1 d1 c2 d2))
  | Noun.atom k, c1, c2, d2 => by
    nock_open so.jibe.battery
    rcases c1 with _ | _ | ⟨a, b⟩ <;> rcases c2 with _ | _ | ⟨a', b'⟩ <;>
      rcases d2 with _ | ⟨x, y⟩ <;>
      simp [nock_exec, nock_ite, Cape.toNoun, So.jibeMk, cape_toNoun_eq, Hoon.loob] <;>
      (repeat' split) <;> simp_all [eqCode]
  | Noun.cell h t, c1, c2, d2 => by
    rcases d2 with k | ⟨x, y⟩
    · nock_open so.jibe.battery
      rcases c1 with _ | _ | ⟨a, b⟩ <;> rcases c2 with _ | _ | ⟨a', b'⟩ <;>
        simp [nock_exec, Cape.toNoun, So.jibeMk, cape_toNoun_eq, Hoon.loob] <;>
        (repeat' split) <;> simp_all [eqCode]
    · have i1 := so_jibe_mk ctx h (Ca.hed c1) (Ca.hed c2) x
      have i2 := so_jibe_mk ctx t (Ca.tel c1) (Ca.tel c2) y
      nock_open so.jibe.battery
      rcases c1 with _ | _ | ⟨a, b⟩ <;> rcases c2 with _ | _ | ⟨a', b'⟩ <;>
        simp only [Ca.hed, Ca.tel, Cape.toNoun] at i1 i2 <;>
        simp [nock_exec, nock_ite, Cape.toNoun, So.jibeMk, cape_toNoun_eq, Ca.hed, Ca.tel, i1,
          i2] <;>
        (repeat' split) <;>
        simp_all [nock_exec, eqCode] <;>
        (simp only [Hoon.loob] at *; (repeat' split) <;> simp_all)

/-- Slamming `jibe` of `+so` on two socks. -/
theorem so_jibe_gate (ctx : Noun) (s1 s2 : Sock) :
    nock (C so.jibe.battery (C (C s1.toNoun s2.toNoun) ctx)) so.jibe.battery
      = some (Hoon.loob (So.jibe s1 s2)) := by
  rcases s1 with _ | ⟨c1, d1⟩ <;> rcases s2 with _ | ⟨c2, d2⟩
  · nock_open so.jibe.battery; simp [nock_exec, Sock.toNoun, So.jibe, Tag.void]
  · nock_open so.jibe.battery; simp [nock_exec, Sock.toNoun, So.jibe, Tag.void]
  · nock_open so.jibe.battery; simp [nock_exec, Sock.toNoun, So.jibe, Tag.void]
  · exact so_jibe_mk ctx d1 c1 c2 d2

/-! ## `+knit:so` -/

/-- The library core `lib` builds the core of `+ca` with the arm at
`ca.lib.axis`, and that core holds `+con:ca`. -/
abbrev CaOf (lib : Noun) : Prop :=
  ∃ f k, slot? ca.lib.axis lib = some f ∧ nock lib f = some k ∧
    slot? ca.con.axis k = some ca.con.arm

/-- What `+knit` reads from its context, the core of `+so`. -/
abbrev KnitIn (c : Noun) : Prop := Hoon.Below CaOf c

@[nock_exec] theorem so_knit_arm (c : Noun) :
    nock c so.knit.arm = some (C so.knit.battery (C (C (C (A 1) (A 0)) (C (A 1) (A 0))) c)) := by
  nock_open so.knit.arm; simp only [nock_exec]

theorem so_knit_gate (ctx : Noun) (hc : KnitIn ctx) (s1 s2 : Sock) :
    nock (C so.knit.battery (C (C s1.toNoun s2.toNoun) ctx)) so.knit.battery
      = some (So.knit s1 s2).toNoun := by
  obtain ⟨bat, lib, rfl, f, k, hf, hk, hcon⟩ := hc.elim
  rcases s1 with _ | ⟨c1, d1⟩ <;> rcases s2 with _ | ⟨c2, d2⟩
  · nock_open so.knit.battery; simp [nock_exec, Sock.toNoun, So.knit, Tag.void]
  · nock_open so.knit.battery; simp [nock_exec, Sock.toNoun, So.knit, Tag.void]
  · nock_open so.knit.battery; simp [nock_exec, Sock.toNoun, So.knit, Tag.void]
  · nock_open so.knit.battery
    simp only [Sock.toNoun]
    cases h : Ca.con c1 c2 <;>
      simp [nock_exec, hf, hk, hcon, ca_con_arm, ca_con_gate, h, So.knit, Cape.toNoun,
        Sock.dunno]

/-! ## `+app:ca` -/

theorem sock_toNoun_mk (c : Cape) (d : Noun) : (Sock.mk c d).toNoun = C c.toNoun d := rfl

/-- The library core `lib` builds the core of `+so` with the arm at
`so.lib.axis`, and that core holds `+knit`, `+hed`, `+tel` of `+so`. -/
abbrev SoOf (lib : Noun) : Prop :=
  ∃ f k, slot? so.lib.axis lib = some f ∧ nock lib f = some k ∧
    slot? so.knit.axis k = some so.knit.arm ∧ slot? so.hed.axis k = some so.hed.arm ∧
    slot? so.tel.axis k = some so.tel.arm ∧ KnitIn k

/-- What `+app` reads from its context, the core of `+ca`. -/
abbrev AppIn (c : Noun) : Prop := Hoon.Below SoOf c

@[nock_exec] theorem ca_app_arm (c : Noun) :
    nock c ca.app.arm = some (C ca.app.battery (C (C (A 1) (C (A 1) (A 0))) c)) := by
  nock_open ca.app.arm; simp only [nock_exec]

theorem ca_app_gate (ctx : Noun) (hc : AppIn ctx) : ∀ (c : Cape) (s : Sock),
    nock (C ca.app.battery (C (C c.toNoun s.toNoun) ctx)) ca.app.battery
      = some (Ca.app c s).toNoun := by
  obtain ⟨bat, lib, rfl, f, k, hf, hk, hknit, hhed, htel, hkc⟩ := hc.elim
  intro c
  induction c with
  | yes =>
    intro s
    nock_open ca.app.battery
    rcases s with _ | ⟨cs, d⟩
    · simp [nock_exec, Sock.toNoun, Ca.app, Tag.void]
    · cases cs <;> simp [nock_exec, Sock.toNoun, Cape.toNoun, Ca.app, Sock.dunno]
  | no =>
    intro s
    nock_open ca.app.battery
    rcases s with _ | ⟨cs, d⟩
    · simp [nock_exec, Sock.toNoun, Ca.app, Tag.void]
    · cases cs <;> simp [nock_exec, Sock.toNoun, Cape.toNoun, Ca.app, Sock.dunno]
  | cell ch ct ih it =>
    intro s
    rcases s with _ | ⟨cs, d⟩
    · nock_open ca.app.battery; simp [nock_exec, Sock.toNoun, Ca.app, Tag.void]
    by_cases hno : cs = Cape.no
    · subst hno; nock_open ca.app.battery
      simp [nock_exec, Sock.toNoun, Cape.toNoun, Ca.app, Sock.dunno]
    by_cases e : Cape.cell ch ct = cs
    · subst e; nock_open ca.app.battery; simp [nock_exec, Sock.toNoun, Cape.toNoun, Ca.app]
    have hno1 : ¬ (A 1 = cs.toNoun) := fun h => hno (cape_toNoun_inj (a := cs) (b := Cape.no) h.symm)
    have he1 : ¬ (C ch.toNoun ct.toNoun = cs.toNoun) := fun h => e (cape_toNoun_inj h)
    generalize hs1 : So.hed (Sock.mk cs d) = s1
    generalize hs2 : So.tel (Sock.mk cs d) = s2
    have h1 : nock (C so.hed.battery (C (C cs.toNoun d) k)) so.hed.battery = some s1.toNoun := by
      rw [← hs1]; exact so_hed_gate k (Sock.mk cs d)
    have h2 : nock (C so.tel.battery (C (C cs.toNoun d) k)) so.tel.battery = some s2.toNoun := by
      rw [← hs2]; exact so_tel_gate k (Sock.mk cs d)
    have hm : Ca.app (Cape.cell ch ct) (Sock.mk cs d) = So.knit (Ca.app ch s1) (Ca.app ct s2) := by
      rw [← hs1, ← hs2]; simp [Ca.app, e, hno]
    rw [hm]
    nock_open ca.app.battery
    simp [nock_exec, sock_toNoun_mk, Cape.toNoun, hno1, he1, hf, hk, hknit, hhed, htel,
      so_hed_arm, so_tel_arm, so_knit_arm, h1, h2, ih, it, so_knit_gate k hkc]

/-! ## `+purr:so` -/

theorem sock_toNoun_void : Sock.void.toNoun = A Tag.void := rfl

theorem sock_toNoun_inj : ∀ {a b : Sock}, a.toNoun = b.toNoun → a = b
  | Sock.void, Sock.void, _ => rfl
  | Sock.mk c d, Sock.mk c' d', h => by
    simp only [sock_toNoun_mk, Noun.cell.injEq] at h
    rw [cape_toNoun_inj h.1, h.2]
  | Sock.void, Sock.mk _ _, h => by simp [sock_toNoun_void, sock_toNoun_mk] at h
  | Sock.mk _ _, Sock.void, h => by simp [sock_toNoun_void, sock_toNoun_mk] at h

/-- What `+purr` reads from its context, the core of `+so`: the arms `knit`,
`hed`, `tel` of that core, and what `knit` reads. -/
abbrev PurrIn (c : Noun) : Prop :=
  slot? so.knit.axis c = some so.knit.arm ∧ slot? so.hed.axis c = some so.hed.arm ∧
    slot? so.tel.axis c = some so.tel.arm ∧ KnitIn c

@[nock_exec] theorem so_purr_arm (c : Noun) :
    nock c so.purr.arm = some (C so.purr.battery (C (C (C (A 1) (A 0)) (C (A 1) (A 0))) c)) := by
  nock_open so.purr.arm; simp only [nock_exec]

theorem so_purr_loop (c : Noun) (hk : slot? so.knit.axis c = some so.knit.arm) (hkc : KnitIn c) :
    ∀ (d1 d2 : Noun),
    nock (C so.purr.loop (C so.purr.battery (C (C (C (A 0) d1) (C (A 0) d2)) c))) so.purr.loop
      = some (So.purrData d1 d2).toNoun
  | Noun.atom n, Noun.atom m => by
    nock_open so.purr.loop
    by_cases e : n = m
    · subst e; simp [nock_exec, So.purrData, sock_toNoun_mk, Cape.toNoun]
    · simp [nock_exec, e, So.purrData, Sock.dunno, sock_toNoun_mk, Cape.toNoun]
  | Noun.atom n, Noun.cell x y => by
    nock_open so.purr.loop
    simp [nock_exec, So.purrData, Sock.dunno, sock_toNoun_mk, Cape.toNoun]
  | Noun.cell a b, Noun.atom n => by
    nock_open so.purr.loop
    simp [nock_exec, So.purrData, Sock.dunno, sock_toNoun_mk, Cape.toNoun]
  | Noun.cell a b, Noun.cell x y => by
    nock_open so.purr.loop
    by_cases e : a = x ∧ b = y
    · obtain ⟨rfl, rfl⟩ := e; simp [nock_exec, So.purrData, sock_toNoun_mk, Cape.toNoun]
    · have e3 : ¬ (Noun.cell a b = Noun.cell x y) := fun h => e (by simpa using h)
      have hm : So.purrData (C a b) (C x y) = So.knit (So.purrData a x) (So.purrData b y) := by
        rw [So.purrData, if_neg e3]
      have i1 := so_purr_loop c hk hkc a x
      have i2 := so_purr_loop c hk hkc b y
      rw [hm]
      simp [nock_exec, e, hk, so_knit_arm, i1, i2, so_knit_gate c hkc]

theorem so_purr_gate (c : Noun) (hc : PurrIn c) : ∀ (s1 s2 : Sock),
    nock (C so.purr.battery (C (C s1.toNoun s2.toNoun) c)) so.purr.battery
      = some (So.purr s1 s2).toNoun
  | s1, s2 => by
    have ⟨hk, hh, ht, hkc⟩ := hc
    by_cases e : s1 = s2
    · subst e; nock_open so.purr.battery; rw [So.purr.eq_def, if_pos rfl]; simp [nock_exec]
    have e' : ¬ s1.toNoun = s2.toNoun := fun h => e (sock_toNoun_inj h)
    rw [So.purr.eq_def, if_neg e]
    rcases s1 with _ | ⟨c1, d1⟩ <;> rcases s2 with _ | ⟨c2, d2⟩
    · exact absurd rfl e
    · simp only [sock_toNoun_void, sock_toNoun_mk] at e' ⊢
      nock_open so.purr.battery; simp [nock_exec, e']
    · simp only [sock_toNoun_void, sock_toNoun_mk] at e' ⊢
      nock_open so.purr.battery; simp [nock_exec, e']
    simp only [sock_toNoun_mk] at e' ⊢
    by_cases hno : c1 = Cape.no ∨ c2 = Cape.no
    · have e2 : ¬ (c1.toNoun = c2.toNoun ∧ d1 = d2) := fun ⟨h1, h2⟩ => e' (by rw [h1, h2])
      rcases hno with rfl | rfl
      · simp only [Cape.toNoun] at e2
        nock_open so.purr.battery; simp [nock_exec, e2, Cape.toNoun, Sock.dunno, sock_toNoun_mk]
      · nock_open so.purr.battery
        cases c1 <;> simp only [Cape.toNoun, true_and] at e2 <;>
          simp [nock_exec, e2, Cape.toNoun, Sock.dunno, sock_toNoun_mk]
    simp only [hno, if_false]
    have hn1 : c1 ≠ Cape.no := fun h => hno (Or.inl h)
    have hn2 : c2 ≠ Cape.no := fun h => hno (Or.inr h)
    rcases c1 with _ | _ | ⟨ch, ct⟩ <;> rcases c2 with _ | _ | ⟨ch', ct'⟩
    all_goals first | exact absurd rfl hn1 | exact absurd rfl hn2 | skip
    all_goals simp only [Cape.toNoun] at e'
    · nock_open so.purr.battery
      simp [nock_exec, e', Cape.toNoun, so_purr_loop c hk hkc d1 d2]
    · have r1 := so_purr_gate c hc (So.hed (Sock.mk (Cape.yes) d1)) (So.hed (Sock.mk (Cape.cell ch' ct') d2))
      have r2 := so_purr_gate c hc (So.tel (Sock.mk (Cape.yes) d1)) (So.tel (Sock.mk (Cape.cell ch' ct') d2))
      have h1 := so_hed_gate c (Sock.mk (Cape.yes) d1)
      have h2 := so_hed_gate c (Sock.mk (Cape.cell ch' ct') d2)
      have h3 := so_tel_gate c (Sock.mk (Cape.yes) d1)
      have h4 := so_tel_gate c (Sock.mk (Cape.cell ch' ct') d2)
      generalize hx1 : So.hed (Sock.mk (Cape.yes) d1) = x1 at r1 h1 ⊢
      generalize hx2 : So.hed (Sock.mk (Cape.cell ch' ct') d2) = x2 at r1 h2 ⊢
      generalize hx3 : So.tel (Sock.mk (Cape.yes) d1) = x3 at r2 h3 ⊢
      generalize hx4 : So.tel (Sock.mk (Cape.cell ch' ct') d2) = x4 at r2 h4 ⊢
      simp only [sock_toNoun_mk, Cape.toNoun] at h1 h2 h3 h4
      nock_open so.purr.battery
      simp [nock_exec, e', Cape.toNoun, hk, hh, ht, so_hed_arm, so_tel_arm, so_knit_arm, h1, h2,
        h3, h4, r1, r2, so_knit_gate c hkc]
      subst hx1 hx2 hx3 hx4; rfl
    · have r1 := so_purr_gate c hc (So.hed (Sock.mk (Cape.cell ch ct) d1)) (So.hed (Sock.mk (Cape.yes) d2))
      have r2 := so_purr_gate c hc (So.tel (Sock.mk (Cape.cell ch ct) d1)) (So.tel (Sock.mk (Cape.yes) d2))
      have h1 := so_hed_gate c (Sock.mk (Cape.cell ch ct) d1)
      have h2 := so_hed_gate c (Sock.mk (Cape.yes) d2)
      have h3 := so_tel_gate c (Sock.mk (Cape.cell ch ct) d1)
      have h4 := so_tel_gate c (Sock.mk (Cape.yes) d2)
      generalize hx1 : So.hed (Sock.mk (Cape.cell ch ct) d1) = x1 at r1 h1 ⊢
      generalize hx2 : So.hed (Sock.mk (Cape.yes) d2) = x2 at r1 h2 ⊢
      generalize hx3 : So.tel (Sock.mk (Cape.cell ch ct) d1) = x3 at r2 h3 ⊢
      generalize hx4 : So.tel (Sock.mk (Cape.yes) d2) = x4 at r2 h4 ⊢
      simp only [sock_toNoun_mk, Cape.toNoun] at h1 h2 h3 h4
      nock_open so.purr.battery
      simp [nock_exec, e', Cape.toNoun, hk, hh, ht, so_hed_arm, so_tel_arm, so_knit_arm, h1, h2,
        h3, h4, r1, r2, so_knit_gate c hkc]
      subst hx1 hx2 hx3 hx4; rfl
    · have r1 := so_purr_gate c hc (So.hed (Sock.mk (Cape.cell ch ct) d1)) (So.hed (Sock.mk (Cape.cell ch' ct') d2))
      have r2 := so_purr_gate c hc (So.tel (Sock.mk (Cape.cell ch ct) d1)) (So.tel (Sock.mk (Cape.cell ch' ct') d2))
      have h1 := so_hed_gate c (Sock.mk (Cape.cell ch ct) d1)
      have h2 := so_hed_gate c (Sock.mk (Cape.cell ch' ct') d2)
      have h3 := so_tel_gate c (Sock.mk (Cape.cell ch ct) d1)
      have h4 := so_tel_gate c (Sock.mk (Cape.cell ch' ct') d2)
      generalize hx1 : So.hed (Sock.mk (Cape.cell ch ct) d1) = x1 at r1 h1 ⊢
      generalize hx2 : So.hed (Sock.mk (Cape.cell ch' ct') d2) = x2 at r1 h2 ⊢
      generalize hx3 : So.tel (Sock.mk (Cape.cell ch ct) d1) = x3 at r2 h3 ⊢
      generalize hx4 : So.tel (Sock.mk (Cape.cell ch' ct') d2) = x4 at r2 h4 ⊢
      simp only [sock_toNoun_mk, Cape.toNoun] at h1 h2 h3 h4
      nock_open so.purr.battery
      simp [nock_exec, e', Cape.toNoun, hk, hh, ht, so_hed_arm, so_tel_arm, so_knit_arm, h1, h2,
        h3, h4, r1, r2, so_knit_gate c hkc]
      subst hx1 hx2 hx3 hx4; rfl
termination_by s1 s2 => So.depth s1 + So.depth s2
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Nat.add_lt_add_of_lt_of_le So.depth_hed_lt (So.depth_hed_le _)
    | exact Nat.add_lt_add_of_lt_of_le So.depth_tel_lt (So.depth_tel_le _)
    | exact Nat.add_lt_add_of_le_of_lt (So.depth_hed_le _) So.depth_hed_lt
    | exact Nat.add_lt_add_of_le_of_lt (So.depth_tel_le _) So.depth_tel_lt

end Compiler
end Formalization
