import lemmas.Compiler.Ca
import lemmas.Pill.Arm.So

/-!
The arms of the compiler's core `+so` (operations on socks) compute track B's
models in `lemmas/Ska/Sock.lean`, on the nouns `Sock.toNoun`.

Proved here: `hed`, `tel`, `jibe`, which read nothing from their context;
each agrees with B's model on every sock.
Not here: `knit`, `pull`, `purr`, `darn` (they read `+ca` or `hoon.hoon`
through the library core, whose arm `+ca` the generator cannot name, since
its battery holds a quoted copy of the hoon core), and `huge`, which the
generator does not name for the same reason.
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

end Compiler
end Formalization
