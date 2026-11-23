import lemmas.Compiler.GitMi
import lemmas.Pill.Arm.He_sock

/-!
`+he-sock` of the analysis core `ana` against `heSock`, written here after the
Hoon, line by line.

```hoon
++  he-sock
  ~%  %he-sock  ..ride  ~
  |=  [big=sock smol=sock]
  ^-  ?
  =*  h-e  .
  ?:  =(big smol)  &
  ?:  |(?=(%void big) ?=(%void smol))  |
  ?:  (lth (cape-size cape.big) (cape-size cape.smol))  |
  ?:  &(?=(@ cape.big) ?=(@ cape.smol))  |
  =/  couple=?
    ?.  &(?=(^ cape.big) ?=(^ cape.smol))  |
    ~+
    ?&  (h-e (hed:so big) (hed:so smol))
        (h-e (tel:so big) (tel:so smol))
    ==
  ?:  couple  &
  ?@  cape.big  |
  ~+
  ?|  (h-e (hed:so big) smol)
      (h-e (tel:so big) smol)
  ==
```

The gate never crashes on two socks, so the model is a `Bool`, and it is the
parameter `Env.he` of `Ska/Analysis.lean` as it stands: `heEnv` is the `Env`
with `he := heSock`.  It reads `+lth` of the library's first layer at axis
`16383` of its context, `+cape-size` at axis `22495` (which reads `+add` of the
same layer), and the cores of `+so` through the pill's library core at axis
`7` (`HeSockIn`).  The two `~+` are `%memo` hints, which change nothing.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

/-! ## The model -/

/-- The measure of the recursion: the size of the cape, `0` for `%void`. -/
def sockSize : Sock → Nat
  | Sock.void => 0
  | Sock.mk c _ => capeSize c

theorem capeSize_pos : ∀ c : Cape, 0 < capeSize c
  | Cape.yes => by simp [capeSize]
  | Cape.no => by simp [capeSize]
  | Cape.cell a _ => by have := capeSize_pos a; simp only [capeSize]; omega

theorem sockSize_hed_lt (a b : Cape) (d : Noun) :
    sockSize (So.hed (Sock.mk (Cape.cell a b) d)) < capeSize a + capeSize b := by
  have ha := capeSize_pos a
  have hb := capeSize_pos b
  cases d <;> simp [So.hed, sockSize, Sock.dunno, capeSize] <;> omega

theorem sockSize_tel_lt (a b : Cape) (d : Noun) :
    sockSize (So.tel (Sock.mk (Cape.cell a b) d)) < capeSize a + capeSize b := by
  have ha := capeSize_pos a
  have hb := capeSize_pos b
  cases d <;> simp [So.tel, sockSize, Sock.dunno, capeSize] <;> omega

/-- `+he-sock`: does `big` homeomorphically embed `smol`?  The branches in
the Hoon's order: equal socks, a `%void`, a smaller cape, two atom capes;
then `couple` (two cell capes, head in head and tail in tail), and for a cell
cape of `big`, `smol` in its head or its tail. -/
def heSock (big smol : Sock) : Bool :=
  if big = smol then true else
  match big, smol with
  | Sock.void, _ => false
  | Sock.mk _ _, Sock.void => false
  | Sock.mk cb db, Sock.mk cs ds =>
    if capeSize cb < capeSize cs then false else
    match cb, cs with
    | Cape.cell a b, Cape.cell c d =>
      (heSock (So.hed (Sock.mk (Cape.cell a b) db)) (So.hed (Sock.mk (Cape.cell c d) ds)) &&
        heSock (So.tel (Sock.mk (Cape.cell a b) db)) (So.tel (Sock.mk (Cape.cell c d) ds))) ||
      (heSock (So.hed (Sock.mk (Cape.cell a b) db)) (Sock.mk (Cape.cell c d) ds) ||
        heSock (So.tel (Sock.mk (Cape.cell a b) db)) (Sock.mk (Cape.cell c d) ds))
    | Cape.cell a b, cs' =>
      heSock (So.hed (Sock.mk (Cape.cell a b) db)) (Sock.mk cs' ds) ||
        heSock (So.tel (Sock.mk (Cape.cell a b) db)) (Sock.mk cs' ds)
    | _, _ => false
termination_by sockSize big + sockSize smol
decreasing_by
  all_goals first
    | (have := sockSize_hed_lt a b db; have := sockSize_hed_lt c d ds
       simp only [sockSize, capeSize] at *; omega)
    | (have := sockSize_tel_lt a b db; have := sockSize_tel_lt c d ds
       simp only [sockSize, capeSize] at *; omega)
    | (have := sockSize_hed_lt a b db; simp only [sockSize, capeSize] at *; omega)
    | (have := sockSize_tel_lt a b db; simp only [sockSize, capeSize] at *; omega)

/-! ## The gate -/

/-- What `+he-sock` reads from its context: `+lth` and `+add` of the
library's first layer, `+cape-size`, and the pill's library core. -/
abbrev HeSockIn (c : Noun) : Prop :=
  (∃ l, slot? capeSize.layer1.axis c = some l ∧ AddIn l ∧ LthIn l) ∧
    slot? cape_size.axis c = some cape_size.arm ∧ slot? knit_anno.lib.axis c = some lib

@[nock_exec] theorem he_sock_arm (c : Noun) :
    nock c he_sock.arm
      = some (C he_sock.battery (C (C (C (A 1) (A 0)) (C (A 1) (A 0))) c)) := by
  nock_open he_sock.arm; simp only [nock_exec]

theorem heSock_self (s : Sock) : heSock s s = true := by
  rw [heSock.eq_def]; simp

/-- Slamming `+he-sock` on two socks, by induction on the measure. -/
theorem he_sock_gate' (ctx : Noun) (hc : HeSockIn ctx) : ∀ (n : Nat) (big smol : Sock),
    sockSize big + sockSize smol < n →
    nock (C he_sock.battery (C (C big.toNoun smol.toNoun) ctx)) he_sock.battery
      = some (loob (heSock big smol)) := by
  obtain ⟨⟨l, hl, hadd, hlth⟩, hcs, hlib⟩ := hc
  have hcsIn : CapeSizeIn ctx := ⟨l, hl, hadd⟩
  have hlib' : slot? 7 ctx = some lib := hlib
  have hl' : slot? 16383 ctx = some l := hl
  have hcs' : slot? 22495 ctx = some cape_size.arm := hcs
  have hcg := cape_size_gate ctx hcsIn
  have hlg := lth_gate l hlth.2
  have hlth1 := hlth.1
  intro n
  induction n with
  | zero => intro _ _ h; omega
  | succ n ih =>
  intro big smol hn
  by_cases e : big = smol
  · subst e
    rw [heSock_self]
    nock_open he_sock.battery
    simp [nock_exec]
  have e' := sock_toNoun_ne e
  rcases big with _ | ⟨cb, db⟩ <;> rcases smol with _ | ⟨cs, ds⟩
  · exact absurd rfl e
  · rw [heSock, if_neg e]
    nock_open he_sock.battery
    simp [nock_exec, sock_mk_toNoun, sock_void_toNoun, Tag.void]
  · rw [heSock, if_neg e]
    nock_open he_sock.battery
    simp [nock_exec, sock_mk_toNoun, sock_void_toNoun, Tag.void]
  have hsz : capeSize cb + capeSize cs < n + 1 := hn
  simp only [sock_mk_toNoun] at e' ⊢
  rw [heSock.eq_def, if_neg e]
  simp only []
  have hhed := so_hed_gate (C so.battery lib)
  have htel := so_tel_gate (C so.battery lib)
  by_cases hlt : capeSize cb < capeSize cs
  · rw [if_pos hlt]
    have hlt' : leafCount cb.toNoun < leafCount cs.toNoun := by rwa [← capeSize_eq, ← capeSize_eq]
    nock_open he_sock.battery
    simp [nock_exec, e', hl', hlth1, lth_arm, hcs', cape_size_arm, hcg, hlg, hlt']
  rw [if_neg hlt]
  have hlt' : ¬ leafCount cb.toNoun < leafCount cs.toNoun := by rwa [← capeSize_eq, ← capeSize_eq]
  rcases cb with _ | _ | ⟨a, b⟩
  · nock_open he_sock.battery
    rcases cs with _ | _ | ⟨c, d⟩ <;> (try simp [Cape.toNoun] at e') <;>
      (try simp only [Cape.toNoun] at hlt') <;>
      simp [nock_exec, e', hl', hlth1, lth_arm, hcs', cape_size_arm, hcg, hlg, hlt', Cape.toNoun]
  · nock_open he_sock.battery
    rcases cs with _ | _ | ⟨c, d⟩ <;> (try simp [Cape.toNoun] at e') <;>
      (try simp only [Cape.toNoun] at hlt') <;>
      simp [nock_exec, e', hl', hlth1, lth_arm, hcs', cape_size_arm, hcg, hlg, hlt', Cape.toNoun]
  have h1 := sockSize_hed_lt a b db
  have h2 := sockSize_tel_lt a b db
  simp only [capeSize] at hsz
  have hb1 := hhed (Sock.mk (Cape.cell a b) db)
  have hb2 := htel (Sock.mk (Cape.cell a b) db)
  simp only [sock_mk_toNoun, cape_cell_toNoun] at hb1 hb2
  have hcz := capeSize_pos cs
  have i3 := ih (So.hed (Sock.mk (Cape.cell a b) db)) (Sock.mk cs ds) (by show sockSize _ + capeSize cs < n; omega)
  have i4 := ih (So.tel (Sock.mk (Cape.cell a b) db)) (Sock.mk cs ds) (by show sockSize _ + capeSize cs < n; omega)
  rcases cs with _ | _ | ⟨c, d⟩
  · simp only [sock_mk_toNoun, Cape.toNoun] at i3 i4
    dsimp only
    try simp [Cape.toNoun] at e'
    try simp only [Cape.toNoun] at hlt'
    generalize heSock (So.hed (Sock.mk (Cape.cell a b) db)) (Sock.mk Cape.yes ds) = b3 at i3 ⊢
    generalize heSock (So.tel (Sock.mk (Cape.cell a b) db)) (Sock.mk Cape.yes ds) = b4 at i4 ⊢
    nock_open he_sock.battery
    cases b3 <;> cases b4 <;>
      simp [nock_exec, hl', hlth1, lth_arm, hcs', cape_size_arm, hcg, hlg, hlt', Cape.toNoun,
        hlib', so.lib.arm_at, so_lib_arm, so.hed.arm_at, so.tel.arm_at, so_hed_arm, so_tel_arm,
        hb1, hb2, i3, i4]
  · simp only [sock_mk_toNoun, Cape.toNoun] at i3 i4
    dsimp only
    try simp [Cape.toNoun] at e'
    try simp only [Cape.toNoun] at hlt'
    generalize heSock (So.hed (Sock.mk (Cape.cell a b) db)) (Sock.mk Cape.no ds) = b3 at i3 ⊢
    generalize heSock (So.tel (Sock.mk (Cape.cell a b) db)) (Sock.mk Cape.no ds) = b4 at i4 ⊢
    nock_open he_sock.battery
    cases b3 <;> cases b4 <;>
      simp [nock_exec, hl', hlth1, lth_arm, hcs', cape_size_arm, hcg, hlg, hlt', Cape.toNoun,
        hlib', so.lib.arm_at, so_lib_arm, so.hed.arm_at, so.tel.arm_at, so_hed_arm, so_tel_arm,
        hb1, hb2, i3, i4]
  · have h3 := sockSize_hed_lt c d ds
    have h4 := sockSize_tel_lt c d ds
    simp only [capeSize] at hsz
    have hs1 := hhed (Sock.mk (Cape.cell c d) ds)
    have hs2 := htel (Sock.mk (Cape.cell c d) ds)
    simp only [sock_mk_toNoun, cape_cell_toNoun] at hs1 hs2 i3 i4
    dsimp only
    have e'' : ¬ ((a.toNoun = c.toNoun ∧ b.toNoun = d.toNoun) ∧ db = ds) :=
      fun ⟨⟨q1, q2⟩, q3⟩ => e (by rw [cape_toNoun_inj q1, cape_toNoun_inj q2, q3])
    try simp only [Cape.toNoun] at hlt'
    have i1 := ih (So.hed (Sock.mk (Cape.cell a b) db)) (So.hed (Sock.mk (Cape.cell c d) ds))
      (by omega)
    have i2 := ih (So.tel (Sock.mk (Cape.cell a b) db)) (So.tel (Sock.mk (Cape.cell c d) ds))
      (by omega)
    generalize heSock (So.hed (Sock.mk (Cape.cell a b) db)) (So.hed (Sock.mk (Cape.cell c d) ds))
      = b1 at i1 ⊢
    generalize heSock (So.tel (Sock.mk (Cape.cell a b) db)) (So.tel (Sock.mk (Cape.cell c d) ds))
      = b2 at i2 ⊢
    generalize heSock (So.hed (Sock.mk (Cape.cell a b) db)) (Sock.mk (Cape.cell c d) ds)
      = b3 at i3 ⊢
    generalize heSock (So.tel (Sock.mk (Cape.cell a b) db)) (Sock.mk (Cape.cell c d) ds)
      = b4 at i4 ⊢
    nock_open he_sock.battery
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
      simp [nock_exec, hl', hlth1, lth_arm, hcs', cape_size_arm, hcg, hlg, hlt', Cape.toNoun,
        hlib', so.lib.arm_at, so_lib_arm, so.hed.arm_at, so.tel.arm_at, so_hed_arm, so_tel_arm,
        hb1, hb2, hs1, hs2, i1, i2, i3, i4, e'']

/-- Slamming `+he-sock` on two socks: `heSock`. -/
theorem he_sock_gate (ctx : Noun) (hc : HeSockIn ctx) (big smol : Sock) :
    nock (C he_sock.battery (C (C big.toNoun smol.toNoun) ctx)) he_sock.battery
      = some (loob (heSock big smol)) :=
  he_sock_gate' ctx hc _ big smol (Nat.lt_succ_self _)

/-! ## On the pill's analysis core -/

theorem heSockIn_ana : HeSockIn ana :=
  ⟨⟨layer1, ana_layer1, arith_layer1.1, arith_layer1.2.2.2.1⟩, cape_size.arm_at,
    knit_anno.lib.arm_at⟩

theorem he_sock_pill (big smol : Sock) :
    nock (C he_sock.battery (C (C big.toNoun smol.toNoun) ana)) he_sock.battery
      = some (loob (heSock big smol)) :=
  he_sock_gate ana heSockIn_ana big smol

/-- The parameters of the analysis model of `Ska/Analysis.lean` with
`+he-sock` given by its model and `he-threshold` by its value: what is left
are `+soft-spot` and `+register-fast`. -/
def heEnv {R : Type} (softSpot : Noun → Option Noun)
    (registerFast : Sock → Sock → R → Option (Bool × R)) : Env R :=
  ⟨heSock, softSpot, registerFast, 32⟩

end Compiler
end Formalization
