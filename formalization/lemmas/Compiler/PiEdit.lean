import lemmas.Compiler.Lib
import lemmas.Pill.Arm.Distribute
import lemmas.Pill.Arm.Double_int

/-!
`edit` and `prune` of the provenance core `+pi`, `+distribute` and
`+double-int` against the models of `lemmas/Ska/Pi.lean`.

The upward loop of `edit` is the same noun as the upward loop of `+darn:so`
(`so.darn.loop0`): both slam the arm at axis `86` of their context, `+knit`
in `+so` and `cons` in `+pi`.  `pi_edit_up` is its theorem for `cons`.

`prune` is `+distribute` with its arguments swapped and its first two tests in
the other order: `pi_prune_gate` says it computes `distribute`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel

/-! ## `edit` -/

/-- The stack of `edit`, `(list [c=?(%2 %3) p=spring])`. -/
def tackN (tack : List (Nat × Noun)) : Noun := Hoon.listN (tack.map fun e => C (A e.1) e.2)

/-- What `edit` of `+pi` reads from its context, the core of `+pi`: `cons`,
`hed`, `tel`, and `+cap`, `+mas`, `+peg` below. -/
abbrev PiEditIn (c : Noun) : Prop :=
  slot? pi.cons.axis c = some pi.cons.arm ∧ slot? pi.hed.axis c = some pi.hed.arm ∧
    slot? pi.tel.axis c = some pi.tel.arm ∧ PiSlotIn c

@[nock_exec] theorem pi_edit_arm (c : Noun) :
    nock c pi.edit.arm = some (C pi.edit.battery (C (C (A 0) (C (A 0) (A 0))) c)) := by
  nock_open pi.edit.arm; simp only [nock_exec]

/-- The loop of `edit` on its way up, which is the loop of `+darn:so` with
`cons` of `+pi` at the axis of `+knit:so`. -/
theorem pi_edit_up (c : Noun) (hk : slot? pi.cons.axis c = some pi.cons.arm) (o x : Noun) :
    ∀ (tack : List (Nat × Noun)) (don : Noun),
    nock (C so.darn.loop0 (C pi.edit.loop1 (C (tackN tack)
        (C pi.edit.battery (C (C o (C x don)) c))))) so.darn.loop0
      = some (Pi.editUp don tack) := by
  intro tack
  induction tack with
  | nil => intro don; nock_open so.darn.loop0; simp [nock_exec, tackN, Pi.editUp]
  | cons e rest ih =>
    intro don
    obtain ⟨n, p⟩ := e
    by_cases hn : n = 2
    · subst hn
      nock_open so.darn.loop0
      simp [nock_exec, tackN, hk, pi_cons_arm, pi_cons_gate, Pi.editUp]
      exact ih _
    · have hn' : ¬ (2 = n) := fun h => hn h.symm
      have hup : Pi.editUp don ((n, p) :: rest) = Pi.editUp (Pi.cons p don) rest := by
        rcases n with _ | _ | _ | n
        · rfl
        · rfl
        · exact absurd rfl hn
        · rfl
      nock_open so.darn.loop0
      simp [nock_exec, tackN, hk, pi_cons_arm, pi_cons_gate, hn', hup]
      exact ih _

/-- The loop of `edit` on its way down, on an axis of at least `1`. -/
theorem pi_edit_down (c : Noun) (hc : PiEditIn c) : ∀ (ax : Nat), 1 ≤ ax →
    ∀ (rec don : Noun) (tack : List (Nat × Noun)),
    nock (C pi.edit.loop1 (C (tackN tack) (C pi.edit.battery (C (C rec (C (A ax) don)) c))))
        pi.edit.loop1
      = some (Pi.editDown rec ax don tack) := by
  obtain ⟨hcons, hhed, htel, hsl⟩ := hc
  have hpeg : PiPegIn c := by
    obtain ⟨bat, lib, rfl, _, hp⟩ := hsl.elim
    exact hp
  obtain ⟨bat, lib, rfl, ⟨l1, hl, ⟨hcap, hdiv⟩, ⟨hmas, hadd, hmod, hmul, hdiv'⟩⟩, _⟩ := hsl.elim
  intro ax
  induction ax using Nat.strongRecOn with
  | ind ax ih =>
    intro h1 rec don tack
    nock_open pi.edit.loop1
    by_cases a1 : ax = 1
    · subst a1
      rw [Pi.editDown.eq_def]
      simp [nock_exec, pi_edit_up _ hcons rec (A 1) tack don]
    have h2 : 2 ≤ ax := by omega
    have hne : ¬ (1 = ax) := fun h => a1 h.symm
    have hcap' := Hoon.cap_gate l1 hdiv ax h2
    have hmas' := Hoon.mas_gate l1 ⟨hadd, hmod, hmul, hdiv'⟩ ax h2
    rw [capF_eq_cap] at hcap'
    rw [masF_eq_mas] at hmas'
    have ih' := ih (SkaModel.mas ax) (SkaModel.mas_lt ax h2) (SkaModel.mas_pos ax h2)
    have hlt : ¬ ax < 2 := by omega
    rw [Pi.editDown.eq_def, if_neg a1, dif_neg hlt]
    rcases cap_cases ax h2 with hc2 | hc3
    · simp [nock_exec, hne, hl, hcap, hmas, Hoon.cap_arm, Hoon.mas_arm, hcap', hmas', hc2,
        hhed, htel, pi_hed_arm, pi_tel_arm, pi_hed_gate _ hpeg, pi_tel_gate _ hpeg]
      exact ih' _ _ ((2, Pi.tel rec) :: tack)
    · simp [nock_exec, hne, hl, hcap, hmas, Hoon.cap_arm, Hoon.mas_arm, hcap', hmas', hc3,
        hhed, htel, pi_hed_arm, pi_tel_arm, pi_hed_gate _ hpeg, pi_tel_gate _ hpeg]
      exact ih' _ _ ((3, Pi.hed rec) :: tack)

/-- Slamming `edit` of `+pi` on a provenance `rec`, an axis of at least `1`
and a provenance `don`. -/
theorem pi_edit_gate (c : Noun) (hc : PiEditIn c) (rec : Noun) (ax : Nat) (hax : 1 ≤ ax)
    (don : Noun) :
    nock (C pi.edit.battery (C (C rec (C (A ax) don)) c)) pi.edit.battery
      = some (Pi.edit rec ax don) := by
  nock_open pi.edit.battery
  by_cases a1 : ax = 1
  · subst a1; simp [nock_exec, Pi.edit]
  have hne : ¬ (ax = 1) := a1
  have hdown := pi_edit_down c hc ax hax rec don []
  by_cases hz : rec = A 0 ∧ don = A 0
  · obtain ⟨rfl, rfl⟩ := hz
    simp [nock_exec, Pi.edit, hne]
  · have hz' : ¬ (A 0 = rec ∧ A 0 = don) := fun ⟨a, b⟩ => hz ⟨a.symm, b.symm⟩
    by_cases hr : A 0 = rec
    · subst hr
      have hd : ¬ (A 0 = don) := fun h => hz' ⟨rfl, h⟩
      simp [nock_exec, Pi.edit, hne, hd, Ne.symm hd, tackN] at hdown ⊢
      exact hdown
    · simp [nock_exec, Pi.edit, hne, hr, Ne.symm hr, tackN] at hdown ⊢
      exact hdown

/-! ## `+distribute` and `prune` of `+pi` -/

/-- The library core gives the core of `+ca` with `pat` and `uni`, and what
they read. -/
abbrev CaPatUniOf (lib : Noun) : Prop :=
  ∃ f k, slot? ca.lib.axis lib = some f ∧ nock lib f = some k ∧
    slot? ca.pat.axis k = some ca.pat.arm ∧ slot? ca.uni.axis k = some ca.uni.arm ∧
    AxisIn k ∧ CaConIn k

@[nock_exec] theorem distribute_arm (c : Noun) :
    nock c distribute.arm = some (C distribute.battery (C (C (A 1) (A 0)) c)) := by
  nock_open distribute.arm; simp only [nock_exec]

/-- Slamming `+distribute` on a cape and a provenance, in a context (the
library core) that gives `pat` and `uni` of `+ca`. -/
theorem distribute_gate (lib : Noun) (hc : CaPatUniOf lib) : ∀ (s : Noun) (c : Cape),
    nock (C distribute.battery (C (C c.toNoun s) lib)) distribute.battery
      = some (distribute c s).toNoun := by
  obtain ⟨f, k, hf, hk, hpat, huni, hax, hcon⟩ := hc
  intro s
  induction s with
  | atom a =>
    intro c
    nock_open distribute.battery
    rcases a with _ | a
    · simp [nock_exec, distribute, Cape.toNoun]
    · rcases c with _ | _ | ⟨p, q⟩
      · have hp := ca_pat_gate k hax Cape.yes (a + 1)
        simp only [Cape.toNoun] at hp
        simp [nock_exec, distribute, Cape.toNoun, hf, hk, hpat, ca_pat_arm, hp, Ca.pat]
      · simp [nock_exec, distribute, Cape.toNoun]
      · have hp := ca_pat_gate k hax (Cape.cell p q) (a + 1)
        simp only [Cape.toNoun] at hp
        simp [nock_exec, distribute, Cape.toNoun, hf, hk, hpat, ca_pat_arm, hp, Ca.pat]
  | cell sh st ih it =>
    intro c
    nock_open distribute.battery
    rcases c with _ | _ | ⟨p, q⟩
    · have h1 := ih Cape.yes
      have h2 := it Cape.yes
      simp only [Cape.toNoun] at h1 h2
      simp [nock_exec, distribute, Cape.toNoun, hf, hk, huni, ca_uni_arm, h1, h2,
        ca_uni_gate k hcon]
    · simp [nock_exec, distribute, Cape.toNoun]
    · have hne : ¬ (Cape.cell p q = Cape.no) := by simp
      have h1 := ih p
      have h2 := it q
      simp [nock_exec, distribute, hne, Cape.toNoun, hf, hk, huni, ca_uni_arm, h1, h2,
        ca_uni_gate k hcon]

/-- What `prune` of `+pi` reads from its context, the core of `+pi`: `pat` and
`uni` of `+ca` through the library core. -/
abbrev PiPruneIn (c : Noun) : Prop := Hoon.Below CaPatUniOf c

@[nock_exec] theorem pi_prune_arm (c : Noun) :
    nock c pi.prune.arm = some (C pi.prune.battery (C (C (A 0) (A 1)) c)) := by
  nock_open pi.prune.arm; simp only [nock_exec]

/-- Slamming `prune` of `+pi` on a provenance and a cape: `+distribute` with
the arguments swapped. -/
theorem pi_prune_gate (c : Noun) (hc : PiPruneIn c) : ∀ (pin : Noun) (cap : Cape),
    nock (C pi.prune.battery (C (C pin cap.toNoun) c)) pi.prune.battery
      = some (distribute cap pin).toNoun := by
  obtain ⟨bat, lib, rfl, f, k, hf, hk, hpat, huni, hax, hcon⟩ := hc.elim
  intro pin
  induction pin with
  | atom a =>
    intro cap
    nock_open pi.prune.battery
    rcases cap with _ | _ | ⟨p, q⟩
    · rcases a with _ | a
      · simp [nock_exec, distribute, Cape.toNoun]
      · have hp := ca_pat_gate k hax Cape.yes (a + 1)
        simp only [Cape.toNoun] at hp
        simp [nock_exec, distribute, Cape.toNoun, hf, hk, hpat, ca_pat_arm, hp, Ca.pat]
    · rcases a with _ | a <;> simp [nock_exec, distribute, Cape.toNoun]
    · rcases a with _ | a
      · simp [nock_exec, distribute, Cape.toNoun]
      · have hp := ca_pat_gate k hax (Cape.cell p q) (a + 1)
        simp only [Cape.toNoun] at hp
        simp [nock_exec, distribute, Cape.toNoun, hf, hk, hpat, ca_pat_arm, hp, Ca.pat]
  | cell sh st ih it =>
    intro cap
    nock_open pi.prune.battery
    rcases cap with _ | _ | ⟨p, q⟩
    · have h1 := ih Cape.yes
      have h2 := it Cape.yes
      simp only [Cape.toNoun] at h1 h2
      simp [nock_exec, distribute, Cape.toNoun, hf, hk, huni, ca_uni_arm, h1, h2,
        ca_uni_gate k hcon]
    · simp [nock_exec, distribute, Cape.toNoun]
    · have hne : ¬ (Cape.cell p q = Cape.no) := by simp
      have h1 := ih p
      have h2 := it q
      simp [nock_exec, distribute, hne, Cape.toNoun, hf, hk, huni, ca_uni_arm, h1, h2,
        ca_uni_gate k hcon]

/-! ## `+double-int` -/

/-- The library core gives the core of `+pi` with `hed`, `tel`, `cons`, and
`+peg` below it. -/
abbrev PiOf (lib : Noun) : Prop :=
  ∃ f k, slot? pi.lib.axis lib = some f ∧ nock lib f = some k ∧
    slot? pi.hed.axis k = some pi.hed.arm ∧ slot? pi.tel.axis k = some pi.tel.arm ∧
    slot? pi.cons.axis k = some pi.cons.arm ∧ PiPegIn k

/-- What `+double-int` reads from its context, the library core: `hed`, `tel`,
`knit` of `+so` and `hed`, `tel`, `cons` of `+pi`. -/
abbrev DoubleIntOf (lib : Noun) : Prop := SoOf lib ∧ PiOf lib

@[nock_exec] theorem double_int_arm (c : Noun) :
    nock c double_int.arm
      = some (C double_int.battery
          (C (C (C (C (A 1) (A 0)) (A 0)) (C (C (A 1) (A 0)) (A 0))) c)) := by
  nock_open double_int.arm; simp only [nock_exec]

theorem anno_toNoun_ne {a b : Anno} (h : a ≠ b) : ¬ (a.toNoun = b.toNoun) := by
  intro e
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  simp only [Anno.toNoun, Noun.cell.injEq] at e
  exact h (by rw [sock_toNoun_inj e.1, e.2])

/-! The encodings on constructors, for `simp`: unfolding `Sock.toNoun` itself
would also open it on `So.hed s` into a `match`. -/
theorem anno_mk_toNoun (s : Sock) (r : Noun) : (Anno.mk s r).toNoun = C s.toNoun r := rfl
theorem sock_mk_toNoun (c : Cape) (d : Noun) : (Sock.mk c d).toNoun = C c.toNoun d := rfl
theorem sock_void_toNoun : Sock.void.toNoun = A Tag.void := rfl
theorem cape_yes_toNoun : Cape.yes.toNoun = A 0 := rfl
theorem cape_no_toNoun : Cape.no.toNoun = A 1 := rfl
theorem cape_cell_toNoun (p q : Cape) : (Cape.cell p q).toNoun = C p.toNoun q.toNoun := rfl
theorem anno_dunno_toNoun : Anno.dunno.toNoun = C (C (A 1) (A 0)) (A 0) := rfl

/-- Slamming `+double-int` on two sock-annotated nouns, by induction on the
measure of the model. -/
theorem double_int_gate (lib : Noun) (hc : DoubleIntOf lib) : ∀ (n : Nat) (a b : Anno),
    Sock.msr a.sock + Sock.msr b.sock < n →
    nock (C double_int.battery (C (C a.toNoun b.toNoun) lib)) double_int.battery
      = some (doubleInt a b).toNoun := by
  obtain ⟨⟨f, k, hf, hk, hknit, hshed, hstel, hkc⟩, ⟨g, p, hg, hp, hphed, hptel, hpcons, hpeg⟩⟩ := hc
  intro n
  induction n with
  | zero => intro a b h; omega
  | succ n ih =>
    intro a b hlt
    by_cases hab : a = b
    · subst hab
      nock_open double_int.battery
      simp [nock_exec, doubleInt_self]
    have hne := anno_toNoun_ne hab
    obtain ⟨sa, ra⟩ := a
    obtain ⟨sb, rb⟩ := b
    cases sa with
    | void =>
      rw [doubleInt_void_left rfl hab]
      nock_open double_int.battery
      simp only [anno_mk_toNoun, sock_void_toNoun, Noun.cell.injEq] at hne
      simp [nock_exec, anno_mk_toNoun, sock_void_toNoun, hne]
    | mk ca da =>
    cases sb with
    | void =>
      rw [doubleInt_void_right rfl (by simp) hab]
      nock_open double_int.battery
      simp only [anno_mk_toNoun, sock_void_toNoun, sock_mk_toNoun, Noun.cell.injEq] at hne
      simp [nock_exec, anno_mk_toNoun, sock_void_toNoun, sock_mk_toNoun, hne]
    | mk cb db =>
    rw [doubleInt_mk hab]
    by_cases hno : ca = Cape.no ∨ cb = Cape.no
    · rw [if_pos hno]
      nock_open double_int.battery
      rcases ca with _ | _ | ⟨_, _⟩ <;> rcases cb with _ | _ | ⟨_, _⟩ <;>
        simp only [reduceCtorEq, or_false, false_or, or_true, true_or] at hno <;>
        simp only [anno_mk_toNoun, sock_mk_toNoun, cape_yes_toNoun, cape_no_toNoun,
          cape_cell_toNoun, Noun.cell.injEq, Noun.atom.injEq, true_and] at hne <;>
        simp [nock_exec, anno_mk_toNoun, sock_mk_toNoun, cape_yes_toNoun, cape_no_toNoun,
          cape_cell_toNoun, anno_dunno_toNoun, hne]
    rw [if_neg hno]
    simp only [not_or] at hno
    obtain ⟨hca, hcb⟩ := hno
    simp only at hlt
    have hh := ih ⟨So.hed (Sock.mk ca da), Pi.hed ra⟩ ⟨So.hed (Sock.mk cb db), Pi.hed rb⟩ (by
      have := msr_hed_lt hca da; have := msr_hed_lt hcb db; simp only; omega)
    have ht := ih ⟨So.tel (Sock.mk ca da), Pi.tel ra⟩ ⟨So.tel (Sock.mk cb db), Pi.tel rb⟩ (by
      have := msr_tel_lt hca da; have := msr_tel_lt hcb db; simp only; omega)
    simp only [anno_mk_toNoun] at hh ht
    have h1 : nock (C so.hed.battery (C (C ca.toNoun da) k)) so.hed.battery
        = some (So.hed (Sock.mk ca da)).toNoun := so_hed_gate k (Sock.mk ca da)
    have h2 : nock (C so.hed.battery (C (C cb.toNoun db) k)) so.hed.battery
        = some (So.hed (Sock.mk cb db)).toNoun := so_hed_gate k (Sock.mk cb db)
    have h3 : nock (C so.tel.battery (C (C ca.toNoun da) k)) so.tel.battery
        = some (So.tel (Sock.mk ca da)).toNoun := so_tel_gate k (Sock.mk ca da)
    have h4 : nock (C so.tel.battery (C (C cb.toNoun db) k)) so.tel.battery
        = some (So.tel (Sock.mk cb db)).toNoun := so_tel_gate k (Sock.mk cb db)
    nock_open double_int.battery
    rcases ca with _ | _ | ⟨_, _⟩ <;> rcases cb with _ | _ | ⟨_, _⟩ <;>
      simp only [ne_eq, not_true_eq_false, reduceCtorEq, not_false_eq_true] at hca hcb <;>
      rcases ra with _ | ⟨_, _⟩ <;> rcases rb with _ | ⟨_, _⟩ <;>
      simp only [cape_yes_toNoun, cape_cell_toNoun] at h1 h2 h3 h4 <;>
      simp only [anno_mk_toNoun, sock_mk_toNoun, cape_yes_toNoun, cape_cell_toNoun,
        Noun.cell.injEq, Noun.atom.injEq, true_and] at hne <;>
      simp [nock_exec, anno_mk_toNoun, sock_mk_toNoun, cape_yes_toNoun, cape_cell_toNoun,
        anno_dunno_toNoun, hne, Cape.isCellB, isCellN, hf, hk, hknit, hshed, hstel, hg, hp, hphed,
        hptel, hpcons, so_hed_arm, so_tel_arm, so_knit_arm, pi_hed_arm, pi_tel_arm, pi_cons_arm,
        h1, h2, h3, h4, pi_hed_gate p hpeg, pi_tel_gate p hpeg, hh, ht, so_knit_gate k hkc,
        pi_cons_gate]

/-- Slamming `+double-int` on two sock-annotated nouns. -/
theorem double_int_gate' (lib : Noun) (hc : DoubleIntOf lib) (a b : Anno) :
    nock (C double_int.battery (C (C a.toNoun b.toNoun) lib)) double_int.battery
      = some (doubleInt a b).toNoun :=
  double_int_gate lib hc _ a b (Nat.lt_succ_self _)

/-! ## On the pill -/

theorem caPatUniOf_lib : CaPatUniOf lib :=
  ⟨ca.lib.arm, C ca.battery lib, ca.lib.arm_at, ca_lib_arm, ca.pat.arm_at lib, ca.uni.arm_at lib,
    caIn_pill.2.2.2.1, caIn_pill.1⟩

theorem piOf_lib : PiOf lib :=
  ⟨pi.lib.arm, C pi.battery lib, pi.lib.arm_at, pi_lib_arm, pi.hed.arm_at lib, pi.tel.arm_at lib,
    pi.cons.arm_at lib, Hoon.Below.cell pegOf_lib⟩

theorem pi_edit_pill (rec : Noun) (ax : Nat) (hax : 1 ≤ ax) (don : Noun) :
    nock (C pi.edit.battery (C (C rec (C (A ax) don)) (C pi.battery lib))) pi.edit.battery
      = some (Pi.edit rec ax don) :=
  pi_edit_gate _ ⟨pi.cons.arm_at lib, pi.hed.arm_at lib, pi.tel.arm_at lib,
    Hoon.Below.cell ⟨axisOf_lib, pegOf_lib⟩⟩ rec ax hax don

theorem pi_prune_pill (pin : Noun) (cap : Cape) :
    nock (C pi.prune.battery (C (C pin cap.toNoun) (C pi.battery lib))) pi.prune.battery
      = some (distribute cap pin).toNoun :=
  pi_prune_gate _ (Hoon.Below.cell caPatUniOf_lib) pin cap

theorem distribute_pill (c : Cape) (s : Noun) :
    nock (C distribute.battery (C (C c.toNoun s) lib)) distribute.battery
      = some (distribute c s).toNoun :=
  distribute_gate lib caPatUniOf_lib s c

theorem double_int_pill (a b : Anno) :
    nock (C double_int.battery (C (C a.toNoun b.toNoun) lib)) double_int.battery
      = some (doubleInt a b).toNoun :=
  double_int_gate' lib ⟨soOf_lib, piOf_lib⟩ a b

end Compiler
end Formalization
