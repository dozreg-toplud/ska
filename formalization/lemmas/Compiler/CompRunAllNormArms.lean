import lemmas.Compiler.CompShapeColFuel
import lemmas.Compiler.CompCopyAll
import lemmas.Ska.CompClean

/-!
# The arms of `+run` keep every sure need `Clean`

`Clean` (`Ska/CompSem.lean`): no subterm `[%pair [%none ~] [%none ~]]`.
`Ska/CompClean.lean` proves it kept by the helpers on one sure need
(`+cons-need`, `+from-sure`, `+split-need`, `+must`, `+into-need`'s loop,
`+copy-need-make-ops`).  Here the lazy versions, on every sure need of a
lazy need, forks and bonds to any depth (`LAll CleanS`):

* `lc_split`, `lc_into`, `lc_from`, `lc_past`, `lc_copy` (with the merge of
  forks and bonds), `lc_copyL`, `lc_copyAll`;
* `lc_fork` (`+fork`: the needs of `+fork-need` have the shape of the old
  one, `NCopy`), `lc_forkL`;
* `lc_sect`, `lc_pastFork`, `lc_lazyShut`;
* `lc_leap` (`+leap`: `+need-cut` rebuilds through `+cons-need`,
  `+need-from` wraps a need that is not `none`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- A sure need with no `[%pair [%none ~] [%none ~]]`. -/
abbrev CleanS (s : Sure CSet) : Prop := Clean s.ned

/-- `Clean` is `ordNormal` of the shape. -/
theorem ordNormal_of_clean : ∀ n : Need, Clean n → ordNormal (needToOrd n) = true
  | Need.none, _ => rfl
  | Need.this _, _ => rfl
  | Need.pair p q, ⟨hn, hp, hq⟩ => by
    have ip := ordNormal_of_clean p hp
    have iq := ordNormal_of_clean q hq
    cases p <;> cases q <;> simp_all [needToOrd, ordNormal]
  | Need.both _ h t, ⟨hh, ht⟩ => by
    simp [needToOrd, ordNormal, ordNormal_of_clean h hh, ordNormal_of_clean t ht]

theorem lc_ofSure {s : Sure CSet} (h : CleanS s) (o : Nat) : WalkP (fun _ s => CleanS s) o (Lazy.ofSure s) :=
  ⟨h, trivial, trivial⟩

theorem lc_bunt (o : Nat) : WalkP (fun _ s => CleanS s) o (Lazy.ofSure (Sure.bunt : Sure CSet)) :=
  ⟨trivial, trivial, trivial⟩

theorem lc_reg (r o : Nat) : WalkP (fun _ s => CleanS s) o (Lazy.ofSure (lazyReg r : Sure CSet)) :=
  ⟨trivial, trivial, trivial⟩

/-! ## `+split` -/

theorem cs_splitSure {s sh st : Sure CSet} {o : Nat} {g g' : Gen (TreapMap mugF)}
    (h : splitSure s o g = some ((sh, st), g')) (hc : CleanS s) : CleanS sh ∧ CleanS st := by
  simp only [splitSure] at h
  obtain ⟨⟨lh, lt⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  exact clean_splitNeed h3 hc

mutual
theorem lc_split : ∀ (laz : Lazy CSet) (o : Nat) (g g' : Gen (TreapMap mugF)) (h t : Lazy CSet),
    LAll CleanS laz → Lazy.splitLoop laz o g = some ((h, t), g') → LAll CleanS h ∧ LAll CleanS t
  | Lazy.mk s fk bd, o, g, g', h, t, ⟨hs, hf, hb⟩, e => by
    simp only [Lazy.splitLoop] at e
    obtain ⟨⟨sh, st⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨lh, lt⟩ := cs_splitSure e1 hs
    split at e
    · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      exact ⟨⟨lh, trivial, trivial⟩, ⟨lt, trivial, trivial⟩⟩
    · obtain ⟨⟨fh, ft⟩, g2, e2, e⟩ := bind_some e
      obtain ⟨fh', ft'⟩ := lc_splitF fk g1 g2 fh ft hf e2
      obtain ⟨⟨bh, bt⟩, g3, e3, e⟩ := bind_some e
      obtain ⟨bh', bt'⟩ := lc_splitB bd g2 g3 bh bt hb e3
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      exact ⟨walkP_prune 0 _ ⟨lh, fh', bh'⟩, walkP_prune 0 _ ⟨lt, ft', bt'⟩⟩

theorem lc_splitF : ∀ (fk : List (Lazy.ForkE CSet)) (g g' : Gen (TreapMap mugF)) (fh ft : List (Lazy.ForkE CSet)),
    WalkPF (fun _ s => CleanS s) fk → Lazy.splitForks fk g = some ((fh, ft), g') →
    WalkPF (fun _ s => CleanS s) fh ∧ WalkPF (fun _ s => CleanS s) ft
  | [], g, g', fh, ft, _, e => by
    simp only [Lazy.splitForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, g, g', fh, ft, ⟨hy, hn, hr⟩, e => by
    simp only [Lazy.splitForks] at e
    obtain ⟨⟨yh, yt⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨yh', yt'⟩ := lc_split y oy g g1 yh yt (lall_of_walkP hy) e1
    obtain ⟨⟨nh, nt⟩, g2, e2, e⟩ := bind_some e
    obtain ⟨nh', nt'⟩ := lc_split n on g1 g2 nh nt (lall_of_walkP hn) e2
    obtain ⟨⟨rh, rt⟩, g3, e3, e⟩ := bind_some e
    obtain ⟨rh', rt'⟩ := lc_splitF rest g2 g3 rh rt hr e3
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨⟨walkP_of_lall oy yh', walkP_of_lall on nh', rh'⟩, ⟨walkP_of_lall oy yt', walkP_of_lall on nt', rt'⟩⟩

theorem lc_splitB : ∀ (bd : List (Nat × Lazy CSet)) (g g' : Gen (TreapMap mugF)) (bh bt : List (Nat × Lazy CSet)),
    WalkPB (fun _ s => CleanS s) bd → Lazy.splitBonds bd g = some ((bh, bt), g') →
    WalkPB (fun _ s => CleanS s) bh ∧ WalkPB (fun _ s => CleanS s) bt
  | [], g, g', bh, bt, _, e => by
    simp only [Lazy.splitBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨trivial, trivial⟩
  | (ob, l) :: rest, g, g', bh, bt, ⟨hl, hr⟩, e => by
    simp only [Lazy.splitBonds] at e
    obtain ⟨⟨lh, lt⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨lh', lt'⟩ := lc_split l ob g g1 lh lt (lall_of_walkP hl) e1
    obtain ⟨⟨rh, rt⟩, g2, e2, e⟩ := bind_some e
    obtain ⟨rh', rt'⟩ := lc_splitB rest g1 g2 rh rt hr e2
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨⟨walkP_of_lall ob lh', rh'⟩, ⟨walkP_of_lall ob lt', rt'⟩⟩
end

theorem lc_splitL {nex : NextL CSet} {g g' : Gen (TreapMap mugF)} {h t : Lazy CSet} {o : Nat}
    (hc : LAll CleanS nex.laz) (e : splitL nex g = some ((h, t, o), g')) : LAll CleanS h ∧ LAll CleanS t := by
  simp only [splitL] at e
  obtain ⟨o1, g1, e1, e⟩ := bind_some e
  obtain ⟨⟨h', t'⟩, g2, e2, e⟩ := bind_some e
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e
  exact lc_split _ _ _ _ _ _ hc e2

/-! ## `+into` -/

theorem cs_intoSure {axe : Nat} {s sd sr : Sure CSet} {o : Nat} {g g' : Gen (TreapMap mugF)}
    (h : intoSure axe s o g = some ((sd, sr), g')) (hc : CleanS s) : CleanS sd ∧ CleanS sr := by
  simp only [intoSure] at h
  obtain ⟨⟨ld, lr⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  simp only [intoNeed] at h3
  by_cases a0 : axe = 0
  · simp [a0] at h3
  rw [if_neg a0] at h3
  by_cases a1 : axe = 1
  · rw [if_pos a1] at h3
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
    exact ⟨hc, trivial⟩
  rw [if_neg a1] at h3
  exact clean_intoLoop _ _ _ _ _ _ _ h3 hc (fun e he => by simp at he)

mutual
theorem lc_into (axe : Nat) : ∀ (laz : Lazy CSet) (o : Nat) (g g' : Gen (TreapMap mugF)) (h t : Lazy CSet),
    LAll CleanS laz → Lazy.intoLoopL axe laz o g = some ((h, t), g') → LAll CleanS h ∧ LAll CleanS t
  | Lazy.mk s fk bd, o, g, g', h, t, ⟨hs, hf, hb⟩, e => by
    simp only [Lazy.intoLoopL] at e
    obtain ⟨⟨sh, st⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨lh, lt⟩ := cs_intoSure e1 hs
    split at e
    · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      exact ⟨⟨lh, trivial, trivial⟩, ⟨lt, trivial, trivial⟩⟩
    · obtain ⟨⟨fh, ft⟩, g2, e2, e⟩ := bind_some e
      obtain ⟨fh', ft'⟩ := lc_intoF axe fk g1 g2 fh ft hf e2
      obtain ⟨⟨bh, bt⟩, g3, e3, e⟩ := bind_some e
      obtain ⟨bh', bt'⟩ := lc_intoB axe bd g2 g3 bh bt hb e3
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      exact ⟨walkP_prune 0 _ ⟨lh, fh', bh'⟩, walkP_prune 0 _ ⟨lt, ft', bt'⟩⟩

theorem lc_intoF (axe : Nat) : ∀ (fk : List (Lazy.ForkE CSet)) (g g' : Gen (TreapMap mugF))
    (fh ft : List (Lazy.ForkE CSet)),
    WalkPF (fun _ s => CleanS s) fk → Lazy.intoForks axe fk g = some ((fh, ft), g') →
    WalkPF (fun _ s => CleanS s) fh ∧ WalkPF (fun _ s => CleanS s) ft
  | [], g, g', fh, ft, _, e => by
    simp only [Lazy.intoForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, g, g', fh, ft, ⟨hy, hn, hr⟩, e => by
    simp only [Lazy.intoForks] at e
    obtain ⟨⟨yh, yt⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨yh', yt'⟩ := lc_into axe y oy g g1 yh yt (lall_of_walkP hy) e1
    obtain ⟨⟨nh, nt⟩, g2, e2, e⟩ := bind_some e
    obtain ⟨nh', nt'⟩ := lc_into axe n on g1 g2 nh nt (lall_of_walkP hn) e2
    obtain ⟨⟨rh, rt⟩, g3, e3, e⟩ := bind_some e
    obtain ⟨rh', rt'⟩ := lc_intoF axe rest g2 g3 rh rt hr e3
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨⟨walkP_of_lall oy yh', walkP_of_lall on nh', rh'⟩, ⟨walkP_of_lall oy yt', walkP_of_lall on nt', rt'⟩⟩

theorem lc_intoB (axe : Nat) : ∀ (bd : List (Nat × Lazy CSet)) (g g' : Gen (TreapMap mugF))
    (bh bt : List (Nat × Lazy CSet)),
    WalkPB (fun _ s => CleanS s) bd → Lazy.intoBonds axe bd g = some ((bh, bt), g') →
    WalkPB (fun _ s => CleanS s) bh ∧ WalkPB (fun _ s => CleanS s) bt
  | [], g, g', bh, bt, _, e => by
    simp only [Lazy.intoBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨trivial, trivial⟩
  | (ob, l) :: rest, g, g', bh, bt, ⟨hl, hr⟩, e => by
    simp only [Lazy.intoBonds] at e
    obtain ⟨⟨lh, lt⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨lh', lt'⟩ := lc_into axe l ob g g1 lh lt (lall_of_walkP hl) e1
    obtain ⟨⟨rh, rt⟩, g2, e2, e⟩ := bind_some e
    obtain ⟨rh', rt'⟩ := lc_intoB axe rest g1 g2 rh rt hr e2
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨⟨walkP_of_lall ob lh', rh'⟩, ⟨walkP_of_lall ob lt', rt'⟩⟩
end

theorem lc_intoL {nex : NextL CSet} {axe : Nat} {g g' : Gen (TreapMap mugF)} {d r : Lazy CSet} {o : Nat}
    (hc : LAll CleanS nex.laz) (e : intoL nex axe g = some ((d, r, o), g')) : LAll CleanS d ∧ LAll CleanS r := by
  simp only [intoL] at e
  obtain ⟨o1, g1, e1, e⟩ := bind_some e
  obtain ⟨⟨d', r'⟩, g2, e2, e⟩ := bind_some e
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e
  exact lc_into axe _ _ _ _ _ _ hc e2

/-! ## `+from` -/

mutual
theorem lc_from (axe : Nat) : ∀ (laz laz' : Lazy CSet),
    LAll CleanS laz → Lazy.fromL axe laz = some laz' → LAll CleanS laz'
  | Lazy.mk s fk bd, laz', ⟨hs, hf, hb⟩, e => by
    simp only [Lazy.fromL] at e
    split at e
    · obtain ⟨s', e1, rfl⟩ := Option.map_eq_some_iff.mp e
      exact ⟨clean_fromSure e1 hs, trivial, trivial⟩
    · obtain ⟨s', e1, e⟩ := Option.bind_eq_some_iff.mp e
      obtain ⟨f', e2, e⟩ := Option.bind_eq_some_iff.mp e
      obtain ⟨b', e3, rfl⟩ := Option.map_eq_some_iff.mp e
      exact ⟨clean_fromSure e1 hs, lc_fromF axe fk f' hf e2, lc_fromB axe bd b' hb e3⟩

theorem lc_fromF (axe : Nat) : ∀ (fk fk' : List (Lazy.ForkE CSet)),
    WalkPF (fun _ s => CleanS s) fk → Lazy.fromForks axe fk = some fk' → WalkPF (fun _ s => CleanS s) fk'
  | [], fk', _, e => by simp only [Lazy.fromForks, Option.some.injEq] at e; subst e; trivial
  | ((oy, y), (on, n)) :: rest, fk', ⟨hy, hn, hr⟩, e => by
    simp only [Lazy.fromForks] at e
    obtain ⟨y', e1, e⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨n', e2, e⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨r', e3, rfl⟩ := Option.map_eq_some_iff.mp e
    exact ⟨walkP_of_lall oy (lc_from axe y y' (lall_of_walkP hy) e1),
      walkP_of_lall on (lc_from axe n n' (lall_of_walkP hn) e2), lc_fromF axe rest r' hr e3⟩

theorem lc_fromB (axe : Nat) : ∀ (bd bd' : List (Nat × Lazy CSet)),
    WalkPB (fun _ s => CleanS s) bd → Lazy.fromBonds axe bd = some bd' → WalkPB (fun _ s => CleanS s) bd'
  | [], bd', _, e => by simp only [Lazy.fromBonds, Option.some.injEq] at e; subst e; trivial
  | (ob, l) :: rest, bd', ⟨hl, hr⟩, e => by
    simp only [Lazy.fromBonds] at e
    obtain ⟨l', e1, e⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨r', e2, rfl⟩ := Option.map_eq_some_iff.mp e
    exact ⟨walkP_of_lall ob (lc_from axe l l' (lall_of_walkP hl) e1), lc_fromB axe rest r' hr e2⟩
end

/-! ## `+past`, `+simple-next`, `+bomb` -/

theorem lc_past {cod : Bell → Option Bool} {nex nex' : NextL CSet} {nom : Nomm} {region : List Nat}
    {g g' : Gen (TreapMap mugF)} (hn : LAll CleanS nex.laz)
    (h : pastL cod nex nom region g = some (nex', g')) : LAll CleanS nex'.laz := by
  obtain ⟨⟨s, fk, bd⟩, th⟩ := nex
  obtain ⟨hs, hf, hb⟩ := hn
  simp only [pastL] at h
  split at h
  · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs, hf, hb⟩
  · rcases hh : hinted cod nom with _ | _ | _
    · simp [hh] at h
    · simp only [hh, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hs, hf, hb⟩
    · simp only [hh] at h
      obtain ⟨o1, g1, e1, h⟩ := bind_some h
      obtain ⟨u, g2, e2, h⟩ := bind_some h
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨trivial, trivial, ⟨⟨hs, hf, trivial⟩, hb⟩⟩

theorem lc_simpleNext {goal : CGoalL CSet} {g g' : Gen (TreapMap mugF)} {nex : NextL CSet}
    (hg : ∀ laz th, goal = CGoalL.next laz th → LAll CleanS laz)
    (h : simpleNextL goal g = some (nex, g')) : LAll CleanS nex.laz := by
  cases goal with
  | next laz th =>
    simp only [simpleNextL, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hg laz th rfl
  | done =>
    simp only [simpleNextL] at h
    obtain ⟨r, g5, h5, h⟩ := bind_some h
    obtain ⟨o, g6, h6, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact lc_reg _ 0
  | pick z o =>
    simp only [simpleNextL] at h
    obtain ⟨r, g5, h5, h⟩ := bind_some h
    obtain ⟨o', g6, h6, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact lc_reg _ 0

theorem lc_bombL {miss : Option Nat} {g g' : Gen (TreapMap mugF)} {nex : NextL CSet}
    (h : bombL miss g = some (nex, g')) : LAll CleanS nex.laz := by
  simp only [bombL] at h
  obtain ⟨o, g1, e1, h⟩ := bind_some h
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact lc_bunt 0

/-! ## `+copy` -/

theorem cs_copyNeed {a b : Need} {ops : List Pole} {g g' : Gen (TreapMap mugF)} {x : Need × List Pole}
    (h : copyNeed a b ops g = some (x, g')) (ha : Clean a) (hb : Clean b) : Clean x.1 :=
  clean_copyNeed _ _ _ _ _ _ h ha hb

mutual
theorem lc_copy : ∀ (f : Lazy CSet) (o : Nat) (s : Lazy CSet) (g g' : Gen (TreapMap mugF)) (r : Lazy CSet),
    LAll CleanS f → LAll CleanS s → Lazy.copyLazyL o f s g = some (r, g') → LAll CleanS r
  | Lazy.mk sf ff bf, o, Lazy.mk ss fs bs, g, g', r, ⟨hsf, hff, hbf⟩, ⟨hss, hfs, hbs⟩, h => by
    rw [copyLazyL_eq] at h
    obtain ⟨⟨ned, ops⟩, g1, e1, h⟩ := bind_some h
    have hroot := cs_copyNeed e1 hsf hss
    obtain ⟨u, g2, e2, h⟩ := bind_some h
    obtain ⟨fk, g3, e3, h⟩ := bind_some h
    obtain ⟨bd, g4, e4, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hfk : WalkPF (fun _ s => CleanS s) fk := by
      unfold forkPart at e3
      split at e3
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
        obtain ⟨rfl, rfl⟩ := e3; exact hff
      · split at e3
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
          obtain ⟨rfl, rfl⟩ := e3; exact hfs
        · obtain ⟨m, g5, e5, e3⟩ := bind_some e3
          simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
          obtain ⟨rfl, rfl⟩ := e3
          have hm := lc_mforks ff fs g2 g5 m (fun v hv => walkPF_mem fs hfs v hv) hff e5
          exact walkPF_append _ _ hm (walkPF_filter _ fs hfs)
    have hbd : WalkPB (fun _ s => CleanS s) bd := by
      unfold bondPart at e4
      split at e4
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e4
        obtain ⟨rfl, rfl⟩ := e4; exact hbf
      · split at e4
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e4
          obtain ⟨rfl, rfl⟩ := e4; exact hbs
        · obtain ⟨m, g5, e5, e4⟩ := bind_some e4
          simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e4
          obtain ⟨rfl, rfl⟩ := e4
          have hm := lc_mbonds bf bs g3 g5 m (fun v hv => walkPB_mem bs hbs v hv) hbf e5
          exact walkPB_append _ _ hm (walkPB_filter _ bs hbs)
    exact ⟨hroot, hfk, hbd⟩

theorem lc_mforks : ∀ (ff fs : List (Lazy.ForkE CSet)) (g g' : Gen (TreapMap mugF)) (r : List (Lazy.ForkE CSet)),
    (∀ v ∈ fs, LAll CleanS v.1.2 ∧ LAll CleanS v.2.2) → WalkPF (fun _ s => CleanS s) ff →
    Lazy.mergeForks (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs) ff g
      = some (r, g') → WalkPF (fun _ s => CleanS s) r
  | [], fs, g, g', r, _, _, h => by
    simp only [Lazy.mergeForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; trivial
  | ((oy, y), (on, n)) :: rest, fs, g, g', r, hfs, ⟨hy, hn, hr⟩, h => by
    simp only [Lazy.mergeForks] at h
    obtain ⟨e', g1, e1, h⟩ := bind_some h
    obtain ⟨r', g2, e2, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases hg : (HoonMap.get (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs) oy
        : Option (Lazy.ForkE CSet)) with
    | none =>
      simp only [hg, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      exact ⟨hy, hn, lc_mforks rest fs g g2 r' hfs hr e2⟩
    | some v =>
      obtain ⟨⟨oy', my⟩, ⟨mon, mn⟩⟩ := v
      have hv := hfs _ (index_mem' _ _ _ _ hg)
      simp only [hg] at e1
      split at e1
      · obtain ⟨y', g3, e3, e1⟩ := bind_some e1
        obtain ⟨n', g4, e4, e1⟩ := bind_some e1
        simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        have hy' := lc_copy y oy my g g3 y' (lall_of_walkP hy) hv.1 e3
        have hn' := lc_copy n on mn g3 g4 n' (lall_of_walkP hn) hv.2 e4
        exact ⟨walkP_of_lall oy hy', walkP_of_lall on hn', lc_mforks rest fs g4 g2 r' hfs hr e2⟩
      · cases e1

theorem lc_mbonds : ∀ (bf bs : List (Nat × Lazy CSet)) (g g' : Gen (TreapMap mugF)) (r : List (Nat × Lazy CSet)),
    (∀ v ∈ bs, LAll CleanS v.2) → WalkPB (fun _ s => CleanS s) bf →
    Lazy.mergeBonds (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs) bf g
      = some (r, g') → WalkPB (fun _ s => CleanS s) r
  | [], bs, g, g', r, _, _, h => by
    simp only [Lazy.mergeBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; trivial
  | (ob, l) :: rest, bs, g, g', r, hbs, ⟨hl, hr⟩, h => by
    simp only [Lazy.mergeBonds] at h
    obtain ⟨e', g1, e1, h⟩ := bind_some h
    obtain ⟨r', g2, e2, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases hg : (HoonMap.get (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs) ob
        : Option (Nat × Lazy CSet)) with
    | none =>
      simp only [hg, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      exact ⟨hl, lc_mbonds rest bs g g2 r' hbs hr e2⟩
    | some v =>
      obtain ⟨ob', m⟩ := v
      have hv := hbs _ (index_mem' _ _ _ _ hg)
      simp only [hg] at e1
      obtain ⟨l', g3, e3, e1⟩ := bind_some e1
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      exact ⟨walkP_of_lall ob (lc_copy l ob m g g3 l' (lall_of_walkP hl) hv e3), lc_mbonds rest bs g3 g2 r' hbs hr e2⟩
end

theorem lc_copyL {first : NextL CSet} {second : Lazy CSet} {g g' : Gen (TreapMap mugF)} {nex : NextL CSet}
    (hf : LAll CleanS first.laz) (hs : LAll CleanS second) (h : copyL first second g = some (nex, g')) :
    LAll CleanS nex.laz := by
  simp only [copyL] at h
  obtain ⟨o, g1, e1, h⟩ := bind_some h
  obtain ⟨laz, g2, e2, h⟩ := bind_some h
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact lc_copy _ _ _ _ _ _ hf hs e2

theorem lc_copyAll : ∀ (bys : List (Lazy CSet)) (nex : NextL CSet) (g g' : Gen (TreapMap mugF)) (nex' : NextL CSet),
    LAll CleanS nex.laz → (∀ b ∈ bys, LAll CleanS b) → copyAll nex bys g = some (nex', g') → LAll CleanS nex'.laz
  | [], nex, g, g', nex', hn, _, h => by
    simp only [copyAll, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hn
  | b :: rest, nex, g, g', nex', hn, hb, h => by
    simp only [copyAll] at h
    obtain ⟨n1, g1, e1, h⟩ := bind_some h
    exact lc_copyAll rest n1 g1 g' nex' (lc_copyL hn (hb b List.mem_cons_self) e1)
      (fun x hx => hb x (List.mem_cons_of_mem _ hx)) h

/-! ## `+fork` -/

theorem cs_forkSure {sur s0 s1 : Sure CSet} {o o0 o1 : Nat} {g g' : Gen (TreapMap mugF)}
    (h : forkSure sur o o0 o1 g = some ((s0, s1), g')) (hc : CleanS sur) : CleanS s0 ∧ CleanS s1 := by
  unfold forkSure at h
  obtain ⟨⟨n0, n1⟩, g1, e1, h⟩ := bind_some h
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  unfold forkNeed at e1
  obtain ⟨⟨m0, m1⟩, g2, e2, e1⟩ := bind_some e1
  obtain ⟨_, g3, _, e1⟩ := bind_some e1
  obtain ⟨_, g4, _, e1⟩ := bind_some e1
  obtain ⟨_, g5, _, e1⟩ := bind_some e1
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e1
  obtain ⟨-, c0, c1, -⟩ := forkNeedGo_spec sur.ned g g2 m0 m1 e2
  exact ⟨c0.clean hc, c1.clean hc⟩

mutual
theorem lc_fork (rc : Nat) : ∀ (laz : Lazy CSet) (o o0 o1 : Nat) (g g' : Gen (TreapMap mugF)) (l0 l1 : Lazy CSet),
    LAll CleanS laz → forkLoop rc laz o o0 o1 g = some ((l0, l1), g') → LAll CleanS l0 ∧ LAll CleanS l1
  | Lazy.mk s fk bd, o, o0, o1, g, g', l0, l1, ⟨hs, hf, hb⟩, e => by
    simp only [forkLoop] at e
    obtain ⟨⟨s0, s1⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨c0, c1⟩ := cs_forkSure e1 hs
    obtain ⟨⟨f0, f1⟩, g2, e2, e⟩ := bind_some e
    obtain ⟨hf0, hf1⟩ := lc_forkF rc fk g1 g2 f0 f1 hf e2
    obtain ⟨⟨b0, b1⟩, g3, e3, e⟩ := bind_some e
    obtain ⟨hb0, hb1⟩ := lc_forkB rc bd g2 g3 b0 b1 hb e3
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨⟨c0, hf0, hb0⟩, ⟨c1, hf1, hb1⟩⟩

theorem lc_forkF (rc : Nat) : ∀ (fk : List (Lazy.ForkE CSet)) (g g' : Gen (TreapMap mugF))
    (f0 f1 : List (Lazy.ForkE CSet)),
    WalkPF (fun _ s => CleanS s) fk → forkForks rc fk g = some ((f0, f1), g') →
    WalkPF (fun _ s => CleanS s) f0 ∧ WalkPF (fun _ s => CleanS s) f1
  | [], g, g', f0, f1, _, e => by
    simp only [forkForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, g, g', f0, f1, ⟨hy, hn, hr⟩, e => by
    simp only [forkForks] at e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨⟨ly0, ly1⟩, _, ey, e⟩ := bind_some e
    obtain ⟨⟨ln0, ln1⟩, _, en, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨⟨r0, r1⟩, _, er, e⟩ := bind_some e
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    obtain ⟨y0, y1⟩ := lc_fork rc y _ _ _ _ _ _ _ (lall_of_walkP hy) ey
    obtain ⟨n0, n1⟩ := lc_fork rc n _ _ _ _ _ _ _ (lall_of_walkP hn) en
    obtain ⟨q0, q1⟩ := lc_forkF rc rest _ _ _ _ hr er
    exact ⟨⟨walkP_of_lall _ y0, walkP_of_lall _ n0, q0⟩, ⟨walkP_of_lall _ y1, walkP_of_lall _ n1, q1⟩⟩

theorem lc_forkB (rc : Nat) : ∀ (bd : List (Nat × Lazy CSet)) (g g' : Gen (TreapMap mugF))
    (b0 b1 : List (Nat × Lazy CSet)),
    WalkPB (fun _ s => CleanS s) bd → forkBonds rc bd g = some ((b0, b1), g') →
    WalkPB (fun _ s => CleanS s) b0 ∧ WalkPB (fun _ s => CleanS s) b1
  | [], g, g', b0, b1, _, e => by
    simp only [forkBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨trivial, trivial⟩
  | (ob, lb) :: rest, g, g', b0, b1, ⟨hl, hr⟩, e => by
    simp only [forkBonds] at e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨⟨l0, l1⟩, _, el, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨_, _, _, e⟩ := bind_some e
    obtain ⟨⟨r0, r1⟩, _, er, e⟩ := bind_some e
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    obtain ⟨x0, x1⟩ := lc_fork rc lb _ _ _ _ _ _ _ (lall_of_walkP hl) el
    obtain ⟨q0, q1⟩ := lc_forkB rc rest _ _ _ _ hr er
    exact ⟨⟨walkP_of_lall _ x0, q0⟩, ⟨walkP_of_lall _ x1, q1⟩⟩
end

theorem lc_forkL {nex n0 n1 : NextL CSet} {rc : Nat} {g g' : Gen (TreapMap mugF)}
    (hc : LAll CleanS nex.laz) (e : forkL nex rc g = some ((n0, n1), g')) : LAll CleanS n0.laz ∧ LAll CleanS n1.laz := by
  simp only [forkL] at e
  obtain ⟨_, _, _, e⟩ := bind_some e
  obtain ⟨_, _, _, e⟩ := bind_some e
  split at e
  · cases e
  · obtain ⟨⟨l0, l1⟩, _, e1, e⟩ := bind_some e
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact lc_fork rc _ _ _ _ _ _ _ _ hc e1

theorem cs_forkSure' {sur s0 s1 : Sure CSet} {o o0 o1 : Nat} {g g' : Gen (TreapMap mugF)}
    (hc : CleanS sur) (h : forkSure sur o o0 o1 g = some ((s0, s1), g')) :
    LAll CleanS (Lazy.ofSure s0) ∧ LAll CleanS (Lazy.ofSure s1) :=
  ⟨lc_ofSure (cs_forkSure h hc).1 0, lc_ofSure (cs_forkSure h hc).2 0⟩

/-! ## `+sect`, `+past-fork`, `+lazy-shut` -/

theorem lc_sect {nex0 nex1 : NextL CSet} {o0 o1 : Nat} {rb : List Nat} {cb cw : TreapMap mugF (Nat × List Nat)}
    {g g' : Gen (TreapMap mugF)} {x : Lazy CSet × Nat × Nat}
    (h0 : LAll CleanS nex0.laz) (h1 : LAll CleanS nex1.laz)
    (h : sect nex0 nex1 o0 o1 rb cb cw g = some (x, g')) : LAll CleanS x.1 := by
  rcases rb with _ | ⟨rid, rest⟩
  · cases h
  simp only [sect] at h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, ⟨walkP_of_lall _ h0, walkP_of_lall _ h1, trivial⟩, trivial⟩
  · obtain ⟨_, _, _, h⟩ := bind_some h
    split at h
    · cases h
    split at h
    · cases h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, ⟨walkP_of_lall _ h0, walkP_of_lall _ h1, trivial⟩, trivial⟩

theorem lc_pastFork {cod : Bell → Option Bool} {laz laz' : Lazy CSet} {nom : Nomm}
    (hc : LAll CleanS laz) (h : Lazy.pastFork cod laz nom = some laz') : LAll CleanS laz' := by
  obtain ⟨s, fk, bd⟩ := laz
  obtain ⟨hs, hf, hb⟩ := hc
  simp only [Lazy.pastFork] at h
  rcases hh : hinted cod nom with _ | _ | _
  · simp [hh] at h
  · simp only [hh, Option.some.injEq] at h
    subst h; exact ⟨hs, hf, hb⟩
  · simp only [hh, Option.some.injEq] at h
    subst h
    refine ⟨hs, ?_, hb⟩
    clear hb hh
    induction fk with
    | nil => trivial
    | cons e rest ih =>
      obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
      obtain ⟨hy, hn, hr⟩ := hf
      exact ⟨⟨trivial, trivial, ⟨hy, trivial⟩⟩, ⟨trivial, trivial, ⟨hn, trivial⟩⟩, ih hr⟩

theorem lc_lazyShut {o : Nat} {lz l : Lazy CSet} {g g' : Gen (TreapMap mugF)} (hc : LAll CleanS lz)
    (h : lazyShut o lz g = some (l, g')) : LAll CleanS l := by
  unfold lazyShut at h
  split at h
  · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hc
  · obtain ⟨r, g1, _, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact lc_reg r 0

/-! ## `+leap` -/

theorem clean_needCut : ∀ (n : Need) (axe : Nat) (d r : Need), needCut axe n = some (some (d, r)) →
    Clean n → Clean d ∧ Clean r
  | Need.none, axe, d, r, h, _ => by
    simp only [needCut, ite_self, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨trivial, trivial⟩
  | Need.this x, axe, d, r, h, _ => by
    simp only [needCut] at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨trivial, trivial⟩
    · simp at h
  | Need.both x p q, axe, d, r, h, hc => by
    simp only [needCut] at h; split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hc, trivial⟩
    · simp at h
  | Need.pair p q, axe, d, r, h, hc => by
    simp only [needCut] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hc, trivial⟩
    split at h
    · cases h
    split at h
    · obtain ⟨k, e1, e2⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨⟨d', r'⟩, rfl, e3⟩ := Option.map_eq_some_iff.mp e2
      simp only [Prod.mk.injEq] at e3
      obtain ⟨rfl, rfl⟩ := e3
      obtain ⟨c1, c2⟩ := clean_needCut p _ _ _ e1 hc.2.1
      exact ⟨c1, clean_consNeed c2 hc.2.2⟩
    · obtain ⟨k, e1, e2⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨⟨d', r'⟩, rfl, e3⟩ := Option.map_eq_some_iff.mp e2
      simp only [Prod.mk.injEq] at e3
      obtain ⟨rfl, rfl⟩ := e3
      obtain ⟨c1, c2⟩ := clean_needCut q _ _ _ e1 hc.2.2
      exact ⟨c1, clean_consNeed hc.2.1 c2⟩

theorem clean_needFrom {axe : Nat} {d nf : Need} (h : needFrom axe d = some nf) (hc : Clean d) : Clean nf := by
  unfold needFrom at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact hc
  split at h
  · cases h
  · simp only [Option.some.injEq] at h; subst h
    rename_i hn _
    exact (clean_fromPath hc hn axe).1

mutual
theorem lc_lazyLeap (p s : Nat) : ∀ (laz b r : Lazy CSet), LAll CleanS laz →
    lazyLeap p s laz = some (b, r) → LAll CleanS b ∧ LAll CleanS r
  | Lazy.mk sur fk bd, b, r, ⟨hs, hf, hb⟩, h => by
    simp only [lazyLeap] at h
    obtain ⟨cut, e1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨sb, sr⟩, e2, h⟩ := Option.bind_eq_some_iff.mp h
    have hsr : CleanS sb ∧ CleanS sr := by
      rcases cut with _ | ⟨don, rec⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at e2
        obtain ⟨rfl, rfl⟩ := e2; exact ⟨trivial, hs⟩
      · obtain ⟨⟨lb, lr⟩, -, e3⟩ := Option.bind_eq_some_iff.mp e2
        obtain ⟨nf, e4, e5⟩ := Option.map_eq_some_iff.mp e3
        simp only [Prod.mk.injEq] at e5
        obtain ⟨rfl, rfl⟩ := e5
        obtain ⟨c1, c2⟩ := clean_needCut _ _ _ _ e1 hs
        exact ⟨clean_needFrom e4 c1, c2⟩
    obtain ⟨fs, e6, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, e7, h⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨f1, f2⟩ := lc_leapF p s fk fs hf e6
    obtain ⟨b1, b2⟩ := lc_leapB p s bd bs hb e7
    exact ⟨walkP_prune 0 _ ⟨hsr.1, f1, b1⟩, walkP_prune 0 _ ⟨hsr.2, f2, b2⟩⟩

theorem lc_leapF (p s : Nat) : ∀ (fk : List (Lazy.ForkE CSet))
    (fs : List (((Nat × Lazy CSet) × (Nat × Lazy CSet)) × ((Nat × Lazy CSet) × (Nat × Lazy CSet)))),
    WalkPF (fun _ s => CleanS s) fk → leapForks p s fk = some fs →
    WalkPF (fun _ s => CleanS s) (fs.map Prod.fst) ∧ WalkPF (fun _ s => CleanS s) (fs.map Prod.snd)
  | [], fs, _, h => by
    simp only [leapForks, Option.some.injEq] at h; subst h; exact ⟨trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, fs, ⟨hy, hn, hr⟩, h => by
    simp only [leapForks] at h
    obtain ⟨⟨yb, yr⟩, e1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨nb, nr⟩, e2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rs, e3, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨y1, y2⟩ := lc_lazyLeap p s y yb yr (lall_of_walkP hy) e1
    obtain ⟨n1, n2⟩ := lc_lazyLeap p s n nb nr (lall_of_walkP hn) e2
    obtain ⟨r1, r2⟩ := lc_leapF p s rest rs hr e3
    exact ⟨⟨walkP_of_lall _ y1, walkP_of_lall _ n1, r1⟩, ⟨walkP_of_lall _ y2, walkP_of_lall _ n2, r2⟩⟩

theorem lc_leapB (p s : Nat) : ∀ (bd : List (Nat × Lazy CSet)) (bs : List ((Nat × Lazy CSet) × (Nat × Lazy CSet))),
    WalkPB (fun _ s => CleanS s) bd → leapBonds p s bd = some bs →
    WalkPB (fun _ s => CleanS s) (bs.map Prod.fst) ∧ WalkPB (fun _ s => CleanS s) (bs.map Prod.snd)
  | [], bs, _, h => by
    simp only [leapBonds, Option.some.injEq] at h; subst h; exact ⟨trivial, trivial⟩
  | (o, l) :: rest, bs, ⟨hl, hr⟩, h => by
    simp only [leapBonds] at h
    obtain ⟨⟨b, r⟩, e1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rs, e2, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨l1, l2⟩ := lc_lazyLeap p s l b r (lall_of_walkP hl) e1
    obtain ⟨r1, r2⟩ := lc_leapB p s rest rs hr e2
    exact ⟨⟨walkP_of_lall _ l1, r1⟩, ⟨walkP_of_lall _ l2, r2⟩⟩
end

theorem lc_leapLoop (sur : Sure CSet) (hs : CleanS sur) : ∀ (pas : List (Nat × Nat)) (lab : Lazy CSet)
    (bys : List (Lazy CSet)) (rest : Lazy CSet) (out : List (Lazy CSet)),
    LAll CleanS lab → (∀ b ∈ bys, LAll CleanS b) → leapLoop sur pas lab bys = some (some (rest, out)) →
    LAll CleanS rest ∧ ∀ b ∈ out, LAll CleanS b
  | [], lab, bys, rest, out, hl, hb, h => by
    simp only [leapLoop] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ls, fk, bd⟩ := lab
      exact ⟨⟨hs, hl.2.1, hl.2.2⟩, hb⟩
  | (p, s) :: pas, lab, bys, rest, out, hl, hb, h => by
    simp only [leapLoop] at h
    obtain ⟨⟨b, r⟩, e1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b1, r1⟩ := lc_lazyLeap p s lab b r hl e1
    split at h
    · exact lc_leapLoop sur hs pas lab bys rest out hl hb h
    · exact lc_leapLoop sur hs pas r (b :: bys) rest out r1
        (fun x hx => by rcases List.mem_cons.1 hx with rfl | hx; exact b1; exact hb x hx) h

theorem lc_leap {laz : Lazy CSet} {q r : Nomm} {rest : Lazy CSet} {out : List (Lazy CSet)}
    (hc : LAll CleanS laz) (h : leap laz q r = some (some (rest, out))) :
    LAll CleanS rest ∧ ∀ b ∈ out, LAll CleanS b := by
  unfold leap at h
  split at h
  · cases h
  · obtain ⟨pas, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨s, fk, bd⟩ := laz
    exact lc_leapLoop s hc.1 pas (Lazy.mk Sure.bunt fk bd) [] rest out ⟨trivial, hc.2.1, hc.2.2⟩ (fun _ h => by cases h) h

end Compiler
end Formalization
