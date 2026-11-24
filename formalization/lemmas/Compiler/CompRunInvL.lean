import lemmas.Compiler.CompClaGen
import lemmas.Compiler.CompIntoGen
import lemmas.Compiler.CompFromGen
import lemmas.Compiler.CompCopyGen
import lemmas.Compiler.CompRunAll

/-!
# The invariant of lazy goals with forks and bonds

The links of the helpers of `+run` on every lazy need (`CompSplitGen.lean`,
`CompIntoGen.lean`, `CompFromGen.lean`, `CompMedeGen.lean`,
`CompKernGen.lean`, `CompClaGen.lean`, `CompCopyGen.lean`) take, besides
the context, these facts of the lazy need:

* no sure need in it looks at axis `0` (`WalkP lok0`), for `+split`,
  `+into`, `+from`, and with every visited block not a key of `soft`
  (`WalkP mdP`), for `+mede`, `+kern`, `+collapse-lazy-atom`: with an
  empty `soft` (`GenRest.NoSoft`) the second is the first (`walk_mdP`);
* for `+copy`: the two needs need no merge (`NoMerge`), and their sure needs
  are below the counter and apart (`cnLt`, `cnMeet`).

`LAll Q laz`: every sure need of `laz` meets `Q` (forks and bonds to any
depth).  Here: `LAll` of the looks (`CrLok`) and of the registers below the
counter (`NB`) is kept by `+lazy-prune`, `+split`, `+into` (the looks),
`+from` and `+past` on every lazy need (`lall_prune`, `split_lall`,
`into_lok`, `from_lall`, `past_lall`), and `CrInvL` gathers the facts of a
goal: the looks, the mode, the registers below the counter, the root need
distinct.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- Every sure need of `laz` (forks and bonds to any depth) meets `Q`. -/
abbrev LAll (Q : Sure CSet → Prop) (laz : Lazy CSet) : Prop := WalkP (fun _ s => Q s) 0 laz

theorem walkP_irrel (Q : Sure CSet → Prop) (o o' : Nat) (laz : Lazy CSet) :
    WalkP (fun _ s => Q s) o laz = WalkP (fun _ s => Q s) o' laz := by
  cases laz; rfl

section
variable {P P' : Nat → Sure CSet → Prop}

mutual
theorem walkP_mono (h : ∀ o s, P o s → P' o s) : ∀ (o : Nat) (laz : Lazy CSet),
    WalkP P o laz → WalkP P' o laz
  | o, Lazy.mk s fk bd, ⟨hs, hf, hb⟩ => ⟨h o s hs, walkPF_mono h fk hf, walkPB_mono h bd hb⟩

theorem walkPF_mono (h : ∀ o s, P o s → P' o s) : ∀ (fk : List (Lazy.ForkE CSet)),
    WalkPF P fk → WalkPF P' fk
  | [], _ => trivial
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩ =>
    ⟨walkP_mono h oy y hy, walkP_mono h on n hn, walkPF_mono h rest hr⟩

theorem walkPB_mono (h : ∀ o s, P o s → P' o s) : ∀ (bd : List (Nat × Lazy CSet)),
    WalkPB P bd → WalkPB P' bd
  | [], _ => trivial
  | (ob, l) :: rest, ⟨hl, hr⟩ => ⟨walkP_mono h ob l hl, walkPB_mono h rest hr⟩
end

end

theorem lall_mono {Q Q' : Sure CSet → Prop} (h : ∀ s, Q s → Q' s) {laz : Lazy CSet} (hl : LAll Q laz) :
    LAll Q' laz :=
  walkP_mono (fun _ s hs => h s hs) 0 laz hl

/-- `WalkP lok0` is `LAll CrLok`, from any block. -/
theorem walkP_lok0_lall (o : Nat) (laz : Lazy CSet) : WalkP lok0 o laz ↔ LAll CrLok laz := by
  cases laz; exact Iff.rfl

/-- With an empty `soft`, the hypothesis of the walks is the looks'. -/
theorem walk_mdP {x : GenRest} (hx : x.NoSoft) (o : Nat) {laz : Lazy CSet} (hl : LAll CrLok laz) :
    WalkP (mdP x) o laz := by
  have h1 : WalkP (fun _ s => CrLok s) o laz := by rw [walkP_irrel]; exact hl
  exact walkP_mono (fun o s hs => ⟨hx o, hs⟩) o laz h1

/-- The same over the forks and the bonds of a lazy need. -/
theorem walk_mdP_parts {x : GenRest} (hx : x.NoSoft) {s : Sure CSet} {fk : List (Lazy.ForkE CSet)}
    {bd : List (Nat × Lazy CSet)} (hl : LAll CrLok (Lazy.mk s fk bd)) :
    WalkPF (mdP x) fk ∧ WalkPB (mdP x) bd := by
  have := walk_mdP hx 0 hl
  exact ⟨this.2.1, this.2.2⟩


/-! ## `+lazy-prune` -/

theorem walkPF_filter {P : Nat → Sure CSet → Prop} (p : Lazy.ForkE CSet → Bool) :
    ∀ fk : List (Lazy.ForkE CSet), WalkPF P fk → WalkPF P (fk.filter p)
  | [], _ => trivial
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩ => by
    rw [List.filter_cons]
    split
    · exact ⟨hy, hn, walkPF_filter p rest hr⟩
    · exact walkPF_filter p rest hr

theorem walkPB_filter {P : Nat → Sure CSet → Prop} (p : Nat × Lazy CSet → Bool) :
    ∀ bd : List (Nat × Lazy CSet), WalkPB P bd → WalkPB P (bd.filter p)
  | [], _ => trivial
  | (ob, l) :: rest, ⟨hl, hr⟩ => by
    rw [List.filter_cons]
    split
    · exact ⟨hl, walkPB_filter p rest hr⟩
    · exact walkPB_filter p rest hr

/-- `+lazy-prune` keeps `WalkP`. -/
theorem walkP_prune {P : Nat → Sure CSet → Prop} (o : Nat) (laz : Lazy CSet) (h : WalkP P o laz) :
    WalkP P o (Lazy.lazyPrune laz) := by
  obtain ⟨s, fk, bd⟩ := laz
  exact ⟨h.1, walkPF_filter _ fk h.2.1, walkPB_filter _ bd h.2.2⟩

/-! ## `+split` -/

/-- The looks and the registers below the counter `k`. -/
def LNB (k : Nat) (s : Sure CSet) : Prop := CrLok s ∧ NB k s.ned

theorem lnb_mono {k k' : Nat} (hk : k ≤ k') {laz : Lazy CSet} (o : Nat)
    (h : WalkP (fun _ s => LNB k s) o laz) : WalkP (fun _ s => LNB k' s) o laz :=
  walkP_mono (fun _ s hs => ⟨hs.1, hs.2.mono hk⟩) o laz h

theorem walkPF_lnb_mono {k k' : Nat} (hk : k ≤ k') {fk : List (Lazy.ForkE CSet)}
    (h : WalkPF (fun _ s => LNB k s) fk) : WalkPF (fun _ s => LNB k' s) fk :=
  walkPF_mono (fun _ s hs => ⟨hs.1, hs.2.mono hk⟩) fk h

theorem walkPB_lnb_mono {k k' : Nat} (hk : k ≤ k') {bd : List (Nat × Lazy CSet)}
    (h : WalkPB (fun _ s => LNB k s) bd) : WalkPB (fun _ s => LNB k' s) bd :=
  walkPB_mono (fun _ s hs => ⟨hs.1, hs.2.mono hk⟩) bd h

/-- `+split-sure` keeps the looks and the registers below the counter. -/
theorem splitSure_lnb {s sh st : Sure CSet} {o : Nat} {g g' : Gen (TreapMap mugF)}
    (hs : LNB g.re s) (h : splitSure s o g = some ((sh, st), g')) :
    Keeps g g' ∧ LNB g'.re sh ∧ LNB g'.re st := by
  simp only [splitSure] at h
  obtain ⟨⟨lh, lt⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  obtain ⟨k, n1, n2⟩ := keeps_splitNeed hs.2 h3
  obtain ⟨l1, l2⟩ := splitLok_ne0 hl
  exact ⟨k, ⟨l1, n1⟩, ⟨l2, n2⟩⟩

mutual
/-- **`+split` keeps the looks and the registers below the counter** on
every lazy need: both halves, at the counter it returns. -/
theorem split_lnb : ∀ (laz : Lazy CSet) (o o' : Nat) (g g' : Gen (TreapMap mugF)) (h t : Lazy CSet),
    WalkP (fun _ s => LNB g.re s) o' laz → Lazy.splitLoop laz o g = some ((h, t), g') →
    Keeps g g' ∧ WalkP (fun _ s => LNB g'.re s) o' h ∧ WalkP (fun _ s => LNB g'.re s) o' t
  | Lazy.mk s fk bd, o, o', g, g', h, t, ⟨hs, hf, hb⟩, e => by
    simp only [Lazy.splitLoop] at e
    obtain ⟨⟨sh, st⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨k1, lh, lt⟩ := splitSure_lnb hs e1
    split at e
    · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      exact ⟨k1, ⟨lh, trivial, trivial⟩, ⟨lt, trivial, trivial⟩⟩
    · obtain ⟨⟨fh, ft⟩, g2, e2, e⟩ := bind_some e
      obtain ⟨k2, fh', ft'⟩ := split_forks_lnb fk g1 g2 fh ft (walkPF_lnb_mono k1.le hf) e2
      obtain ⟨⟨bh, bt⟩, g3, e3, e⟩ := bind_some e
      obtain ⟨k3, bh', bt'⟩ := split_bonds_lnb bd g2 g3 bh bt (walkPB_lnb_mono (k1.trans k2).le hb) e3
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      have k23 := (k2.trans k3).le
      refine ⟨k1.trans (k2.trans k3), walkP_prune o' _ ⟨⟨lh.1, lh.2.mono k23⟩, walkPF_lnb_mono k3.le fh', bh'⟩,
        walkP_prune o' _ ⟨⟨lt.1, lt.2.mono k23⟩, walkPF_lnb_mono k3.le ft', bt'⟩⟩

theorem split_forks_lnb : ∀ (fk : List (Lazy.ForkE CSet)) (g g' : Gen (TreapMap mugF))
    (fh ft : List (Lazy.ForkE CSet)),
    WalkPF (fun _ s => LNB g.re s) fk → Lazy.splitForks fk g = some ((fh, ft), g') →
    Keeps g g' ∧ WalkPF (fun _ s => LNB g'.re s) fh ∧ WalkPF (fun _ s => LNB g'.re s) ft
  | [], g, g', fh, ft, _, e => by
    simp only [Lazy.splitForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨Keeps.refl _, trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, g, g', fh, ft, ⟨hy, hn, hr⟩, e => by
    simp only [Lazy.splitForks] at e
    obtain ⟨⟨yh, yt⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨k1, yh', yt'⟩ := split_lnb y oy oy g g1 yh yt hy e1
    obtain ⟨⟨nh, nt⟩, g2, e2, e⟩ := bind_some e
    obtain ⟨k2, nh', nt'⟩ := split_lnb n on on g1 g2 nh nt (lnb_mono k1.le on hn) e2
    obtain ⟨⟨rh, rt⟩, g3, e3, e⟩ := bind_some e
    obtain ⟨k3, rh', rt'⟩ := split_forks_lnb rest g2 g3 rh rt (walkPF_lnb_mono (k1.trans k2).le hr) e3
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨k1.trans (k2.trans k3),
      ⟨lnb_mono (k2.trans k3).le oy yh', lnb_mono k3.le on nh', rh'⟩,
      ⟨lnb_mono (k2.trans k3).le oy yt', lnb_mono k3.le on nt', rt'⟩⟩

theorem split_bonds_lnb : ∀ (bd : List (Nat × Lazy CSet)) (g g' : Gen (TreapMap mugF))
    (bh bt : List (Nat × Lazy CSet)),
    WalkPB (fun _ s => LNB g.re s) bd → Lazy.splitBonds bd g = some ((bh, bt), g') →
    Keeps g g' ∧ WalkPB (fun _ s => LNB g'.re s) bh ∧ WalkPB (fun _ s => LNB g'.re s) bt
  | [], g, g', bh, bt, _, e => by
    simp only [Lazy.splitBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨Keeps.refl _, trivial, trivial⟩
  | (ob, l) :: rest, g, g', bh, bt, ⟨hl, hr⟩, e => by
    simp only [Lazy.splitBonds] at e
    obtain ⟨⟨lh, lt⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨k1, lh', lt'⟩ := split_lnb l ob ob g g1 lh lt hl e1
    obtain ⟨⟨rh, rt⟩, g2, e2, e⟩ := bind_some e
    obtain ⟨k2, rh', rt'⟩ := split_bonds_lnb rest g1 g2 rh rt (walkPB_lnb_mono k1.le hr) e2
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨k1.trans k2, ⟨lnb_mono k2.le ob lh', rh'⟩, ⟨lnb_mono k2.le ob lt', rt'⟩⟩
end

/-! ## `+into` -/

/-- `+into-sure` keeps the looks and the registers below the counter. -/
theorem intoSure_lnb {axe : Nat} (ha : axe ≠ 0) {s sd sr : Sure CSet} {o : Nat} {g g' : Gen (TreapMap mugF)}
    (hs : LNB g.re s) (h : intoSure axe s o g = some ((sd, sr), g')) :
    Keeps g g' ∧ LNB g'.re sd ∧ LNB g'.re sr := by
  simp only [intoSure] at h
  obtain ⟨⟨ld, lr⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  obtain ⟨l1, l2⟩ := cra_intoLok hl
  have hlr : CrLok (⟨nr, if axe = 1 then lr else HoonSet.put lr axe⟩ : Sure CSet) := by
    intro y hy
    split at hy
    · exact l2 y hy
    · rcases (HoonSet.mem_put lr axe y).1 hy with e | e
      · rw [e]; exact ha
      · exact l2 y e
  simp only [intoNeed] at h3
  rw [if_neg ha] at h3
  by_cases a1 : axe = 1
  · rw [if_pos a1] at h3
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
    exact ⟨Keeps.refl _, ⟨l1, hs.2⟩, ⟨hlr, nb_none _⟩⟩
  rw [if_neg a1] at h3
  obtain ⟨k3, n1, n2⟩ := keeps_intoLoop _ _ _ _ _ _ _ h3 hs.2 (fun e he => by simp at he) (RegsIn.nil _)
  exact ⟨k3, ⟨l1, n1⟩, ⟨hlr, n2⟩⟩

mutual
/-- **`+into` keeps the looks and the registers below the counter** on
every lazy need: both halves, at the counter it returns. -/
theorem into_lnb (axe : Nat) (ha : axe ≠ 0) : ∀ (laz : Lazy CSet) (o o' : Nat) (g g' : Gen (TreapMap mugF)) (h t : Lazy CSet),
    WalkP (fun _ s => LNB g.re s) o' laz → Lazy.intoLoopL axe laz o g = some ((h, t), g') →
    Keeps g g' ∧ WalkP (fun _ s => LNB g'.re s) o' h ∧ WalkP (fun _ s => LNB g'.re s) o' t
  | Lazy.mk s fk bd, o, o', g, g', h, t, ⟨hs, hf, hb⟩, e => by
    simp only [Lazy.intoLoopL] at e
    obtain ⟨⟨sh, st⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨k1, lh, lt⟩ := intoSure_lnb ha hs e1
    split at e
    · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      exact ⟨k1, ⟨lh, trivial, trivial⟩, ⟨lt, trivial, trivial⟩⟩
    · obtain ⟨⟨fh, ft⟩, g2, e2, e⟩ := bind_some e
      obtain ⟨k2, fh', ft'⟩ := into_forks_lnb axe ha fk g1 g2 fh ft (walkPF_lnb_mono k1.le hf) e2
      obtain ⟨⟨bh, bt⟩, g3, e3, e⟩ := bind_some e
      obtain ⟨k3, bh', bt'⟩ := into_bonds_lnb axe ha bd g2 g3 bh bt (walkPB_lnb_mono (k1.trans k2).le hb) e3
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
      have k23 := (k2.trans k3).le
      refine ⟨k1.trans (k2.trans k3), walkP_prune o' _ ⟨⟨lh.1, lh.2.mono k23⟩, walkPF_lnb_mono k3.le fh', bh'⟩,
        walkP_prune o' _ ⟨⟨lt.1, lt.2.mono k23⟩, walkPF_lnb_mono k3.le ft', bt'⟩⟩

theorem into_forks_lnb (axe : Nat) (ha : axe ≠ 0) : ∀ (fk : List (Lazy.ForkE CSet)) (g g' : Gen (TreapMap mugF))
    (fh ft : List (Lazy.ForkE CSet)),
    WalkPF (fun _ s => LNB g.re s) fk → Lazy.intoForks axe fk g = some ((fh, ft), g') →
    Keeps g g' ∧ WalkPF (fun _ s => LNB g'.re s) fh ∧ WalkPF (fun _ s => LNB g'.re s) ft
  | [], g, g', fh, ft, _, e => by
    simp only [Lazy.intoForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨Keeps.refl _, trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, g, g', fh, ft, ⟨hy, hn, hr⟩, e => by
    simp only [Lazy.intoForks] at e
    obtain ⟨⟨yh, yt⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨k1, yh', yt'⟩ := into_lnb axe ha y oy oy g g1 yh yt hy e1
    obtain ⟨⟨nh, nt⟩, g2, e2, e⟩ := bind_some e
    obtain ⟨k2, nh', nt'⟩ := into_lnb axe ha n on on g1 g2 nh nt (lnb_mono k1.le on hn) e2
    obtain ⟨⟨rh, rt⟩, g3, e3, e⟩ := bind_some e
    obtain ⟨k3, rh', rt'⟩ := into_forks_lnb axe ha rest g2 g3 rh rt (walkPF_lnb_mono (k1.trans k2).le hr) e3
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨k1.trans (k2.trans k3),
      ⟨lnb_mono (k2.trans k3).le oy yh', lnb_mono k3.le on nh', rh'⟩,
      ⟨lnb_mono (k2.trans k3).le oy yt', lnb_mono k3.le on nt', rt'⟩⟩

theorem into_bonds_lnb (axe : Nat) (ha : axe ≠ 0) : ∀ (bd : List (Nat × Lazy CSet)) (g g' : Gen (TreapMap mugF))
    (bh bt : List (Nat × Lazy CSet)),
    WalkPB (fun _ s => LNB g.re s) bd → Lazy.intoBonds axe bd g = some ((bh, bt), g') →
    Keeps g g' ∧ WalkPB (fun _ s => LNB g'.re s) bh ∧ WalkPB (fun _ s => LNB g'.re s) bt
  | [], g, g', bh, bt, _, e => by
    simp only [Lazy.intoBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨Keeps.refl _, trivial, trivial⟩
  | (ob, l) :: rest, g, g', bh, bt, ⟨hl, hr⟩, e => by
    simp only [Lazy.intoBonds] at e
    obtain ⟨⟨lh, lt⟩, g1, e1, e⟩ := bind_some e
    obtain ⟨k1, lh', lt'⟩ := into_lnb axe ha l ob ob g g1 lh lt hl e1
    obtain ⟨⟨rh, rt⟩, g2, e2, e⟩ := bind_some e
    obtain ⟨k2, rh', rt'⟩ := into_bonds_lnb axe ha rest g1 g2 rh rt (walkPB_lnb_mono k1.le hr) e2
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
    exact ⟨k1.trans k2, ⟨lnb_mono k2.le ob lh', rh'⟩, ⟨lnb_mono k2.le ob lt', rt'⟩⟩
end

/-! ## `+from` -/

theorem fromSure_lnb {axe k : Nat} {s s' : Sure CSet} (hs : LNB k s) (h : fromSure axe s = some s') : LNB k s' :=
  ⟨fromSure_lok_ne0 h hs.1, fun r hr => hs.2 r ((fromSure_spec (Map := TreapMap mugF) h).2.2.2 r hr)⟩

mutual
/-- **`+from` keeps the looks and the registers below a bound** on every
lazy need. -/
theorem from_lnb (axe k : Nat) : ∀ (laz laz' : Lazy CSet) (o : Nat),
    WalkP (fun _ s => LNB k s) o laz → Lazy.fromL axe laz = some laz' → WalkP (fun _ s => LNB k s) o laz'
  | Lazy.mk s fk bd, laz', o, ⟨hs, hf, hb⟩, e => by
    simp only [Lazy.fromL] at e
    split at e
    · obtain ⟨s', e1, rfl⟩ := Option.map_eq_some_iff.mp e
      exact ⟨fromSure_lnb hs e1, trivial, trivial⟩
    · obtain ⟨s', e1, e⟩ := Option.bind_eq_some_iff.mp e
      obtain ⟨f', e2, e⟩ := Option.bind_eq_some_iff.mp e
      obtain ⟨b', e3, rfl⟩ := Option.map_eq_some_iff.mp e
      exact ⟨fromSure_lnb hs e1, from_forks_lnb axe k fk f' hf e2, from_bonds_lnb axe k bd b' hb e3⟩

theorem from_forks_lnb (axe k : Nat) : ∀ (fk fk' : List (Lazy.ForkE CSet)),
    WalkPF (fun _ s => LNB k s) fk → Lazy.fromForks axe fk = some fk' → WalkPF (fun _ s => LNB k s) fk'
  | [], fk', _, e => by simp only [Lazy.fromForks, Option.some.injEq] at e; subst e; trivial
  | ((oy, y), (on, n)) :: rest, fk', ⟨hy, hn, hr⟩, e => by
    simp only [Lazy.fromForks] at e
    obtain ⟨y', e1, e⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨n', e2, e⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨r', e3, rfl⟩ := Option.map_eq_some_iff.mp e
    exact ⟨from_lnb axe k y y' oy hy e1, from_lnb axe k n n' on hn e2, from_forks_lnb axe k rest r' hr e3⟩

theorem from_bonds_lnb (axe k : Nat) : ∀ (bd bd' : List (Nat × Lazy CSet)),
    WalkPB (fun _ s => LNB k s) bd → Lazy.fromBonds axe bd = some bd' → WalkPB (fun _ s => LNB k s) bd'
  | [], bd', _, e => by simp only [Lazy.fromBonds, Option.some.injEq] at e; subst e; trivial
  | (ob, l) :: rest, bd', ⟨hl, hr⟩, e => by
    simp only [Lazy.fromBonds] at e
    obtain ⟨l', e1, e⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨r', e2, rfl⟩ := Option.map_eq_some_iff.mp e
    exact ⟨from_lnb axe k l l' ob hl e1, from_bonds_lnb axe k rest r' hr e2⟩
end

/-! ## `+past` -/

/-- **`+past` keeps the looks and the registers below the counter**: the
need parked in a bond is the old one with its bonds moved up, and the new
sure need is the bunt. -/
theorem past_lnb {cod : Bell → Option Bool} {nex nex' : NextL CSet} {nom : Nomm} {region : List Nat}
    {g g' : Gen (TreapMap mugF)} (o : Nat) (hn : WalkP (fun _ s => LNB g.re s) o nex.laz)
    (h : pastL cod nex nom region g = some (nex', g')) :
    g.re = g'.re ∧ WalkP (fun _ s => LNB g'.re s) o nex'.laz := by
  obtain ⟨⟨s, fk, bd⟩, th⟩ := nex
  obtain ⟨hs, hf, hb⟩ := hn
  simp only [pastL] at h
  split at h
  · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hs, hf, hb⟩
  · rcases hh : hinted cod nom with _ | _ | _
    · simp [hh] at h
    · simp only [hh, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hs, hf, hb⟩
    · simp only [hh] at h
      obtain ⟨o1, g1, e1, h⟩ := bind_some h
      obtain ⟨u, g2, e2, h⟩ := bind_some h
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have r1 : g1.re = g.re := by
        rw [emit_apply] at e1; simp at e1; rw [← e1.2]; unfold Gen.emitted; split <;> rfl
      have r2 : g2.re = g1.re := by
        simp only [setTag, Option.some.injEq, Prod.mk.injEq] at e2
        rw [← e2.2]; split <;> rfl
      rw [r2, r1]
      exact ⟨rfl, ⟨cra_lok_bunt, nb_none _⟩, trivial, ⟨⟨hs, hf, trivial⟩, hb⟩⟩

/-! ## The invariant -/

/-- **The invariant of a lazy goal and a state** (`CrInv` for goals with
forks and bonds): the mode is `%run`; for `%next`, every sure need of the
goal's lazy need (forks and bonds to any depth) looks at no axis `0` and has
its registers below the counter, the jump's arguments are below the counter,
and the root need has no register twice; for `%pick`, both jumps are below
the counter. -/
def CrInvL (g : Gen (TreapMap mugF)) : CGoalL CSet → Prop
  | CGoalL.next laz th => LAll (LNB g.re) laz ∧ g.drop = false ∧ JmpIn (· < g.re) th ∧ Distinct laz.sure.ned
  | CGoalL.pick z o => g.drop = false ∧ JmpIn (· < g.re) z ∧ JmpIn (· < g.re) o
  | CGoalL.done => g.drop = false

/-- On a fork-free goal, `CrInv` gives `CrInvL`. -/
theorem crInvL_of_crInv {g : Gen (TreapMap mugF)} {gl : CGoal CSet} (h : CrInv g gl) :
    CrInvL g (CGoal.toL gl) := by
  obtain ⟨hl, hd, hi, hD⟩ := h
  cases gl with
  | next laz th => exact ⟨⟨⟨hl, hi.1⟩, trivial, trivial⟩, hd, hi.2, hD⟩
  | pick z o => exact ⟨hd, hi.1, hi.2⟩
  | done => exact hd

/-- What `+split`, `+into` and `+from` take of a goal with the invariant. -/
theorem crInvL_lok {g : Gen (TreapMap mugF)} {laz : Lazy CSet} {th : Jmp} (h : CrInvL g (CGoalL.next laz th))
    (o : Nat) : WalkP lok0 o laz :=
  (walkP_lok0_lall o laz).2 (lall_mono (fun _ hs => hs.1) h.1)

/-- What `+mede`, `+kern` and `+collapse-lazy-atom` take of a goal with the
invariant, with an empty `soft`. -/
theorem crInvL_mdP {g : Gen (TreapMap mugF)} {laz : Lazy CSet} {th : Jmp} (h : CrInvL g (CGoalL.next laz th))
    {x : GenRest} (hx : x.NoSoft) (o : Nat) : WalkP (mdP x) o laz :=
  walk_mdP hx o (lall_mono (fun _ hs => hs.1) h.1)

/-- **`+split` keeps the invariant**: both halves of a goal with the
invariant have their looks and registers below the counter it returns, and
the mode stays `%run`. -/
theorem crInvL_split {g g' : Gen (TreapMap mugF)} {laz h t : Lazy CSet} {th : Jmp} {o : Nat}
    (hi : CrInvL g (CGoalL.next laz th)) (e : splitL ⟨laz, th⟩ g = some ((h, t, o), g')) :
    g.re ≤ g'.re ∧ g'.drop = false ∧ LAll (LNB g'.re) h ∧ LAll (LNB g'.re) t := by
  obtain ⟨hl, hd, hj, -⟩ := hi
  simp only [splitL] at e
  obtain ⟨o1, g1, e1, e⟩ := bind_some e
  obtain ⟨k1, r1⟩ := keeps_emit hd (blobIn_fin (f := Termin.hop th) hj) e1
  obtain ⟨⟨h', t'⟩, g2, e2, e⟩ := bind_some e
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e
  have hl1 : WalkP (fun _ s => LNB g1.re s) 0 laz := by rw [r1]; exact hl
  obtain ⟨k2, hh, ht⟩ := split_lnb laz o1 0 g1 g2 h' t' hl1 e2
  exact ⟨(k1.trans k2).le, (k1.trans k2).dropF hd, hh, ht⟩

/-- **`+into` keeps the invariant**, for an axis not `0`. -/
theorem crInvL_into {g g' : Gen (TreapMap mugF)} {laz d r : Lazy CSet} {th : Jmp} {o axe : Nat} (ha : axe ≠ 0)
    (hi : CrInvL g (CGoalL.next laz th)) (e : intoL ⟨laz, th⟩ axe g = some ((d, r, o), g')) :
    g.re ≤ g'.re ∧ g'.drop = false ∧ LAll (LNB g'.re) d ∧ LAll (LNB g'.re) r := by
  obtain ⟨hl, hd, hj, -⟩ := hi
  simp only [intoL] at e
  obtain ⟨o1, g1, e1, e⟩ := bind_some e
  obtain ⟨k1, r1⟩ := keeps_emit hd (blobIn_fin (f := Termin.hop th) hj) e1
  obtain ⟨⟨d', r'⟩, g2, e2, e⟩ := bind_some e
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e
  have hl1 : WalkP (fun _ s => LNB g1.re s) 0 laz := by rw [r1]; exact hl
  obtain ⟨k2, hh, ht⟩ := into_lnb axe ha laz o1 0 g1 g2 d' r' hl1 e2
  exact ⟨(k1.trans k2).le, (k1.trans k2).dropF hd, hh, ht⟩

/-- **`+from` keeps the invariant's lazy part.** -/
theorem crInvL_from {k axe : Nat} {laz laz' : Lazy CSet} (hl : LAll (LNB k) laz)
    (e : Lazy.fromL axe laz = some laz') : LAll (LNB k) laz' :=
  from_lnb axe k laz laz' 0 hl e

end Compiler
end Formalization
