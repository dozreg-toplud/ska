import lemmas.Compiler.CompSccOne

/-!
# `+need-ord-alloc-regs` of `sur` succeeds on the fragment

`+need-ord-alloc-regs` crashes on a cell or a `%both` whose two halves are
`%none` (`?<  &(?=(%none -.hed) ?=(%none -.tel))`).  `NN` says a need has no
such node.  It holds of the sure need of every run of the fragment
(`nn_run`): the needs a run builds come from `+simple-next` (`this`), `+bomb`
(`%none`), `+from` (`fromPath`, a non-`%none` need on one side of each cell),
`+split` (halves, and `+must`), `+into` (a half, and `+cons-need`), `+copy`
(`copyNeed`, `%none` only from two `%none`); and `NNo` of the shape follows
through `needToOrd` and `+sure-of` (`sureLook` rebuilds with `consOrd`), on
which `+need-ord-alloc-regs` succeeds (`noar_nno`).  So `hnoar` holds for
`sccSur` (`noar_frag`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The invariant -/

/-- No cell and no `%both` of a need has two `%none` halves. -/
def NN : Need → Prop
  | Need.none => True
  | Need.this _ => True
  | Need.pair p q => NN p ∧ NN q ∧ ¬ (p = Need.none ∧ q = Need.none)
  | Need.both _ h t => NN h ∧ NN t ∧ ¬ (h = Need.none ∧ t = Need.none)

/-- The same of a shape. -/
def NNo : NeedOrd → Prop
  | NeedOrd.none => True
  | NeedOrd.this => True
  | NeedOrd.pair p q => NNo p ∧ NNo q ∧ ¬ (p = NeedOrd.none ∧ q = NeedOrd.none)
  | NeedOrd.both h t => NNo h ∧ NNo t ∧ ¬ (h = NeedOrd.none ∧ t = NeedOrd.none)

theorem nn_consNeed {a b : Need} (ha : NN a) (hb : NN b) : NN (consNeed a b) := by
  unfold consNeed
  split
  · trivial
  · exact ⟨ha, hb, by assumption⟩

theorem needToOrd_none {n : Need} : needToOrd n = NeedOrd.none ↔ n = Need.none := by
  cases n <;> simp [needToOrd]

theorem nno_needToOrd : ∀ {n : Need}, NN n → NNo (needToOrd n)
  | Need.none, _ => trivial
  | Need.this _, _ => trivial
  | Need.pair p q, ⟨hp, hq, hn⟩ => ⟨nno_needToOrd hp, nno_needToOrd hq, by rwa [needToOrd_none, needToOrd_none]⟩
  | Need.both _ h t, ⟨hh, ht, hn⟩ => ⟨nno_needToOrd hh, nno_needToOrd ht, by rwa [needToOrd_none, needToOrd_none]⟩

/-! ## `+sure-of` keeps it -/

theorem nno_consOrd {a b : NeedOrd} (ha : NNo a) (hb : NNo b) : NNo (consOrd a b) := by
  unfold consOrd
  split
  · trivial
  · exact ⟨ha, hb, by assumption⟩

theorem nno_halves : ∀ {o : NeedOrd}, NNo o → NNo (ordHalves o).1 ∧ NNo (ordHalves o).2
  | NeedOrd.none, _ => ⟨trivial, trivial⟩
  | NeedOrd.this, _ => ⟨trivial, trivial⟩
  | NeedOrd.pair _ _, ⟨hp, hq, _⟩ => ⟨hp, hq⟩
  | NeedOrd.both _ _, ⟨hh, ht, _⟩ => ⟨hh, ht⟩

theorem nno_rebuild (new x : NeedOrd) (hx : NNo x) : NNo (ordRebuild new x) := by
  unfold ordRebuild
  split
  · exact hx
  · exact hx
  · split
    · rename_i a b
      obtain ⟨ha, hb, hn⟩ := hx
      exact ⟨ha, hb, hn⟩
    · trivial

theorem nno_sureLook (axe : Nat) : ∀ (new : NeedOrd), NNo new → NNo (sureLook axe new) := by
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro new hn
    rw [sureLook.eq_def]
    split
    · split
      · trivial
      · exact hn
    · rename_i h1
      have hm := mas_lt axe (by omega)
      obtain ⟨h1', h2'⟩ := nno_halves hn
      apply nno_rebuild
      split
      · exact nno_consOrd (ih _ hm _ h1') h2'
      · exact nno_consOrd h1' (ih _ hm _ h2')

theorem nno_sureOf (less : Cape) (lok : CSet) : ∀ (ned : NeedOrd), NNo ned →
    ∀ r, sureOf ned lok less = some r → NNo r := by
  unfold sureOf
  generalize HoonSet.toList lok = L
  induction L with
  | nil => intro ned hn r h; simp [List.foldlM] at h; subst h; exact hn
  | cons y ys ih =>
    intro ned hn r h
    simp only [List.foldlM] at h
    cases e : sureOfStep less ned y with
    | none => simp [e] at h
    | some n' =>
      simp only [e, Option.bind_some] at h
      apply ih n' _ r h
      unfold sureOfStep at e
      split at e
      · simp at e; subst e; exact hn
      · cases e2 : axeInLessCape y less with
        | none => simp [e2] at e
        | some b =>
          simp [e2] at e
          subst e
          split
          · exact hn
          · exact nno_sureLook y ned hn

/-! ## `+need-ord-alloc-regs` succeeds on it -/

theorem noar_nno : ∀ (ord : NeedOrd) (g : Gen (TreapMap mugF)), NNo ord →
    ∃ n g', needOrdAllocRegs ord g = some (n, g') ∧ (n = Need.none ↔ ord = NeedOrd.none)
  | NeedOrd.none, g, _ => ⟨Need.none, g, rfl, by simp⟩
  | NeedOrd.this, g, _ => ⟨_, _, rfl, by simp⟩
  | NeedOrd.pair p q, g, ⟨hp, hq, hn⟩ => by
    obtain ⟨h, g1, e1, eh⟩ := noar_nno p g hp
    obtain ⟨t, g2, e2, et⟩ := noar_nno q g1 hq
    have hn' : ¬ (h = Need.none ∧ t = Need.none) := by rw [eh, et]; exact hn
    refine ⟨Need.pair h t, g2, ?_, by simp⟩
    simp [needOrdAllocRegs, bind, StateT.bind, e1, e2, hn', pure, StateT.pure]
  | NeedOrd.both p q, g, ⟨hp, hq, hn⟩ => by
    obtain ⟨h, g1, e1, eh⟩ := noar_nno p { g with re := g.re + 1 } hp
    obtain ⟨t, g2, e2, et⟩ := noar_nno q g1 hq
    have hn' : ¬ (h = Need.none ∧ t = Need.none) := by rw [eh, et]; exact hn
    refine ⟨Need.both g.re h t, g2, ?_, by simp⟩
    simp [needOrdAllocRegs, bind, StateT.bind, re, e1, e2, hn', pure, StateT.pure]

/-! ## The arms that build needs keep it -/

theorem nn_fromPath (ned : Need) (hn : NN ned) (h0 : ned ≠ Need.none) :
    ∀ axe, NN (fromPath ned axe) ∧ fromPath ned axe ≠ Need.none := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    rw [fromPath.eq_def]
    split
    · exact ⟨hn, h0⟩
    · rename_i h1
      have hm := mas_lt axe (by omega)
      obtain ⟨i1, i2⟩ := ih _ hm
      split
      · exact ⟨⟨i1, trivial, fun ⟨e, _⟩ => i2 e⟩, by simp⟩
      · exact ⟨⟨trivial, i1, fun ⟨_, e⟩ => i2 e⟩, by simp⟩

theorem nn_must {ned : Need} {g g' : Gen (TreapMap mugF)} {r : Nat} {n' : Need}
    (h : must ned g = some ((r, n'), g')) (hn : NN ned) : NN n' := by
  cases ned with
  | none =>
    simp [must, re, bind, StateT.bind, pure, StateT.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h; trivial
  | this x =>
    simp [must, pure, StateT.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h; trivial
  | pair p q =>
    simp [must, re, bind, StateT.bind, pure, StateT.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h; exact hn
  | both x a b =>
    simp [must, pure, StateT.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h; exact hn

theorem nn_splitNeed {ned : Need} {o : Nat} {g g' : Gen (TreapMap mugF)} {nh nt : Need}
    (h : splitNeed ned o g = some ((nh, nt), g')) (hn : NN ned) : NN nh ∧ NN nt := by
  cases ned with
  | none =>
    simp [splitNeed, pure, StateT.pure] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h; exact ⟨trivial, trivial⟩
  | this x =>
    simp only [splitNeed, cra_bind] at h
    obtain ⟨a, g1, -, b, g2, -, u, g3, -, h⟩ := h
    simp [pure, StateT.pure] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h; exact ⟨trivial, trivial⟩
  | pair p q =>
    simp [splitNeed, pure, StateT.pure] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h; exact ⟨hn.1, hn.2.1⟩
  | both x a b =>
    simp only [splitNeed, cra_bind] at h
    obtain ⟨⟨r1, n1⟩, g1, e1, ⟨r2, n2⟩, g2, e2, u, g3, -, h⟩ := h
    simp [pure, StateT.pure] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact ⟨nn_must e1 hn.1, nn_must e2 hn.2.1⟩

theorem nn_copyNeed : ∀ (a b : Need) (ops : List Pole) (g g' : Gen (TreapMap mugF)) (c : Need) (ops' : List Pole),
    copyNeed a b ops g = some ((c, ops'), g') → NN a → NN b → NN c ∧ (c = Need.none → a = Need.none ∧ b = Need.none)
  | Need.none, b, ops, g, g', c, ops', h, ha, hb => by
    simp [copyNeed, pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨hb, fun e => ⟨rfl, e⟩⟩
  | Need.this x, Need.none, ops, g, g', c, ops', h, ha, hb => by
    simp [copyNeed, pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨ha, fun e => by cases e⟩
  | Need.pair p q, Need.none, ops, g, g', c, ops', h, ha, hb => by
    simp [copyNeed, pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨ha, fun e => by cases e⟩
  | Need.both x p q, Need.none, ops, g, g', c, ops', h, ha, hb => by
    simp [copyNeed, pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨ha, fun e => by cases e⟩
  | Need.this x, Need.this y, ops, g, g', c, ops', h, ha, hb => by
    simp [copyNeed, pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨trivial, fun e => by cases e⟩
  | Need.this x, Need.both y p q, ops, g, g', c, ops', h, ha, hb => by
    simp [copyNeed, pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨hb, fun e => by cases e⟩
  | Need.this x, Need.pair p q, ops, g, g', c, ops', h, ha, hb => by
    simp [copyNeed, re, bind, StateT.bind, pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨hb, fun e => by cases e⟩
  | Need.both y p q, Need.this x, ops, g, g', c, ops', h, ha, hb => by
    simp [copyNeed, pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨ha, fun e => by cases e⟩
  | Need.pair p q, Need.this x, ops, g, g', c, ops', h, ha, hb => by
    simp [copyNeed, re, bind, StateT.bind, pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨ha, fun e => by cases e⟩
  | Need.both rl hl tl, Need.both x hr tr, ops, g, g', c, ops', h, ha, hb => by
    simp only [copyNeed, cra_bind] at h
    obtain ⟨⟨a1, o1⟩, g1, e1, ⟨b1, o2⟩, g2, e2, h⟩ := h
    simp [pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    obtain ⟨n1, z1⟩ := nn_copyNeed hl hr _ _ _ _ _ e1 ha.1 hb.1
    obtain ⟨n2, z2⟩ := nn_copyNeed tl tr _ _ _ _ _ e2 ha.2.1 hb.2.1
    exact ⟨⟨n1, n2, fun ⟨c1, c2⟩ => ha.2.2 ⟨(z1 c1).1, (z2 c2).1⟩⟩, fun e => by cases e⟩
  | Need.both rl hl tl, Need.pair p q, ops, g, g', c, ops', h, ha, hb => by
    simp only [copyNeed, cra_bind] at h
    obtain ⟨x, g0, -, ⟨a1, o1⟩, g1, e1, ⟨b1, o2⟩, g2, e2, h⟩ := h
    simp [pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    obtain ⟨n1, z1⟩ := nn_copyNeed hl p _ _ _ _ _ e1 ha.1 hb.1
    obtain ⟨n2, z2⟩ := nn_copyNeed tl q _ _ _ _ _ e2 ha.2.1 hb.2.1
    exact ⟨⟨n1, n2, fun ⟨c1, c2⟩ => ha.2.2 ⟨(z1 c1).1, (z2 c2).1⟩⟩, fun e => by cases e⟩
  | Need.pair pl ql, Need.pair pr qr, ops, g, g', c, ops', h, ha, hb => by
    simp only [copyNeed, cra_bind] at h
    obtain ⟨⟨a1, o1⟩, g1, e1, ⟨b1, o2⟩, g2, e2, h⟩ := h
    simp [pure, StateT.pure] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    obtain ⟨n1, z1⟩ := nn_copyNeed pl pr _ _ _ _ _ e1 ha.1 hb.1
    obtain ⟨n2, z2⟩ := nn_copyNeed ql qr _ _ _ _ _ e2 ha.2.1 hb.2.1
    refine ⟨nn_consNeed n1 n2, fun e => ?_⟩
    unfold consNeed at e
    split at e
    · rename_i hc
      exact absurd ⟨(z1 hc.1).1, (z2 hc.2).1⟩ ha.2.2
    · cases e
  | Need.pair pl ql, Need.both x h t, ops, g, g', c, ops', hc, ha, hb => by
    simp only [copyNeed, cra_bind] at hc
    obtain ⟨⟨a1, o1⟩, g1, e1, ⟨b1, o2⟩, g2, e2, hc⟩ := hc
    simp [pure, StateT.pure] at hc
    obtain ⟨⟨rfl, -⟩, -⟩ := hc
    obtain ⟨n1, z1⟩ := nn_copyNeed pl h _ _ _ _ _ e1 ha.1 hb.1
    obtain ⟨n2, z2⟩ := nn_copyNeed ql t _ _ _ _ _ e2 ha.2.1 hb.2.1
    exact ⟨⟨n1, n2, fun ⟨c1, c2⟩ => ha.2.2 ⟨(z1 c1).1, (z2 c2).1⟩⟩, fun e => by cases e⟩

theorem nn_rollTack : ∀ (tack : List (Bool × Need)) (acc : Need), NN acc → (∀ e ∈ tack, NN e.2) →
    NN (tack.foldl (fun acc e => side e.1 acc e.2) acc)
  | [], acc, ha, _ => ha
  | e :: rest, acc, ha, ht => by
    simp only [List.foldl]
    apply nn_rollTack rest _ _ (fun x hx => ht x (by simp [hx]))
    unfold side
    split
    · exact nn_consNeed ha (ht e (by simp))
    · exact nn_consNeed (ht e (by simp)) ha

theorem nn_intoLoop (o : Nat) (axe : Nat) : ∀ (ned : Need) (tack : List (Bool × Need)) (ops : List Pole)
    (g g' : Gen (TreapMap mugF)) (d r : Need), intoLoop o axe ned tack ops g = some ((d, r), g') →
    NN ned → (∀ e ∈ tack, NN e.2) → NN d ∧ NN r := by
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ned tack ops g g' d r h hn ht
    rw [intoLoop.eq_def] at h
    split at h
    · simp only [cra_bind] at h
      obtain ⟨u, g1, -, h⟩ := h
      simp [pure, StateT.pure] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      exact ⟨hn, nn_rollTack tack _ trivial ht⟩
    · rename_i h1
      have hm := mas_lt axe (by omega)
      split at h
      · exact ih _ hm _ _ _ _ _ _ _ h trivial (fun e he => by
          simp at he; rcases he with rfl | he
          · trivial
          · exact ht e he)
      · simp only [cra_bind] at h
        obtain ⟨l, g1, -, r', g2, -, h⟩ := h
        exact ih _ hm _ _ _ _ _ _ _ h trivial (fun e he => by
          simp at he; rcases he with rfl | he
          · trivial
          · exact ht e he)
      · rename_i p q
        exact ih _ hm _ _ _ _ _ _ _ h (by split <;> first | exact hn.1 | exact hn.2.1) (fun e he => by
          simp at he; rcases he with rfl | he
          · simp only; split <;> first | exact hn.1 | exact hn.2.1
          · exact ht e he)
      · rename_i rr hh t
        simp only [cra_bind] at h
        obtain ⟨⟨l1, l2⟩, g1, e1, ⟨r1, r2⟩, g2, e2, h⟩ := h
        have n1 := nn_must e1 hn.1
        have n2 := nn_must e2 hn.2.1
        exact ih _ hm _ _ _ _ _ _ _ h (by split <;> assumption) (fun e he => by
          simp at he; rcases he with rfl | he
          · simp only; split <;> assumption
          · exact ht e he)

theorem nn_into {nex : Next CSet} {a : Nat} {g g' : Gen (TreapMap mugF)} {don rec : Sure CSet} {o : Nat}
    (h : into nex a g = some ((don, rec, o), g')) (hn : NN nex.laz.ned) : NN don.ned ∧ NN rec.ned := by
  simp only [into, intoSure, cra_bind, cf_emit_g] at h
  obtain ⟨o', g1, -, ⟨d, r⟩, g2, e2, e3⟩ := h
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
  obtain ⟨⟨rfl, rfl, -⟩, -⟩ := e3
  cases el : intoLok a nex.laz.lok with
  | none => simp [el] at e2
  | some ll =>
    obtain ⟨ld, lr⟩ := ll
    cases en : intoNeed a nex.laz.ned o' g1 with
    | none => simp [el, en] at e2
    | some pn =>
      obtain ⟨⟨nd, nr⟩, g3⟩ := pn
      simp [el, en] at e2
      obtain ⟨⟨rfl, rfl⟩, -⟩ := e2
      unfold intoNeed at en
      split at en
      · cases en
      · split at en
        · simp [pure, StateT.pure] at en
          obtain ⟨⟨rfl, rfl⟩, -⟩ := en
          exact ⟨hn, trivial⟩
        · exact nn_intoLoop o' a _ [] [] _ _ _ _ en hn (fun e he => by cases he)

theorem nn_split {nex : Next CSet} {g g' : Gen (TreapMap mugF)} {hed tel : Sure CSet} {o : Nat}
    (h : split nex g = some ((hed, tel, o), g')) (hn : NN nex.laz.ned) : NN hed.ned ∧ NN tel.ned := by
  simp only [Comp.split, splitSure, bind, StateT.bind, cf_emit_g] at h
  cases e : splitLok nex.laz.lok with
  | none => simp [e] at h
  | some lt =>
    obtain ⟨lh, lt'⟩ := lt
    cases e2 : splitNeed nex.laz.ned g.bo (cfEmitG ⟨[], [], Termin.hop nex.th⟩ g) with
    | none => simp [e, e2] at h
    | some r =>
      obtain ⟨⟨nh, nt⟩, g2⟩ := r
      simp [e, e2, pure, StateT.pure] at h
      obtain ⟨⟨rfl, rfl, -⟩, -⟩ := h
      exact nn_splitNeed e2 hn

theorem nn_copy {f : Next CSet} {s : Sure CSet} {g g' : Gen (TreapMap mugF)} {nex : Next CSet}
    (h : copy f s g = some (nex, g')) (hf : NN f.laz.ned) (hs : NN s.ned) : NN nex.laz.ned := by
  simp only [copy, copyLazy, cra_bind, cf_emit_g] at h
  obtain ⟨o, g1, e1, a, g2, e2, e3⟩ := h
  obtain ⟨⟨ned, ops⟩, g3, e4, u, g4, e5, e6⟩ := e2
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e6 e3
  obtain ⟨rfl, rfl⟩ := e6
  obtain ⟨rfl, rfl⟩ := e3
  exact (nn_copyNeed _ _ _ _ _ _ _ e4 hf hs).1

theorem nn_bomb {miss : Option Nat} {g g' : Gen (TreapMap mugF)} {nex : Next CSet}
    (h : bomb miss g = some (nex, g')) : NN nex.laz.ned := by
  simp only [bomb, cra_bind, cf_emit_g, pure, StateT.pure] at h
  obtain ⟨o, g1, -, h⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  trivial

/-- The goal's need has the invariant. -/
def NNg : CGoal CSet → Prop
  | CGoal.next laz _ => NN laz.ned
  | _ => True

theorem nn_sn (gl : CGoal CSet) (hg : NNg gl) (g : Gen (TreapMap mugF)) (nex : Next CSet)
    (g1 : Gen (TreapMap mugF)) (e : simpleNext gl g = some (nex, g1)) : NN nex.laz.ned := by
  cases gl with
  | next laz th =>
    simp [simpleNext, pure, StateT.pure] at e
    rw [← e.1]; exact hg
  | done =>
    simp [simpleNext, re, bind, StateT.bind, pure, StateT.pure, cd_emit_eq] at e
    rcases e with ⟨rfl, -⟩
    trivial
  | pick z o =>
    simp [simpleNext, re, bind, StateT.bind, pure, StateT.pure, cd_emit_eq] at e
    rcases e with ⟨rfl, -⟩
    trivial

theorem nn_from {axe : Nat} {sur sur' : Sure CSet} (h : «from» axe sur = some sur') (hn : NN sur.ned) :
    NN sur'.ned := by
  simp only [«from», fromSure] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · simp at h; rw [← h]; trivial
    · rename_i h1 h2
      simp at h; rw [← h]
      exact (nn_fromPath sur.ned hn h2 axe).1

/-! ## A run keeps it -/

/-- **A run of the model from a goal with the invariant returns a `next`
with it**, for every pure nomm with no `%6`. -/
theorem nn_run : ∀ (n : Nomm), n.pure = true → noSix n = true → ∀ (gl : CGoal CSet)
    (g g' : Gen (TreapMap mugF)) (nex : Next CSet), run n gl g = some (nex, g') → NNg gl → NN nex.laz.ned
  | Nomm.cons p q, hpu, h6, gl, g, g', nex, h, hg => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp := nn_run p hpu.1 h6.1
    have ihq := nn_run q hpu.2 h6.2
    have hnext : ∀ s th g, NN s.ned → run (Nomm.cons p q) (CGoal.next s th) g = some (nex, g') →
        NN nex.laz.ned := by
      intro s th g hs h
      rw [crc_run_next p q hpu.1 hpu.2] at h
      simp only [cra_bind] at h
      obtain ⟨⟨hed, tel, o⟩, g1, e1, nex2, g2, e2, nex1, g3, e3, e4⟩ := h
      obtain ⟨hh, ht⟩ := nn_split e1 hs
      exact nn_copy e4 (ihp _ _ _ _ e3 hh) (ihq _ _ _ _ e2 ht)
    cases gl with
    | next s th => exact hnext s th g hg h
    | done => rw [crc_run_done] at h; exact hnext (lazyReg g.re) _ _ trivial h
    | pick z o =>
      rw [crc_run_pick p q hpu.1] at h
      simp only [cra_bind] at h
      obtain ⟨nex2, g2, e2, nex1, g3, e3, e4⟩ := h
      exact nn_copy e4 (ihp _ _ _ _ e3 trivial) (ihq _ _ _ _ e2 trivial)
  | Nomm.n0 ax, _, _, gl, g, g', nex, h, hg => by
    simp only [run] at h
    split at h
    · exact nn_bomb h
    · rw [cra_bind] at h
      obtain ⟨nex0, g1, e1, h⟩ := h
      have h0 := nn_sn gl hg g nex0 g1 e1
      split at h
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h; exact h0
      · cases ef : «from» ax nex0.laz with
        | none => simp [ef] at h
        | some laz =>
          simp [ef, pure, StateT.pure] at h
          obtain ⟨rfl, -⟩ := h
          exact nn_from ef h0
  | Nomm.n1 k, _, _, gl, g, g', nex, h, hg => by
    cases gl with
    | done =>
      simp only [run, cra_bind, pure, StateT.pure] at h
      obtain ⟨r, g1, -, o, g2, -, h⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; trivial
    | pick z o =>
      simp only [run] at h
      split at h
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h; trivial
      · split at h
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h; trivial
        · exact nn_bomb h
    | next laz th =>
      simp only [run, cra_bind, pure, StateT.pure] at h
      obtain ⟨o, g1, -, h⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; trivial
  | Nomm.n3 p, hpu, h6, gl, g, g', nex, h, hg => by
    have ih := nn_run p hpu h6
    cases gl with
    | next laz th =>
      simp only [run] at h
      split at h
      · exact ih _ _ _ _ h hg
      · rw [cra_bind] at h
        obtain ⟨a, g1, -, h⟩ := h
        rcases a with _ | ⟨r, o⟩
        · cases h
        · simp only [cra_bind] at h
          obtain ⟨⟨z, o'⟩, g2, -, r', g3, -, oc, g4, -, h⟩ := h
          exact ih _ _ _ _ h trivial
    | pick z o =>
      simp only [run, cra_bind] at h
      obtain ⟨r, g1, -, oc, g2, -, h⟩ := h
      exact ih _ _ _ _ h trivial
    | done =>
      simp only [run, cra_bind] at h
      obtain ⟨⟨o0, o1⟩, g1, -, r, g2, -, oc, g3, -, h⟩ := h
      exact ih _ _ _ _ h trivial
  | Nomm.n4 p, hpu, h6, gl, g, g', nex, h, hg => by
    have ih := nn_run p hpu h6
    cases gl with
    | done =>
      simp only [run, cra_bind] at h
      obtain ⟨pro, g1, -, arg, g2, -, o, g3, -, h⟩ := h
      exact ih _ _ _ _ h trivial
    | pick z o =>
      simp only [run, cra_bind] at h
      obtain ⟨pro, g1, -, arg, g2, -, o', g3, -, h⟩ := h
      exact ih _ _ _ _ h trivial
    | next laz th =>
      simp only [run, cra_bind] at h
      obtain ⟨a, g1, -, ⟨pro, th'⟩, g2, -, arg, g3, -, o, g4, -, h⟩ := h
      exact ih _ _ _ _ h trivial
  | Nomm.n5 p q, hpu, h6, gl, g, g', nex, h, hg => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp := nn_run p hpu.1 h6.1
    have ihq := nn_run q hpu.2 h6.2
    rw [cr_run_n5_eq p q hpu.1] at h
    simp only [cra_bind] at h
    obtain ⟨o, g1, -, nexq, g2, e2, nexp, g3, e3, e4⟩ := h
    exact nn_copy e4 (ihp _ _ _ _ e3 trivial) (ihq _ _ _ _ e2 trivial)
  | Nomm.n7 p q, hpu, h6, gl, g, g', nex, h, hg => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp := nn_run p hpu.1 h6.1
    have ihq := nn_run q hpu.2 h6.2
    simp only [run, cra_bind] at h
    obtain ⟨nex1, g1, e1, h⟩ := h
    exact ihp _ _ _ _ h (ihq _ _ _ _ e1 hg)
  | Nomm.n10 a v q, hpu, h6, gl, g, g', nex, h, hg => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihv := nn_run v hpu.1 h6.1
    have ihq := nn_run q hpu.2 h6.2
    rw [cr_run_n10_eq a v q hpu.1 hpu.2] at h
    simp only [cra_bind] at h
    obtain ⟨nex0, g1, e1, ⟨don, rec, o⟩, g2, e2, nexD, g3, e3, nexR, g4, e4, e5⟩ := h
    obtain ⟨hd, hr⟩ := nn_into e2 (nn_sn gl hg g nex0 g1 e1)
    exact nn_copy e5 (ihq _ _ _ _ e4 hr) (ihv _ _ _ _ e3 hd)
  | Nomm.n2 _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n6 _ _ _, _, h6, _, _, _, _, _, _ => by simp [noSix] at h6
  | Nomm.n11s _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n11d _ _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n12 _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.mean _ _ _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu

/-- **`hnoar` from the run**: on the fragment, `+need-ord-alloc-regs` of
`sccSur` succeeds after the run for `[%done ~]`. -/
theorem noar_frag (nm : Nomm) (hpu : nm.pure = true) (h6 : noSix nm = true) (nex : NextL CSet)
    (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) (cape : Cape) :
    ∃ nedF g2, needOrdAllocRegs (sccSur nex cape) g1 = some (nedF, g2) := by
  obtain ⟨hlz, hsur⟩ := scc_sur_frag nm hpu h6 nex g1 hrunL cape
  have hnn : NN nex.laz.sure.ned := by
    have hr := hrunL
    rw [show (CGoalL.done : CGoalL CSet) = CGoal.toL CGoal.done from rfl, runL_toL nm hpu h6] at hr
    cases e : run (S := CSet) (Map := TreapMap mugF) nm CGoal.done gen0 with
    | none => simp [e, Functor.map, StateT.map] at hr
    | some q =>
      obtain ⟨nex0, g0⟩ := q
      simp [e, Functor.map, StateT.map] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact nn_run nm hpu h6 CGoal.done gen0 g0 nex0 e trivial
  have hno := nno_sureOf cape nex.laz.sure.lok _ (nno_needToOrd hnn) _ hsur
  obtain ⟨n, g2, e, -⟩ := noar_nno (sccSur nex cape) g1 hno
  exact ⟨n, g2, e⟩

end Compiler
end Formalization
