import lemmas.Compiler.CompSixFork

/-!
# What `+fork` keeps

`KM` of `+fork` (`km_forkL`): the counters grow, the mode stays, every tag
stays.  `+copy-tag` puts a tag under each new kid label; `TagsUp` only asks
that a block with a tag keep one, and `put` never removes a key, so no
freshness fact about the tags is needed (`km_copyTag`).  `+insert-hop`
writes only `blocks` (`km_insertHop`).

What the loop returns (`fkl_spec`, mutual with `fkf_spec`, `fkb_spec`): the
registers of the two new lazy needs together have no duplicate and lie in
`[g.re, g'.re)` (each sure part is forked by `+fork-sure`, whose registers
are fresh, and the parts are made one after the other); their labels
together have no duplicate and lie in `[g.bo, g'.bo)` (every kid label is
an `+oo`); the looks are kept.  `ginv_forkL`: the two goals that `+fork`
returns meet `GInv`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp Lazy

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## `KM` -/

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem tagsUp_foldl_put (region : List Nat) : ∀ (tos : List Nat) (m : Map (List Nat)) (o : Nat),
    (HoonMap.get m o).isSome = true →
      (HoonMap.get (tos.foldl (fun m o => HoonMap.put m o region) m) o).isSome = true
  | [], _, _, h => h
  | t :: ts, m, o, h => tagsUp_foldl_put region ts _ o (by
      simp only [HoonMap.get_put]
      split
      · rfl
      · exact h)

/-- **`+copy-tag` keeps every tag**: it only puts. -/
theorem km_copyTag (frm : Nat) (tos : List Nat) : KM (copyTag frm tos : CM Map Unit) := by
  constructor
  · intro g x g' h
    unfold copyTag at h
    split at h
    · cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
    · obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
  · intro g x g' h
    unfold copyTag at h
    split at h
    · cases h; exact TagsUp.refl _
    · obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h; cases e
      exact fun o ho => tagsUp_foldl_put _ tos _ o ho

/-- **`+insert-hop` writes only `blocks`.** -/
theorem km_insertHop (a o1 o2 : Nat) : KM (insertHop a o1 o2 : CM Map Unit) :=
  KM.of_gen fun g x g' h => by
    unfold insertHop at h
    split at h
    · cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩
    · obtain ⟨b, _, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · split at h
        · cases h
        · cases h; exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩
      · cases h

theorem km_forkNeedGo : ∀ ned : Need, KM (forkNeedGo ned : CM Map (Need × Need))
  | Need.none => by rw [forkNeedGo]; exact KM.pure' _
  | Need.this _ => by rw [forkNeedGo]; exact KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.pure' _
  | Need.pair p q => by
    rw [forkNeedGo]
    refine KM.bind' (km_forkNeedGo p) fun x => ?_
    obtain ⟨a, b⟩ := x
    refine KM.bind' (km_forkNeedGo q) fun y => ?_
    obtain ⟨c, d⟩ := y
    exact KM.pure' _
  | Need.both _ h t => by
    rw [forkNeedGo]
    refine KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (km_forkNeedGo h) fun x => ?_
    obtain ⟨a, b⟩ := x
    refine KM.bind' (km_forkNeedGo t) fun y => ?_
    obtain ⟨c, d⟩ := y
    exact KM.pure' _

theorem km_forkSure (sur : Sure S) (o o0 o1 : Nat) : KM (forkSure sur o o0 o1 : CM Map (Sure S × Sure S)) := by
  unfold forkSure forkNeed
  refine KM.bind' (KM.bind' (km_forkNeedGo _) fun x => ?_) fun y => ?_
  · obtain ⟨n0, n1⟩ := x
    exact KM.bind' (KM.emit' _) fun _ => KM.bind' (KM.emir' _ _) fun _ => KM.bind' (KM.emir' _ _) fun _ => KM.pure' _
  · obtain ⟨n0, n1⟩ := y
    exact KM.pure' _

mutual
/-- **The loop of `+fork` keeps the counters growing, the mode and the tags.** -/
theorem km_forkLoop (rc : Nat) : ∀ (laz : Lazy S) (o o0 o1 : Nat),
    KM (forkLoop rc laz o o0 o1 : CM Map (Lazy S × Lazy S))
  | Lazy.mk s fk bd, o, o0, o1 => by
    rw [forkLoop]
    refine KM.bind' (km_forkSure _ _ _ _) fun x => ?_
    obtain ⟨s0, s1⟩ := x
    refine KM.bind' (km_forkForks rc fk) fun y => ?_
    obtain ⟨f0, f1⟩ := y
    refine KM.bind' (km_forkBonds rc bd) fun z => ?_
    obtain ⟨b0, b1⟩ := z
    exact KM.pure' _

theorem km_forkForks (rc : Nat) : ∀ fk : List ((Nat × Lazy S) × (Nat × Lazy S)),
    KM (forkForks rc fk : CM Map (List ((Nat × Lazy S) × (Nat × Lazy S)) × List ((Nat × Lazy S) × (Nat × Lazy S))))
  | [] => by rw [forkForks]; exact KM.pure' _
  | ((oy, y), (on, n)) :: rest => by
    rw [forkForks]
    refine KM.bind' KM.oo' fun _ => KM.bind' KM.oo' fun _ => KM.bind' KM.oo' fun _ =>
      KM.bind' KM.oo' fun _ => KM.bind' KM.oo' fun _ => KM.bind' KM.oo' fun _ =>
      KM.bind' (km_copyTag _ _) fun _ => KM.bind' (km_copyTag _ _) fun _ => ?_
    refine KM.bind' (km_forkLoop rc y _ _ _) fun a => ?_
    obtain ⟨ly0, ly1⟩ := a
    refine KM.bind' (km_forkLoop rc n _ _ _) fun b => ?_
    obtain ⟨ln0, ln1⟩ := b
    refine KM.bind' (KM.proxy' _ _) fun _ => KM.bind' (KM.proxy' _ _) fun _ => KM.bind' (KM.emit' _) fun _ =>
      KM.bind' (KM.emit' _) fun _ => KM.bind' (km_insertHop _ _ _) fun _ => KM.bind' (km_insertHop _ _ _) fun _ => ?_
    refine KM.bind' (km_forkForks rc rest) fun c => ?_
    obtain ⟨r0, r1⟩ := c
    exact KM.pure' _

theorem km_forkBonds (rc : Nat) : ∀ bd : List (Nat × Lazy S),
    KM (forkBonds rc bd : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [] => by rw [forkBonds]; exact KM.pure' _
  | (ob, lb) :: rest => by
    rw [forkBonds]
    refine KM.bind' KM.oo' fun _ => KM.bind' KM.oo' fun _ => KM.bind' KM.oo' fun _ =>
      KM.bind' (km_copyTag _ _) fun _ => ?_
    refine KM.bind' (km_forkLoop rc lb _ _ _) fun a => ?_
    obtain ⟨l0, l1⟩ := a
    refine KM.bind' (KM.proxy' _ _) fun _ => KM.bind' (KM.emit' _) fun _ =>
      KM.bind' (km_insertHop _ _ _) fun _ => ?_
    refine KM.bind' (km_forkBonds rc rest) fun c => ?_
    obtain ⟨r0, r1⟩ := c
    exact KM.pure' _
end

/-- **`+fork` keeps the counters growing, the mode and the tags.** -/
theorem km_forkL (nex : NextL S) (rc : Nat) : KM (forkL nex rc : CM Map (NextL S × NextL S)) := by
  unfold forkL
  refine KM.bind' KM.oo' fun o0 => KM.bind' KM.oo' fun o1 => KM.ite' _ KM.fail ?_
  refine KM.bind' (km_forkLoop _ _ _ _ _) fun x => ?_
  obtain ⟨l0, l1⟩ := x
  exact KM.pure' _

end

/-! ## Fresh ranges -/

/-- No duplicate, every member in `[lo, hi)`. -/
def FR (lo hi : Nat) (L : List Nat) : Prop := L.Nodup ∧ ∀ y ∈ L, lo ≤ y ∧ y < hi

theorem FR.nil (lo hi : Nat) : FR lo hi [] := ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem FR.app {a b c : Nat} {L M : List Nat} (h1 : FR a b L) (h2 : FR b c M) (hab : a ≤ b) (hbc : b ≤ c) :
    FR a c (L ++ M) := by
  refine ⟨List.nodup_append.2 ⟨h1.1, h2.1, fun x hx y hy e => ?_⟩, fun y hy => ?_⟩
  · have := (h1.2 x hx).2; have := (h2.2 y hy).1; omega
  · rcases List.mem_append.1 hy with hy | hy
    · have := h1.2 y hy; constructor <;> omega
    · have := h2.2 y hy; constructor <;> omega

theorem FR.mono {lo hi lo' hi' : Nat} {L : List Nat} (h : FR lo hi L) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
    FR lo' hi' L :=
  ⟨h.1, fun y hy => by have := h.2 y hy; constructor <;> omega⟩

theorem FR.perm {lo hi : Nat} {L M : List Nat} (h : FR lo hi L) (p : L.Perm M) : FR lo hi M :=
  ⟨p.nodup_iff.1 h.1, fun y hy => h.2 y (p.mem_iff.2 hy)⟩

theorem FR.left {lo hi : Nat} {L M : List Nat} (h : FR lo hi (L ++ M)) : FR lo hi L :=
  ⟨(List.nodup_append.1 h.1).1, fun y hy => h.2 y (List.mem_append_left _ hy)⟩

theorem FR.right {lo hi : Nat} {L M : List Nat} (h : FR lo hi (L ++ M)) : FR lo hi M :=
  ⟨(List.nodup_append.1 h.1).2.1, fun y hy => h.2 y (List.mem_append_right _ hy)⟩

theorem perm4 (a b c d : List Nat) : ((a ++ b) ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) :=
  List.perm_iff_count.2 fun x => by simp only [List.count_append]; omega

theorem perm6 (a b c d e f : List Nat) :
    ((a ++ (b ++ c)) ++ (d ++ (e ++ f))).Perm ((a ++ d) ++ ((b ++ e) ++ (c ++ f))) :=
  List.perm_iff_count.2 fun x => by simp only [List.count_append]; omega

theorem perm10 (a b c d e f g h i j : List Nat) :
    ((a ++ (b ++ (c ++ (d ++ e)))) ++ (f ++ (g ++ (h ++ (i ++ j))))).Perm
      ((a ++ (f ++ (b ++ g))) ++ ((c ++ h) ++ ((d ++ i) ++ (e ++ j)))) :=
  List.perm_iff_count.2 fun x => by simp only [List.count_append]; omega

/-! ## What the loop returns -/

section
variable (rc : Nat)

theorem fk_oo (g : Gen (TreapMap mugF)) : (oo : CM (TreapMap mugF) Nat) g = some (g.bo, { g with bo := g.bo + 1 }) := rfl

/-- One `+oo` in a chain of binds. -/
macro "fk_oo_step" h:ident e:ident : tactic => `(tactic|
  (rw [fk_oo] at $e:ident; simp only [Option.some.injEq, Prod.mk.injEq] at $e:ident))

mutual
/-- **What the loop of `+fork` returns**: fresh registers, fresh labels, the
looks kept. -/
theorem fkl_spec : ∀ (laz : Lazy CSet) (o o0 o1 : Nat) (g g' : Gen (TreapMap mugF)) (l0 l1 : Lazy CSet),
    LAll CrLok laz → forkLoop rc laz o o0 o1 g = some ((l0, l1), g') →
    FR g.re g'.re (lregs l0 ++ lregs l1) ∧ FR g.bo g'.bo (llabs l0 ++ llabs l1) ∧ LAll CrLok l0 ∧ LAll CrLok l1
  | Lazy.mk s fk bd, o, o0, o1, g, g', l0, l1, ⟨hs, hf, hb⟩, h => by
    rw [forkLoop] at h
    obtain ⟨⟨s0, s1⟩, g1, e1, h⟩ := bind_some h
    obtain ⟨⟨f0, f1⟩, g2, e2, h⟩ := bind_some h
    obtain ⟨⟨b0, b1⟩, g3, e3, h⟩ := bind_some h
    dsimp only at h
    rw [pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨r1, b1', -, lk0, lk1, D0, D1, ap, fr⟩ := forkSure_inv e1
    obtain ⟨F, FL, W0, W1⟩ := fkf_spec fk g1 g2 f0 f1 hf e2
    obtain ⟨B, BL, V0, V1⟩ := fkb_spec bd g2 g3 b0 b1 hb e3
    obtain ⟨k2, c2, -⟩ := (km_forkForks (Map := TreapMap mugF) rc fk).keep _ _ _ e2
    obtain ⟨k3, c3, -⟩ := (km_forkBonds (Map := TreapMap mugF) rc bd).keep _ _ _ e3
    have S : FR g.re g1.re (flattenNeed s0.ned ++ flattenNeed s1.ned) := by
      refine ⟨List.nodup_append.2 ⟨(distinct_iff_nodup _).1 D0, (distinct_iff_nodup _).1 D1,
        fun a ha b hb e => ?_⟩, fun y hy => ?_⟩
      · subst e; exact ap a ((mem_flat _ _).1 ha) ((mem_flat _ _).1 hb)
      · rcases List.mem_append.1 hy with hy | hy
        · exact fr y (Or.inl ((mem_flat _ _).1 hy))
        · exact fr y (Or.inr ((mem_flat _ _).1 hy))
    refine ⟨?_, ?_, ⟨fun y hy => hs y (lk0 ▸ hy), W0, V0⟩, ⟨fun y hy => hs y (lk1 ▸ hy), W1, V1⟩⟩
    · simp only [lregs]
      exact FR.perm (S.app (F.app B k2 k3) r1 (by omega)) (perm6 _ _ _ _ _ _).symm
    · simp only [llabs]
      exact FR.perm ((FL.app BL c2 c3).mono (by omega) (Nat.le_refl _)) (perm4 _ _ _ _).symm

theorem fkf_spec : ∀ (fk : List (Lazy.ForkE CSet)) (g g' : Gen (TreapMap mugF)) (f0 f1 : List (Lazy.ForkE CSet)),
    WalkPF (fun _ s => CrLok s) fk → forkForks rc fk g = some ((f0, f1), g') →
    FR g.re g'.re (fregs f0 ++ fregs f1) ∧ FR g.bo g'.bo (flabs f0 ++ flabs f1) ∧
      WalkPF (fun _ s => CrLok s) f0 ∧ WalkPF (fun _ s => CrLok s) f1
  | [], g, g', f0, f1, _, h => by
    rw [forkForks, pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨FR.nil _ _, FR.nil _ _, trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, g, g', f0, f1, ⟨wy, wn, wr⟩, h => by
    rw [forkForks] at h
    obtain ⟨a1, gA, eA, h⟩ := bind_some h
    fk_oo_step h eA
    obtain ⟨rfl, rfl⟩ := eA
    obtain ⟨a2, gB, eB, h⟩ := bind_some h
    fk_oo_step h eB
    obtain ⟨rfl, rfl⟩ := eB
    obtain ⟨a3, gC, eC, h⟩ := bind_some h
    fk_oo_step h eC
    obtain ⟨rfl, rfl⟩ := eC
    obtain ⟨a4, gD, eD, h⟩ := bind_some h
    fk_oo_step h eD
    obtain ⟨rfl, rfl⟩ := eD
    obtain ⟨a5, gE, eE, h⟩ := bind_some h
    fk_oo_step h eE
    obtain ⟨rfl, rfl⟩ := eE
    obtain ⟨a6, gF, eF, h⟩ := bind_some h
    fk_oo_step h eF
    obtain ⟨rfl, rfl⟩ := eF
    obtain ⟨_, gG, eG, h⟩ := bind_some h
    obtain ⟨_, gH, eH, h⟩ := bind_some h
    obtain ⟨⟨ly0, ly1⟩, gI, eI, h⟩ := bind_some h
    obtain ⟨⟨ln0, ln1⟩, gJ, eJ, h⟩ := bind_some h
    obtain ⟨_, gK, eK, h⟩ := bind_some h
    obtain ⟨_, gL, eL, h⟩ := bind_some h
    obtain ⟨_, gM, eM, h⟩ := bind_some h
    obtain ⟨_, gN, eN, h⟩ := bind_some h
    obtain ⟨_, gO, eO, h⟩ := bind_some h
    obtain ⟨_, gP, eP, h⟩ := bind_some h
    obtain ⟨⟨r0, r1⟩, gQ, eQ, h⟩ := bind_some h
    dsimp only at h
    rw [pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨kG, bG, -⟩ := (km_copyTag (Map := TreapMap mugF) _ _).keep _ _ _ eG
    obtain ⟨kH, bH, -⟩ := (km_copyTag (Map := TreapMap mugF) _ _).keep _ _ _ eH
    obtain ⟨kK, bK, -⟩ := (KM.proxy' (Map := TreapMap mugF) _ _).keep _ _ _ eK
    obtain ⟨kL, bL, -⟩ := (KM.proxy' (Map := TreapMap mugF) _ _).keep _ _ _ eL
    obtain ⟨kM, bM, -⟩ := (KM.emit' (Map := TreapMap mugF) _).keep _ _ _ eM
    obtain ⟨kN, bN, -⟩ := (KM.emit' (Map := TreapMap mugF) _).keep _ _ _ eN
    obtain ⟨kO, bO, -⟩ := (km_insertHop (Map := TreapMap mugF) _ _ _).keep _ _ _ eO
    obtain ⟨kP, bP, -⟩ := (km_insertHop (Map := TreapMap mugF) _ _ _).keep _ _ _ eP
    rw [walkP_irrel] at wy wn
    obtain ⟨Y, YL, Y0, Y1⟩ := fkl_spec y _ _ _ gH gI ly0 ly1 wy eI
    obtain ⟨N, NL, N0, N1⟩ := fkl_spec n _ _ _ gI gJ ln0 ln1 wn eJ
    obtain ⟨R, RL, R0, R1⟩ := fkf_spec rest gP gQ r0 r1 wr eQ
    obtain ⟨kI, bI, -⟩ := (km_forkLoop (Map := TreapMap mugF) rc y _ _ _).keep _ _ _ eI
    obtain ⟨kJ, bJ, -⟩ := (km_forkLoop (Map := TreapMap mugF) rc n _ _ _).keep _ _ _ eJ
    obtain ⟨kQ, bQ, -⟩ := (km_forkForks (Map := TreapMap mugF) rc rest).keep _ _ _ eQ
    simp only at kG bG
    refine ⟨?_, ?_, ⟨by rw [walkP_irrel]; exact Y0, by rw [walkP_irrel]; exact N0, R0⟩,
      ⟨by rw [walkP_irrel]; exact Y1, by rw [walkP_irrel]; exact N1, R1⟩⟩
    · simp only [fregs]
      refine FR.perm ((Y.mono (by omega) (Nat.le_refl _)).app
        (N.app (R.mono (by omega) (Nat.le_refl _)) (by omega) (by omega)) (by omega) (by omega))
        (perm6 _ _ _ _ _ _).symm
    · simp only [flabs]
      have H4 : FR g.bo (g.bo + 4) ([g.bo] ++ ([g.bo + 1] ++ ([g.bo + 2] ++ [g.bo + 3]))) := by
        refine ⟨by simp [List.nodup_cons], fun z hz => ?_⟩
        simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> omega
      exact FR.perm ((H4.app ((YL.mono (by omega) (Nat.le_refl _)).app
        (NL.app (RL.mono (by omega) (Nat.le_refl _)) (by omega) (by omega)) (by omega) (by omega))
        (by omega) (by omega)).mono
        (Nat.le_refl _) (Nat.le_refl _))
        (perm10 [g.bo] [g.bo + 2] _ _ _ [g.bo + 1] [g.bo + 3] _ _ _).symm

theorem fkb_spec : ∀ (bd : List (Nat × Lazy CSet)) (g g' : Gen (TreapMap mugF)) (b0 b1 : List (Nat × Lazy CSet)),
    WalkPB (fun _ s => CrLok s) bd → forkBonds rc bd g = some ((b0, b1), g') →
    FR g.re g'.re (bregs b0 ++ bregs b1) ∧ FR g.bo g'.bo (blabs b0 ++ blabs b1) ∧
      WalkPB (fun _ s => CrLok s) b0 ∧ WalkPB (fun _ s => CrLok s) b1
  | [], g, g', b0, b1, _, h => by
    rw [forkBonds, pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨FR.nil _ _, FR.nil _ _, trivial, trivial⟩
  | (ob, lb) :: rest, g, g', b0, b1, ⟨wl, wr⟩, h => by
    rw [forkBonds] at h
    obtain ⟨a1, gA, eA, h⟩ := bind_some h
    fk_oo_step h eA
    obtain ⟨rfl, rfl⟩ := eA
    obtain ⟨a2, gB, eB, h⟩ := bind_some h
    fk_oo_step h eB
    obtain ⟨rfl, rfl⟩ := eB
    obtain ⟨a3, gC, eC, h⟩ := bind_some h
    fk_oo_step h eC
    obtain ⟨rfl, rfl⟩ := eC
    obtain ⟨_, gD, eD, h⟩ := bind_some h
    obtain ⟨⟨l0, l1⟩, gE, eE, h⟩ := bind_some h
    obtain ⟨_, gF, eF, h⟩ := bind_some h
    obtain ⟨_, gG, eG, h⟩ := bind_some h
    obtain ⟨_, gH, eH, h⟩ := bind_some h
    obtain ⟨⟨r0, r1⟩, gI, eI, h⟩ := bind_some h
    dsimp only at h
    rw [pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨kD, bD, -⟩ := (km_copyTag (Map := TreapMap mugF) _ _).keep _ _ _ eD
    obtain ⟨kF, bF, -⟩ := (KM.proxy' (Map := TreapMap mugF) _ _).keep _ _ _ eF
    obtain ⟨kG, bG, -⟩ := (KM.emit' (Map := TreapMap mugF) _).keep _ _ _ eG
    obtain ⟨kH, bH, -⟩ := (km_insertHop (Map := TreapMap mugF) _ _ _).keep _ _ _ eH
    rw [walkP_irrel] at wl
    obtain ⟨L, LL, L0, L1⟩ := fkl_spec lb _ _ _ gD gE l0 l1 wl eE
    obtain ⟨R, RL, R0, R1⟩ := fkb_spec rest gH gI r0 r1 wr eI
    obtain ⟨kE, bE, -⟩ := (km_forkLoop (Map := TreapMap mugF) rc lb _ _ _).keep _ _ _ eE
    obtain ⟨kI, bI, -⟩ := (km_forkBonds (Map := TreapMap mugF) rc rest).keep _ _ _ eI
    simp only at kD bD
    refine ⟨?_, ?_, ⟨by rw [walkP_irrel]; exact L0, R0⟩, ⟨by rw [walkP_irrel]; exact L1, R1⟩⟩
    · simp only [bregs]
      exact FR.perm ((L.mono (by omega) (Nat.le_refl _)).app (R.mono (by omega) (Nat.le_refl _))
        (by omega) (by omega))
        (perm4 _ _ _ _).symm
    · simp only [blabs]
      have H2 : FR g.bo (g.bo + 2) ([g.bo] ++ [g.bo + 1]) := by
        refine ⟨by simp [List.nodup_cons], fun z hz => ?_⟩
        simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> omega
      exact FR.perm ((H2.app ((LL.mono (by omega) (Nat.le_refl _)).app
        (RL.mono (by omega) (Nat.le_refl _)) (by omega) (by omega)) (by omega) (by omega)).mono
        (Nat.le_refl _) (Nat.le_refl _))
        (perm6 [g.bo] _ _ [g.bo + 1] _ _).symm
end

end

/-! ## The goals of `+fork` -/

mutual
theorem walkP_andK {P Q : Nat → Sure CSet → Prop} : ∀ (o : Nat) (laz : Lazy CSet),
    WalkP P o laz → WalkP Q o laz → WalkP (fun o s => P o s ∧ Q o s) o laz
  | o, Lazy.mk s fk bd, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩ => ⟨⟨a1, b1⟩, walkPF_andK fk a2 b2, walkPB_andK bd a3 b3⟩

theorem walkPF_andK {P Q : Nat → Sure CSet → Prop} : ∀ (fk : List (Lazy.ForkE CSet)),
    WalkPF P fk → WalkPF Q fk → WalkPF (fun o s => P o s ∧ Q o s) fk
  | [], _, _ => trivial
  | ((oy, y), (on, n)) :: rest, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩ =>
    ⟨walkP_andK oy y a1 b1, walkP_andK on n a2 b2, walkPF_andK rest a3 b3⟩

theorem walkPB_andK {P Q : Nat → Sure CSet → Prop} : ∀ (bd : List (Nat × Lazy CSet)),
    WalkPB P bd → WalkPB Q bd → WalkPB (fun o s => P o s ∧ Q o s) bd
  | [], _, _ => trivial
  | (ob, l) :: rest, ⟨a1, a2⟩, ⟨b1, b2⟩ => ⟨walkP_andK ob l a1 b1, walkPB_andK rest a2 b2⟩
end

/-- `LNB` from the looks and the registers. -/
theorem lall_lnb {k : Nat} {laz : Lazy CSet} (hl : LAll CrLok laz) (hr : ∀ r ∈ lregs laz, r < k) :
    LAll (LNB k) laz :=
  walkP_andK 0 laz hl (lall_regs (· < k) laz hr)

theorem fyes_mem : ∀ (f : List (Lazy.ForkE CSet)) (x : Nat), x ∈ f.map (fun e => e.1.1) → x ∈ flabs f
  | [], x, h => by simp at h
  | ((oy, y), (on, n)) :: rest, x, h => by
    simp only [List.map_cons, List.mem_cons] at h
    simp only [flabs, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (fyes_mem rest x h))))

theorem bkey_mem : ∀ (b : List (Nat × Lazy CSet)) (x : Nat), x ∈ b.map (fun e => e.1) → x ∈ blabs b
  | [], x, h => by simp at h
  | (o, l) :: rest, x, h => by
    simp only [List.map_cons, List.mem_cons] at h
    simp only [blabs, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (bkey_mem rest x h))

mutual
/-- **No label twice gives no key twice at a level.** -/
theorem lkeys_of_nodup : ∀ laz : Lazy CSet, (llabs laz).Nodup → LKeys laz
  | Lazy.mk s f b, h => by
    simp only [llabs, List.nodup_append] at h
    obtain ⟨hf, hb, -⟩ := h
    obtain ⟨f1, f2⟩ := fkeys_of_nodup f hf
    obtain ⟨b1, b2⟩ := bkeys_of_nodup b hb
    exact ⟨f1, b1, f2, b2⟩

theorem fkeys_of_nodup : ∀ f : List (Lazy.ForkE CSet), (flabs f).Nodup →
    (f.map fun e => e.1.1).Nodup ∧ FKeys f
  | [], _ => ⟨List.nodup_nil, trivial⟩
  | ((oy, y), (on, n)) :: rest, h => by
    simp only [flabs, List.nodup_cons, List.nodup_append, List.mem_cons, List.mem_append, not_or] at h
    obtain ⟨⟨-, -, -, h1⟩, -, hy, ⟨hn, hr, -⟩, -⟩ := h
    obtain ⟨r1, r2⟩ := fkeys_of_nodup rest hr
    refine ⟨List.nodup_cons.2 ⟨fun hm => h1 (fyes_mem rest oy hm), r1⟩, lkeys_of_nodup y hy,
      lkeys_of_nodup n hn, r2⟩

theorem bkeys_of_nodup : ∀ b : List (Nat × Lazy CSet), (blabs b).Nodup →
    (b.map fun e => e.1).Nodup ∧ BKeys b
  | [], _ => ⟨List.nodup_nil, trivial⟩
  | (o, l) :: rest, h => by
    simp only [blabs, List.nodup_cons, List.nodup_append, List.mem_append, not_or] at h
    obtain ⟨⟨-, h1⟩, hl, hr, -⟩ := h
    obtain ⟨r1, r2⟩ := bkeys_of_nodup rest hr
    exact ⟨List.nodup_cons.2 ⟨fun hm => h1 (bkey_mem rest o hm), r1⟩, lkeys_of_nodup l hl, r2⟩
end

/-- **What `+fork` returns**: the two goals jump to the two first labels it
takes, with no argument, and their lazy needs have fresh registers and
labels, apart, with the looks kept. -/
theorem forkL_spec {laz : Lazy CSet} {th : Jmp} {rc : Nat} {g g' : Gen (TreapMap mugF)} {n0 n1 : NextL CSet}
    (hl : LAll CrLok laz) (h : forkL ⟨laz, th⟩ rc g = some ((n0, n1), g')) :
    n0.th = jmp0 g.bo ∧ n1.th = jmp0 (g.bo + 1) ∧ FR g.re g'.re (lregs n0.laz ++ lregs n1.laz) ∧
      FR g.bo g'.bo (llabs n0.laz ++ llabs n1.laz) ∧ LAll CrLok n0.laz ∧ LAll CrLok n1.laz := by
  unfold forkL at h
  obtain ⟨a1, gA, eA, h⟩ := bind_some h
  rw [fk_oo] at eA
  simp only [Option.some.injEq, Prod.mk.injEq] at eA
  obtain ⟨rfl, rfl⟩ := eA
  obtain ⟨a2, gB, eB, h⟩ := bind_some h
  rw [fk_oo] at eB
  simp only [Option.some.injEq, Prod.mk.injEq] at eB
  obtain ⟨rfl, rfl⟩ := eB
  split at h
  · cases h
  · obtain ⟨⟨l0, l1⟩, gC, eC, h⟩ := bind_some h
    dsimp only at h
    rw [pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨R, L, W0, W1⟩ := fkl_spec rc laz _ _ _ _ _ l0 l1 hl eC
    exact ⟨rfl, rfl, R, L.mono (by simp only; omega) (Nat.le_refl _), W0, W1⟩

/-- **The two goals that `+fork` returns meet `GInv`.** -/
theorem ginv_forkL {laz : Lazy CSet} {th : Jmp} {rc : Nat} {g g' : Gen (TreapMap mugF)} {n0 n1 : NextL CSet}
    (hi : GInv g (CGoalL.next laz th)) (h : forkL ⟨laz, th⟩ rc g = some ((n0, n1), g')) :
    GInv g' n0.goal ∧ GInv g' n1.goal := by
  have hl : LAll CrLok laz := lall_mono (fun _ h => h.1) hi.1.1
  obtain ⟨t0, t1, R, L, W0, W1⟩ := forkL_spec hl h
  obtain ⟨-, -, kd⟩ := (km_forkL (Map := TreapMap mugF) (S := CSet) _ _).keep _ _ _ h
  have hd : g'.drop = false := kd.trans (ginv_drop hi)
  refine ⟨⟨⟨lall_lnb W0 fun r hr => (R.2 r (List.mem_append_left _ hr)).2, R.left.1,
      lkeys_of_nodup _ L.left.1, fun o ho => (L.2 o (List.mem_append_left _ ho)).2⟩, hd, ?_⟩,
    ⟨⟨lall_lnb W1 fun r hr => (R.2 r (List.mem_append_right _ hr)).2, R.right.1,
      lkeys_of_nodup _ L.right.1, fun o ho => (L.2 o (List.mem_append_right _ ho)).2⟩, hd, ?_⟩⟩
  · rw [t0]; exact jmpIn_jmp0 _ _
  · rw [t1]; exact jmpIn_jmp0 _ _

end Compiler
end Formalization
