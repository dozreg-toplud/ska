import lemmas.Glue.SplitDefBase

/-!
# Every split register is defined earlier in its body: the runs (track G)

LEDGER 2.c.  The arms of `runLC` on `PlainN` in the frame `KS` of
`Glue/SplitDefBase.lean`, in the order and shape of `Ska/CompSimBody.lean`
(`SimM`): the needs (as `Glue/GuardArms.lean`: `+copy-need-make-ops`
returns a list with no split), the lazy walks, `+mede`, `+collapse-lazy-atom`,
`+kern` (its ops are `+kern-need`'s, `kernNeed_sd`), `+kerf`, `+past`, the
indirect call and every arm of `runLC`.  Every emitted body and every other
added list has no split.

* **`ks_runLC`**: `runLC env sup nm` on `PlainN` keeps `SDS`, for every goal;
* **`splitDefEnd_plain`**: track G's body-local leaf `SplitDefEnd` (the
  state after the top run and its `+kerf` meets `SDS`; `gen0` has no block);
* **`entryMono_plainK`**: `EntryMono` on `PlainM` from `KIMid` ALONE.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy Raw

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## The needs -/

theorem ks_must (ned : Need) : KSB (must ned : CM Map (Nat × Need)) := by unfold must; ksb

theorem ks_splitNeed (ned : Need) (o : Nat) : KSB (splitNeed ned o : CM Map (Need × Need)) := by
  unfold splitNeed
  split
  · ksb
  · ksb
  · ksb
  · exact KS.bind' (ks_must _) fun _ _ => KS.bind' (ks_must _) fun _ _ => by ksb

theorem ks_splitSure (sur : Sure S) (o : Nat) : KSB (splitSure sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g1 hb h
  unfold splitSure at h
  obtain ⟨⟨l1, l2⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, g2⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨((ks_splitNeed sur.ned o).k g y g2 hb h1).1, trivial⟩

theorem ks_intoLoop (o : Nat) : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole),
    NoSplit ops → KSB (intoLoop o axe ned tack ops : CM Map (Need × Need)) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned tack ops hops
    rw [intoLoop]
    split
    · exact KS.bind' (KS.addOpsN _ hops) fun _ _ => KS.pure' trivial
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact ih _ hl _ _ _ hops
      · exact KS.bind' KS.re' fun _ _ => KS.bind' KS.re' fun _ _ => ih _ hl _ _ _ (noSplit_cons rfl hops)
      · exact ih _ hl _ _ _ hops
      · exact KS.bind' (ks_must _) fun _ _ => KS.bind' (ks_must _) fun _ _ => ih _ hl _ _ _ (noSplit_cons rfl hops)

theorem ks_intoNeed (axe : Nat) (ned : Need) (o : Nat) : KSB (intoNeed axe ned o : CM Map (Need × Need)) := by
  unfold intoNeed
  exact KS.ite' _ KS.fail (KS.ite' _ (KS.pure' trivial) (ks_intoLoop _ _ _ _ _ noSplit_nil))

theorem ks_intoSure (axe : Nat) (sur : Sure S) (o : Nat) : KSB (intoSure axe sur o : CM Map (Sure S × Sure S)) := by
  constructor
  intro g x g1 hb h
  unfold intoSure at h
  obtain ⟨⟨l1, l2⟩, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨y, g2⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨((ks_intoNeed axe sur.ned o).k g y g2 hb h1).1, trivial⟩

/-- **The ops of `+copy-need-make-ops` have no split** (moves only). -/
theorem ks_copyNeed : ∀ (a b : Need) (ops : List Pole), NoSplit ops →
    KS (fun x : Need × List Pole => NoSplit x.2) (copyNeed a b ops : CM Map (Need × List Pole))
  | Need.none, _, _, h => by rw [copyNeed]; exact KS.pure' h
  | Need.this _, Need.none, _, h => by rw [copyNeed] <;> first | exact KS.pure' h | nofun
  | Need.pair _ _, Need.none, _, h => by rw [copyNeed] <;> first | exact KS.pure' h | nofun
  | Need.both _ _ _, Need.none, _, h => by rw [copyNeed] <;> first | exact KS.pure' h | nofun
  | Need.this _, Need.this _, _, h => by rw [copyNeed]; exact KS.pure' (noSplit_cons rfl h)
  | Need.this _, Need.both _ _ _, _, h => by rw [copyNeed]; exact KS.pure' (noSplit_cons rfl h)
  | Need.this _, Need.pair _ _, _, h => by
    rw [copyNeed]; exact KS.bind' KS.re' fun _ _ => KS.pure' (noSplit_cons rfl h)
  | Need.both _ _ _, Need.this _, _, h => by rw [copyNeed]; exact KS.pure' (noSplit_cons rfl h)
  | Need.pair _ _, Need.this _, _, h => by
    rw [copyNeed]; exact KS.bind' KS.re' fun _ _ => KS.pure' (noSplit_cons rfl h)
  | Need.both _ hl tl, Need.both _ hr tr, _, h => by
    rw [copyNeed]
    exact KS.bind' (ks_copyNeed hl hr _ (noSplit_cons rfl h)) fun x hx =>
      KS.bind' (ks_copyNeed tl tr _ hx) fun y hy => KS.pure' hy
  | Need.both _ hl tl, Need.pair p q, _, h => by
    rw [copyNeed]
    exact KS.bind' KS.re' fun _ _ => KS.bind' (ks_copyNeed hl p _ (noSplit_cons rfl h)) fun x hx =>
      KS.bind' (ks_copyNeed tl q _ hx) fun y hy => KS.pure' hy
  | Need.pair pl ql, Need.pair pr qr, _, h => by
    rw [copyNeed]
    exact KS.bind' (ks_copyNeed pl pr _ h) fun x hx => KS.bind' (ks_copyNeed ql qr _ hx) fun y hy => KS.pure' hy
  | Need.pair pl ql, Need.both _ h' t, _, h => by
    rw [copyNeed]
    exact KS.bind' (ks_copyNeed pl h' _ h) fun x hx => KS.bind' (ks_copyNeed ql t _ hx) fun y hy => KS.pure' hy

theorem ks_lookPath : ∀ (axe : Nat) (ned : Need), KSB (lookPath ned axe : CM Map Need) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
    intro ned
    rw [lookPath.eq_def]
    split
    · split <;> ksb
    · have hl : mas axe < axe := mas_lt axe (by omega)
      split
      · exact KS.bind' (ih _ hl _) fun _ _ => by ksb
      · exact KS.bind' (ih _ hl _) fun _ _ => by ksb

theorem ks_sureRequireLook (sur : Sure S) : KSB (sureRequireLook sur : CM Map Need) := by
  unfold sureRequireLook
  refine KS.foldl' _ (fun acc b h => KS.bind' h fun ned _ => ?_) _ _ (KS.pure' trivial)
  exact KS.ite' _ (KS.pure' trivial) (KS.ite' _ KS.fail (ks_lookPath _ _))

theorem noSplit_immsS (v : Noun) (l : List Nat) : NoSplit (l.map fun x => Pole.imm v x) := by
  intro p hp; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hp; rfl

theorem ks_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : KSB (crashNeed o atom ned : CM Map Unit) := by
  unfold crashNeed
  split
  · exact KS.addOpsN _ (noSplit_cons rfl (noSplit_immsS _ _))
  · exact KS.bind' KS.re' fun _ _ => KS.addOpsN _ (noSplit_cons rfl (noSplit_cons rfl (noSplit_immsS _ _)))

theorem ks_medeLoop (o : Nat) : ∀ (som : Noun) (ned : Need), KSB (medeLoop o som ned : CM Map Unit)
  | _, Need.none => by rw [medeLoop]; ksb
  | _, Need.this _ => by rw [medeLoop]; ksb
  | Noun.atom _, Need.pair _ _ => by rw [medeLoop]; exact ks_crashNeed _ _ _
  | Noun.cell a b, Need.pair p q => by
    rw [medeLoop]; exact KS.bind' (ks_medeLoop o a p) fun _ _ => ks_medeLoop o b q
  | Noun.atom _, Need.both _ _ _ => by rw [medeLoop]; exact ks_crashNeed _ _ _
  | Noun.cell a b, Need.both _ h t => by
    rw [medeLoop]
    exact KS.bind' (KS.addOpsN _ (noSplit_cons rfl noSplit_nil)) fun _ _ =>
      KS.bind' (ks_medeLoop o a h) fun _ _ => ks_medeLoop o b t

theorem ks_forl (r o : Nat) : KSB (forl r o : CM Map (Nat × Nat)) := by
  unfold forl; ksb

theorem ks_doneBlocks : KSB (doneBlocks : CM Map (Nat × Nat)) := by
  unfold doneBlocks; ksb

/-! ## The lazy needs and the runs -/

/-! ## The arms of the lazy needs -/

mutual
theorem ks_splitLoop : ∀ (l : Lazy S) (o : Nat), KSB (splitLoop l o : CM Map (Lazy S × Lazy S))
  | mk s f b, o => by
    rw [splitLoop]
    refine KS.bind' (ks_splitSure s o) fun a _ => ?_
    rcases a with ⟨sh, st⟩
    refine KS.ite' _ (KS.pure' trivial) (KS.bind' (ks_splitForks f) fun x _ => ?_)
    rcases x with ⟨fh, ft⟩
    refine KS.bind' (ks_splitBonds b) fun y _ => ?_
    rcases y with ⟨bh, bt⟩
    exact KS.pure' trivial

theorem ks_splitForks : ∀ (l : List (ForkE S)), KSB (splitForks l : CM Map (List (ForkE S) × List (ForkE S)))
  | [] => by rw [splitForks]; exact KS.pure' trivial
  | ((oy, y), (on, n)) :: rest => by
    rw [splitForks]
    refine KS.bind' (ks_splitLoop y oy) fun a _ => ?_
    rcases a with ⟨yh, yt⟩
    refine KS.bind' (ks_splitLoop n on) fun b _ => ?_
    rcases b with ⟨nh, nt⟩
    refine KS.bind' (ks_splitForks rest) fun c _ => ?_
    rcases c with ⟨rh, rt⟩
    exact KS.pure' trivial

theorem ks_splitBonds : ∀ (l : List (Nat × Lazy S)),
    KSB (splitBonds l : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [] => by rw [splitBonds]; exact KS.pure' trivial
  | (o, l) :: rest => by
    rw [splitBonds]
    refine KS.bind' (ks_splitLoop l o) fun a _ => ?_
    rcases a with ⟨lh, lt⟩
    refine KS.bind' (ks_splitBonds rest) fun c _ => ?_
    rcases c with ⟨rh, rt⟩
    exact KS.pure' trivial
end

mutual
theorem ks_intoLoopL (axe : Nat) : ∀ (l : Lazy S) (o : Nat), KSB (intoLoopL axe l o : CM Map (Lazy S × Lazy S))
  | mk s f b, o => by
    rw [intoLoopL]
    refine KS.bind' (ks_intoSure axe s o) fun a _ => ?_
    rcases a with ⟨sd, sr⟩
    refine KS.ite' _ (KS.pure' trivial) (KS.bind' (ks_intoForks axe f) fun x _ => ?_)
    rcases x with ⟨fd, fr⟩
    refine KS.bind' (ks_intoBonds axe b) fun y _ => ?_
    rcases y with ⟨bd', br⟩
    exact KS.pure' trivial

theorem ks_intoForks (axe : Nat) : ∀ (l : List (ForkE S)),
    KSB (intoForks axe l : CM Map (List (ForkE S) × List (ForkE S)))
  | [] => by rw [intoForks]; exact KS.pure' trivial
  | ((oy, y), (on, n)) :: rest => by
    rw [intoForks]
    refine KS.bind' (ks_intoLoopL axe y oy) fun a _ => ?_
    rcases a with ⟨yd, yr⟩
    refine KS.bind' (ks_intoLoopL axe n on) fun b _ => ?_
    rcases b with ⟨nd, nr⟩
    refine KS.bind' (ks_intoForks axe rest) fun c _ => ?_
    rcases c with ⟨rd, rr⟩
    exact KS.pure' trivial

theorem ks_intoBonds (axe : Nat) : ∀ (l : List (Nat × Lazy S)),
    KSB (intoBonds axe l : CM Map (List (Nat × Lazy S) × List (Nat × Lazy S)))
  | [] => by rw [intoBonds]; exact KS.pure' trivial
  | (o, l) :: rest => by
    rw [intoBonds]
    refine KS.bind' (ks_intoLoopL axe l o) fun a _ => ?_
    rcases a with ⟨ld, lr⟩
    refine KS.bind' (ks_intoBonds axe rest) fun c _ => ?_
    rcases c with ⟨rd, rr⟩
    exact KS.pure' trivial
end

mutual
theorem ks_copyLazyL (o : Nat) : ∀ (a b : Lazy S), KSB (copyLazyL o a b : CM Map (Lazy S))
  | mk s1 f1 b1, second => by
    rw [copyLazyL]
    refine KS.bind' (ks_copyNeed _ _ _ noSplit_nil) fun a ha => ?_
    rcases a with ⟨ned, ops⟩
    refine KS.bind' (KS.addOpsN _ ha) fun _ _ => KS.bind' (P := fun _ => True) ?_ fun _ _ => KS.bind' (P := fun _ => True) ?_ fun _ _ => KS.pure' trivial
    · split
      · exact KS.pure' trivial
      · split
        · exact KS.pure' trivial
        · exact KS.bind' (ks_mergeForks _ f1) fun _ _ => KS.pure' trivial
    · split
      · exact KS.pure' trivial
      · split
        · exact KS.pure' trivial
        · exact KS.bind' (ks_mergeBonds _ b1) fun _ _ => KS.pure' trivial

theorem ks_mergeForks (idx : Map (ForkE S)) : ∀ (l : List (ForkE S)),
    KSB (mergeForks idx l : CM Map (List (ForkE S)))
  | [] => by rw [mergeForks]; exact KS.pure' trivial
  | ((oy, y), (on, n)) :: rest => by
    rw [mergeForks]
    refine KS.bind' (P := fun _ => True) ?_ fun _ _ => KS.bind' (ks_mergeForks idx rest) fun _ _ => KS.pure' trivial
    split
    · exact KS.pure' trivial
    · split
      · exact KS.bind' (ks_copyLazyL oy y _) fun _ _ => KS.bind' (ks_copyLazyL on n _) fun _ _ => KS.pure' trivial
      · exact KS.fail

theorem ks_mergeBonds (idx : Map (Nat × Lazy S)) : ∀ (l : List (Nat × Lazy S)),
    KSB (mergeBonds idx l : CM Map (List (Nat × Lazy S)))
  | [] => by rw [mergeBonds]; exact KS.pure' trivial
  | (ob, l) :: rest => by
    rw [mergeBonds]
    refine KS.bind' (P := fun _ => True) ?_ fun _ _ => KS.bind' (ks_mergeBonds idx rest) fun _ _ => KS.pure' trivial
    split
    · exact KS.pure' trivial
    · exact KS.bind' (ks_copyLazyL ob l _) fun _ _ => KS.pure' trivial
end

mutual
theorem ks_walkLazy {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, KSB (f o s)) :
    ∀ (o : Nat) (l : Lazy S), KSB (walkLazy f o l : CM Map Unit)
  | o, mk s fk bd => by
    rw [walkLazy]
    exact KS.bind' (hf o s) fun _ _ => KS.ite' _ (KS.pure' trivial)
      (KS.bind' (ks_walkForks hf fk) fun _ _ => ks_walkBonds hf bd)

theorem ks_walkForks {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, KSB (f o s)) :
    ∀ (l : List ((Nat × Lazy S) × (Nat × Lazy S))), KSB (walkForks f l : CM Map Unit)
  | [] => by rw [walkForks]; exact KS.pure' trivial
  | ((oy, y), (on, n)) :: rest => by
    rw [walkForks]
    exact KS.bind' (ks_walkLazy hf oy y) fun _ _ => KS.bind' (ks_walkLazy hf on n) fun _ _ =>
      ks_walkForks hf rest

theorem ks_walkBonds {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, KSB (f o s)) :
    ∀ (l : List (Nat × Lazy S)), KSB (walkBonds f l : CM Map Unit)
  | [] => by rw [walkBonds]; exact KS.pure' trivial
  | (o, l) :: rest => by
    rw [walkBonds]
    exact KS.bind' (ks_walkLazy hf o l) fun _ _ => ks_walkBonds hf rest
end

theorem ks_medeL (th : Jmp) (som : Noun) (laz : Lazy S) : KSB (medeL th som laz : CM Map Nat) := by
  unfold medeL
  refine KS.bind' (KS.emit' (by ksblk)) fun o _ => KS.getThen fun g => ?_
  refine KS.ite' _ (KS.pure' trivial) (KS.bind' (ks_walkLazy (fun o' sur => ?_) o laz) fun _ _ => KS.pure' trivial)
  exact KS.bind' (ks_sureRequireLook _) fun _ _ => ks_medeLoop _ _ _

theorem ks_collapseGate (r o oLaz : Nat) (sur : Sure S) : KSB (collapseGate r o oLaz sur : CM Map Unit) := by
  unfold collapseGate
  refine KS.bind' (ks_sureRequireLook _) fun ned _ => ?_
  split
  · exact KS.pure' trivial
  · exact KS.ite' _ (KS.pure' trivial) (KS.bind' (KS.ite' _ (KS.pure' trivial) (KS.proxy' _ _)) fun _ _ =>
      KS.addOps' _ (by ksblk))
  · exact KS.bind' (KS.ite' _ (KS.pure' trivial) (KS.proxy' _ _)) fun _ _ => ks_crashNeed _ _ _

theorem ks_collapseLazyAtomL (nex : NextL S) : KSB (collapseLazyAtomL nex : CM Map (Option (Nat × Nat))) := by
  unfold collapseLazyAtomL
  refine KS.ite' _ KS.fail (KS.ite' _ (KS.pure' trivial) (KS.bind' (ks_sureRequireLook _) fun ned _ => ?_))
  refine KS.bind' (P := fun _ => True) (by split <;> ksb) fun p _ => ?_
  rcases p with ⟨r, there⟩
  refine KS.getThen fun g => ?_
  exact KS.ite' _ (KS.pure' trivial)
    (KS.bind' (ks_walkLazy (fun o s => ks_collapseGate r there o s) _ _) fun _ _ => KS.pure' trivial)

theorem ks_kern (o : Nat) (laz : Lazy S) : KSB (kern o laz : CM Map Nat) := by
  unfold kern
  refine KS.bind' KS.re' fun r _ => KS.getThen fun g => ?_
  refine KS.ite' _ (KS.pure' trivial) (KS.bind' (ks_walkLazy (fun oLaz sur => ?_) o laz) fun _ _ => KS.pure' trivial)
  refine KS.bind' (ks_sureRequireLook _) fun ned _ => KS.ite' _ (KS.pure' trivial) ?_
  refine KS.bind' (KS.ite' _ (KS.pure' trivial) (KS.proxy' _ _)) fun src _ => KS.ite' _ KS.fail ?_
  exact KS.bind' (ks_kernNeed _ _) fun ops hops => KS.addOps' _ hops

theorem ks_kerf (nex : NextL S) : KSB (kerf nex : CM Map (Nat × Nat)) := by
  unfold kerf
  exact KS.bind' (KS.emit' (by ksblk)) fun _ _ => KS.bind' (ks_kern _ _) fun _ _ => KS.pure' trivial

theorem ks_lazyShut (o : Nat) (laz : Lazy S) : KSB (lazyShut o laz : CM Map (Lazy S)) := by
  unfold lazyShut
  exact KS.ite' _ (KS.pure' trivial) (KS.bind' (ks_kern _ _) fun _ _ => KS.pure' trivial)

theorem ks_pastL (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat) :
    KSB (pastL cod nex nom region : CM Map (NextL S)) := by
  unfold pastL; ksb

theorem ks_simpleNextL (goal : CGoalL S) : KSB (simpleNextL goal : CM Map (NextL S)) := by
  unfold simpleNextL; ksb

theorem ks_bombL (miss : Option Nat) : KSB (bombL miss : CM Map (NextL S)) := by unfold bombL; ksb

theorem ks_splitL (nex : NextL S) : KSB (splitL nex : CM Map (Lazy S × Lazy S × Nat)) := by
  unfold splitL
  refine KS.bind' (KS.emit' (by ksblk)) fun o _ => KS.bind' (ks_splitLoop _ _) fun a _ => ?_
  rcases a with ⟨h, t⟩
  exact KS.pure' trivial

theorem ks_intoL (nex : NextL S) (axe : Nat) : KSB (intoL nex axe : CM Map (Lazy S × Lazy S × Nat)) := by
  unfold intoL
  refine KS.bind' (KS.emit' (by ksblk)) fun o _ => KS.bind' (ks_intoLoopL _ _ _) fun a _ => ?_
  rcases a with ⟨d, r⟩
  exact KS.pure' trivial

theorem ks_copyL (first : NextL S) (second : Lazy S) : KSB (copyL first second : CM Map (NextL S)) := by
  unfold copyL
  exact KS.bind' (KS.emit' (by ksblk)) fun _ _ => KS.bind' (ks_copyLazyL _ _ _) fun _ _ => KS.pure' trivial

theorem ks_callL (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)} (p q : Nomm)
    (sup : Option Nomm) (hp : ∀ g r, KSB (rp g r)) (hq : ∀ g r, KSB (rq g r)) (goal : CGoalL S)
    (region : List Nat) : KSB (callL env rp rq p q Option.none sup goal region : CM Map (NextL S)) := by
  unfold callL
  refine KS.bind' (ks_simpleNextL _) fun nex _ => KS.bind' (ks_kerf _) fun a _ => ?_
  rcases a with ⟨out, pro⟩
  exact KS.bind' KS.re' fun _ _ => KS.bind' KS.re' fun _ _ => KS.bind' (KS.emit' (by ksblk)) fun _ _ =>
    KS.bind' (hq _ _) fun _ _ => KS.bind' (ks_pastL _ _ _ _) fun _ _ => KS.bind' (hp _ _) fun _ _ =>
      ks_copyL _ _

variable [HoonMapKeys Map]

/-- **`runLC` on `PlainN` keeps `SDS`**, for every goal. -/
theorem ks_runLC (env : CallEnv) : ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm) (goal : CGoalL S)
    (region : List Nat), KSB (runLC (Map := Map) env sup nm goal region)
  | Nomm.cons p q, h, sup, goal, region => by
    unfold runLC
    refine KS.bind' (P := fun _ => True) (by cases goal <;> dsimp only <;> ksb) fun goal' _ => ?_
    cases goal' <;> dsimp only
    · exact KS.bind' (KS.emit' (by ksblk)) fun _ _ => KS.bind' (ks_runLC env q h.2 _ _ _) fun _ _ =>
        KS.bind' (ks_pastL _ _ _ _) fun _ _ => KS.bind' (ks_runLC env p h.1 _ _ _) fun _ _ => ks_copyL _ _
    · exact KS.fail
    · refine KS.bind' (ks_splitL _) fun a _ => ?_
      rcases a with ⟨hed, tel, o⟩
      exact KS.bind' (ks_pastL _ _ _ _) fun _ _ => KS.bind' (ks_runLC env q h.2 _ _ _) fun _ _ =>
        KS.bind' (ks_pastL _ _ _ _) fun _ _ => KS.bind' (ks_runLC env p h.1 _ _ _) fun _ _ => ks_copyL _ _
  | Nomm.n0 ax, _, sup, goal, region => by
    unfold runLC
    refine KS.ite' _ (ks_bombL _) (KS.bind' (ks_simpleNextL _) fun nex _ => KS.ite' _ (KS.pure' trivial) ?_)
    cases fromL ax nex.laz
    · exact KS.fail
    · exact KS.pure' trivial
  | Nomm.n1 k, _, sup, goal, region => by
    unfold runLC
    cases goal <;> dsimp only
    · exact KS.ite' _ (KS.pure' trivial) (KS.ite' _ (KS.pure' trivial) (ks_bombL _))
    · exact KS.bind' KS.re' fun _ _ => KS.bind' (KS.emit' (by ksblk)) fun _ _ => KS.pure' trivial
    · exact KS.bind' (ks_medeL _ _ _) fun _ _ => KS.pure' trivial
  | Nomm.n3 p, h, sup, goal, region => by
    unfold runLC
    have ih := ks_runLC env p h
    cases goal <;> dsimp only
    · exact KS.bind' KS.re' fun _ _ => KS.bind' (KS.emit' (by ksblk)) fun _ _ => ih _ _ _
    · exact KS.bind' ks_doneBlocks fun _ _ => KS.bind' KS.re' fun _ _ => KS.bind' (KS.emit' (by ksblk)) fun _ _ =>
        ih _ _ _
    · refine KS.ite' _ (ih _ _ _) (KS.bind' (ks_collapseLazyAtomL _) fun a _ => ?_)
      cases a
      · exact KS.fail
      · exact KS.bind' (ks_forl _ _) fun _ _ => KS.bind' KS.re' fun _ _ => KS.bind' (KS.emit' (by ksblk)) fun _ _ =>
          ih _ _ _
  | Nomm.n4 p, h, sup, goal, region => by
    unfold runLC
    have ih := ks_runLC env p h
    cases goal <;> dsimp only
    · exact KS.bind' KS.re' fun _ _ => KS.bind' KS.re' fun _ _ => KS.bind' (KS.emit' (by ksblk)) fun _ _ => ih _ _ _
    · exact KS.bind' KS.re' fun _ _ => KS.bind' KS.re' fun _ _ => KS.bind' (KS.emit' (by ksblk)) fun _ _ => ih _ _ _
    · refine KS.bind' (ks_collapseLazyAtomL _) fun a _ => KS.bind' (P := fun _ => True) ?_ fun _ _ => ?_
      · cases a <;> dsimp only
        · exact KS.bind' KS.re' fun _ _ => KS.ite' _ (KS.pure' trivial) KS.fail
        · exact KS.pure' trivial
      · exact KS.bind' KS.re' fun _ _ => KS.bind' (KS.emit' (by ksblk)) fun _ _ => ih _ _ _
  | Nomm.n5 p q, h, sup, goal, region => by
    unfold runLC
    refine KS.bind' KS.re' fun _ _ => KS.bind' KS.re' fun _ _ => KS.bind' (P := fun _ => True) ?_ fun _ _ =>
      KS.bind' (ks_runLC env q h.2 _ _ _) fun _ _ => KS.bind' (ks_pastL _ _ _ _) fun _ _ =>
        KS.bind' (ks_runLC env p h.1 _ _ _) fun _ _ => ks_copyL _ _
    cases goal <;> dsimp only
    · exact KS.emit' (by ksblk)
    · exact KS.bind' ks_doneBlocks fun _ _ => KS.emit' (by ksblk)
    · refine KS.bind' (ks_collapseLazyAtomL _) fun a _ => ?_
      cases a <;> dsimp only
      · exact KS.ite' _ (KS.emit' (by ksblk)) KS.fail
      · exact KS.bind' (ks_forl _ _) fun _ _ => KS.emit' (by ksblk)
  | Nomm.n7 p q, h, sup, goal, region => by
    unfold runLC
    exact KS.bind' (ks_runLC env q h.2 _ _ _) fun _ _ => ks_runLC env p h.1 _ _ _
  | Nomm.n10 a v q, h, sup, goal, region => by
    unfold runLC
    refine KS.bind' (ks_simpleNextL _) fun _ _ => KS.bind' (ks_intoL _ _) fun x _ => ?_
    rcases x with ⟨don, rec, o⟩
    exact KS.bind' (ks_pastL _ _ _ _) fun _ _ => KS.bind' (ks_runLC env v h.1 _ _ _) fun _ _ =>
      KS.bind' (ks_pastL _ _ _ _) fun _ _ => KS.bind' (ks_runLC env q h.2 _ _ _) fun _ _ => ks_copyL _ _
  | Nomm.n2 p q Option.none, h, sup, goal, region => by
    unfold runLC
    exact ks_callL env p q sup (fun g r => ks_runLC env p h.1 _ _ _) (fun g r => ks_runLC env q h.2 _ _ _)
      goal region

/-! ## The top -/

theorem sds_gen0 : SDS (gen0 : Comp.Gen Map) := by
  intro o b hb
  simp [gen0, HoonMap.get_empty] at hb

/-- **Track G's body-local leaf on `PlainN`.** -/
theorem splitDefEnd_plain {env : CallEnv} : SplitDefEnd S Map env := by
  intro nm hp nex g1 g2 o sub h1 h2
  have s1 := ((ks_runLC (S := S) (Map := Map) env nm hp Option.none CGoalL.done []).k _ _ _ sds_gen0 h1).1
  exact ((ks_kerf nex).k _ _ _ s1 h2).1

/-- **`EntryMono` on `PlainM` from `KIMid` alone.** -/
theorem entryMono_plainK [Opt.MapKeys Map] (lib : Lib) (hD : ∀ env, KIMid S Map env) :
    EntryMono S Map lib PlainM :=
  entryMono_plainE lib hD fun env => splitDefEnd_plain

end Glue
end SkaModel
end Formalization
