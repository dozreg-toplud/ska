import lemmas.Glue.GuardFrag

/-!
# `KP` of the lazy arms that `FragX` reaches (track G, step 3 of `GuardMonoX`)

On `FragX` every goal is fork-free, so the arms `+split`, `+into`,
`+collapse-lazy-atom`, `+mede`, `+past` and `+simple-next` of `runL` are
the sure arms (`splitL_mk`, `intoL_mk`, ... of `CompLazyAgree.lean`) mapped
into lazy needs (`KP.map'`).  What is left: `+copy` of a lazy need with
forks (`kp_copyLazyL`: only moves, at the root and at each merged fork or
bond, the text of track D's `qm_copyLazyL`), and `+fork-sure` (its two fork
blocks pass `(flattenNeed n).map some`, no `~`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `<$>`: the result is the image of one in `P`. -/
theorem KP.map' {α β : Type} {P : α → Prop} {m : CM Map α} (f : α → β) (h : KP P m) :
    KP (fun y => ∃ x, P x ∧ y = f x) (f <$> m) := by
  constructor
  intro g y g' hb e
  rw [map_apply] at e
  obtain ⟨⟨x, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp e
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨b1, px⟩ := h.k g x g1 hb h1
  exact ⟨b1, x, px, rfl⟩

theorem jok_mapSome (l : List Nat) : JOK ⟨l.map some, 0⟩ := by simp [JOK]

theorem jok_mapSome' (l : List Nat) (t : Nat) : JOK ⟨l.map some, t⟩ := by simp [JOK]

mutual
theorem kp_copyLazyL (o : Nat) : ∀ (a b : Lazy S), KB (copyLazyL o a b : CM Map (Lazy S))
  | mk s1 f1 b1, second => by
    rw [copyLazyL]
    refine KP.bind' (kp_copyNeed _ _ _ noSplit_nil) fun a ha => ?_
    rcases a with ⟨ned, ops⟩
    refine KP.bind' (KP.addOps' _ ha) fun _ _ => KP.bind' (P := fun _ => True) ?_ fun _ _ =>
      KP.bind' (P := fun _ => True) ?_ fun _ _ => KP.pure' trivial
    · split
      · exact KP.pure' trivial
      · split
        · exact KP.pure' trivial
        · exact KP.bind' (kp_mergeForks _ f1) fun _ _ => KP.pure' trivial
    · split
      · exact KP.pure' trivial
      · split
        · exact KP.pure' trivial
        · exact KP.bind' (kp_mergeBonds _ b1) fun _ _ => KP.pure' trivial

theorem kp_mergeForks (idx : Map (ForkE S)) : ∀ (l : List (ForkE S)),
    KB (mergeForks idx l : CM Map (List (ForkE S)))
  | [] => by rw [mergeForks]; exact KP.pure' trivial
  | ((oy, y), (on, n)) :: rest => by
    rw [mergeForks]
    refine KP.bind' (P := fun _ => True) ?_ fun _ _ => KP.bind' (kp_mergeForks idx rest) fun _ _ => KP.pure' trivial
    split
    · exact KP.pure' trivial
    · split
      · exact KP.bind' (kp_copyLazyL oy y _) fun _ _ => KP.bind' (kp_copyLazyL on n _) fun _ _ => KP.pure' trivial
      · exact KP.fail

theorem kp_mergeBonds (idx : Map (Nat × Lazy S)) : ∀ (l : List (Nat × Lazy S)),
    KB (mergeBonds idx l : CM Map (List (Nat × Lazy S)))
  | [] => by rw [mergeBonds]; exact KP.pure' trivial
  | (ob, l) :: rest => by
    rw [mergeBonds]
    refine KP.bind' (P := fun _ => True) ?_ fun _ _ => KP.bind' (kp_mergeBonds idx rest) fun _ _ => KP.pure' trivial
    split
    · exact KP.pure' trivial
    · exact KP.bind' (kp_copyLazyL ob l _) fun _ _ => KP.pure' trivial
end

/-- **`+copy` of a lazy need, forks and all.** -/
theorem kp_copyL {first : NextL S} (hth : JOK first.th) (second : Lazy S) :
    KP (fun n : NextL S => JOK n.th) (copyL first second : CM Map (NextL S)) := by
  unfold copyL
  refine KP.bind' (KP.emit' (blockOK_of (by simpa [getJmps] using hth) noSplit_nil)) fun o _ => ?_
  exact KP.bind' (kp_copyLazyL _ _ _) fun _ _ => KP.pure' (jok_jmp0 _)

theorem kp_forkNeedGo : ∀ (ned : Need), KB (forkNeedGo ned : CM Map (Need × Need))
  | Need.none => by rw [forkNeedGo]; exact KP.pure' trivial
  | Need.this _ => by rw [forkNeedGo]; kpb
  | Need.pair p q => by
    rw [forkNeedGo]
    exact KP.bind' (kp_forkNeedGo p) fun x _ => by
      obtain ⟨h0, h1⟩ := x
      exact KP.bind' (kp_forkNeedGo q) fun y _ => by obtain ⟨t0, t1⟩ := y; exact KP.pure' trivial
  | Need.both _ h t => by
    rw [forkNeedGo]
    refine KP.bind' KP.re' fun _ _ => KP.bind' KP.re' fun _ _ => ?_
    exact KP.bind' (kp_forkNeedGo h) fun x _ => by
      obtain ⟨h0, h1⟩ := x
      exact KP.bind' (kp_forkNeedGo t) fun y _ => by obtain ⟨t0, t1⟩ := y; exact KP.pure' trivial

/-- **`+fork-sure`**: the join block hops with no argument, the two fork
blocks pass registers. -/
theorem kp_forkSure (sur : Sure S) (o o0 o1 : Nat) : KB (forkSure sur o o0 o1 : CM Map (Sure S × Sure S)) := by
  unfold forkSure forkNeed
  refine KP.bind' (P := fun _ => True) (KP.bind' (kp_forkNeedGo _) fun x _ => ?_) fun y _ => ?_
  · obtain ⟨n0, n1⟩ := x
    refine KP.bind' (KP.emit' (blockOK_of (by simp [getJmps, JOK, jmp0]) noSplit_nil)) fun barg _ => ?_
    refine KP.bind' (KP.emir' _ (blockOK_of (by simp [getJmps, JOK]) noSplit_nil)) fun _ _ => ?_
    exact KP.bind' (KP.emir' _ (blockOK_of (by simp [getJmps, JOK]) noSplit_nil)) fun _ _ => KP.pure' trivial
  · obtain ⟨n0, n1⟩ := y
    exact KP.pure' trivial

end Glue
end SkaModel
end Formalization
