import lemmas.Ska.SccLoopSoft

/-! # Without soft calls, `runLCS` is `runLC` (README Gaps 21.15)

`SimS m n`: from every state with an empty `soft.gen`, the step `m` of `CMS` does what the step
`n` of `CM` does, and leaves `soft.gen` empty.  The arms of `+comp` that read `soft.gen` are
`SimS` to the model's (`kernS_sim`, `lazyShutS_sim`, `kerfS_sim`, the arms of `%6`), and so is
`callLS` when `sof` is false at its call; **`runLCS_eq`**: with `sof` false at every call,
`runLCS env snd` is `SimS` to `runLC env` (`runLC` of `Ska/CompRunLC.lean` is not changed);
**`memDoneMS_eq`**: then `memDoneMS` is `memDoneM`. -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- A product of `CM` in `CMS`, `soft.gen` empty. -/
def embS {α : Type} (p : α × Gen Map) : α × GenSf Map := (p.1, GenSf.ofGen p.2)

/-- **`m` does what `n` does from every state with an empty `soft.gen`.** -/
def SimS {α : Type} (m : CMS Map α) (n : CM Map α) : Prop :=
  ∀ g, m (GenSf.ofGen g) = (n g).map embS

theorem simS_liftS {α : Type} (n : CM Map α) : SimS (liftS n) n := fun _ => rfl

theorem simS_pure {α : Type} (a : α) : SimS (pure a : CMS Map α) (pure a) := fun _ => rfl

theorem simS_none {α : Type} : SimS (fun _ => Option.none : CMS Map α) (fun _ => Option.none) := fun _ => rfl

theorem simS_bind {α β : Type} {m : CMS Map α} {n : CM Map α} {f : α → CMS Map β} {k : α → CM Map β}
    (hm : SimS m n) (hf : ∀ a, SimS (f a) (k a)) : SimS (m >>= f) (n >>= k) := by
  intro g
  show (m (GenSf.ofGen g)).bind _ = ((n g).bind _).map embS
  rw [hm g]
  cases n g with
  | none => rfl
  | some p => exact hf p.1 p.2

theorem simS_bind2 {α₁ α₂ β : Type} {m : CMS Map (α₁ × α₂)} {n : CM Map (α₁ × α₂)}
    {f : α₁ × α₂ → CMS Map β} {k : α₁ × α₂ → CM Map β}
    (hm : SimS m n) (hf : ∀ a b, SimS (f (a, b)) (k (a, b))) : SimS (m >>= f) (n >>= k) :=
  simS_bind hm fun ⟨a, b⟩ => hf a b

theorem simS_bind3 {α₁ α₂ α₃ β : Type} {m : CMS Map (α₁ × α₂ × α₃)} {n : CM Map (α₁ × α₂ × α₃)}
    {f : α₁ × α₂ × α₃ → CMS Map β} {k : α₁ × α₂ × α₃ → CM Map β}
    (hm : SimS m n) (hf : ∀ a b c, SimS (f (a, b, c)) (k (a, b, c))) : SimS (m >>= f) (n >>= k) :=
  simS_bind hm fun ⟨a, b, c⟩ => hf a b c

theorem simS_get {α : Type} {f : GenSf Map → CMS Map α} {k : Gen Map → CM Map α}
    (h : ∀ g, SimS (f (GenSf.ofGen g)) (k g)) : SimS (get >>= f) (get >>= k) := fun g => h g g

theorem simS_ite {α : Type} (c : Prop) [Decidable c] {a b : CMS Map α} {a' b' : CM Map α}
    (ha : SimS a a') (hb : SimS b b') : SimS (if c then a else b) (if c then a' else b') := by
  by_cases h : c <;> simp [h, ha, hb]

theorem isSoft_ofGen (g : Gen Map) : (GenSf.ofGen g).isSoft = noSoft := by
  funext o; simp [GenSf.isSoft, GenSf.ofGen, HoonMap.get_empty, noSoft]

theorem simS_withSoft {α : Type} {k : (Nat → Bool) → CMS Map α} {n : CM Map α}
    (h : SimS (k noSoft) n) : SimS (withSoft k) n := by
  intro g
  show k (GenSf.ofGen g).isSoft (GenSf.ofGen g) = _
  rw [isSoft_ofGen]; exact h g

mutual
theorem softFork_noSoftS (u : Need → Bool) : ∀ (l : Lazy S), softFork noSoft u l = false
  | mk _ f b => by
    unfold softFork; rw [softForkBonds_noSoftS u b, softForkForks_noSoftS u f]; rfl

theorem softForkBonds_noSoftS (u : Need → Bool) : ∀ (b : List (Nat × Lazy S)), softForkBonds noSoft u b = false
  | [] => rfl
  | (o, l) :: rest => by
    unfold softForkBonds; rw [softFork_noSoftS u l, softForkBonds_noSoftS u rest]; simp [noSoft]

theorem softForkForks_noSoftS (u : Need → Bool) :
    ∀ (f : List ((Nat × Lazy S) × (Nat × Lazy S))), softForkForks noSoft u f = false
  | [] => rfl
  | ((_, a), (_, b)) :: rest => by
    unfold softForkForks; rw [softFork_noSoftS u a, softFork_noSoftS u b, softForkForks_noSoftS u rest]; rfl
end

mutual
theorem walkLazyS_sim {f' : Nat → Sure S → CMS Map Unit} {f : Nat → Sure S → CM Map Unit}
    (hf : ∀ o s, SimS (f' o s) (f o s)) : ∀ (o : Nat) (l : Lazy S), SimS (walkLazyS f' o l) (walkLazy f o l)
  | o, mk s fk bd => by
    unfold walkLazyS walkLazy
    refine simS_bind (hf o s) fun _ => ?_
    exact simS_ite _ (simS_pure _) (simS_bind (walkForksS_sim hf fk) fun _ => walkBondsS_sim hf bd)

theorem walkForksS_sim {f' : Nat → Sure S → CMS Map Unit} {f : Nat → Sure S → CM Map Unit}
    (hf : ∀ o s, SimS (f' o s) (f o s)) :
    ∀ (fk : List ((Nat × Lazy S) × (Nat × Lazy S))), SimS (walkForksS f' fk) (walkForks f fk)
  | [] => simS_pure _
  | ((oy, y), (on, n)) :: rest => by
    unfold walkForksS walkForks
    exact simS_bind (walkLazyS_sim hf oy y) fun _ => simS_bind (walkLazyS_sim hf on n) fun _ =>
      walkForksS_sim hf rest

theorem walkBondsS_sim {f' : Nat → Sure S → CMS Map Unit} {f : Nat → Sure S → CM Map Unit}
    (hf : ∀ o s, SimS (f' o s) (f o s)) : ∀ (bd : List (Nat × Lazy S)), SimS (walkBondsS f' bd) (walkBonds f bd)
  | [] => simS_pure _
  | (o, l) :: rest => by
    unfold walkBondsS walkBonds
    exact simS_bind (walkLazyS_sim hf o l) fun _ => walkBondsS_sim hf rest
end

theorem kernS_sim (o : Nat) (laz : Lazy S) : SimS (kernS (Map := Map) o laz) (kern o laz) := by
  unfold kernS kern
  refine simS_bind (simS_liftS _) fun r => simS_get fun g => simS_ite _ (simS_pure _) ?_
  refine simS_bind (walkLazyS_sim (fun oLaz sur => ?_) o laz) fun _ => simS_pure _
  refine simS_bind (simS_liftS _) fun ned => simS_ite _ (simS_pure _) ?_
  refine simS_bind (simS_ite _ (simS_pure _) (simS_liftS _)) fun src => simS_withSoft ?_
  rw [if_neg (by simp [noSoft]), if_neg (by simp [noSoft])]
  exact simS_bind (simS_liftS _) fun _ => simS_liftS _

theorem lazyShutS_sim (o : Nat) (laz : Lazy S) : SimS (lazyShutS (Map := Map) o laz) (lazyShut o laz) := by
  unfold lazyShutS lazyShut
  exact simS_withSoft (simS_ite _ (simS_pure _) (simS_bind (kernS_sim o laz) fun _ => simS_pure _))

theorem kerfS_sim (nex : NextL S) : SimS (kerfS (Map := Map) nex) (kerf nex) := by
  unfold kerfS kerf
  exact simS_bind (simS_liftS _) fun o => simS_bind (kernS_sim o nex.laz) fun _ => simS_pure _

theorem simS_pure_bind {α β : Type} (a : α) {f : α → CMS Map β} {k : α → CM Map β}
    (h : SimS (f a) (k a)) : SimS (pure a >>= f) (pure a >>= k) := fun g => h g

theorem simS_bind_pure {α : Type} {m : CMS Map α} {n : CM Map α} {f : α → CMS Map α}
    (hm : SimS m n) (hf : ∀ a, SimS (f a) (pure a)) : SimS (m >>= f) n := by
  have := simS_bind (k := pure) hm hf
  rwa [bind_pure] at this

theorem simS_bind_left {α β : Type} {m : CMS Map α} {a : α} {f : α → CMS Map β} {n : CM Map β}
    (hm : SimS m (pure a)) (hf : SimS (f a) n) : SimS (m >>= f) n := by
  intro g
  show (m (GenSf.ofGen g)).bind _ = _
  rw [hm g]; exact hf g

variable [HoonMapKeys Map]

theorem sixNextForkCS_sim (cod : Bell → Option Bool) {rp' rq' rr' : CGoalL S → List Nat → CMS Map (NextL S)}
    {rp rq rr : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : ∀ g r, SimS (rp' g r) (rp g r)) (hq : ∀ g r, SimS (rq' g r) (rq g r)) (hr : ∀ g r, SimS (rr' g r) (rr g r))
    (p : Nomm) (laz : Lazy S) (th : Jmp) (region : List Nat) :
    SimS (sixNextForkCS cod rp' rq' rr' p laz th region) (sixNextForkC cod rp rq rr p laz th region) := by
  unfold sixNextForkCS sixNextForkC
  exact simS_bind (simS_liftS _) fun rCond => simS_bind2 (simS_liftS _) fun g0 g1 =>
    simS_bind (simS_liftS _) fun rid => simS_bind (simS_liftS _) fun cb =>
    simS_bind (hr _ _) fun nex1 => simS_bind (simS_liftS _) fun cbt => simS_bind (hq _ _) fun nex0 =>
    simS_bind3 (simS_liftS _) fun lazy yes nuh => simS_bind (simS_liftS _) fun lazy =>
    simS_bind (simS_liftS _) fun o => simS_bind (lazyShutS_sim _ _) fun lazy =>
    simS_bind (hp _ _) fun nexCond => simS_liftS _

theorem sixNextSimpleCS_sim (cod : Bell → Option Bool) {rp' rq' rr' : CGoalL S → List Nat → CMS Map (NextL S)}
    {rp rq rr : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : ∀ g r, SimS (rp' g r) (rp g r)) (hq : ∀ g r, SimS (rq' g r) (rq g r)) (hr : ∀ g r, SimS (rr' g r) (rr g r))
    (p : Nomm) (laz : Lazy S) (th : Jmp) (region : List Nat) :
    SimS (sixNextSimpleCS cod rp' rq' rr' p laz th region) (sixNextSimpleC cod rp rq rr p laz th region) := by
  unfold sixNextSimpleCS sixNextSimpleC
  exact simS_bind (simS_liftS _) fun o0 => simS_bind (simS_liftS _) fun o1 =>
    simS_bind2 (simS_liftS _) fun s0 s1 => simS_bind (simS_liftS _) fun rid =>
    simS_bind (simS_liftS _) fun cb => simS_bind (hr _ _) fun nex1 => simS_bind (simS_liftS _) fun cbt =>
    simS_bind (hq _ _) fun nex0 => simS_bind3 (simS_liftS _) fun lazy yes nuh =>
    simS_bind (simS_liftS _) fun lazy => simS_bind (hp _ _) fun nexCond =>
    simS_withSoft (simS_ite _ (simS_liftS _) (simS_bind (simS_liftS _) fun o =>
      simS_bind (lazyShutS_sim _ _) fun lazy => simS_liftS _))

theorem sixNextLCS_sim (cod : Bell → Option Bool) (snd : Nomm → NeedOrd → Bool)
    {rp' rq' rr' : CGoalL S → List Nat → CMS Map (NextL S)}
    {rp rq rr : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : ∀ g r, SimS (rp' g r) (rp g r)) (hq : ∀ g r, SimS (rq' g r) (rq g r)) (hr : ∀ g r, SimS (rr' g r) (rr g r))
    (p q r : Nomm) : ∀ (fuel : Nat) (laz : Lazy S) (th : Jmp) (region : List Nat),
    SimS (sixNextLCS cod snd rp' rq' rr' p q r fuel laz th region) (sixNextLC cod rp rq rr p q r fuel laz th region)
  | 0, _, _, _ => simS_none
  | fuel + 1, laz, th, region => by
    rw [sixNextLCS, sixNextLC]
    split
    · next h => rw [h]; exact simS_none
    · next rest bys h =>
      rw [h]
      exact simS_bind (sixNextLCS_sim cod snd hp hq hr p q r fuel rest th region) fun _ => simS_liftS _
    · next h =>
      rw [h]
      refine simS_ite _ (simS_withSoft ?_) (sixNextSimpleCS_sim cod hp hq hr p laz th region)
      rw [softFork_noSoftS, softFork_noSoftS]
      exact simS_ite _ (simS_bind2 (kerfS_sim _) fun _ _ => sixNextLCS_sim cod snd hp hq hr p q r fuel _ _ _)
        (sixNextForkCS_sim cod hp hq hr p laz th region)

theorem callLS_sim (env : CallEnv) {rp' rq' : CGoalL S → List Nat → CMS Map (NextL S)}
    {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : ∀ g r, SimS (rp' g r) (rp g r)) (hq : ∀ g r, SimS (rq' g r) (rq g r))
    (p q : Nomm) (info : Option (Bell × Option Noun)) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat)
    (hsof : ∀ b n, env.sof (made p sup) p q b n = false) :
    SimS (callLS env rp' rq' p q info sup goal region) (callL env rp rq p q info sup goal region) := by
  unfold callLS callL
  rcases info with _ | ⟨b, key⟩
  · exact simS_bind (simS_liftS _) fun nex => simS_bind2 (kerfS_sim _) fun out pro =>
      simS_bind (simS_liftS _) fun rSub => simS_bind (simS_liftS _) fun rFol =>
      simS_bind (simS_liftS _) fun o => simS_bind (hq _ _) fun nexFol =>
      simS_bind (simS_liftS _) fun nexFol => simS_bind (hp _ _) fun nexSub => simS_liftS _
  · have hdrop : ∀ th, SimS (Map := Map) (do
        let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
          else rq' (CGoalL.next (ofSure Sure.bunt) th) region : CMS Map (NextL S))
        let nexFol ← liftS (pastL env.cod nexFol p region)
        let nexSub ← rp' (CGoalL.next (ofSure Sure.bunt) nexFol.th) region
        liftS (copyL nexSub nexFol.laz)) (do
        let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
          else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
        let nexFol ← pastL env.cod nexFol p region
        let nexSub ← rp (CGoalL.next (ofSure Sure.bunt) nexFol.th) region
        copyL nexSub nexFol.laz) := fun th =>
      simS_bind (simS_ite _ (simS_pure _) (hq _ _)) fun nexFol => simS_bind (simS_liftS _) fun nexFol =>
        simS_bind (hp _ _) fun nexSub => simS_liftS _
    have hrest : ∀ (c : Nat) (sn : Need), SimS (Map := Map) (do
        let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, (jmp0 c)⟩
          else rq' (CGoalL.next (ofSure Sure.bunt) (jmp0 c)) region : CMS Map (NextL S))
        let nexFol ← liftS (pastL env.cod nexFol p region)
        let nexSub ← rp' (CGoalL.next (ofSure ⟨sn, HoonSet.empty⟩) nexFol.th) region
        liftS (copyL nexSub nexFol.laz)) (do
        let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, (jmp0 c)⟩
          else rq (CGoalL.next (ofSure Sure.bunt) (jmp0 c)) region : CM Map (NextL S))
        let nexFol ← pastL env.cod nexFol p region
        let nexSub ← rp (CGoalL.next (ofSure ⟨sn, HoonSet.empty⟩) nexFol.th) region
        copyL nexSub nexFol.laz) := fun c sn =>
      simS_bind (simS_ite _ (simS_pure _) (hq _ _)) fun nexFol => simS_bind (simS_liftS _) fun nexFol =>
        simS_bind (hp _ _) fun nexSub => simS_liftS _
    cases goal with
    | next laz th =>
      by_cases hc : (env.pure b && noneEquivalentL laz) = true
      · simp only [hc, if_true]; exact hdrop th
      · simp only [hc, Bool.false_eq_true, if_false]
        rcases key with _ | k
        · rcases hr : env.ring b with _ | rg
          · rcases hn : env.need b with _ | bNed
            · exact simS_none
            · simp only [hsof, Bool.false_eq_true, if_false]
              refine simS_bind (simS_liftS _) fun sn => ?_
              refine simS_bind (simS_bind (simS_liftS _) fun nex => simS_bind2 (kerfS_sim _) fun out pro =>
                simS_bind_pure (simS_liftS _) fun o => ?_) fun c => ?_
              · exact fun _ => rfl
              · refine simS_bind_left (a := (⟨ofSure ⟨sn, HoonSet.empty⟩, jmp0 c⟩ : NextL S)) (simS_withSoft ?_) ?_
                · rw [if_neg (by simp [noSoft])]; exact simS_pure _
                · exact hrest c sn
          · exact simS_none
        · exact simS_none
    | done =>
      simp only []
      rcases key with _ | k
      · rcases hr : env.ring b with _ | rg
        · rcases hn : env.need b with _ | bNed
          · exact simS_none
          · simp only [hsof, Bool.false_eq_true, if_false]
            refine simS_bind (simS_liftS _) fun sn => ?_
            refine simS_bind (simS_bind_pure (simS_liftS _) fun o => ?_) fun c => ?_
            · exact fun _ => rfl
            · refine simS_bind_left (a := (⟨ofSure ⟨sn, HoonSet.empty⟩, jmp0 c⟩ : NextL S)) (simS_withSoft ?_) ?_
              · rw [if_neg (by simp [noSoft])]; exact simS_pure _
              · exact hrest c sn
        · exact simS_none
      · exact simS_none
    | pick z o =>
      simp only []
      rcases key with _ | k
      · rcases hr : env.ring b with _ | rg
        · rcases hn : env.need b with _ | bNed
          · exact simS_none
          · simp only [hsof, Bool.false_eq_true, if_false]
            refine simS_bind (simS_liftS _) fun sn => ?_
            refine simS_bind (simS_bind (simS_liftS _) fun nex => simS_bind2 (kerfS_sim _) fun out pro =>
                simS_bind_pure (simS_liftS _) fun o => ?_) fun c => ?_
            · exact fun _ => rfl
            · refine simS_bind_left (a := (⟨ofSure ⟨sn, HoonSet.empty⟩, jmp0 c⟩ : NextL S)) (simS_withSoft ?_) ?_
              · rw [if_neg (by simp [noSoft])]; exact simS_pure _
              · exact hrest c sn
        · exact simS_none
      · exact simS_none

/-- **Without soft calls, `runLCS` is `runLC`**: with `sof` false at every call, from a state
with an empty `soft.gen`, `runLCS env snd` gives what `runLC env` gives and leaves `soft.gen`
empty (`snd` is then never read). -/
theorem runLCS_sim (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    (hsof : ∀ m p q b n, env.sof m p q b n = false) :
    ∀ (nm : Nomm) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat),
      SimS (runLCS (Map := Map) env snd sup nm goal region) (runLC env sup nm goal region) := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro sup goal region
    simp only [runLCS, runLC]
    refine simS_bind ?_ fun g' => ?_
    · cases goal with
      | done => exact simS_bind (simS_liftS _) fun r => simS_bind (simS_liftS _) fun o => simS_pure (Map := Map) _
      | pick _ _ => exact simS_pure _
      | next _ _ => exact simS_pure _
    · cases g' with
      | pick _ _ =>
        exact simS_bind (simS_liftS _) fun o => simS_bind (ihq _ _ _) fun nex2 =>
              simS_bind (simS_liftS _) fun nex2 => simS_bind (ihp _ _ _) fun nex1 => simS_liftS _
      | next laz th =>
        exact simS_bind3 (simS_liftS _) fun hed tel o => simS_bind (simS_liftS _) fun nexh =>
              simS_bind (ihq _ _ _) fun nex2 => simS_bind (simS_liftS _) fun nex2 =>
              simS_bind (ihp _ _ _) fun nex1 => simS_liftS _
      | done => exact simS_none
  | n0 _ => intro sup goal region; rw [runLCS]; exact simS_liftS _
  | n1 _ => intro sup goal region; rw [runLCS]; exact simS_liftS _
  | n2 p q info ihp ihq =>
    intro sup goal region
    simp only [runLCS, runLC]
    exact callLS_sim env (fun g rg => ihp sup g rg) (fun g rg => ihq sup g rg) p q info sup goal region
      (fun b n => hsof _ _ _ b n)
  | n3 p ihp =>
    intro sup goal region
    simp only [runLCS, runLC]
    cases goal with
    | next laz th =>
      refine simS_ite _ (ihp _ _ _) (simS_bind (simS_liftS _) fun a => ?_)
      rcases a with _ | ⟨r, o⟩
      · exact simS_none
      · exact simS_bind2 (simS_liftS _) fun z o' => simS_bind (simS_liftS _) fun r' =>
          simS_bind (simS_liftS _) fun oc => ihp _ _ _
    | pick z o => exact simS_bind (simS_liftS _) fun r => simS_bind (simS_liftS _) fun oc => ihp _ _ _
    | done =>
      exact simS_bind2 (simS_liftS _) fun o0 o1 => simS_bind (simS_liftS _) fun r =>
            simS_bind (simS_liftS _) fun oc => ihp _ _ _
  | n4 p ihp =>
    intro sup goal region
    simp only [runLCS, runLC]
    cases goal with
    | done =>
      exact simS_bind (simS_liftS _) fun pro => simS_bind (simS_liftS _) fun arg =>
            simS_bind (simS_liftS _) fun o => ihp _ _ _
    | pick z o =>
      exact simS_bind (simS_liftS _) fun pro => simS_bind (simS_liftS _) fun arg =>
            simS_bind (simS_liftS _) fun o => ihp _ _ _
    | next laz th =>
      refine simS_bind (simS_liftS _) fun a => simS_bind2 ?_ fun pro th' =>
        simS_bind (simS_liftS _) fun arg => simS_bind (simS_liftS _) fun o => ihp _ _ _
      rcases a with _ | x
      · exact simS_bind (simS_liftS _) fun r => simS_ite _ (simS_pure _) simS_none
      · exact simS_pure _
  | n5 p q ihp ihq =>
    intro sup goal region
    simp only [runLCS, runLC]
    refine simS_bind (simS_liftS _) fun rp => simS_bind (simS_liftS _) fun rq => simS_bind ?_ fun o =>
      simS_bind (ihq _ _ _) fun nexq => simS_bind (simS_liftS _) fun nexq =>
      simS_bind (ihp _ _ _) fun nexp => simS_liftS _
    cases goal with
    | pick z o => exact simS_liftS _
    | done => exact simS_bind2 (simS_liftS _) fun o0 o1 => simS_liftS _
    | next laz th =>
      refine simS_bind (simS_liftS _) fun a => ?_
      rcases a with _ | ⟨r, o⟩
      · exact simS_ite _ (simS_liftS _) simS_none
      · exact simS_bind2 (simS_liftS _) fun z o' => simS_liftS _
  | n6 p q r ihp ihq ihr =>
    intro sup goal region
    simp only [runLCS, runLC]
    have h6 : ∀ g : CGoalL S, SimS (Map := Map) (do
        let nex1 ← runLCS env snd sup r g region
        let nex0 ← runLCS env snd sup q g region
        let yes ← liftS (emit ⟨[], [], Termin.hop nex0.th⟩)
        let nuh ← liftS (emit ⟨[], [], Termin.hop nex1.th⟩)
        liftS (setTag yes region)
        liftS (setTag nuh region)
        if nex0.th.args ≠ [] then fun _ => Option.none else
        if nex1.th.args ≠ [] then fun _ => Option.none else
        let lazy ← liftS (liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p))
        let nexCond ← runLCS env snd sup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
        withSoft fun sf => if !(lazyBig (softLess sf lazy)) then liftS (copyL nexCond lazy) else do
          let o ← liftS (emit ⟨[], [], Termin.hop nexCond.th⟩)
          let lazy ← lazyShutS o lazy
          liftS (copyL ⟨nexCond.laz, jmp0 o⟩ lazy)) (do
        let nex1 ← runLC env sup r g region
        let nex0 ← runLC env sup q g region
        let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
        let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
        setTag yes region
        setTag nuh region
        if nex0.th.args ≠ [] then fun _ => Option.none else
        if nex1.th.args ≠ [] then fun _ => Option.none else
        let lazy ← liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p)
        let nexCond ← runLC env sup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
        if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
          let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
          let lazy ← lazyShut o lazy
          copyL ⟨nexCond.laz, jmp0 o⟩ lazy) := fun g =>
      simS_bind (ihr _ _ _) fun nex1 => simS_bind (ihq _ _ _) fun nex0 => simS_bind (simS_liftS _) fun yes =>
        simS_bind (simS_liftS _) fun nuh => simS_bind (simS_liftS _) fun _ => simS_bind (simS_liftS _) fun _ =>
        simS_ite _ simS_none (simS_ite _ simS_none (simS_bind (simS_liftS _) fun lazy =>
          simS_bind (ihp _ _ _) fun nexCond => simS_withSoft (simS_ite _ (simS_liftS _)
            (simS_bind (simS_liftS _) fun o => simS_bind (lazyShutS_sim _ _) fun lazy => simS_liftS _))))
    cases goal with
    | next laz th =>
      exact sixNextLCS_sim _ _ (fun g rg => ihp sup g rg) (fun g rg => ihq sup g rg)
            (fun g rg => ihr sup g rg) p q r 3 laz th region
    | done => exact h6 _
    | pick z o => exact h6 _
  | n7 p q ihp ihq =>
    intro sup goal region
    simp only [runLCS, runLC]
    exact simS_bind (ihq _ _ _) fun nex => ihp _ _ _
  | n10 a v q ihv ihq =>
    intro sup goal region
    simp only [runLCS, runLC]
    exact simS_bind (simS_liftS _) fun next => simS_bind3 (simS_liftS _) fun don rec o =>
      simS_bind (simS_liftS _) fun nexR => simS_bind (ihv _ _ _) fun nexDon =>
      simS_bind (simS_liftS _) fun nexDon => simS_bind (ihq _ _ _) fun nexRec => simS_liftS _
  | n11s _ _ _ _ => intro sup goal region; exact fun _ => rfl
  | n11d _ _ _ _ _ _ => intro sup goal region; exact fun _ => rfl
  | n12 _ _ _ _ => intro sup goal region; exact fun _ => rfl
  | mean _ _ _ _ _ _ _ => intro sup goal region; exact fun _ => rfl

/-- **`runLCS_eq`**: the equation of `runLCS_sim` at a state. -/
theorem runLCS_eq (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    (hsof : ∀ m p q b n, env.sof m p q b n = false) (nm : Nomm) (sup : Option Nomm) (goal : CGoalL S)
    (region : List Nat) (g : Gen Map) :
    runLCS env snd sup nm goal region (GenSf.ofGen g) = (runLC env sup nm goal region g).map embS :=
  runLCS_sim env snd hsof nm sup goal region g

end Comp
end SkaModel

namespace SkaModel.SccLoop

open Nock Formalization.Hoon Formalization.SkaModel Formalization.SkaModel.Comp Formalization.Compiler

/-- **Without soft calls, `memDoneMS` is `memDoneM`.** -/
theorem memDoneMS_eq (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    (hsof : ∀ m p q b n, env.sof m p q b n = false) (m : MemInfo) :
    memDoneMS env snd m = memDoneM env m := by
  unfold memDoneMS memDoneM
  rw [runLCS_eq (S := CSet) (Map := TreapMap mugF) env snd hsof m.nm Option.none CGoalL.done [] gen0]
  cases runLC (S := CSet) (Map := TreapMap mugF) env Option.none m.nm CGoalL.done [] gen0 with
  | none => rfl
  | some p => rfl

/-- `envView` keeps `sof`. -/
theorem envView_sof (e : CallEnv) (scc : List Noun) (vn vs : Noun → NeedOrd) :
    (envView e scc vn vs).sof = e.sof := rfl

/-- **Without soft calls outside, `compRealS` is `compReal`.** -/
theorem compRealS_eq (r : RealCfg) (snd : Nomm → NeedOrd → Bool)
    (hsof : ∀ m p q b n, r.env.sof m p q b n = false) : compRealS r snd = compReal r := by
  have key : ∀ vn vs (m : MemInfo), memDoneMS (envView r.env r.scc vn vs) snd m =
      memDoneM (envView r.env r.scc vn vs) m :=
    fun vn vs m => memDoneMS_eq (envView r.env r.scc vn vs) snd (fun m p q b n => hsof m p q b n) m
  funext b mode vn vs
  cases mode <;> simp only [compRealS, compReal, key]

/-- **Without soft calls, `cfgRealS` is `cfgReal`**, so every theorem on `cfgReal`
(`memGate_done_real`, `memGate_done_K`) holds for `cfgRealS`. -/
theorem cfgRealS_eq (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun) (kids : Noun → List Noun)
    (hsof : ∀ m p q b n, r.env.sof m p q b n = false) : cfgRealS r snd order kids = cfgReal r order kids := by
  simp only [cfgRealS, cfgReal, compRealS_eq r snd hsof]

/-- Without soft calls `DoneRetS` is `DoneRet`. -/
theorem doneRetS_iff (r : RealCfg) (snd : Nomm → NeedOrd → Bool)
    (hsof : ∀ m p q b n, r.env.sof m p q b n = false) : DoneRetS r snd ↔ DoneRet r := by
  have key : ∀ vn vs (m : MemInfo), memDoneMS (envView r.env r.scc vn vs) snd m =
      memDoneM (envView r.env r.scc vn vs) m :=
    fun vn vs m => memDoneMS_eq (envView r.env r.scc vn vs) snd (fun m p q b n => hsof m p q b n) m
  simp only [DoneRetS, DoneRet, key]

end SkaModel.SccLoop
end Formalization
