import lemmas.Ska.RawInvCQ

/-!
# Raw `+comp` output with indirect calls: `Closed`, `ArityOK`, `TwoNA`

README Gaps 14 (b), track D.  The facts of `RunAT` for `runLC` (calls) on
`PlainN` (track C, `CompSimBody.lean`: no `%6`, no direct call, no hint;
indirect calls anywhere, nested), under every goal, lazy ones with forks
and bonds included.  Without `%6` no block jumps up, so a state invariant
does it where `FragX` needed the relation `GA`:
* `ATS g`: no `drop`, every block lies below `bo` and meets `BATC` (each
  jump goes to a block with as many parameters as it passes, a two-way end
  passes none) in the map itself;
* `HT P m Q`: from a state with `ATS` and `P`, a run of `m` ends in a state
  with `ATS`, keeps the blocks' parameters and ends (`KP`), and meets `Q`.
  Kept by `bind`, `pure`, `if`; a `QM` step keeps every stable `P`
  (`HT.quiet`), an `+emit` keeps `ATS` when the block meets `BATC`
  (`HT.emit'`).
The arms say: a jump in that is `Fresh` (track C: no argument, to a block
with no parameter) gives a `Fresh` jump out.  The only jumps with
arguments are those of `+forl` into `barg` (`ht_forl`); `+kern`'s ops go
into existing blocks through `+add-ops` and its proxies only touch `cond`
(`qm_kern`), so the indirect call (`+kerf`'s hop, the `%nok` block) emits
only `Fresh` hops (`ht_kerf`, `ht_callL`).
* **`ht_runLC`**: `runLC env sup nm` on `PlainN` is `HT` from `Fresh` goal
  jumps to a `Fresh` result jump.
* **`runATC_plain`**: the raw blocks of the top run of `runLC env` on a
  nomm of `PlainN` meet `Closed`, `ArityOK` and `TwoNA`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The invariant and the triples -/

/-- **A block's jumps go to blocks of `bl` with as many parameters as they
pass**, and a two-way end passes none. -/
def BATC (bl : Map Blob) (b : Blob) : Prop :=
  (∀ j ∈ finJumps b.fin, ∃ b2, HoonMap.get bl j.there = some b2 ∧ j.args.length = b2.par.length) ∧
  (Compiler.twoWay b.fin = true → ∀ j ∈ finJumps b.fin, j.args = [])

/-- **The state invariant.** -/
def ATS (g : Comp.Gen Map) : Prop :=
  g.drop = false ∧ ∀ k b, HoonMap.get g.blocks k = some b → k < g.bo ∧ BATC g.blocks b

/-- **The blocks of `g` keep their parameters and ends in `g'`.** -/
def KP (g g' : Comp.Gen Map) : Prop :=
  g'.drop = g.drop ∧ g.bo ≤ g'.bo ∧ ∀ k b, HoonMap.get g.blocks k = some b →
    ∃ b', HoonMap.get g'.blocks k = some b' ∧ b'.par = b.par ∧ b'.fin = b.fin

theorem KP.refl (g : Comp.Gen Map) : KP g g := ⟨rfl, Nat.le_refl _, fun _ b h => ⟨b, h, rfl, rfl⟩⟩

theorem KP.trans {g0 g1 g2 : Comp.Gen Map} (a : KP g0 g1) (b : KP g1 g2) : KP g0 g2 :=
  ⟨b.1.trans a.1, Nat.le_trans a.2.1 b.2.1, fun k x hx => by
    obtain ⟨x1, h1, p1, f1⟩ := a.2.2 k x hx
    obtain ⟨x2, h2, p2, f2⟩ := b.2.2 k x1 h1
    exact ⟨x2, h2, p2.trans p1, f2.trans f1⟩⟩

/-- A predicate that `KP` keeps. -/
def Stab (P : Comp.Gen Map → Prop) : Prop := ∀ g g', KP g g' → P g → P g'

theorem stab_true : Stab (Map := Map) fun _ => True := fun _ _ _ _ => trivial

theorem stab_and {P Q : Comp.Gen Map → Prop} (hp : Stab P) (hq : Stab Q) : Stab fun g => P g ∧ Q g :=
  fun g g' k h => ⟨hp g g' k h.1, hq g g' k h.2⟩

theorem fresh_kp {g g' : Comp.Gen Map} {j : Jmp} (h : Fresh g j) (k : KP g g') : Fresh g' j := by
  obtain ⟨b, hb, hp, ha⟩ := h
  obtain ⟨b', hb', hp', -⟩ := k.2.2 _ b hb
  exact ⟨b', hb', hp'.trans hp, ha⟩

theorem stab_fresh (j : Jmp) : Stab (Map := Map) fun g => Fresh g j := fun _ _ k h => fresh_kp h k

/-- Block `o` has the parameters `p`. -/
def HasPar (o : Nat) (p : List Nat) (g : Comp.Gen Map) : Prop :=
  ∃ b, HoonMap.get g.blocks o = some b ∧ b.par = p

theorem stab_hasPar (o : Nat) (p : List Nat) : Stab (Map := Map) (HasPar o p) := by
  intro g g' k ⟨b, hb, hp⟩
  obtain ⟨b', hb', hp', -⟩ := k.2.2 _ b hb
  exact ⟨b', hb', hp'.trans hp⟩

theorem fresh_of_hasPar {o : Nat} {g : Comp.Gen Map} (h : HasPar o [] g) : Fresh g (jmp0 o) := by
  obtain ⟨b, hb, hp⟩ := h
  exact ⟨b, hb, hp, rfl⟩

theorem batc_kp {g g' : Comp.Gen Map} {b : Blob} (h : BATC g.blocks b) (k : KP g g') : BATC g'.blocks b := by
  refine ⟨fun j hj => ?_, h.2⟩
  obtain ⟨b2, h2, e2⟩ := h.1 j hj
  obtain ⟨b2', h2', p2, -⟩ := k.2.2 _ b2 h2
  exact ⟨b2', h2', by rw [p2]; exact e2⟩

theorem batc_fresh {g : Comp.Gen Map} {b : Blob} (h : ∀ j ∈ finJumps b.fin, Fresh g j) : BATC g.blocks b := by
  refine ⟨fun j hj => ?_, fun _ j hj => ?_⟩
  · obtain ⟨b2, h2, p2, a2⟩ := h j hj
    exact ⟨b2, h2, by rw [a2, p2]; rfl⟩
  · obtain ⟨b2, h2, p2, a2⟩ := h j hj
    exact a2

theorem ats_quiet {g g' : Comp.Gen Map} (a : ATS g) (q : Quiet g g') : ATS g' ∧ KP g g' := by
  have K : KP g g' := ⟨q.1.drop, q.1.bo, fun k b hb => q.1.keep k b (a.2 k b hb).1 hb⟩
  refine ⟨⟨q.1.drop.trans a.1, fun k b' hb' => ?_⟩, K⟩
  rcases q.1.new k b' hb' with ⟨b, hb, -, hf⟩ | ⟨l, u, -⟩
  · obtain ⟨l, B⟩ := a.2 k b hb
    refine ⟨by rw [q.2]; exact l, ?_⟩
    have B' := batc_kp B K
    exact ⟨fun j hj => B'.1 j (by rw [hf] at hj; exact hj), fun ht j hj => B'.2 (by rw [hf] at ht; exact ht) j
      (by rw [hf] at hj; exact hj)⟩
  · rw [q.2] at u; omega

theorem ats_emit {g : Comp.Gen Map} {b : Blob} (a : ATS g) (hb : BATC g.blocks b) :
    ATS (g.emitted b) ∧ KP g (g.emitted b) ∧ HoonMap.get (g.emitted b).blocks g.bo = some b := by
  have K : KP g (g.emitted b) := ⟨rfl, Nat.le_succ _, fun k x hx => ⟨x, by
    rw [em_get a.1, if_neg (Nat.ne_of_lt (a.2 k x hx).1)]; exact hx, rfl, rfl⟩⟩
  refine ⟨⟨a.1, fun k x hx => ?_⟩, K, by rw [em_get a.1, if_pos rfl]⟩
  rw [em_get a.1] at hx
  by_cases e : k = g.bo
  · rw [if_pos e] at hx
    cases hx
    exact ⟨by simp only [emitted_bo]; omega, batc_kp hb K⟩
  · rw [if_neg e] at hx
    obtain ⟨l, B⟩ := a.2 k x hx
    exact ⟨by simp only [emitted_bo]; omega, batc_kp B K⟩

/-- **The triple**: from `ATS` and `P`, a run of `m` keeps `ATS`, keeps the
blocks (`KP`) and meets `Q`. -/
structure HT {α : Type} (P : Comp.Gen Map → Prop) (m : CM Map α) (Q : α → Comp.Gen Map → Prop) : Prop where
  run : ∀ g x g', ATS g → P g → m g = some (x, g') → ATS g' ∧ KP g g' ∧ Q x g'

namespace HT

theorem pure' {α : Type} {P : Comp.Gen Map → Prop} {Q : α → Comp.Gen Map → Prop} {a : α}
    (h : ∀ g, P g → Q a g) : HT P (pure a : CM Map α) Q := by
  constructor; intro g x g' A p e; cases e; exact ⟨A, KP.refl g, h g p⟩

theorem bind' {α β : Type} {P : Comp.Gen Map → Prop} {R : α → Comp.Gen Map → Prop} {Q : β → Comp.Gen Map → Prop}
    {m : CM Map α} {f : α → CM Map β} (hm : HT P m R) (hf : ∀ a, HT (R a) (f a) Q) : HT P (m >>= f) Q := by
  constructor
  intro g x g' A p h
  rw [bind_apply] at h
  obtain ⟨⟨a, g1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨A1, K1, r1⟩ := hm.run g a g1 A p h1
  obtain ⟨A2, K2, q2⟩ := (hf a).run g1 x g' A1 r1 h2
  exact ⟨A2, K1.trans K2, q2⟩

theorem fail {α : Type} {P : Comp.Gen Map → Prop} {Q : α → Comp.Gen Map → Prop} :
    HT P (fun _ => Option.none : CM Map α) Q := by
  constructor; intro g x g' _ _ h; cases h

theorem ite' {α : Type} {P : Comp.Gen Map → Prop} {Q : α → Comp.Gen Map → Prop} (c : Prop) [Decidable c]
    {a b : CM Map α} (ha : HT P a Q) (hb : HT P b Q) : HT P (if c then a else b) Q := by
  split
  · exact ha
  · exact hb

theorem conseq {α : Type} {P P' : Comp.Gen Map → Prop} {Q Q' : α → Comp.Gen Map → Prop} {m : CM Map α}
    (h : HT P m Q) (hp : ∀ g, P' g → P g) (hq : ∀ x g, Q x g → Q' x g) : HT P' m Q' := by
  constructor
  intro g x g' A p e
  obtain ⟨A1, K1, q1⟩ := h.run g x g' A (hp g p) e
  exact ⟨A1, K1, hq x g' q1⟩

theorem weak {α : Type} {P P' : Comp.Gen Map → Prop} {Q : α → Comp.Gen Map → Prop} {m : CM Map α}
    (h : HT P m Q) (hp : ∀ g, P' g → P g) : HT P' m Q := conseq h hp (fun _ _ h => h)

theorem frame {α : Type} {P F : Comp.Gen Map → Prop} {Q : α → Comp.Gen Map → Prop} {m : CM Map α}
    (h : HT P m Q) (hF : Stab F) : HT (fun g => P g ∧ F g) m (fun x g => Q x g ∧ F g) := by
  constructor
  intro g x g' A p e
  obtain ⟨A1, K1, q1⟩ := h.run g x g' A p.1 e
  exact ⟨A1, K1, q1, hF g g' K1 p.2⟩

theorem quiet {α : Type} {P : Comp.Gen Map → Prop} {m : CM Map α} (h : QM m) (hP : Stab P) :
    HT P m (fun _ => P) := by
  constructor
  intro g x g' A p e
  obtain ⟨A1, K1⟩ := ats_quiet A (h.q g x g' e)
  exact ⟨A1, K1, hP g g' K1 p⟩

theorem emit' {P : Comp.Gen Map → Prop} {b : Blob} (hb : ∀ g, P g → BATC g.blocks b) (hP : Stab P) :
    HT P (emit b : CM Map Nat) (fun o g => P g ∧ HasPar o b.par g) := by
  constructor
  intro g x g' A p e
  rw [emit_apply] at e
  cases e
  obtain ⟨A1, K1, hg⟩ := ats_emit A (hb g p)
  exact ⟨A1, K1, hP g _ K1 p, b, hg, rfl⟩

end HT

/-- An `+emit` of a block with no parameter whose jumps are `Fresh`: the
label is `Fresh` after it. -/
theorem ht_emitJ {P : Comp.Gen Map → Prop} {b : Blob} (hp : b.par = [])
    (hb : ∀ g, P g → ∀ j ∈ finJumps b.fin, Fresh g j) (hP : Stab P) :
    HT P (emit b : CM Map Nat) (fun o g => P g ∧ Fresh g (jmp0 o)) :=
  HT.conseq (HT.emit' (fun g h => batc_fresh (hb g h)) hP) (fun _ h => h)
    (fun _ _ h => ⟨h.1, fresh_of_hasPar (by rw [← hp]; exact h.2)⟩)

theorem js_nil {P : Comp.Gen Map → Prop} {fin : Termin} (hf : finJumps fin = []) :
    ∀ g, P g → ∀ j ∈ finJumps fin, Fresh g j := fun _ _ j hj => by rw [hf] at hj; cases hj

theorem js_hop {P : Comp.Gen Map → Prop} {t : Jmp} (h : ∀ g, P g → Fresh g t) :
    ∀ g, P g → ∀ j ∈ finJumps (Termin.hop t), Fresh g j := fun g p j hj => by
  simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj; subst hj; exact h g p

theorem js_two {P : Comp.Gen Map → Prop} {fin : Termin} {z o : Jmp} (hf : finJumps fin = [z, o])
    (h : ∀ g, P g → Fresh g z ∧ Fresh g o) : ∀ g, P g → ∀ j ∈ finJumps fin, Fresh g j := fun g p j hj => by
  rw [hf] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact (h g p).1
  · exact (h g p).2

/-- A `QM` step under a `Fresh` jump. -/
theorem ht_qf {α : Type} {m : CM Map α} (h : QM m) (j : Jmp) :
    HT (fun g => Fresh g j) m (fun _ g => Fresh g j) := HT.quiet h (stab_fresh j)

/-! ## The arms -/

/-- The goal's jumps are `Fresh`. -/
def GFL (goal : CGoalL S) (g : Comp.Gen Map) : Prop :=
  match goal with
  | CGoalL.next _ th => Fresh g th
  | CGoalL.pick z o => Fresh g z ∧ Fresh g o
  | CGoalL.done => True

theorem stab_gfl (goal : CGoalL S) : Stab (Map := Map) (GFL goal) := by
  cases goal with
  | next _ th => exact stab_fresh th
  | pick z o => exact stab_and (stab_fresh z) (stab_fresh o)
  | done => exact stab_true

theorem ht_simpleNextL (goal : CGoalL S) :
    HT (GFL (Map := Map) goal) (simpleNextL goal : CM Map (NextL S)) (fun nex g => Fresh g nex.th) := by
  unfold simpleNextL
  cases goal with
  | next laz th => exact HT.pure' fun g h => h
  | done =>
    exact HT.bind' (HT.quiet QM.re' stab_true) fun r =>
      HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o => HT.pure' fun g h => h.2
  | pick z o =>
    exact HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun r =>
      HT.bind' (ht_emitJ rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o))) fun o' =>
        HT.pure' fun g h => h.2

theorem ht_bombL {P : Comp.Gen Map → Prop} (miss : Option Nat) :
    HT P (bombL miss : CM Map (NextL S)) (fun nex g => Fresh g nex.th) := by
  unfold bombL
  exact HT.conseq (HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o => HT.pure' fun g h => h.2)
    (fun _ _ => trivial) (fun _ _ h => h)

theorem ht_splitL (nex : NextL S) :
    HT (fun g => Fresh g nex.th) (splitL nex : CM Map (Lazy S × Lazy S × Nat))
      (fun x g => Fresh g (jmp0 x.2.2)) := by
  unfold splitL
  refine HT.bind' (ht_emitJ rfl (js_hop fun g h => h) (stab_fresh _)) fun o =>
    HT.bind' (HT.conseq (ht_qf (qm_splitLoop _ _) (jmp0 o)) (fun _ h => h.2) (fun _ _ h => h)) fun a => ?_
  rcases a with ⟨h, t⟩
  exact HT.pure' fun g h => h

theorem ht_intoL (nex : NextL S) (axe : Nat) :
    HT (fun g => Fresh g nex.th) (intoL nex axe : CM Map (Lazy S × Lazy S × Nat))
      (fun x g => Fresh g (jmp0 x.2.2)) := by
  unfold intoL
  refine HT.bind' (ht_emitJ rfl (js_hop fun g h => h) (stab_fresh _)) fun o =>
    HT.bind' (HT.conseq (ht_qf (qm_intoLoopL _ _ _) (jmp0 o)) (fun _ h => h.2) (fun _ _ h => h)) fun a => ?_
  rcases a with ⟨d, r⟩
  exact HT.pure' fun g h => h

theorem ht_copyL (first : NextL S) (second : Lazy S) :
    HT (fun g => Fresh g first.th) (copyL first second : CM Map (NextL S)) (fun x g => Fresh g x.th) := by
  unfold copyL
  exact HT.bind' (ht_emitJ rfl (js_hop fun g h => h) (stab_fresh _)) fun o =>
    HT.bind' (HT.conseq (ht_qf (qm_copyLazyL _ _ _) (jmp0 o)) (fun _ h => h.2) (fun _ _ h => h)) fun _ =>
      HT.pure' fun g h => h

theorem ht_pastL (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat) :
    HT (fun g => Fresh g nex.th) (pastL cod nex nom region : CM Map (NextL S)) (fun x g => Fresh g x.th) := by
  unfold pastL
  refine HT.ite' _ (HT.pure' fun g h => h) ?_
  split
  · exact HT.fail
  · exact HT.pure' fun g h => h
  · exact HT.bind' (ht_emitJ rfl (js_hop fun g h => h) (stab_fresh _)) fun o =>
      HT.bind' (HT.conseq (ht_qf (QM.setTag' _ _) (jmp0 o)) (fun _ h => h.2) (fun _ _ h => h)) fun _ =>
        HT.pure' fun g h => h

theorem ht_medeL (th : Jmp) (som : Noun) (laz : Lazy S) :
    HT (fun g => Fresh g th) (medeL th som laz : CM Map Nat) (fun o g => Fresh g (jmp0 o)) := by
  unfold medeL
  refine HT.bind' (ht_emitJ rfl (js_hop fun g h => h) (stab_fresh _)) fun o =>
    HT.bind' (HT.conseq (ht_qf QM.get' (jmp0 o)) (fun _ h => h.2) (fun _ _ h => h)) fun g => ?_
  refine HT.ite' _ (HT.pure' fun g h => h) (HT.bind' (ht_qf ?_ (jmp0 o)) fun _ => HT.pure' fun g h => h)
  exact qm_walkLazy (fun o' sur => QM.bind' (qm_sureRequireLook _) fun _ => qm_medeLoop _ _ _) _ _

theorem ht_collapse (nex : NextL S) :
    HT (fun g => Fresh g nex.th) (collapseLazyAtomL nex : CM Map (Option (Nat × Nat)))
      (fun a g => ∀ r o, a = some (r, o) → Fresh g (jmp0 o)) := by
  unfold collapseLazyAtomL
  refine HT.ite' _ HT.fail (HT.ite' _ (HT.pure' fun g h r o e => by cases e) ?_)
  refine HT.bind' (ht_qf (qm_sureRequireLook _) nex.th) fun ned => ?_
  refine HT.bind' (R := fun (x : Nat × Nat) (g : Comp.Gen Map) => Fresh g (jmp0 x.2)) ?_ fun p => ?_
  · split
    · exact HT.pure' fun g h => fresh_jmp0 h
    · exact HT.bind' (ht_qf QM.re' nex.th) fun r => HT.pure' fun g h => fresh_jmp0 h
    · exact HT.bind' (ht_qf QM.re' nex.th) fun r =>
        HT.bind' (ht_emitJ rfl (js_nil rfl) (stab_fresh _)) fun o => HT.pure' fun g h => h.2
    · exact HT.bind' (ht_emitJ rfl (js_nil rfl) (stab_fresh _)) fun o => HT.pure' fun g h => h.2
  · rcases p with ⟨r, there⟩
    refine HT.bind' (ht_qf QM.get' (jmp0 there)) fun g => ?_
    refine HT.ite' _ (HT.pure' fun g h r' o e => by cases e; exact h) ?_
    exact HT.bind' (ht_qf (qm_walkLazy (fun o s => qm_collapseGate r there o s) _ _) (jmp0 there)) fun _ =>
      HT.pure' fun g h r' o e => by cases e; exact h

theorem ht_forl (r o : Nat) :
    HT (fun g => Fresh g (jmp0 o)) (forl r o : CM Map (Nat × Nat))
      (fun x g => Fresh g (jmp0 x.1) ∧ Fresh g (jmp0 x.2)) := by
  unfold forl
  refine HT.bind' (ht_qf QM.re' (jmp0 o)) fun r0 => HT.bind' (ht_qf QM.re' (jmp0 o)) fun r1 => ?_
  refine HT.bind' (HT.emit' (fun g h => batc_fresh (js_hop (fun g h => h) g h)) (stab_fresh _)) fun barg => ?_
  have hb : ∀ (rr : Nat) (g : Comp.Gen Map), HasPar barg [r] g →
      BATC g.blocks ⟨[], [Pole.imm (A 0) rr], Termin.hop ⟨[some rr], barg⟩⟩ := by
    intro rr g ⟨b, hb, hp⟩
    refine ⟨fun j hj => ?_, fun ht => by cases ht⟩
    simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
    subst hj
    exact ⟨b, hb, by rw [hp]; rfl⟩
  have hb1 : ∀ (rr : Nat) (g : Comp.Gen Map), HasPar barg [r] g →
      BATC g.blocks ⟨[], [Pole.imm (A 1) rr], Termin.hop ⟨[some rr], barg⟩⟩ := by
    intro rr g ⟨b, hb, hp⟩
    refine ⟨fun j hj => ?_, fun ht => by cases ht⟩
    simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
    subst hj
    exact ⟨b, hb, by rw [hp]; rfl⟩
  refine HT.bind' (HT.conseq (HT.emit' (P := HasPar barg [r]) (hb r0) (stab_hasPar _ _)) (fun _ h => h.2)
    (fun _ _ h => h)) fun if0 => ?_
  refine HT.bind' (HT.conseq (HT.frame (HT.emit' (P := HasPar barg [r]) (hb1 r1) (stab_hasPar _ _))
    (stab_hasPar if0 [])) (fun _ h => ⟨h.1, h.2⟩) (fun _ _ h => h)) fun if1 => ?_
  exact HT.pure' fun g h => ⟨fresh_of_hasPar h.2, fresh_of_hasPar h.1.2⟩

theorem ht_doneBlocks : HT (fun _ => True) (doneBlocks : CM Map (Nat × Nat))
    (fun x g => Fresh g (jmp0 x.1) ∧ Fresh g (jmp0 x.2)) := by
  unfold doneBlocks
  refine HT.bind' (HT.quiet QM.re' stab_true) fun r => HT.bind' (HT.quiet QM.re' stab_true) fun r1 => ?_
  refine HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o0 => ?_
  refine HT.bind' (HT.conseq (ht_emitJ rfl (js_nil rfl) (stab_fresh (jmp0 o0))) (fun _ h => h.2)
    (fun _ _ h => h)) fun o1 => ?_
  exact HT.pure' fun g h => ⟨h.1, h.2⟩

theorem ht_kerf (nex : NextL S) :
    HT (fun g => Fresh g nex.th) (kerf nex : CM Map (Nat × Nat)) (fun x g => Fresh g (jmp0 x.1)) := by
  unfold kerf
  exact HT.bind' (ht_emitJ rfl (js_hop fun g h => h) (stab_fresh _)) fun o =>
    HT.bind' (HT.conseq (ht_qf (qm_kern _ _) (jmp0 o)) (fun _ h => h.2) (fun _ _ h => h)) fun _ =>
      HT.pure' fun g h => h

/-! ## The case `%2` and the induction -/

/-- What a run owes: `Fresh` goal jumps in, a `Fresh` result jump out. -/
abbrev HR (rp : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ goal region, HT (GFL (Map := Map) goal) (rp goal region) (fun nex g => Fresh g nex.th)

theorem hr_next {rp : CGoalL S → List Nat → CM Map (NextL S)} (h : HR (Map := Map) rp) (laz : Lazy S) (th : Jmp)
    (region : List Nat) :
    HT (fun g => Fresh g th) (rp (CGoalL.next laz th) region) (fun nex g => Fresh g nex.th) :=
  HT.conseq (h (CGoalL.next laz th) region) (fun _ h => h) (fun _ _ h => h)

/-- **The indirect call**: `+simple-next`, `+kerf` (its hop and `+kern`'s
ops), the `%nok` block, the two runs, `+past` and `+copy`. -/
theorem ht_callL (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)} (p q : Nomm)
    (sup : Option Nomm) (hp : HR (Map := Map) rp) (hq : HR (Map := Map) rq) (goal : CGoalL S) (region : List Nat) :
    HT (GFL (Map := Map) goal) (callL env rp rq p q Option.none sup goal region : CM Map (NextL S))
      (fun nex g => Fresh g nex.th) := by
  unfold callL
  refine HT.bind' (ht_simpleNextL _) fun nex => HT.bind' (ht_kerf _) fun a => ?_
  rcases a with ⟨out, pro⟩
  exact HT.bind' (ht_qf QM.re' _) fun _ => HT.bind' (ht_qf QM.re' _) fun _ =>
    HT.bind' (ht_emitJ rfl (js_hop fun g h => h) (stab_fresh _)) fun o =>
    HT.bind' (HT.conseq (hr_next hq _ _ _) (fun _ h => h.2) (fun _ _ h => h)) fun _ =>
    HT.bind' (ht_pastL _ _ _ _) fun _ => HT.bind' (hr_next hp _ _ _) fun _ => ht_copyL _ _

/-- A run for the goal of a block just emitted, from the state before. -/
theorem ht_tail {P : Comp.Gen Map → Prop} {rp : CGoalL S → List Nat → CM Map (NextL S)} (h : HR (Map := Map) rp)
    {b : Blob} (hpar : b.par = []) (hb : ∀ g, P g → ∀ j ∈ finJumps b.fin, Fresh g j) (hP : Stab P)
    (laz : Nat → Lazy S) (region : List Nat) :
    HT P (do let o ← emit b; rp (CGoalL.next (laz o) (jmp0 o)) region : CM Map (NextL S))
      (fun nex g => Fresh g nex.th) :=
  HT.bind' (ht_emitJ hpar hb hP) fun o => HT.conseq (hr_next h _ _ _) (fun _ h => h.2) (fun _ _ h => h)

/-- The tail of the binary cases: run `q` for a `Fresh` jump, `+past`, run
`p`, `+copy`. -/
theorem ht_bin (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : HR (Map := Map) (runLC (S := S) env sup p))
    (hq : HR (Map := Map) (runLC (S := S) env sup q)) (lq : Lazy S) (lp : NextL S → Lazy S) (th : Jmp) (region : List Nat) :
    HT (fun g => Fresh g th) (do
      let nex2 ← runLC env sup q (CGoalL.next lq th) region
      let nex2 ← pastL env.cod nex2 p region
      let nex1 ← runLC env sup p (CGoalL.next (lp nex2) nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) (fun nex g => Fresh g nex.th) :=
  HT.bind' (hr_next hq _ _ _) fun _ => HT.bind' (ht_pastL _ _ _ _) fun _ =>
    HT.bind' (hr_next hp _ _ _) fun _ => ht_copyL _ _

/-- **`runLC` on `PlainN`**, every goal: `Fresh` goal jumps give a `Fresh`
result jump, and the run keeps `ATS`. -/
theorem ht_runLC (env : CallEnv) : ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm),
    HR (Map := Map) (runLC (S := S) env sup nm)
  | Nomm.cons p q, h, sup, goal, region => by
    have ihp := ht_runLC env p h.1 sup
    have ihq := ht_runLC env q h.2 sup
    unfold runLC
    refine HT.bind' (Q := fun (nex : NextL S) (g : Comp.Gen Map) => Fresh g nex.th)
      (R := fun (goal' : CGoalL S) (g : Comp.Gen Map) => GFL goal' g ∧ GFL goal g) ?_
      fun goal' => ?_
    · cases goal with
      | done =>
        exact HT.bind' (HT.quiet QM.re' stab_true) fun r =>
          HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o => HT.pure' fun g h => ⟨h.2, trivial⟩
      | next laz th => exact HT.pure' fun g h => ⟨h, h⟩
      | pick z o => exact HT.pure' fun g h => ⟨h, h⟩
    · cases goal' with
      | pick z o =>
        exact HT.bind' (HT.conseq (ht_emitJ rfl (js_nil rfl) stab_true) (fun _ _ => trivial) (fun _ _ h => h))
          fun o => HT.conseq (ht_bin env sup ihp ihq _ (fun _ => ofSure Sure.bunt) _ _) (fun _ h => h.2)
            (fun _ _ h => h)
      | done => exact HT.fail
      | next laz th =>
        refine HT.bind' (HT.conseq (ht_splitL ⟨laz, th⟩) (fun _ h => h.1) (fun _ _ h => h)) fun a => ?_
        rcases a with ⟨hed, tel, o⟩
        exact HT.bind' (HT.weak (ht_pastL _ _ _ _) fun _ h => h) fun nexh =>
          ht_bin env sup ihp ihq _ (fun _ => nexh.laz) _ _
  | Nomm.n0 ax, _, sup, goal, region => by
    unfold runLC
    refine HT.ite' _ (ht_bombL _) (HT.bind' (ht_simpleNextL _) fun nex => HT.ite' _ (HT.pure' fun g h => h) ?_)
    cases fromL ax nex.laz
    · exact HT.fail
    · exact HT.pure' fun g h => h
  | Nomm.n1 k, _, sup, goal, region => by
    unfold runLC
    cases goal with
    | done =>
      exact HT.bind' (HT.quiet QM.re' stab_true) fun r =>
        HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o => HT.pure' fun g h => h.2
    | pick z o =>
      exact HT.ite' _ (HT.pure' fun g h => h.1) (HT.ite' _ (HT.pure' fun g h => h.2) (ht_bombL _))
    | next laz th => exact HT.bind' (ht_medeL _ _ _) fun o => HT.pure' fun g h => h
  | Nomm.n3 p, h, sup, goal, region => by
    have ih := ht_runLC env p h sup
    unfold runLC
    cases goal with
    | pick z o =>
      exact HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun r =>
        ht_tail ih rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o)) (fun _ => ofSure (S := S) (lazyReg r)) _
    | done =>
      refine HT.bind' (HT.conseq ht_doneBlocks (fun _ _ => trivial) (fun _ _ h => h)) fun a => ?_
      rcases a with ⟨o0, o1⟩
      exact HT.bind' (HT.quiet QM.re' (stab_and (stab_fresh _) (stab_fresh _))) fun r =>
        ht_tail ih rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _))
          (fun _ => ofSure (S := S) (lazyReg r)) _
    | next laz th =>
      refine HT.ite' _ (ih _ _) (HT.bind' (ht_collapse ⟨laz, th⟩) fun a => ?_)
      rcases a with _ | ⟨r, o⟩
      · exact HT.fail
      · refine HT.bind' (HT.conseq (ht_forl r o) (fun _ h => h r o rfl) (fun _ _ h => h)) fun x => ?_
        rcases x with ⟨z, o'⟩
        exact HT.bind' (HT.quiet QM.re' (stab_and (stab_fresh _) (stab_fresh _))) fun r' =>
          ht_tail ih rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _))
            (fun _ => ofSure (S := S) (lazyReg r')) _
  | Nomm.n4 p, h, sup, goal, region => by
    have ih := ht_runLC env p h sup
    unfold runLC
    cases goal with
    | done =>
      exact HT.bind' (HT.quiet QM.re' stab_true) fun _ => HT.bind' (HT.quiet QM.re' stab_true) fun arg =>
        ht_tail ih rfl (js_nil rfl) stab_true (fun _ => ofSure (S := S) (lazyReg arg)) _
    | pick z o =>
      exact HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun _ =>
        HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun arg =>
          ht_tail ih rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o)) (fun _ => ofSure (S := S) (lazyReg arg)) _
    | next laz th =>
      refine HT.bind' (HT.weak (HT.frame (ht_collapse ⟨laz, th⟩) (stab_fresh th)) fun _ h => ⟨h, h⟩) fun a => ?_
      refine HT.bind' (Q := fun (nex : NextL S) (g : Comp.Gen Map) => Fresh g nex.th)
        (R := fun (x : Nat × Nat) (g : Comp.Gen Map) => Fresh g (jmp0 x.2)) ?_ fun x => ?_
      · cases a with
        | some x => exact HT.pure' fun g h => h.1 x.1 x.2 rfl
        | none =>
          refine HT.bind' (HT.conseq (ht_qf QM.re' th) (fun _ h => h.2) (fun _ _ h => h)) fun r => ?_
          refine HT.ite' _ (HT.pure' fun g h => fresh_jmp0 h) HT.fail
      · rcases x with ⟨pro, th'⟩
        exact HT.bind' (ht_qf QM.re' _) fun arg =>
          ht_tail ih rfl (js_hop fun g h => h) (stab_fresh _) (fun _ => ofSure (S := S) (lazyReg arg)) _
  | Nomm.n5 p q, h, sup, goal, region => by
    have ihp := ht_runLC env p h.1 sup
    have ihq := ht_runLC env q h.2 sup
    unfold runLC
    refine HT.bind' (HT.quiet QM.re' (stab_gfl goal)) fun rp => HT.bind' (HT.quiet QM.re' (stab_gfl goal)) fun rq =>
      HT.bind' (R := fun (o : Nat) (g : Comp.Gen Map) => Fresh g (jmp0 o)) ?_ fun o =>
        ht_bin env sup ihp ihq _ (fun _ => _) _ _
    cases goal with
    | pick z o =>
      exact HT.conseq (ht_emitJ rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o))) (fun _ h => h)
        (fun _ _ h => h.2)
    | done =>
      refine HT.bind' (HT.conseq ht_doneBlocks (fun _ _ => trivial) (fun _ _ h => h)) fun a => ?_
      rcases a with ⟨o0, o1⟩
      exact HT.conseq (ht_emitJ rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)))
        (fun _ h => h) (fun _ _ h => h.2)
    | next laz th =>
      refine HT.bind' (HT.weak (HT.frame (ht_collapse ⟨laz, th⟩) (stab_fresh th)) fun _ h => ⟨h, h⟩) fun a => ?_
      cases a with
      | none =>
        refine HT.ite' _ ?_ HT.fail
        exact HT.conseq (ht_emitJ rfl (js_hop fun g h => fresh_jmp0 h) (stab_fresh th)) (fun _ h => h.2)
          (fun _ _ h => h.2)
      | some x =>
        rcases x with ⟨r, o⟩
        refine HT.bind' (HT.conseq (ht_forl r o) (fun _ h => h.1 r o rfl) (fun _ _ h => h)) fun x => ?_
        rcases x with ⟨z, o'⟩
        exact HT.conseq (ht_emitJ rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)))
          (fun _ h => h) (fun _ _ h => h.2)
  | Nomm.n7 p q, h, sup, goal, region => by
    unfold runLC
    exact HT.bind' (ht_runLC env q h.2 (some p) goal region) fun nex =>
      HT.weak (ht_runLC env p h.1 sup nex.goal region) fun _ h => h
  | Nomm.n10 a v q, h, sup, goal, region => by
    have ihv := ht_runLC env v h.1 sup
    have ihq := ht_runLC env q h.2 sup
    unfold runLC
    refine HT.bind' (ht_simpleNextL _) fun next => HT.bind' (ht_intoL _ _) fun x => ?_
    rcases x with ⟨don, rec, o⟩
    exact HT.bind' (HT.weak (ht_pastL _ _ _ _) fun _ h => h) fun nexR =>
      ht_bin env sup ihq ihv _ (fun _ => nexR.laz) _ _
  | Nomm.n2 p q Option.none, h, sup, goal, region => by
    unfold runLC
    exact ht_callL env p q sup (ht_runLC env p h.1 sup) (ht_runLC env q h.2 sup) goal region

/-! ## The top run -/

/-- **The facts of `RunAT` for `runLC`**: the raw blocks of the top run
meet `Closed`, `ArityOK` and `TwoNA`. -/
def RunATC (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv)
    (nm : Nomm) : Prop :=
  ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) →
    Compiler.Closed g1.blocks ∧ Compiler.ArityOK g1.blocks ∧ Compiler.TwoNA g1.blocks

theorem stIn_of_ats {g : Comp.Gen Map} (a : ATS g) :
    Compiler.Closed g.blocks ∧ Compiler.ArityOK g.blocks ∧ Compiler.TwoNA g.blocks := by
  refine ⟨fun o b j hb hj => ?_, fun o b j b2 hb hj hb2 => ?_, fun o b j hb ht hj => ?_⟩
  · obtain ⟨b2, h2, -⟩ := (a.2 o b hb).2.1 j (by rw [← getJmps_eq]; exact hj)
    rw [h2]; rfl
  · obtain ⟨b3, h3, e3⟩ := (a.2 o b hb).2.1 j (by rw [← getJmps_eq]; exact hj)
    rw [h3] at hb2; cases hb2; exact e3
  · exact (a.2 o b hb).2.2 ht j (by rw [← getJmps_eq]; exact hj)

theorem ats_gen0 : ATS (gen0 : Comp.Gen Map) :=
  ⟨rfl, fun k b hb => by simp [gen0, HoonMap.get_empty] at hb⟩

/-- **`RunATC` on `PlainN`**: every nomm with no `%6`, no direct call and no
hint, indirect calls anywhere. -/
theorem runATC_plain (env : CallEnv) {nm : Nomm} (hp : PlainN nm) : RunATC S Map env nm := by
  intro nex g1 h
  exact stIn_of_ats ((ht_runLC env nm hp Option.none CGoalL.done []).run _ _ _ ats_gen0 trivial h).1

end Raw
end SkaModel
end Formalization
