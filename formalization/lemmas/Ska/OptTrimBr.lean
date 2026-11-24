import lemmas.Ska.OptTrimSim
import lemmas.Ska.OptDriverTopo

/-!
# `TrimBr` through the passes of `+optimize-once`

`TrimBr bl K` asks of every block reachable in `bl` that its body takes the
stack `K o` to a stack that every jump target starts with.  A pass keeps it
(`trimBr_of`) when every block after is reached only through jumps whose
targets are reachable before, and the body of every reachable block after
takes `K o` to the stack its targets start with.

* `+remove-useless-branching` (`rub_trimBr`): the new `%hop` goes to the yes
  side of the old branch, whose stack is the stack at the end, and the
  epilogue `%equ` or `%lob` has no frame (`NoFrame`).
* `+remove-hops` (`hops_trimBr`): a merged block is the chain of a block and
  its one-predecessor hop targets (`MTail`); along the chain each hop target
  starts with the stack at the end of the block before (`TrimBr` of the old
  block), and the `%mov` and `%imm` ops of `hopSeg` have no frame.
* `+remove-empty-middle` (`mid_trimBr`): a jump is redirected through empty
  blocks that end in a `%hop`; an empty reachable block starts and ends with
  the same stack, so its hop target starts with the stack of the redirected
  jump's old target (`rewriteJump_br`, `rewriteHop_br`).
* `+remove-dead-code` (`dead_trimBr`): it drops only `%imm`, `%mov`, `%con`,
  `%hed`, `%tal`, which have no frame (`deadF_br`).
* `+trim-trace-hints` (`trim_trimBr`): it drops both the pushes and the pops
  of a dropped key, so the stacks after are the stacks before with the frames
  of dropped keys filtered out (`trim_br_body`; a pop of a kept key finds its
  frame on top of the filtered stack, since it was on top before).

So every pass that `+optimize-once` runs keeps `TrimBr`, but `+alias`, which
is a parameter of the driver; that is part of its field in `DriverRestT`.
`DriverRestT` is `DriverRest` with `DInvT` (`DInv` and some `TrimBr`) as the
block invariant and the field `trim` replaced by the real pass
(`trimTraceHints`), which is discharged (`trim_fieldT`).  **`optimize_keeps_restT`**:
`optimizeF` keeps the code on blocks with `DInvT`, given the fields `alias`
(with `TrimBr` of its result) and `switch`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-! ## The general form -/

/-- An op without a frame: `brOp` leaves every stack as it is. -/
def NoFrame (op : Pole) : Prop := ∀ g, brOp g op = some g

theorem brBody_noFrame : ∀ (l : List Pole) (g : List (Option TKey)), (∀ op ∈ l, NoFrame op) → brBody g l = some g
  | [], _, _ => rfl
  | op :: l, g, h => by
    simp only [brBody, h op List.mem_cons_self g, Option.bind_some]
    exact brBody_noFrame l g (fun o ho => h o (List.mem_cons_of_mem _ ho))

theorem noFrame_safe {op : Pole} {d : Nat} (h : safeAssign op = some d) : NoFrame op := by
  intro g; cases op <;> simp_all [safeAssign, brOp, traceKey]

/-- **`TrimBr` carried to new blocks.** -/
theorem trimBr_of {bl bl' : Map Blob} {K' : Nat → List (Option TKey)} (hK0 : K' 0 = [])
    (hr : ∀ y b' j', Reach bl y → HoonMap.get bl' y = some b' → j' ∈ getJmps b'.fin → Reach bl j'.there)
    (hb : ∀ o b', Reach bl o → HoonMap.get bl' o = some b' →
      ∃ g, brBody (K' o) b'.body = some g ∧ ∀ j ∈ getJmps b'.fin, K' j.there = g) : TrimBr bl' K' := by
  have hsub : ∀ o, Reach bl' o → Reach bl o := by
    intro o h
    induction h with
    | zero => exact Reach.zero
    | jump _ hb' hj ih => exact hr _ _ _ ih hb' hj
  exact ⟨hK0, fun o b' ho hb' => hb o b' (hsub o ho) hb'⟩

/-- `trimBr_of` with both facts of a reachable block in one. -/
theorem trimBr_of' {bl bl' : Map Blob} {K' : Nat → List (Option TKey)} (hK0 : K' 0 = [])
    (hb : ∀ o b', Reach bl o → HoonMap.get bl' o = some b' →
      ∃ g, brBody (K' o) b'.body = some g ∧ ∀ j ∈ getJmps b'.fin, K' j.there = g ∧ Reach bl j.there) :
    TrimBr bl' K' :=
  trimBr_of hK0 (fun y b' j' hy hb' hj' => by
      obtain ⟨g, -, h⟩ := hb y b' hy hb'
      exact (h j' hj').2)
    (fun o b' ho hb' => by
      obtain ⟨g, h1, h2⟩ := hb o b' ho hb'
      exact ⟨g, h1, fun j hj => (h2 j hj).1⟩)

/-! ## `+remove-useless-branching` -/

section
variable [MapKeys Map]

theorem rub_trimBr {bl bl' : Map Blob} {ch : Bool} {K : Nat → List (Option TKey)}
    (h : removeUselessBranching bl = some (ch, bl')) (hb : TrimBr bl K) : TrimBr bl' K := by
  have H := rub_blocks h
  refine trimBr_of' (bl := bl) hb.1 fun o b' ho hb' => ?_
  obtain ⟨b, e, hb0, he, rfl⟩ := H.back hb'
  obtain ⟨g, hg, hK⟩ := hb.2 o b ho hb0
  simp only [rubBlob]
  rcases rubFin_cases he with rfl | ⟨z, o', nz, -, -, -, -, h2, hf⟩
  · exact ⟨g, by simpa using hg, fun j hj => ⟨hK j hj, Reach.jump ho hb0 hj⟩⟩
  · have hz : z ∈ getJmps b.fin := by
      rcases hf with ⟨s, hf, -⟩ | ⟨s, hf, -⟩ | ⟨l, r, hf, -⟩ | ⟨s, hf, -⟩ <;> simp [hf, getJmps]
    have he1 : ∀ op ∈ e.1, NoFrame op := by
      rcases hf with ⟨s, -, h1⟩ | ⟨s, -, h1⟩ | ⟨l, r, -, h1⟩ | ⟨s, -, h1⟩ <;> rw [h1] <;>
        simp [NoFrame, brOp, traceKey]
    refine ⟨g, by rw [brBody_append, hg, Option.bind_some]; exact brBody_noFrame _ _ he1, fun j hj => ?_⟩
    rw [h2] at hj
    simp only [getJmps, List.mem_singleton] at hj
    subst hj
    exact ⟨hK z hz, Reach.jump (j := z) ho hb0 hz⟩

end

/-! ## `+remove-hops` -/

theorem hopSeg_noFrame : ∀ (as : List (Option Nat)) (ps : List Nat) (acc ops : List Pole),
    (∀ op ∈ acc, NoFrame op) → hopSeg as ps acc = some ops → ∀ op ∈ ops, NoFrame op
  | [], [], acc, ops, h, e => by simp only [hopSeg, Option.some.injEq] at e; subst e; exact h
  | [], _ :: _, _, _, _, e => by simp [hopSeg] at e
  | _ :: _, [], _, _, _, e => by simp [hopSeg] at e
  | a :: as, p :: ps, acc, ops, h, e => by
    simp only [hopSeg] at e
    refine hopSeg_noFrame as ps _ ops (fun op hop => ?_) e
    rcases List.mem_cons.mp hop with rfl | hop
    · intro g; cases a <;> simp [brOp, traceKey]
    · exact h op hop

/-- Along a merged chain the stacks agree. -/
theorem mtail_br {bl : Map Blob} {rev : Map (List Nat)} {K : Nat → List (Option TKey)} (hb : TrimBr bl K)
    {o : Nat} {b : Blob} {T : List Pole} {F : Termin} (h : MTail bl rev o b T F) :
    Reach bl o → HoonMap.get bl o = some b →
      ∃ g, brBody (K o) (b.body ++ T) = some g ∧ ∀ j ∈ getJmps F, K j.there = g ∧ Reach bl j.there := by
  induction h with
  | @stop o b _ =>
    intro ho hb0
    obtain ⟨g, hg, hK⟩ := hb.2 o b ho hb0
    exact ⟨g, by simpa using hg, fun j hj => ⟨hK j hj, Reach.jump ho hb0 hj⟩⟩
  | @link o b t b1 ops T F hf _ hb1 hs _ ih =>
    intro ho hb0
    obtain ⟨g0, hg0, hK0⟩ := hb.2 o b ho hb0
    have ht : t ∈ getJmps b.fin := by simp [hf, getJmps]
    obtain ⟨g, hg, hK⟩ := ih (Reach.jump ho hb0 ht) hb1
    refine ⟨g, ?_, hK⟩
    rw [List.append_assoc ops b1.body T, brBody_append (K o), hg0, Option.bind_some, brBody_append g0 ops,
      brBody_noFrame ops g0 (hopSeg_noFrame _ _ [] ops (fun _ h => absurd h List.not_mem_nil) hs),
      Option.bind_some]
    rw [← hK0 t ht]
    exact hg

theorem hops_trimBr {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} {K : Nat → List (Option TKey)} (hn : topo.Nodup) (h0 : topo.head? = some 0)
    (h : removeHops fuel bl rev topo = some (ch, bl')) (hb : TrimBr bl K) : TrimBr bl' K := by
  have H := hops_blocks hn h0 h
  refine trimBr_of' (bl := bl) hb.1 fun o b' ho hb' => ?_
  obtain ⟨b, T, F, hb0, hmt, rfl⟩ := H.back o b' hb'
  exact mtail_br hb hmt ho hb0

/-! ## `+remove-empty-middle` -/

theorem rewriteJump_br {bl : Map Blob} {K : Nat → List (Option TKey)} (hb : TrimBr bl K) :
    ∀ (n : Nat) (j j' : Jmp), rewriteJump bl n j = some j' → Reach bl j.there →
      K j'.there = K j.there ∧ Reach bl j'.there
  | 0, _, _, h, _ => by simp [rewriteJump] at h
  | n + 1, j, j', h, hr => by
    simp only [rewriteJump] at h
    split at h
    · cases h; exact ⟨rfl, hr⟩
    · obtain ⟨nex, hnex, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · cases h
      · split at h
        · cases h; exact ⟨rfl, hr⟩
        · rename_i hbody
          have hbody' : nex.body = [] := by simpa using hbody
          split at h
          · rename_i t hfin
            split at h
            · cases h; exact ⟨rfl, hr⟩
            · obtain ⟨g, hg, hK⟩ := hb.2 j.there nex hr hnex
              rw [hbody'] at hg
              simp only [brBody, Option.some.injEq] at hg
              subst hg
              have ht : t ∈ getJmps nex.fin := by simp [hfin, getJmps]
              obtain ⟨e1, e2⟩ := rewriteJump_br hb n t j' h (Reach.jump hr hnex ht)
              exact ⟨e1.trans (hK t ht), e2⟩
          · cases h; exact ⟨rfl, hr⟩

theorem rewriteHop_br {bl : Map Blob} {rd : Nat → List Nat} {K : Nat → List (Option TKey)} (hb : TrimBr bl K) :
    ∀ (n : Nat) (j j' : Jmp), rewriteHop bl rd n j = some j' → Reach bl j.there →
      K j'.there = K j.there ∧ Reach bl j'.there
  | 0, _, _, h, _ => by simp [rewriteHop] at h
  | n + 1, j, j', h, hr => by
    simp only [rewriteHop] at h
    obtain ⟨nex, hnex, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h; exact ⟨rfl, hr⟩
    · rename_i hbody
      have hbody' : nex.body = [] := by simpa using hbody
      split at h
      · rename_i t hfin
        split at h
        · cases h; exact ⟨rfl, hr⟩
        · obtain ⟨s, -, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨g, hg, hK⟩ := hb.2 j.there nex hr hnex
          rw [hbody'] at hg
          simp only [brBody, Option.some.injEq] at hg
          subst hg
          have ht : t ∈ getJmps nex.fin := by simp [hfin, getJmps]
          obtain ⟨e1, e2⟩ := rewriteHop_br hb n _ j' h (show Reach bl t.there from Reach.jump hr hnex ht)
          exact ⟨e1.trans (hK t ht), e2⟩
      · cases h; exact ⟨rfl, hr⟩

theorem middleFin_br {bl : Map Blob} {rd : Nat → List Nat} {fuel : Nat} {K : Nat → List (Option TKey)}
    (hb : TrimBr bl K) {f f' : Termin} (h : middleFin bl rd fuel f = some f')
    (hr : ∀ j ∈ getJmps f, Reach bl j.there) :
    ∀ j' ∈ getJmps f', ∃ j ∈ getJmps f, K j'.there = K j.there ∧ Reach bl j'.there := by
  have two : ∀ (z o z' o' : Jmp), rewriteJump bl fuel z = some z' → rewriteJump bl fuel o = some o' →
      Reach bl z.there → Reach bl o.there → ∀ j' ∈ [z', o'], ∃ j ∈ [z, o], K j'.there = K j.there ∧ Reach bl j'.there := by
    intro z o z' o' hz ho rz ro j' hj'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl
    · exact ⟨z, by simp, rewriteJump_br hb fuel z _ hz rz⟩
    · exact ⟨o, by simp, rewriteJump_br hb fuel o _ ho ro⟩
  cases f with
  | clq s z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨z', hz, o', ho, rfl⟩ := h
    exact two z o z' o' hz ho (hr z (by simp [getJmps])) (hr o (by simp [getJmps]))
  | eqq l r z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨z', hz, o', ho, rfl⟩ := h
    exact two z o z' o' hz ho (hr z (by simp [getJmps])) (hr o (by simp [getJmps]))
  | brn s z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨z', hz, o', ho, rfl⟩ := h
    exact two z o z' o' hz ho (hr z (by simp [getJmps])) (hr o (by simp [getJmps]))
  | brz s z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨z', hz, o', ho, rfl⟩ := h
    exact two z o z' o' hz ho (hr z (by simp [getJmps])) (hr o (by simp [getJmps]))
  | hop t =>
    simp only [middleFin, Option.map_eq_some_iff] at h
    obtain ⟨t', ht', rfl⟩ := h
    intro j' hj'
    simp only [getJmps, List.mem_singleton] at hj'
    subst hj'
    exact ⟨t, by simp [getJmps], rewriteHop_br hb fuel t _ ht' (hr t (by simp [getJmps]))⟩
  | lti n s z o =>
    simp only [middleFin, Option.some.injEq] at h
    subst h
    exact fun j' hj' => ⟨j', hj', rfl, hr j' hj'⟩
  | jmp => simp only [middleFin, Option.some.injEq] at h; subst h; simp [getJmps]
  | jmf => simp only [middleFin, Option.some.injEq] at h; subst h; simp [getJmps]
  | jsp => simp only [middleFin, Option.some.injEq] at h; subst h; simp [getJmps]
  | jsf => simp only [middleFin, Option.some.injEq] at h; subst h; simp [getJmps]
  | don => simp only [middleFin, Option.some.injEq] at h; subst h; simp [getJmps]
  | bom => simp only [middleFin, Option.some.injEq] at h; subst h; simp [getJmps]

section
variable [MapKeys Map]

theorem mid_trimBr {fuel : Nat} {bl bl' : Map Blob} {ch : Bool} {K : Nat → List (Option TKey)}
    (h : removeEmptyMiddle fuel bl = some (ch, bl')) (hb : TrimBr bl K) : TrimBr bl' K := by
  have H := mid_blocks h
  refine trimBr_of' (bl := bl) hb.1 fun o b' ho hb' => ?_
  obtain ⟨b, f', hb0, hf', rfl⟩ := H.back hb'
  obtain ⟨g, hg, hK⟩ := hb.2 o b ho hb0
  refine ⟨g, hg, fun j' hj' => ?_⟩
  obtain ⟨j, hj, e1, e2⟩ := middleFin_br hb hf' (fun j hj => Reach.jump ho hb0 hj) j' hj'
  exact ⟨e1.trans (hK j hj), e2⟩

end

/-! ## `+remove-dead-code` -/

theorem deadF_br : ∀ (l : List Pole) (S : List Nat) (g : List (Option TKey)), brBody g (deadF l S).1 = brBody g l
  | [], _, _ => rfl
  | p :: rest, S, g => by
    rcases deadF_cons p rest S with h | ⟨d, hd, -, h⟩
    · rw [h]
      simp only [brBody]
      cases brOp g p with
      | none => rfl
      | some g' => exact deadF_br rest S g'
    · rw [h, deadF_br rest S g]
      simp only [brBody, noFrame_safe hd g, Option.bind_some]

theorem dead_trimBr {bl bl' : Map Blob} {topo : List Nat} {K : Nat → List (Option TKey)} (ht : TopoOK bl topo)
    (h : removeDeadCode bl topo.reverse = some bl') (hb : TrimBr bl K) : TrimBr bl' K := by
  obtain ⟨Sf, DW⟩ := dead_walk ht h
  refine trimBr_of' (bl := bl) hb.1 fun o b' ho hb' => ?_
  obtain ⟨b, hb0, hb1, -⟩ := DW.blk o (ht.2.2.2.1 o ho)
  rw [hb1] at hb'; cases hb'
  obtain ⟨g, hg, hK⟩ := hb.2 o b ho hb0
  exact ⟨g, by rw [deadF_br]; exact hg, fun j hj => ⟨hK j hj, Reach.jump ho hb0 hj⟩⟩

/-! ## `+trim-trace-hints` -/

/-- The frames the code after keeps: those without key and those of keys not
dropped. -/
def kf (uns : Uns) (opened : List TKey) : Option TKey → Bool
  | some k => !(!uns k && decide (k ∈ opened))
  | none => true

theorem tkeep_of {uns : Uns} {opened : List TKey} {op : Pole} {b : Bool} {k : TKey}
    (he : traceKey op = some (b, k)) : tkeep uns opened op = kf uns opened (some k) := by
  simp [tkeep, trimDrop, he, kf]

theorem brOp_pop_some {op : Pole} {k : TKey} {g : List (Option TKey)} (he : traceKey op = some (false, k)) :
    brOp (some k :: g) op = some g := by
  unfold brOp; rw [he]; simp

/-- One op: the filtered stacks follow the filtered body. -/
theorem trim_brOp (uns : Uns) (opened : List TKey) {op : Pole} {g g1 : List (Option TKey)}
    (h : brOp g op = some g1) :
    (tkeep uns opened op = true → brOp (g.filter (kf uns opened)) op = some (g1.filter (kf uns opened))) ∧
    (tkeep uns opened op = false → g.filter (kf uns opened) = g1.filter (kf uns opened)) := by
  cases e : traceKey op with
  | some p =>
    obtain ⟨b, k⟩ := p
    rw [tkeep_of e]
    cases b with
    | true =>
      rw [brOp_push e h]
      refine ⟨fun hk => ?_, fun hk => ?_⟩
      · unfold brOp; rw [e]; simp [List.filter_cons, hk]
      · simp [List.filter_cons, hk]
    | false =>
      rw [brOp_pop e h]
      refine ⟨fun hk => ?_, fun hk => ?_⟩
      · simp only [List.filter_cons, hk, if_true]; exact brOp_pop_some e
      · simp [List.filter_cons, hk]
  | none =>
    have hkp : tkeep uns opened op = true := by simp [tkeep, trimDrop, e]
    refine ⟨fun _ => ?_, fun hk => by rw [hkp] at hk; cases hk⟩
    cases op with
    | hdp n p f =>
      simp only [brOp, e] at h ⊢
      split at h
      · rename_i hs; simp only [Option.some.injEq] at h; subst h; simp [hs, List.filter_cons, kf]
      · rename_i hs; simp only [Option.some.injEq] at h; subst h; simp [hs]
    | hde n p f =>
      simp only [brOp, e] at h ⊢
      split at h
      · rename_i hs
        rcases g with _ | ⟨_ | k', g0⟩
        · cases h
        · simp only [Option.some.injEq] at h; subst h; simp [hs, List.filter_cons, kf]
        · cases h
      · rename_i hs; simp only [Option.some.injEq] at h; subst h; simp [hs]
    | hmp => simp [traceKey] at e
    | hme => simp [traceKey] at e
    | hcp => simp [traceKey] at e
    | hce => simp [traceKey] at e
    | _ => simp only [brOp, e, Option.some.injEq] at h ⊢; subst h; rfl

theorem trim_br_body (uns : Uns) (opened : List TKey) : ∀ (l : List Pole) (g g' : List (Option TKey)),
    brBody g l = some g' →
    brBody (g.filter (kf uns opened)) (l.filter (tkeep uns opened)) = some (g'.filter (kf uns opened))
  | [], g, g', h => by simp only [brBody, Option.some.injEq] at h; subst h; rfl
  | op :: l, g, g', h => by
    simp only [brBody, Option.bind_eq_some_iff] at h
    obtain ⟨g1, h1, h2⟩ := h
    have ih := trim_br_body uns opened l g1 g' h2
    obtain ⟨hk, hd⟩ := trim_brOp uns opened h1
    rw [List.filter_cons]
    cases e : tkeep uns opened op with
    | true => simp only [if_true, brBody, hk e, Option.bind_some]; exact ih
    | false => simp only [Bool.false_eq_true, if_false]; rw [hd e]; exact ih

section
variable [MapKeys Map]

/-- **`+trim-trace-hints` keeps `TrimBr`**, with the frames of dropped keys
filtered out of every stack. -/
theorem trim_trimBr {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {bl' : Map Blob}
    {K : Nat → List (Option TKey)} (h : trimTraceHints bl topo rev = some bl') (hb : TrimBr bl K) :
    ∃ K', TrimBr bl' K' := by
  unfold trimTraceHints at h
  obtain ⟨uns, -, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨fun o => (K o).filter (kf uns (trimOpened bl)), trimBr_of' (bl := bl) (by rw [hb.1]; rfl) fun o b' ho hb' => ?_⟩
  rw [trimRun_get] at hb'
  obtain ⟨b, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb'
  obtain ⟨g, hg, hK⟩ := hb.2 o b ho hb0
  exact ⟨g.filter (kf uns (trimOpened bl)), trim_br_body uns _ b.body (K o) g hg,
    fun j hj => ⟨by rw [hK j hj], Reach.jump ho hb0 hj⟩⟩

/-- `+trim-trace-hints` keeps the parameters and the end of every block. -/
theorem trim_shape {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {bl' : Map Blob}
    (h : trimTraceHints bl topo rev = some bl') :
    SameShape bl bl' ∧ ∀ k, (HoonMap.get bl' k).isSome = (HoonMap.get bl k).isSome := by
  unfold trimTraceHints at h
  obtain ⟨uns, -, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨fun k b' hb' => ?_, fun k => ?_⟩
  · rw [trimRun_get] at hb'
    obtain ⟨b, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb'
    exact ⟨b, hb0, rfl, rfl⟩
  · rw [trimRun_get]; cases HoonMap.get bl k <;> rfl

/-! ## The driver with `TrimBr` -/

/-- The block invariant with bracketed hints. -/
def DInvT (bl : Map Blob) : Prop := DInv bl ∧ ∃ K, TrimBr bl K

/-- **The field `trim`**, for the real pass, at `DInvT`. -/
theorem trim_fieldT {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {bl' : Map Blob}
    (hb : DInvT bl) (hi : TopoInv bl topo rev) (h : trimTraceHints bl topo rev = some bl') :
    KeepsB bl bl' ∧ DInvT bl' ∧ TopoInv bl' topo rev := by
  obtain ⟨hd, K, hK⟩ := hb
  obtain ⟨hs, hm⟩ := trim_shape h
  refine ⟨fun c hc => ?_, ⟨sameShape_inv hs hd, trim_trimBr h hK⟩,
    topoInv_sub hi (fun k b' hb' => ?_) fun o ho => by rw [hm]; exact hi.1.2.2.1 o ho⟩
  · subst hc; exact trim_keeps c hi.1 hi.2 hK h
  · obtain ⟨b, hb, -, hfin⟩ := hs k b' hb'
    exact ⟨b, hb, fun j' hj' => ⟨j', by rw [← hfin]; exact hj', rfl⟩⟩

/-- **What the driver still assumes**, at `DInvT`: `+alias` keeps the code,
`DInv`, `TopoInv` of the filtered `topo`, and gives bracketed hints again; the
trim pass is the real one; `+switch-chains` keeps the code. -/
structure DriverRestT (fuel : Nat) (P : Passes Map) : Prop where
  alias : ∀ n (bl : Map Blob) topo rev f bl', DInvT bl → TopoInv bl topo rev → P.alias n bl rev topo = some (f, bl') →
    KeepsB bl bl' ∧ DInvT bl' ∧
      TopoInv bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome))
  trim : P.trim = trimTraceHints
  switch : ∀ (bl : Map Blob) bl', DInvT bl → P.switch bl = some bl' → KeepsB bl bl'

theorem driverHypT_of {fuel : Nat} {P : Passes Map} (H : DriverRestT fuel P) : DriverHyp fuel P DInvT TopoInv where
  topo := fun _ _ hb h => topo_field hb.1 h
  hops := fun _ _ _ _ _ hb hi h => by
    obtain ⟨k, d, t⟩ := hops_fieldD hb.1 hi h
    obtain ⟨K, hK⟩ := hb.2
    exact ⟨k, ⟨d, K, hops_trimBr hi.1.1 hi.1.2.1 h hK⟩, t⟩
  rub := fun _ _ _ _ _ hb h => by
    obtain ⟨k, d, t⟩ := rub_fieldD hb.1 h
    obtain ⟨K, hK⟩ := hb.2
    exact ⟨k, ⟨d, K, rub_trimBr h hK⟩, t⟩
  middle := fun _ _ _ _ _ hb h => by
    obtain ⟨k, d, t⟩ := middle_fieldD hb.1 h
    obtain ⟨K, hK⟩ := hb.2
    exact ⟨k, ⟨d, K, mid_trimBr h hK⟩, t⟩
  alias := H.alias
  trim := fun bl topo rev bl' hb hi h => by
    rw [H.trim] at h
    exact trim_fieldT hb hi h
  dead := fun bl topo rev bl' hb hi h => by
    obtain ⟨K, hK⟩ := hb.2
    obtain ⟨d, t⟩ := dead_inv hb.1 hi h
    exact ⟨fun c hc => by subst hc; exact dead_keeps c hi.1 h, ⟨d, K, dead_trimBr hi.1 h hK⟩, t⟩
  switch := H.switch

/-- **`+optimize` keeps the code** on blocks with `DInvT` (`DInv` and
bracketed trace hints), with the real `+trim-trace-hints`, given that
`+alias` keeps the code and the invariants (`TrimBr` among them) and that
`+switch-chains` keeps the code. -/
theorem optimize_keeps_restT {fuel : Nat} {P : Passes Map} (H : DriverRestT fuel P) {s s' : Straight Map}
    (hb : DInvT s.blocks) (h : optimizeF fuel P s = some s') : Keeps s s' :=
  optimize_keeps (driverHypT_of H) hb h

end

end Opt
end SkaModel
end Formalization
