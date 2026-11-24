import lemmas.Ska.OptSwitch

/-!
# `+switch-chains`: the search tree and the cases

Two standalone facts about the model of `OptSwitch.lean`, the parts (a) and
(b) of the decomposition of `SwitchKeepsM`.

(b) `cases_spec`: `casesOf` returns the cases sorted by their constants,
strictly (so without two cases of one constant), and for every constant `a`
the case of `a` it keeps is the first case of `a` in the chain (`find?`).
Through `casesAcc_spec` (the loop keeps the first of each constant) and
`hsort_mem`, `hsort_sorted` (the quicksort of hoon.hoon returns the same
members, sorted, when the keys are distinct).

(a) `stree_go`: the tree that `stree` builds, followed by the meaning of its
ends (`treeGo`: an `%lti c` goes to its first target on an atom below `c`,
else to the second, a cell included; a leaf `%imm c r` then `%eqq d r` hits
when the value is `c`), takes the hit of the case whose constant is the value
of `d` and the miss otherwise (`pickHit`), on every map that holds the nodes
under the labels it used, and the map it returns differs from the one it was
given only at those labels.  For example a cell goes to the right of every
`%lti` and misses at its leaf, since no case has a cell as its constant.
`treeGo_exec` links `treeGo` to the interpreter: running the root runs the
target block on registers that differ only at the register of one leaf.

`tag_tree` and `plain_tree` put the two together for `switchTag` and
`switchPlain`: the tree of the new block holds the hit of the first test of
the chain whose constant is the value, as the chain does (`chainPick`,
`plainPick`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

variable {Map : Type → Type} [HoonMap Map]

open Nock

/-! ## (b) The cases -/

/-- The loop of `cases` keeps, for every constant not yet seen, the first case
of it in the chain. -/
theorem casesAcc_spec : ∀ (ces : List SCase) (saw : List Nat) (acc : List SCase),
    (∀ x ∈ acc, x.c ∈ saw) → (acc.map SCase.c).Nodup →
    ((casesAcc ces saw acc).map SCase.c).Nodup ∧
    ∀ a x, (x ∈ casesAcc ces saw acc ∧ x.c = a) ↔
      ((x ∈ acc ∧ x.c = a) ∨ (a ∉ saw ∧ ces.find? (fun y => decide (y.c = a)) = some x))
  | [], saw, acc, _, hn => by
    refine ⟨hn, fun a x => ?_⟩
    simp [casesAcc]
  | y :: t, saw, acc, hs, hn => by
    by_cases hy : y.c ∈ saw
    · have := casesAcc_spec t saw acc hs hn
      simp only [casesAcc, hy, if_true]
      refine ⟨this.1, fun a x => ?_⟩
      rw [this.2 a x]
      by_cases hya : y.c = a
      · subst hya
        simp [hy]
      · simp [hya]
    · have hs' : ∀ x ∈ y :: acc, x.c ∈ y.c :: saw := by
        intro x hx
        rcases List.mem_cons.mp hx with h | h
        · subst h; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hs x h)
      have hn' : ((y :: acc).map SCase.c).Nodup := by
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun h => ?_, hn⟩
        obtain ⟨z, hz, hzc⟩ := List.mem_map.mp h
        exact hy (hzc ▸ hs z hz)
      have := casesAcc_spec t (y.c :: saw) (y :: acc) hs' hn'
      simp only [casesAcc, hy, if_false]
      refine ⟨this.1, fun a x => ?_⟩
      rw [this.2 a x]
      by_cases hya : y.c = a
      · subst hya
        constructor
        · rintro (⟨hx, hxc⟩ | ⟨hm, _⟩)
          · rcases List.mem_cons.mp hx with h | h
            · subst h; right; simp [hy]
            · exact absurd (hxc ▸ hs x h) hy
          · exact absurd List.mem_cons_self hm
        · rintro (⟨hx, hxc⟩ | ⟨_, hf⟩)
          · exact absurd (hxc ▸ hs x hx) hy
          · simp at hf
            subst hf
            left; exact ⟨List.mem_cons_self, rfl⟩
      · have hne : ∀ x, x.c = a → x ≠ y := fun x hx h => hya (h ▸ hx)
        constructor
        · rintro (⟨hx, hxc⟩ | ⟨hm, hf⟩)
          · rcases List.mem_cons.mp hx with h | h
            · exact absurd h (hne x hxc)
            · left; exact ⟨h, hxc⟩
          · right
            refine ⟨fun h => hm (List.mem_cons_of_mem _ h), ?_⟩
            simp [hya, hf]
        · rintro (⟨hx, hxc⟩ | ⟨hm, hf⟩)
          · left; exact ⟨List.mem_cons_of_mem _ hx, hxc⟩
          · right
            refine ⟨?_, ?_⟩
            · intro h
              rcases List.mem_cons.mp h with h | h
              · exact hya h.symm
              · exact hm h
            · simpa [List.find?_cons, hya] using hf

/-- The lesser-than of `cases`. -/
def caseLt (a b : SCase) : Bool := decide (a.c < b.c)

/-- The quicksort returns the members it was given. -/
theorem hsort_mem {α : Type} (lt : α → α → Bool) : ∀ (n : Nat) (l R : List α),
    hsort lt n l = some R → ∀ x, x ∈ R ↔ x ∈ l
  | _, [], R, h => by
    simp [hsort] at h; subst h; simp
  | 0, _ :: _, R, h => by simp [hsort] at h
  | n + 1, a :: t, R, h => by
    simp only [hsort, List.partition_eq_filter_filter] at h
    cases hp : hsort lt n (t.filter fun c => lt c a) with
    | none => simp [hp] at h
    | some p =>
      cases hq : hsort lt n (t.filter (not ∘ fun c => lt c a)) with
      | none => simp [hp, hq] at h
      | some q =>
        simp [hp, hq] at h
        subst h
        intro x
        have e1 := hsort_mem lt n _ p hp x
        have e2 := hsort_mem lt n _ q hq x
        simp only [List.mem_append, List.mem_cons, e1, e2, List.mem_filter, Function.comp]
        by_cases hx : lt x a <;> simp [hx, or_comm]

/-- The quicksort of cases with distinct constants returns them sorted,
strictly. -/
theorem hsort_sorted : ∀ (n : Nat) (l R : List SCase),
    (l.map SCase.c).Nodup → hsort caseLt n l = some R → R.Pairwise (fun a b => a.c < b.c)
  | _, [], R, _, h => by
    simp [hsort] at h; subst h; simp
  | 0, _ :: _, R, _, h => by simp [hsort] at h
  | n + 1, a :: t, R, hn, h => by
    simp only [hsort, List.partition_eq_filter_filter] at h
    have hn' := List.nodup_cons.mp (by simpa using hn : (a.c :: t.map SCase.c).Nodup)
    have n1 : ((t.filter fun c => caseLt c a).map SCase.c).Nodup :=
      List.Nodup.sublist (List.filter_sublist.map _) hn'.2
    have n2 : ((t.filter (not ∘ fun c => caseLt c a)).map SCase.c).Nodup :=
      List.Nodup.sublist (List.filter_sublist.map _) hn'.2
    cases hp : hsort caseLt n (t.filter fun c => caseLt c a) with
    | none => simp [hp] at h
    | some p =>
      cases hq : hsort caseLt n (t.filter (not ∘ fun c => caseLt c a)) with
      | none => simp [hp, hq] at h
      | some q =>
        simp [hp, hq] at h
        subst h
        have sp := hsort_sorted n _ p n1 hp
        have sq := hsort_sorted n _ q n2 hq
        have mp := hsort_mem caseLt n _ p hp
        have mq := hsort_mem caseLt n _ q hq
        have hq' : ∀ b ∈ q, a.c < b.c := by
          intro b hb
          have hb' := (mq b).mp hb
          simp only [List.mem_filter, Function.comp, caseLt, Bool.not_eq_true', decide_eq_false_iff_not] at hb'
          have hne : b.c ≠ a.c := fun he => hn'.1 (he ▸ List.mem_map_of_mem hb'.1)
          omega
        have hp' : ∀ b ∈ p, b.c < a.c := by
          intro b hb
          have hb' := (mp b).mp hb
          simp only [List.mem_filter, caseLt, decide_eq_true_eq] at hb'
          exact hb'.2
        rw [List.pairwise_append, List.pairwise_cons]
        refine ⟨sp, ⟨hq', sq⟩, fun x hx y hy => ?_⟩
        rcases List.mem_cons.mp hy with h | h
        · subst h; exact hp' x hx
        · exact Nat.lt_trans (hp' x hx) (hq' y h)

/-- **(b)** `casesOf` returns the cases sorted strictly by their constants,
and the case of a constant `a` it keeps is the first case of `a` in the
chain. -/
theorem cases_spec {ces cas : List SCase} (h : casesOf ces = some cas) :
    cas.Pairwise (fun a b => a.c < b.c) ∧
    ∀ a x, (x ∈ cas ∧ x.c = a) ↔ ces.find? (fun y => decide (y.c = a)) = some x := by
  have hs := casesAcc_spec ces [] [] (by simp) (by simp)
  simp only [casesOf] at h
  have hm := hsort_mem caseLt _ _ _ h
  refine ⟨hsort_sorted _ _ _ hs.1 h, fun a x => ?_⟩
  rw [hm x, hs.2 a x]
  simp

/-! ## (a) The tree -/

/-- The target of the chain at the value `v`: the hit of the first case whose
constant is `v`, else the miss. -/
def pickHit (cas : List SCase) (mis : Nat) (v : Noun) : Nat :=
  match cas.find? (fun x => decide (v = A x.c)) with
  | some x => x.hit
  | none => mis

/-- The test of `%lti c`: an atom below `c`. -/
def ltOf (c : Nat) : Noun → Bool
  | Noun.atom a => decide (a < c)
  | _ => false

/-- The tree followed by the meaning of its ends, from the block `b`, on the
value `v` of `d`: an `%lti` on `d` that passes nothing goes on to the block it
takes, a leaf (`%imm c r` and `%eqq d r` that pass nothing, `r` in `rs` and
not `d`) gives its hit when `v` is `c`, else its miss. -/
def treeGo (M : Map Blob) (d : Nat) (rs : List Nat) (v : Noun) : Nat → Blob → Option Nat
  | 0, _ => none
  | n + 1, ⟨[], [], Termin.lti c d' ⟨[], l⟩ ⟨[], r⟩⟩ =>
    if d' = d then (HoonMap.get M (if ltOf c v then l else r)).bind (treeGo M d rs v n) else none
  | _ + 1, ⟨[], [Pole.imm (Noun.atom c) r], Termin.eqq d' r' ⟨[], hit⟩ ⟨[], mis⟩⟩ =>
    if d' = d ∧ r' = r ∧ r ≠ d ∧ r ∈ rs then some (if v = A c then hit else mis) else none
  | _ + 1, _ => none

theorem pickHit_left {L R : List SCase} {mis : Nat} {v : Noun} (h : ∀ x ∈ R, v ≠ A x.c) :
    pickHit (L ++ R) mis v = pickHit L mis v := by
  have : R.find? (fun x => decide (v = A x.c)) = none :=
    List.find?_eq_none.mpr fun x hx => by simpa using h x hx
  simp only [pickHit, List.find?_append, this, Option.or_none]

theorem pickHit_right {L R : List SCase} {mis : Nat} {v : Noun} (h : ∀ x ∈ L, v ≠ A x.c) :
    pickHit (L ++ R) mis v = pickHit R mis v := by
  have : L.find? (fun x => decide (v = A x.c)) = none :=
    List.find?_eq_none.mpr fun x hx => by simpa using h x hx
  simp only [pickHit, List.find?_append, this, Option.none_or]

/-- The split of an `%lti` node: on a value it takes to the first target no
case of the upper half has the value as its constant, on one it takes to the
second no case of the lower half has. -/
theorem pick_split {all tl : List SCase} {h0 : SCase} {haf mis : Nat} {v : Noun}
    (hpw : all.Pairwise (fun a b => a.c < b.c)) (hd : all.drop haf = h0 :: tl) :
    pickHit all mis v = (if ltOf h0.c v then pickHit (all.take haf) mis v else pickHit (h0 :: tl) mis v) := by
  have e := List.take_append_drop haf all
  rw [hd] at e
  have hpw' : (all.take haf ++ h0 :: tl).Pairwise (fun a b => a.c < b.c) := by rw [e]; exact hpw
  rw [List.pairwise_append, List.pairwise_cons] at hpw'
  have hall : pickHit all mis v = pickHit (all.take haf ++ h0 :: tl) mis v := by rw [e]
  rw [hall]
  cases hl : ltOf h0.c v
  · simp only [Bool.false_eq_true, if_false]
    refine pickHit_right fun x hx he => ?_
    have := hpw'.2.2 x hx h0 List.mem_cons_self
    subst he
    simp [ltOf, this] at hl
  · simp only [if_true]
    refine pickHit_left fun x hx he => ?_
    cases v with
    | cell _ _ => simp [ltOf] at hl
    | atom a =>
      simp only [ltOf, decide_eq_true_eq] at hl
      simp only [A, Noun.atom.injEq] at he
      subst he
      rcases List.mem_cons.mp hx with h | h
      · subst h; omega
      · have := hpw'.2.1.1 x h; omega

/-- **(a)** The tree of `stree` on cases sorted strictly by their constants
takes the hit of the case whose constant is the value and the miss
otherwise, on every map that holds its nodes at the labels it used; the map
it returns is the one it was given but at those labels, which are the first
of `ids`. -/
theorem stree_go (d mis : Nat) (rs : List Nat) : ∀ (n : Nat) (cas : List SCase) (ids : List Nat)
    (out : Map Blob) (nb : List Pole) (nf : Termin) (ids' : List Nat) (out' : Map Blob),
    stree d mis n cas ids out = some (nb, nf, ids', out') →
    cas.Pairwise (fun a b => a.c < b.c) → (∀ x ∈ cas, x.r ≠ d ∧ x.r ∈ rs) → ids.Nodup →
    ∃ used, ids = used ++ ids' ∧
      (∀ k, k ∉ used → HoonMap.get out' k = HoonMap.get out k) ∧
      ∀ (M : Map Blob), (∀ k ∈ used, HoonMap.get M k = HoonMap.get out' k) →
        ∀ v, treeGo M d rs v n ⟨[], nb, nf⟩ = some (pickHit cas mis v)
  | 0, cas, ids, out, nb, nf, ids', out', h, _, _, _ => by simp [stree] at h
  | n + 1, [], ids, out, nb, nf, ids', out', h, _, _, _ => by simp [stree] at h
  | n + 1, [x], ids, out, nb, nf, ids', out', h, _, hr, _ => by
    simp only [stree, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨[], by simp, fun _ _ => rfl, fun M _ v => ?_⟩
    have hx := hr x List.mem_cons_self
    by_cases hv : v = A x.c
    · simp [treeGo, pickHit, hx.1, hx.2, hv]
    · simp [treeGo, pickHit, hx.1, hx.2, hv]
  | n + 1, x :: y :: t, ids, out, nb, nf, ids', out', h, hpw, hr, hnd => by
    rw [stree.eq_def] at h
    simp only at h
    generalize hall : x :: y :: t = all at h hpw hr ⊢
    generalize (all.length / 2) = haf at h
    cases hd : List.drop haf all with
    | nil => rw [hd] at h; simp at h
    | cons h0 tl =>
    rw [hd] at h
    rcases ids with _ | ⟨lid, _ | ⟨rid, rest⟩⟩
    · simp at h
    · simp at h
    simp only at h
    cases hL : stree d mis n (all.take haf) rest out with
    | none => simp [hL] at h
    | some L =>
    obtain ⟨lb, lf, lids, lout⟩ := L
    simp only [hL, Option.bind_some] at h
    cases hR : stree d mis n (h0 :: tl) lids (HoonMap.put lout lid ⟨[], lb, lf⟩) with
    | none => simp [hR] at h
    | some R =>
    obtain ⟨rb, rf, rids, rout⟩ := R
    simp only [hR, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    have pwT : (all.take haf).Pairwise (fun a b => a.c < b.c) := hpw.sublist (List.take_sublist _ _)
    have pwD : (h0 :: tl).Pairwise (fun a b => a.c < b.c) := hd ▸ hpw.sublist (List.drop_sublist _ _)
    have hrT : ∀ x ∈ all.take haf, x.r ≠ d ∧ x.r ∈ rs := fun x hx => hr x (List.mem_of_mem_take hx)
    have hrD : ∀ x ∈ h0 :: tl, x.r ≠ d ∧ x.r ∈ rs := fun x hx =>
      hr x (List.mem_of_mem_drop (hd ▸ hx : x ∈ all.drop haf))
    have ndRest : rest.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
    obtain ⟨usedL, eL, frL, goL⟩ := stree_go d mis rs n _ rest out lb lf lids lout hL pwT hrT ndRest
    have ndLids : lids.Nodup := by rw [eL] at ndRest; exact (List.nodup_append.mp ndRest).2.1
    obtain ⟨usedR, eR, frR, goR⟩ := stree_go d mis rs n _ lids _ rb rf rids rout hR pwD hrD ndLids
    subst eL; subst eR
    have nd := hnd
    simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at nd
    obtain ⟨⟨hlr, hlL, hlR, -⟩, ⟨hrL, hrR, -⟩, ndA⟩ := nd
    have hLR : ∀ k ∈ usedL, k ∉ usedR := fun k hk hk' =>
      (List.nodup_append.mp ndA).2.2 k hk k (List.mem_append_left _ hk') rfl
    refine ⟨lid :: rid :: (usedL ++ usedR), by simp, fun k hk => ?_, fun M hM v => ?_⟩
    · simp only [List.mem_cons, List.mem_append, not_or] at hk
      rw [HoonMap.get_put, if_neg hk.2.1, frR k hk.2.2.2, HoonMap.get_put, if_neg hk.1, frL k hk.2.2.1]
    · have oL : HoonMap.get (HoonMap.put rout rid (⟨[], rb, rf⟩ : Blob)) lid = some ⟨[], lb, lf⟩ := by
        rw [HoonMap.get_put, if_neg hlr, frR lid hlR, HoonMap.get_put, if_pos rfl]
      have oR : HoonMap.get (HoonMap.put rout rid (⟨[], rb, rf⟩ : Blob)) rid = some ⟨[], rb, rf⟩ := by
        rw [HoonMap.get_put, if_pos rfl]
      have mL := (hM lid (by simp)).trans oL
      have mR := (hM rid (by simp)).trans oR
      have aL : ∀ k ∈ usedL, HoonMap.get M k = HoonMap.get lout k := by
        intro k hk
        have hne1 : k ≠ rid := fun h => hrL (h ▸ hk)
        have hne2 : k ≠ lid := fun h => hlL (h ▸ hk)
        rw [hM k (by simp [hk]), HoonMap.get_put, if_neg hne1, frR k (hLR k hk), HoonMap.get_put,
          if_neg hne2]
      have aR : ∀ k ∈ usedR, HoonMap.get M k = HoonMap.get rout k := by
        intro k hk
        have hne1 : k ≠ rid := fun h => hrR (h ▸ hk)
        rw [hM k (by simp [hk]), HoonMap.get_put, if_neg hne1]
      rw [pick_split hpw hd]
      cases hl : ltOf h0.c v
      · simp [treeGo, hl, mR, goR M aR v]
      · simp [treeGo, hl, mL, goL M aL v]


section
variable {σ : Type}

/-- **`treeGo` in the interpreter**: running the root of a tree on registers
where `d` holds `v` runs the target block that `treeGo` names, on the
registers with one leaf register of `rs` set. -/
theorem treeGo_exec (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ)
    (trace : Trace) {d : Nat} {rs : List Nat} {v : Noun} :
    ∀ (n : Nat) (b : Blob) (regs : Map (Option Noun)) (k : Nat), read d regs = some v →
      treeGo c.blocks d rs v n b = some k →
      ∃ r ∈ rs, ∃ w, execBlob lib O c gul st regs trace b [] =
        (HoonMap.get c.blocks k).bind fun b' => execBlob lib O c gul st (store r w regs) trace b' []
  | 0, b, regs, k, _, h => by simp [treeGo] at h
  | n + 1, b, regs, k, hv, h => by
    rw [treeGo.eq_def] at h
    split at h
    · simp at h
    · rename_i n' c0 d' l r heq
      obtain rfl : n = n' := Nat.succ.inj heq
      by_cases hd' : d' = d
      · subst hd'
        simp only [if_true] at h
        cases hg : HoonMap.get c.blocks (if ltOf c0 v then l else r) with
        | none => simp [hg] at h
        | some b'' =>
        simp only [hg, Option.bind_some] at h
        obtain ⟨r', hr', w, e⟩ := treeGo_exec lib O c gul st trace n b'' regs k hv h
        refine ⟨r', hr', w, ?_⟩
        rw [execBlob]
        simp only [ne_eq, not_true_eq_false, or_self, if_false, hv, Option.bind_eq_bind,
          Option.bind_some]
        cases v with
        | cell _ _ => simp only [ltOf, Bool.false_eq_true, if_false] at hg; simp [hg, e]
        | atom a =>
          by_cases ha : a < c0
          · simp only [ltOf, ha, decide_true, if_true] at hg; simp [ha, hg, e]
          · simp only [ltOf, ha, decide_false, Bool.false_eq_true, if_false] at hg; simp [ha, hg, e]
      · simp [hd'] at h
    · rename_i n' c0 r0 d' r' hit mis heq
      by_cases hc : d' = d ∧ r' = r0 ∧ r0 ≠ d ∧ r0 ∈ rs
      · obtain ⟨rfl, rfl, hne, hin⟩ := hc
        simp only [hne, hin, ne_eq, not_false_eq_true, and_self, if_true, Option.some.injEq] at h
        refine ⟨r', hin, A c0, ?_⟩
        rw [execBlob]
        simp only [ne_eq, not_true_eq_false, or_self, if_false]
        simp only [execPole, localPole, Option.map_some, Option.bind_eq_bind, Option.bind_some]
        rw [execBlob]
        simp only [ne_eq, not_true_eq_false, or_self, if_false]
        rw [read_store_other (Ne.symm hne), hv, read_store_self]
        subst h
        by_cases hvc : v = A c0 <;> simp [hvc]
      · simp [hc] at h
    · simp at h

end

/-! ## The tree against the chain -/

/-- Two members of a list sorted strictly by their constants with one
constant are one. -/
theorem sorted_uniq : ∀ {l : List SCase}, l.Pairwise (fun a b => a.c < b.c) →
    ∀ {x y : SCase}, x ∈ l → y ∈ l → x.c = y.c → x = y
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | z :: t, hp, x, y, hx, hy, he => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · have := hp.1 y hy'; omega
    · have := hp.1 x hx'; omega
    · exact sorted_uniq hp.2 hx' hy' he

/-- The search over the cases `casesOf` keeps takes the target of the first
case of the value. -/
theorem pickHit_cases {ces cas : List SCase} (h : casesOf ces = some cas) (mis : Nat) (v : Noun) :
    pickHit cas mis v = pickHit ces mis v := by
  obtain ⟨hpw, hsp⟩ := cases_spec h
  cases v with
  | cell p q =>
    have e1 : ∀ l : List SCase, l.find? (fun x => decide (Noun.cell p q = A x.c)) = none :=
      fun l => List.find?_eq_none.mpr (by simp [A])
    simp only [pickHit, e1]
  | atom a =>
    have ep : (fun x : SCase => decide (Noun.atom a = A x.c)) = fun x => decide (x.c = a) := by
      funext x; simp [A, eq_comm]
    simp only [pickHit, ep]
    cases hf : ces.find? (fun y => decide (y.c = a)) with
    | some x =>
      have hx := (hsp a x).mpr hf
      cases hg : cas.find? (fun y => decide (y.c = a)) with
      | none =>
        have := List.find?_eq_none.mp hg x hx.1
        simp [hx.2] at this
      | some z =>
        have hz := List.mem_of_find?_eq_some hg
        have hzc := List.find?_some hg
        simp only [decide_eq_true_eq] at hzc
        rw [sorted_uniq hpw hz hx.1 (hzc.trans hx.2.symm)]
    | none =>
      cases hg : cas.find? (fun y => decide (y.c = a)) with
      | none => rfl
      | some z =>
        have hz := List.mem_of_find?_eq_some hg
        have hzc := List.find?_some hg
        simp only [decide_eq_true_eq] at hzc
        have := (hsp a z).mp ⟨hz, hzc⟩
        rw [hf] at this; cases this

/-- The case a test of the tagged chain makes. -/
def tagCase (t : STest) : SCase := ⟨t.c, t.hit, t.r⟩

/-- The target of the tagged chain at the value `v` of the head: the hit of
the first test whose constant is `v`, else `mis`. -/
def chainPick (cs : List STest) (mis : Nat) (v : Noun) : Nat :=
  match cs.find? (fun t => decide (v = A t.c)) with
  | some t => t.hit
  | none => mis

theorem pickHit_tag (cs : List STest) (mis : Nat) (v : Noun) :
    pickHit (cs.map tagCase) mis v = chainPick cs mis v := by
  simp only [pickHit, chainPick, List.find?_map]
  have e : ((fun x : SCase => decide (v = A x.c)) ∘ tagCase) = fun t => decide (v = A t.c) := rfl
  rw [e]
  cases cs.find? (fun t => decide (v = A t.c)) <;> rfl

/-- Deleting a list of labels. -/
theorem get_foldl_del (ids : List Nat) : ∀ (m : Map Blob) (k : Nat),
    HoonMap.get (ids.foldl HoonMap.del m) k = if k ∈ ids then none else HoonMap.get m k := by
  induction ids with
  | nil => intro m k; simp
  | cons i t ih =>
    intro m k
    simp only [List.foldl_cons, ih, HoonMap.get_del, List.mem_cons]
    by_cases h1 : k = i <;> by_cases h2 : k ∈ t <;> simp [h1, h2]

/-- The labels of the tagged chain other than the yes side of the first test:
the yes sides of the others, then the no sides of all but the last. -/
def tagIds (cs : List STest) : List Nat := (cs.drop 1).map STest.y ++ cs.dropLast.map STest.miss

/-- The final miss of a chain: the no side of its last test. -/
def tagMiss (t0 : STest) (tl : List STest) : Nat := ((t0 :: tl).getLast (List.cons_ne_nil _ _)).miss

/-- **The tagged chain against its tree**: after `switchTag`, the first block
ends in a `%clq` to the yes side of the first test and to the final miss, that
block does the `%hed` and then the root of the tree, the tree takes the
target the chain takes (`chainPick`) on every value of the head, and no other
label changes but those of the chain.  Given that the labels of the chain
are distinct and its leaf registers are not the head. -/
theorem tag_tree {bl out out' : Map Blob} {fuel o : Nat} {t0 : STest} {tl : List STest}
    {done done' : List Nat} (h : switchTag bl out fuel o (t0 :: tl) done = some (out', done'))
    (hnd : (tagIds (t0 :: tl)).Nodup) (hy : t0.y ∉ tagIds (t0 :: tl)) (ho : o ∉ tagIds (t0 :: tl))
    (hoy : o ≠ t0.y) (hr : ∀ t ∈ t0 :: tl, t.r ≠ t0.d) :
    ∃ b nb nf, HoonMap.get bl o = some b ∧
      HoonMap.get out' o = some { b with fin := Termin.clq t0.s ⟨[], t0.y⟩ ⟨[], tagMiss t0 tl⟩ } ∧
      HoonMap.get out' t0.y = some ⟨[], Pole.hed t0.s t0.d :: nb, nf⟩ ∧
      (∀ v, treeGo out' t0.d ((t0 :: tl).map STest.r) v fuel ⟨[], nb, nf⟩ =
        some (chainPick (t0 :: tl) (tagMiss t0 tl) v)) ∧
      (∀ k, k ≠ o → k ≠ t0.y → k ∉ tagIds (t0 :: tl) → HoonMap.get out' k = HoonMap.get out k) ∧
      done' = tagIds (t0 :: tl) ++ done := by
  rw [switchTag] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨cas, hc, ⟨nb, nf, ids2, nout⟩, hs, b, hb, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hc' : casesOf ((t0 :: tl).map tagCase) = some cas := hc
  obtain ⟨hpw, hsp⟩ := cases_spec hc'
  have hrc : ∀ x ∈ cas, x.r ≠ t0.d ∧ x.r ∈ (t0 :: tl).map STest.r := by
    intro x hx
    have hf := (hsp x.c x).mp ⟨hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    exact ⟨hr t ht, List.mem_map_of_mem ht⟩
  obtain ⟨used, eu, fr, go⟩ := stree_go _ _ _ fuel cas _ _ nb nf ids2 nout hs hpw hrc hnd
  have hus : ∀ k ∈ used, k ∈ tagIds (t0 :: tl) := fun k hk => by
    show k ∈ tl.map STest.y ++ (t0 :: tl).dropLast.map STest.miss
    rw [eu]; exact List.mem_append_left _ hk
  refine ⟨b, nb, nf, hb, by rw [HoonMap.get_put, if_pos rfl]; rfl, ?_, fun v => ?_, fun k k1 k2 k3 => ?_, rfl⟩
  · rw [HoonMap.get_put, if_neg (Ne.symm hoy), HoonMap.get_put, if_pos rfl]
  · rw [go _ (fun k hk => ?_) v, pickHit_cases hc', pickHit_tag]
    · rfl
    · have h1 : k ≠ o := fun e => ho (e ▸ hus k hk)
      have h2 : k ≠ t0.y := fun e => hy (e ▸ hus k hk)
      rw [HoonMap.get_put, if_neg h1, HoonMap.get_put, if_neg h2]
  · have k4 : k ∉ used := fun hk => k3 (hus k hk)
    rw [HoonMap.get_put, if_neg k1, HoonMap.get_put, if_neg k2, fr k k4, get_foldl_del]
    have : k ∉ tl.map STest.y ++ (t0 :: tl).dropLast.map STest.miss := k3
    simp only [this, if_false]

end Opt
end SkaModel
end Formalization
