import lemmas.Compiler.OptLinkTotalPass

/-!
# `+switch-chains` returns (`SwitchRet`)

The model of `+switch-chains` (`Opt.switchChains`, `OptSwitch.lean`) takes
one fuel for `+bb-topo`, `chain-of`, `plains-of` and `tree`; `+sort` takes the
length of its list.  On blocks with `StInv ρ L` the model returns once the
fuel is above the rank of every member of `L` (`switchRet_of`):

* `+bb-topo` returns past `ρ 0` (`dfs_isSome`), and its members are blocks
  (`bbTopo_ok`);
* `chain-of` and `plains-of` follow the no side of a test, a jump, so the
  rank falls at each step (`chainOf_some`, `plainsOf_some`), and they return
  lists no longer than the fuel;
* `cases` is a `+sort` of at least one and at most as many cases as the chain
  (`casesOf_some`);
* `tree` over `k` cases takes `2 (k - 1)` labels and depth at most `k`
  (`stree_some`); the tagged chain gives it `2 (|chain| - 1)` labels, the
  plain chain `freshIds` at least `2 (k - 1)` (`freshIds_len`).

Only `RkDown`, `Closed` and the keys of `StInv` are used; `DInvR` is not.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map]

/-! ## `+sort` and `cases` -/

theorem len_filter_add {α : Type} (p : α → Bool) : ∀ l : List α,
    (l.filter p).length + (l.filter fun c => !p c).length = l.length
  | [] => rfl
  | a :: l => by
    have := len_filter_add p l
    cases h : p a <;> simp only [List.filter_cons, h, Bool.not_true, Bool.not_false, if_true, if_false,
      Bool.false_eq_true, List.length_cons] <;> omega

theorem hsort_some {α : Type} (lt : α → α → Bool) : ∀ (n : Nat) (l : List α), l.length ≤ n →
    ∃ l', Opt.hsort lt n l = some l' ∧ l'.length = l.length
  | n, [], _ => ⟨[], by cases n <;> rfl, rfl⟩
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: t, h => by
    have e := len_filter_add (fun c => lt c a) t
    have h1 : (t.filter fun c => lt c a).length ≤ n := by simp only [List.length_cons] at h; omega
    have h2 : (t.filter fun c => !lt c a).length ≤ n := by simp only [List.length_cons] at h; omega
    obtain ⟨p, hp, ep⟩ := hsort_some lt n _ h1
    obtain ⟨q, hq, eq⟩ := hsort_some lt n _ h2
    refine ⟨p ++ a :: q, ?_, ?_⟩
    · simp only [Opt.hsort, List.partition_eq_filter_filter, Function.comp_def, hp, hq, Option.bind_some,
        Option.map_some]
    · simp only [List.length_append, List.length_cons, ep, eq]; omega

theorem casesAcc_len : ∀ (l : List Opt.SCase) (saw : List Nat) (acc : List Opt.SCase),
    acc.length ≤ (Opt.casesAcc l saw acc).length ∧ (Opt.casesAcc l saw acc).length ≤ acc.length + l.length
  | [], _, _ => by simp [Opt.casesAcc]
  | x :: t, saw, acc => by
    simp only [Opt.casesAcc]
    split
    · have := casesAcc_len t saw acc; simp only [List.length_cons]; omega
    · have := casesAcc_len t (x.c :: saw) (x :: acc); simp only [List.length_cons] at this ⊢; omega

theorem casesOf_some (ces : List Opt.SCase) (h : ces ≠ []) :
    ∃ cas, Opt.casesOf ces = some cas ∧ 1 ≤ cas.length ∧ cas.length ≤ ces.length := by
  obtain ⟨l', hl, el⟩ := hsort_some (fun a b : Opt.SCase => decide (a.c < b.c)) _ (Opt.casesAcc ces [] [])
    (Nat.le_refl _)
  refine ⟨l', hl, ?_⟩
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil h
  have := casesAcc_len t [x.c] [x]
  have e : Opt.casesAcc (x :: t) [] [] = Opt.casesAcc t [x.c] [x] := by simp [Opt.casesAcc]
  rw [el, e]; simp only [List.length_cons, List.length_nil] at this ⊢; omega

/-! ## `tree` -/

theorem stree_some (d mis : Nat) : ∀ (n : Nat) (cas : List Opt.SCase) (ids : List Nat) (out : Map Blob),
    cas ≠ [] → cas.length ≤ n → 2 * (cas.length - 1) ≤ ids.length →
    ∃ r, Opt.stree d mis n cas ids out = some r ∧ r.2.2.1.length + 2 * (cas.length - 1) = ids.length
  | 0, cas, _, _, hne, hl, _ => by
    cases cas with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hl
  | n + 1, [], _, _, hne, _, _ => absurd rfl hne
  | n + 1, [x], ids, out, _, _, _ => ⟨_, rfl, by simp⟩
  | n + 1, a :: b :: t, ids, out, _, hl, hid => by
    have hlen : (a :: b :: t).length = t.length + 2 := rfl
    obtain ⟨h, hs, ehi⟩ : ∃ h hs, (a :: b :: t).drop ((a :: b :: t).length / 2) = h :: hs := by
      cases e : (a :: b :: t).drop ((a :: b :: t).length / 2) with
      | nil => have := congrArg List.length e; simp only [List.length_drop, List.length_nil] at this; omega
      | cons h hs => exact ⟨h, hs, rfl⟩
    obtain ⟨lid, rid, rest, rfl⟩ : ∃ lid rid rest, ids = lid :: rid :: rest := by
      match ids, hid with
      | lid :: rid :: rest, _ => exact ⟨lid, rid, rest, rfl⟩
      | [], hid => simp only [List.length_cons, List.length_nil] at hid; omega
      | [_], hid => simp only [List.length_cons, List.length_nil] at hid; omega
    have hlo : ((a :: b :: t).take ((a :: b :: t).length / 2)).length = (t.length + 2) / 2 := by
      rw [List.length_take, hlen]; omega
    have hhi : hs.length + 1 = t.length + 2 - (t.length + 2) / 2 := by
      have := congrArg List.length ehi
      rw [List.length_drop, hlen] at this; simp only [List.length_cons] at this; omega
    simp only [hlen, List.length_cons] at hl hid
    have ht : ((a :: b :: t).take ((a :: b :: t).length / 2)) ≠ [] := by
      intro e; have := congrArg List.length e; rw [hlo, List.length_nil] at this; omega
    obtain ⟨⟨lb, lf, lids, lout⟩, el, hle⟩ := stree_some d mis n _ rest out ht (by rw [hlo]; omega)
      (by rw [hlo]; omega)
    rw [hlo] at hle
    obtain ⟨⟨rb, rf, rids, rout⟩, er, hre⟩ := stree_some d mis n (h :: hs) lids
      (HoonMap.put lout lid ⟨[], lb, lf⟩) (List.cons_ne_nil _ _) (by simp only [List.length_cons]; omega)
      (by simp only [List.length_cons] at hle ⊢; omega)
    refine ⟨([], Termin.lti h.c d ⟨[], lid⟩ ⟨[], rid⟩, rids, HoonMap.put rout rid ⟨[], rb, rf⟩), ?_, ?_⟩
    · simp only [Opt.stree, ehi, el, Option.bind_some, er, Option.map_some]
    · simp only [hlen, List.length_cons] at hre hle ⊢; omega

theorem freshIds_len : ∀ (f : Nat) (ids : List Nat) (ned nex : Nat), ned ≤ f + ids.length →
    ned ≤ (Opt.freshIds f ids ned nex).1.length
  | 0, ids, ned, nex, h => by simp only [Opt.freshIds]; omega
  | f + 1, ids, ned, nex, h => by
    simp only [Opt.freshIds]
    split
    · assumption
    · exact freshIds_len f _ ned _ (by simp only [List.length_cons]; omega)

/-! ## `chain-of` and `plains-of` -/

variable [Opt.MapKeys Map]

theorem testOf_some {bl : Map Blob} (hc : Closed bl) (rev : Map (List Nat)) {p : Nat}
    (hp : (HoonMap.get bl p).isSome) : (Opt.testOf bl rev p).isSome := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hp
  simp only [Opt.testOf, hb, Option.bind_some]
  split
  · rename_i s y n e
    split
    · rfl
    · obtain ⟨yb, hy⟩ := Option.isSome_iff_exists.1 (hc p b ⟨[], y⟩ hb (by rw [e]; simp [Opt.getJmps]))
      simp only [hy, Option.bind_some]
      repeat' split
      all_goals rfl
  · rfl

theorem testOf_miss {bl : Map Blob} {rev : Map (List Nat)} {p : Nat} {t : Opt.STest}
    (h : Opt.testOf bl rev p = some (some t)) :
    ∃ b j, HoonMap.get bl p = some b ∧ j ∈ Opt.getJmps b.fin ∧ j.there = t.miss := by
  simp only [Opt.testOf, Option.bind_eq_some_iff] at h
  obtain ⟨b, hb, h⟩ := h
  split at h
  · rename_i s y n e
    split at h
    · cases h
    · obtain ⟨yb, -, h⟩ := Option.bind_eq_some_iff.1 h
      repeat' split at h
      all_goals first
        | (cases h; done)
        | (injection h with h; injection h with h; subst h
           exact ⟨b, ⟨[], n⟩, hb, by rw [e]; simp [Opt.getJmps], rfl⟩)
  · cases h

theorem chainOf_some {ρ : Nat → Nat} {bl : Map Blob} (hr : RkDown ρ bl) (hc : Closed bl) (rev : Map (List Nat)) :
    ∀ (n p : Nat), ρ p < n → (HoonMap.get bl p).isSome →
      ∃ cs, Opt.chainOf bl rev n p = some cs ∧ cs.length ≤ n
  | 0, p, h, _ => by omega
  | n + 1, p, h, hp => by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (testOf_some hc rev hp)
    simp only [Opt.chainOf, ht, Option.bind_some]
    cases t with
    | none => exact ⟨[], rfl, by simp⟩
    | some t =>
      simp only
      obtain ⟨b, j, hb, hj, ej⟩ := testOf_miss ht
      have hlt := hr p b j hb hj
      rw [ej] at hlt
      have hm := hc p b j hb hj
      rw [ej] at hm
      obtain ⟨nb, hnb⟩ := Option.isSome_iff_exists.1 hm
      obtain ⟨cs, hcs, hl⟩ := chainOf_some hr hc rev n t.miss (by omega) hm
      obtain ⟨t2, ht2⟩ := Option.isSome_iff_exists.1 (testOf_some hc rev hm)
      simp only [hnb, Option.bind_some]
      split
      · exact ⟨_, rfl, by simp⟩
      · split
        · exact ⟨_, rfl, by simp⟩
        · simp only [ht2, Option.bind_some]
          cases t2 with
          | none => exact ⟨_, rfl, by simp⟩
          | some t2 =>
            simp only
            split
            · exact ⟨_, rfl, by simp⟩
            · rw [hcs]; exact ⟨_, rfl, by simp only [List.length_cons]; omega⟩

theorem plainOf_some (bl : Map Blob) {p : Nat} (hp : (HoonMap.get bl p).isSome) : (Opt.plainOf bl p).isSome := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hp
  simp only [Opt.plainOf, hb, Option.bind_some]
  repeat' split
  all_goals rfl

theorem plainOf_miss {bl : Map Blob} {p : Nat} {t : Opt.SPlain} (h : Opt.plainOf bl p = some (some t)) :
    ∃ b j, HoonMap.get bl p = some b ∧ j ∈ Opt.getJmps b.fin ∧ j.there = t.miss := by
  simp only [Opt.plainOf, Option.bind_eq_some_iff] at h
  obtain ⟨b, hb, h⟩ := h
  split at h
  · rename_i l r hit miss e
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (injection h with h; injection h with h; subst h
         exact ⟨b, ⟨[], miss⟩, hb, by rw [e]; simp [Opt.getJmps], rfl⟩)
  · cases h

theorem plainsOf_some {ρ : Nat → Nat} {bl : Map Blob} (hr : RkDown ρ bl) (hc : Closed bl) (rev : Map (List Nat)) :
    ∀ (n p : Nat), ρ p < n → (HoonMap.get bl p).isSome →
      ∃ ps, Opt.plainsOf bl rev n p = some ps ∧ ps.length ≤ n
  | 0, p, h, _ => by omega
  | n + 1, p, h, hp => by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (plainOf_some bl hp)
    simp only [Opt.plainsOf, ht, Option.bind_some]
    cases t with
    | none => exact ⟨[], rfl, by simp⟩
    | some t =>
      simp only
      obtain ⟨b, j, hb, hj, ej⟩ := plainOf_miss ht
      have hlt := hr p b j hb hj
      rw [ej] at hlt
      have hm := hc p b j hb hj
      rw [ej] at hm
      obtain ⟨nb, hnb⟩ := Option.isSome_iff_exists.1 hm
      obtain ⟨ps, hps, hl⟩ := plainsOf_some hr hc rev n t.miss (by omega) hm
      obtain ⟨t2, ht2⟩ := Option.isSome_iff_exists.1 (plainOf_some bl hm)
      simp only [hnb, Option.bind_some]
      split
      · exact ⟨_, rfl, by simp⟩
      · split
        · split
          · exact ⟨_, rfl, by simp⟩
          · simp only [ht2, Option.bind_some]
            cases t2 with
            | none => exact ⟨_, rfl, by simp⟩
            | some t2 =>
              simp only
              split
              · exact ⟨_, rfl, by simp⟩
              · rw [hps]; exact ⟨_, rfl, by simp only [List.length_cons]; omega⟩
        · exact ⟨_, rfl, by simp⟩


/-! ## The two rewrites and the walk -/

theorem bind_isSome {α β : Type} {x : Option α} {f : α → Option β} (hx : x.isSome) (hf : ∀ a, (f a).isSome) :
    (x.bind f).isSome := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hx
  rw [ha, Option.bind_some]; exact hf a

theorem stree_isSome (d mis n : Nat) (cas : List Opt.SCase) (ids : List Nat) (out : Map Blob)
    (h1 : cas ≠ []) (h2 : cas.length ≤ n) (h3 : 2 * (cas.length - 1) ≤ ids.length) :
    (Opt.stree d mis n cas ids out).isSome := by
  obtain ⟨r, e, -⟩ := stree_some d mis n cas ids out h1 h2 h3
  rw [e]; rfl

theorem switchTag_some {bl out : Map Blob} {fuel o : Nat} {cs : List Opt.STest} {done : List Nat}
    (hne : cs ≠ []) (hl : cs.length ≤ fuel) (ho : (HoonMap.get bl o).isSome) :
    (Opt.switchTag bl out fuel o cs done).isSome := by
  obtain ⟨t0, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨cas, hc, h1, h2⟩ := casesOf_some ((t0 :: tl).map fun t => (⟨t.c, t.hit, t.r⟩ : Opt.SCase)) (by simp)
  simp only [List.length_map] at h2
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ho
  simp only [Opt.switchTag, hc, Option.bind_some]
  refine bind_isSome (stree_isSome _ _ _ _ _ _ ?_ ?_ ?_) fun _ => by simp [hb]
  · intro e; rw [e] at h1; simp at h1
  · omega
  · simp only [List.length_append, List.length_map, List.length_dropLast, List.length_cons] at h2 hl ⊢; omega

theorem switchPlain_some {bl out : Map Blob} {fuel o : Nat} {ps : List (Nat × Opt.SPlain)} {done : List Nat}
    {nex : Nat} (hne : ps ≠ []) (hl : ps.length ≤ fuel) (ho : (HoonMap.get bl o).isSome) :
    (Opt.switchPlain bl out fuel o ps done nex).isSome := by
  obtain ⟨p0, pl, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨cas, hc, h1, h2⟩ := casesOf_some ((p0 :: pl).map fun t => (⟨t.2.c, t.2.hit, t.2.r⟩ : Opt.SCase))
    (by simp)
  simp only [List.length_map] at h2
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ho
  simp only [Opt.switchPlain, hc, Option.bind_some]
  have hf := freshIds_len (2 * cas.length - 2 + 1) ((pl.map Prod.fst).take (2 * cas.length - 2))
    (2 * cas.length - 2) nex (by omega)
  cases e : Opt.freshIds (2 * cas.length - 2 + 1) ((pl.map Prod.fst).take (2 * cas.length - 2))
    (2 * cas.length - 2) nex with
  | mk ids nex' =>
    rw [e] at hf
    simp only
    refine bind_isSome (stree_isSome _ _ _ _ _ _ ?_ ?_ ?_) fun _ => by simp [hb]
    · intro e; rw [e] at h1; simp at h1
    · simp only [List.length_cons] at h2 hl; omega
    · simp only at hf; omega

theorem switchWalk_some {ρ : Nat → Nat} {bl : Map Blob} (hr : RkDown ρ bl) (hc : Closed bl) (rev : Map (List Nat))
    {fuel : Nat} : ∀ (topo : List Nat) (out : Map Blob) (done : List Nat) (nex : Nat),
      (∀ o ∈ topo, (HoonMap.get bl o).isSome ∧ ρ o < fuel) →
      (Opt.switchWalk bl rev fuel topo out done nex).isSome
  | [], _, _, _, _ => rfl
  | o :: rest, out, done, nex, h => by
    have ih := fun out done nex => switchWalk_some hr hc rev rest out done nex (fun x hx => h x (by simp [hx]))
    obtain ⟨ho, hρ⟩ := h o (by simp)
    simp only [Opt.switchWalk]
    split
    · exact ih _ _ _
    · obtain ⟨cs, hcs, hl⟩ := chainOf_some hr hc rev fuel o hρ ho
      simp only [hcs, Option.bind_some]
      split
      · rename_i h4
        obtain ⟨⟨out', done'⟩, hr'⟩ := Option.isSome_iff_exists.1
          (switchTag_some (out := out) (done := done) (by intro e; rw [e] at h4; simp at h4) hl ho)
        simp only [hr', Option.bind_some]; exact ih _ _ _
      · obtain ⟨ps, hps, hl'⟩ := plainsOf_some hr hc rev fuel o hρ ho
        simp only [hps, Option.bind_some]
        split
        · exact ih _ _ _
        · rename_i h4
          obtain ⟨⟨out', done', nex'⟩, hr'⟩ := Option.isSome_iff_exists.1
            (switchPlain_some (out := out) (done := done) (nex := nex) (by intro e; rw [e] at h4; simp at h4) hl' ho)
          simp only [hr', Option.bind_some]; exact ih _ _ _

/-- **`+switch-chains` returns** on blocks with `StInv ρ L` once the fuel is
above the rank of every member of `L`. -/
theorem switchChains_some {ρ : Nat → Nat} {L : List Nat} {bl : Map Blob} (hI : StInv ρ L bl) {fuel : Nat}
    (hf : ∀ o ∈ L, ρ o < fuel) : (Opt.switchChains fuel bl).isSome := by
  obtain ⟨topo, ht⟩ := Option.isSome_iff_exists.1 (show (Opt.bbTopo fuel bl).isSome by
    simp only [Opt.bbTopo, Option.isSome_map]
    exact dfs_isSome hI.closed hI.rank fuel 0 _ (hf 0 (hI.keys 0 hI.zero)) hI.zero)
  have hok := Opt.bbTopo_ok hI.acyclic ht
  simp only [Opt.switchChains, ht, Option.bind_some]
  exact switchWalk_some hI.rank hI.closed _ topo _ _ _
    fun o ho => ⟨hok.2.2.1 o ho, hf o (hI.keys o (hok.2.2.1 o ho))⟩

/-- **`SwitchRet`**, for a fuel above the rank of every member of `L`. -/
theorem switchRet_of {sfuel : Nat} {ρ : Nat → Nat} {L : List Nat} (hf : ∀ o ∈ L, ρ o < sfuel) :
    SwitchRet (Map := Map) sfuel ρ L :=
  fun _ hI _ => switchChains_some hI hf

end

end Compiler
end Formalization
