import lemmas.Compiler.OptLinkTrimNouns

/-!
# `+trim-trace-hints`: the maps of counts, the sets of keys

The Hoon keeps the counts of the open keys in a `(map key @ud)` that never
holds `0` (an epilogue at count `1` or less deletes the key), the model in a
function `Cnt`; the unsafe keys in a `(set key)`, the model in a test `Uns`;
the counts at the end of each walked block in a `(map @uwoo (map key
@ud))`, the model in a `TreapMap mugF Cnt`.

* `CntRel N c`: `N` is a map whose value at each key noun is `look`ed as
  `cntLook c` (the count of a key of positive count, nothing elsewhere).
* `UnsRel S u`: `S` is a set of key nouns, the keys `u` holds.
* `OutRel N out`: `N` is a map from labels to maps of counts, those of
  `out`.
* `cnt_gut`, `cnt_put`, `cnt_del`, `cnt_key`, `uns_add`: `+gut:by`,
  `+put:by`, `+del:by` at a key, `~(key by open)` and `(~(uni in unsafe)
  ~(key by open))`.
* `cnt_uno`: `(~(uno by acc) b)` with the gate of `+max` is `Cnt.join`.
* `out_gut`, `out_put`: `+gut:by` and `+put:by` on `out`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Maps of counts -/

/-- The value at a key noun of the map of counts `c`. -/
def cntLook (c : Opt.Cnt) (kn : Noun) : Option Noun :=
  if keyN (keyDec kn) = kn ∧ 0 < c (keyDec kn) then some (A (c (keyDec kn))) else none

theorem cntLook_keyN (c : Opt.Cnt) (k : Opt.TKey) :
    cntLook c (keyN k) = if 0 < c k then some (A (c k)) else none := by
  simp [cntLook, keyDec_keyN]

theorem cntLook_not {c : Opt.Cnt} {kn : Noun} (h : ∀ k, kn ≠ keyN k) : cntLook c kn = none := by
  simp only [cntLook]
  rw [if_neg]
  rintro ⟨e, -⟩
  exact h _ e.symm

/-- The noun `N` is the map of the counts `c`. -/
def CntRel (N : Noun) (c : Opt.Cnt) : Prop := IsMap mugF N ∧ ∀ kn, look N kn = cntLook c kn

theorem cntRel_nil : CntRel (A 0) Opt.Cnt.empty :=
  ⟨IsMap.nil, fun kn => by simp [look_nil, cntLook, Opt.Cnt.empty]⟩

/-- `look` after a `putF`. -/
theorem look_put {a out k v : Noun} (ho : IsMap mugF out) (ha : IsMap mugF a)
    (hg : ∀ k' v', Get out k' v' ↔ (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Get a k' v')) (kn : Noun) :
    look out kn = if kn = k then some v else look a kn := by
  apply Option.ext
  intro w
  rw [look_get ho, hg]
  by_cases e : kn = k
  · subst e; simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false, if_true, Option.some.injEq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · simp only [e, false_and, ne_eq, not_false_eq_true, true_and, false_or, if_false]
    rw [look_get ha]

/-- `look` after a `delF`. -/
theorem look_del {a out k : Noun} (ho : IsMap mugF out) (ha : IsMap mugF a)
    (hg : ∀ k' v', Get out k' v' ↔ k' ≠ k ∧ Get a k' v') (kn : Noun) :
    look out kn = if kn = k then none else look a kn := by
  apply Option.ext
  intro w
  rw [look_get ho, hg]
  by_cases e : kn = k
  · subst e; simp
  · simp only [e, ne_eq, not_false_eq_true, true_and, if_false]
    rw [look_get ha]

theorem cntLook_set (c : Opt.Cnt) (k : Opt.TKey) (n : Nat) (kn : Noun) :
    cntLook (c.set k n) kn = if kn = keyN k then (if 0 < n then some (A n) else none) else cntLook c kn := by
  by_cases e : kn = keyN k
  · subst e; simp [cntLook_keyN, Opt.Cnt.set]
  · rw [if_neg e]
    by_cases hk : keyN (keyDec kn) = kn
    · have hne : keyDec kn ≠ k := fun h => e (by rw [← hk, h])
      simp [cntLook, Opt.Cnt.set, hne]
    · simp [cntLook, hk]

theorem gutIn_layer2 : FallIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
  ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩

/-- **`(~(gut by open) key 0)`**: the count of the key. -/
theorem cnt_gut {N : Noun} {c : Opt.Cnt} (h : CntRel N c) (k : Opt.TKey) :
    nock (C by.gut.battery (C (C (keyN k) (A 0)) (C by.battery (C N layer2)))) by.gut.battery
      = some (A (c k)) := by
  have hl := h.2 (keyN k)
  rw [cntLook_keyN] at hl
  by_cases hp : 0 < c k
  · rw [if_pos hp] at hl
    have hg := getF_some h.1 ((look_get h.1 _ _).1 hl)
    rw [gut_gate (mug := mugF) layer2 gutIn_layer2 _ _ _ _ hg (Or.inr ⟨_, rfl⟩)]
    simp
  · rw [if_neg hp] at hl
    have hg := getF_none h.1 (fun v hv => by rw [← look_get h.1] at hv; rw [hl] at hv; cases hv)
    rw [gut_gate (mug := mugF) layer2 gutIn_layer2 _ _ _ _ hg (Or.inl rfl)]
    have : c k = 0 := by omega
    simp [this]

/-- **`(~(put by open) key n)`** with `0 < n`. -/
theorem cnt_put {N : Noun} {c : Opt.Cnt} (h : CntRel N c) (k : Opt.TKey) (n : Nat) (hn : 0 < n) :
    ∃ N', nock (C by.put.battery (C (C (keyN k) (A n)) (C by.battery (C N layer2)))) by.put.battery = some N' ∧
      CntRel N' (c.set k n) := by
  obtain ⟨out, hp, ho, hg⟩ := putF_spec mugF N (keyN k) (A n) h.1
  refine ⟨out, put_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ _ hp, ho, fun kn => ?_⟩
  rw [look_put ho h.1 hg, cntLook_set, h.2 kn, if_pos hn]

/-- **`(~(del by open) key)`**. -/
theorem cnt_del {N : Noun} {c : Opt.Cnt} (h : CntRel N c) (k : Opt.TKey) :
    ∃ N', nock (C by.del.battery (C (keyN k) (C by.battery (C N layer2)))) by.del.battery = some N' ∧
      CntRel N' (c.set k 0) := by
  obtain ⟨out, hd, ho, hg⟩ := delF_spec (mug := mugF) (keyN k) h.1
  refine ⟨out, del_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ hd, ho, fun kn => ?_⟩
  rw [look_del ho h.1 hg, cntLook_set, h.2 kn]
  simp

/-! ## Sets of keys -/

/-- The noun `S` is the set of the keys `u` holds. -/
def UnsRel (S : Noun) (u : Opt.Uns) : Prop := IsSet mugF S ∧ ∀ x, Has S x ↔ ∃ k, x = keyN k ∧ u k = true

theorem unsRel_nil : UnsRel (A 0) (fun _ => false) := ⟨isSet_nil, fun x => by simp [uni_has_nil]⟩

/-- **`~(key by open)`**: the keys of positive count. -/
theorem cnt_key {N : Noun} {c : Opt.Cnt} (h : CntRel N c) :
    ∃ K, nock (C by.battery (C N layer2)) by.key.arm = some K ∧ IsSet mugF K ∧
      ∀ x, Has K x ↔ ∃ k, x = keyN k ∧ 0 < c k := by
  obtain ⟨K, hk, hs, hh⟩ := keyF_spec h.1 (A 0) isSet_nil
  refine ⟨K, ?_, hs, fun x => ?_⟩
  · rw [key_arm, key_loop layer2 cs_inIn_layer2 by.battery N (A 0) K hk]
  · rw [hh]
    simp only [uni_has_nil, false_or]
    constructor
    · rintro ⟨v, hv⟩
      rw [← look_get h.1, h.2 x] at hv
      simp only [cntLook] at hv
      split at hv
      · rename_i hc; exact ⟨keyDec x, hc.1.symm, hc.2⟩
      · cases hv
    · rintro ⟨k, rfl, hk⟩
      refine ⟨A (c k), ?_⟩
      rw [← look_get h.1, h.2, cntLook_keyN, if_pos hk]

/-- **`(~(uni in unsafe) ~(key by open))`**: the keys of positive count added. -/
theorem uns_add {S N : Noun} {u : Opt.Uns} {c : Opt.Cnt} (hu : UnsRel S u) (hc : CntRel N c) :
    ∃ K S', nock (C by.battery (C N layer2)) by.key.arm = some K ∧
      nock (C in.uni.battery (C K (C in.battery (C S layer2)))) in.uni.battery = some S' ∧
      UnsRel S' (u.add c) := by
  obtain ⟨K, hk, hks, hkh⟩ := cnt_key hc
  obtain ⟨out, hn, hs, hh⟩ := uni_in (mug := mugF) layer2 gorIn_morIn_layer2 S K hu.1 hks
  refine ⟨K, out, hk, hn, hs, fun x => ?_⟩
  rw [hh, hu.2, hkh]
  simp only [Opt.Uns.add, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (⟨k, rfl, h⟩ | ⟨k, rfl, h⟩)
    · exact ⟨k, rfl, Or.inl h⟩
    · exact ⟨k, rfl, Or.inr h⟩
  · rintro ⟨k, rfl, h | h⟩
    · exact Or.inl ⟨k, rfl, h⟩
    · exact Or.inr ⟨k, rfl, h⟩

/-! ## `+uno:by` with `+max` -/

/-- A positive count. -/
def PosV (v : Noun) : Prop := ∃ n, 0 < n ∧ v = A n

/-- The gate `|=([k=key v=@ud w=@ud] (max v w))` on two values. -/
def maxF (k va vb : Noun) : Noun := A (max (OptDec.atomOf va) (OptDec.atomOf vb))

/-- The gate of `+max` built in the gate of the `+roll`. -/
theorem tr_maxg (RS : Noun) (hRS : slot? 0x3ffffff RS = some layer1) (k va vb : Noun) (ha : PosV va)
    (hb : PosV vb) : nock (C trMaxG (C (C k (C va vb)) RS)) trMaxG = some (maxF k va vb) := by
  obtain ⟨m, -, rfl⟩ := ha
  obtain ⟨n, -, rfl⟩ := hb
  have hm := max_gate layer1 arith_layer1.2.2.2.2.2.2.1 m n
  have h1 := max.arm_at
  unfold trMaxG
  generalize layer1 = L1 at hRS hm h1
  simp [nock_exec, hRS, h1, max_arm, hm, maxF, OptDec.atomOf]

theorem cnt_vall {N : Noun} {c : Opt.Cnt} (h : CntRel N c) : VAll PosV N := by
  intro kn v hv
  rw [← look_get h.1, h.2] at hv
  simp only [cntLook] at hv
  split at hv
  · rename_i hc; cases hv; exact ⟨_, hc.2, rfl⟩
  · cases hv

/-- **`(~(uno by acc) b)` with the gate of `+max`** is `Cnt.join`. -/
theorem cnt_uno {ACC B RS : Noun} {ca cb : Opt.Cnt} (ha : CntRel ACC ca) (hb : CntRel B cb)
    (hRS : slot? 0x3ffffff RS = some layer1) :
    ∃ OUT, nock (C unoMegGate (C (C trMaxG (C trMaxB RS)) (C unoOuter (C B (C by.battery (C ACC layer2))))))
        unoMegGate = some OUT ∧ CntRel OUT (ca.join cb) := by
  obtain ⟨out, hn, hm, -, hl⟩ := uno_by (mug := mugF) layer2 gorIn_morIn_layer2 PosV maxF trMaxG trMaxB RS
    (tr_maxg RS hRS) (fun k va vb ⟨m, hm, e1⟩ ⟨n, hn, e2⟩ => ⟨max m n, by omega, by subst e1 e2; rfl⟩)
    ACC B ha.1 hb.1 (cnt_vall ha) (cnt_vall hb)
  refine ⟨out, hn, hm, fun kn => ?_⟩
  rw [hl kn, ha.2 kn, hb.2 kn]
  simp only [cntLook, Opt.Cnt.join]
  by_cases e : keyN (keyDec kn) = kn
  · by_cases p1 : 0 < ca (keyDec kn) <;> by_cases p2 : 0 < cb (keyDec kn) <;>
      simp [e, p1, p2, mergeO, maxF, OptDec.atomOf] <;> omega
  · simp [e, mergeO]

/-! ## The counts at the end of each walked block -/

/-- The noun `N` is the map `out` from labels to maps of counts. -/
def OutRel (N : Noun) (out : TreapMap mugF Opt.Cnt) : Prop :=
  IsMap mugF N ∧ (∀ kn v, Get N kn v → ∃ o c, kn = A o ∧ HoonMap.get out o = some c ∧ CntRel v c) ∧
    (∀ o c, HoonMap.get out o = some c → ∃ v, Get N (A o) v)

theorem outRel_nil : OutRel (A 0) HoonMap.empty :=
  ⟨IsMap.nil, fun _ _ h => absurd h Get_atom, fun o c h => by simp [HoonMap.get_empty] at h⟩

/-- **`(~(gut by out) p *(map key @ud))`**: the counts at the end of `p`, or
none. -/
theorem out_gut {N : Noun} {out : TreapMap mugF Opt.Cnt} (h : OutRel N out) (p : Nat) :
    ∃ B, nock (C by.gut.battery (C (C (A p) (A 0)) (C by.battery (C N layer2)))) by.gut.battery = some B ∧
      CntRel B ((HoonMap.get out p).getD Opt.Cnt.empty) := by
  cases e : HoonMap.get out p with
  | none =>
    have hg := getF_none (k := A p) h.1 (fun v hv => by
      obtain ⟨o, c, ho, hc, -⟩ := h.2.1 _ _ hv
      have := Noun.atom.inj ho; subst this; rw [e] at hc; cases hc)
    refine ⟨A 0, ?_, cntRel_nil⟩
    rw [gut_gate (mug := mugF) layer2 gutIn_layer2 _ _ _ _ hg (Or.inl rfl)]
    simp
  | some c =>
    obtain ⟨v, hv⟩ := h.2.2 p c e
    obtain ⟨o, c', ho, hc', hr⟩ := h.2.1 _ _ hv
    have := Noun.atom.inj ho; subst this
    rw [e] at hc'; cases hc'
    refine ⟨v, ?_, hr⟩
    rw [gut_gate (mug := mugF) layer2 gutIn_layer2 _ _ _ _ (getF_some h.1 hv) (Or.inr ⟨_, rfl⟩)]
    simp

/-- **`(~(put by out) i.topo open)`**. -/
theorem out_put {N V : Noun} {out : TreapMap mugF Opt.Cnt} {c : Opt.Cnt} (h : OutRel N out) (hv : CntRel V c)
    (o : Nat) :
    ∃ N', nock (C by.put.battery (C (C (A o) V) (C by.battery (C N layer2)))) by.put.battery = some N' ∧
      OutRel N' (HoonMap.put out o c) := by
  obtain ⟨out', hp, ho, hg⟩ := putF_spec mugF N (A o) V h.1
  refine ⟨out', put_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ _ hp, ho, fun kn w hw => ?_,
    fun o' c' hc' => ?_⟩
  · rcases (hg kn w).1 hw with ⟨e1, e2⟩ | ⟨hne, hw'⟩
    · rw [e1, e2]; exact ⟨o, c, rfl, by rw [HoonMap.get_put]; simp, hv⟩
    · obtain ⟨o', c', rfl, hc', hr⟩ := h.2.1 _ _ hw'
      have : o' ≠ o := fun e => hne (by rw [e])
      exact ⟨o', c', rfl, by rw [HoonMap.get_put, if_neg this]; exact hc', hr⟩
  · rw [HoonMap.get_put] at hc'
    by_cases e : o' = o
    · subst e; exact ⟨V, (hg _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · rw [if_neg e] at hc'
      obtain ⟨v, hv'⟩ := h.2.2 o' c' hc'
      exact ⟨v, (hg _ _).2 (Or.inr ⟨fun h => e (Noun.atom.inj h), hv'⟩)⟩

end Compiler
end Formalization
