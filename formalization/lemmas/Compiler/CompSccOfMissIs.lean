import lemmas.Ska.TarjanSccOfSem
import lemmas.Compiler.PokeLinkGood5
import lemmas.Compiler.PokeLinkScc

/-!
# The `sub` graph of `+scc-of`'s miss against the table's SCCs (track Q)

`+scc-of` on a miss builds `sub` from `b` along `ScoKids` (`Ska/TarjanSccOfTotal.lean`:
a member of `calls` of the node that `sccs` does not have) and stores for each
node `k` of `sub` the set of the `x` with `ScoReach k x` and `ScoReach x k`
(`scoMiss_spec`).  On the nouns of the state (`callsNoun L`, `sccsNoun sc`):

* `scoKids_enc`: a `ScoKids` step is an encoded call `b' → c'` of the table
  with `c'` not in `sc`;
* `scoReach_key`: on a closed table, from a key `k`, `ScoReach` reaches only
  encoded keys `c` with `Reach T k c`, and each is `k` or has no `sc` entry;
* `reach_sco`: a `Reach` path inside `k`'s SCC whose nodes have no `sc`
  entry is a `ScoReach` path;
* **`scoScc_iff`**: on a closed table with `SccsIs` and `SccsGoodM` of `sc`,
  `b` a key without an entry, for each node `k` of `sub`: mutual `ScoReach`
  from `k` is `InScc T k`; **`scoScc_set`**: so the stored set is
  `sccSet T k`.

Track P's `SccOfIs` (`PokeLinkGood5.lean`) has neither `SccsGoodM sc` nor
`b` a key, and both are needed (witnesses):

* `sccOfIs_needs_key`: off the keys the miss stores `b` in `b`'s set
  (`ScoReach b b`), while `sccSet T b` is empty (`sccSet_nonkey`);
* **`sccOfIs_needs_good`**: on the two-cycle `b ↔ m` (`twoCyc`, any two
  distinct bells) with `sc = {m ↦ sccSet T m}` (`SccsIs` holds, `b` has no
  entry, `CodeClosed` holds), `sub` does not reach `m` (`scoReach_blocked`),
  so `b`'s stored set lacks `m`, while `m ∈ sccSet T b`; `SccsGoodM sc`
  fails there.
-/

namespace Formalization
namespace Compiler

open Nock Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM Tarjan

theorem sco_bell_inj {a b : Bell} (h : a.toNoun = b.toNoun) : a = b := TKey.enc_inj a b h

theorem opt_unit_ext {o1 o2 : Option Unit} (h : o1 = some () ↔ o2 = some ()) : o1 = o2 := by
  cases o1 <;> cases o2 <;> simp_all

section Sub

variable {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)}

/-- **A `ScoKids` step on the state's nouns**: an encoded call of the table to
a bell without an `sc` entry. -/
theorem scoKids_enc (x c : Noun) :
    ScoKids (callsNoun L) (sccsNoun sc) x c ↔ ∃ (b' c' : Bell) (e : VarEntry FinMap), x = b'.toNoun ∧
      c = c'.toNoun ∧ FinMap.get L.code b' = some e ∧ FinMap.get e.calls c' = some () ∧ FinMap.get sc c' = none := by
  unfold ScoKids callsNoun sccsNoun
  constructor
  · rintro ⟨⟨v, hv, hc⟩, hn⟩
    obtain ⟨b', e, he, rfl, rfl⟩ := (FinMap.get_toNoun _ L.code x v).1 hv
    obtain ⟨c', hc', rfl⟩ := (FinMap.has_setNoun e.calls c).1 hc
    refine ⟨b', c', e, rfl, rfl, he, hc', ?_⟩
    cases h : sc.1 c' with
    | none => exact h
    | some S => exact absurd ((FinMap.get_toNoun _ sc _ _).2 ⟨c', S, h, rfl, rfl⟩) (hn _)
  · rintro ⟨b', c', e, rfl, rfl, he, hc', hs⟩
    refine ⟨⟨_, (FinMap.get_toNoun _ L.code _ _).2 ⟨b', e, he, rfl, rfl⟩,
      (FinMap.has_setNoun e.calls _).2 ⟨c', hc', rfl⟩⟩, ?_⟩
    intro w hw
    obtain ⟨k, S, hk, he', -⟩ := (FinMap.get_toNoun _ sc _ _).1 hw
    have hck : c' = k := TKey.enc_inj c' k he'
    subst hck
    have hs' : sc.1 c' = none := hs
    rw [hs'] at hk
    cases hk

/-- **From a key, `ScoReach` reaches encoded keys it `Reach`es**, each the
start or without an `sc` entry. -/
theorem scoReach_key (hC : CodeClosed L.code) {k : Bell} (hk : ∃ e, FinMap.get L.code k = some e) {y : Noun}
    (h : ScoReach (callsNoun L) (sccsNoun sc) k.toNoun y) :
    ∃ c : Bell, y = c.toNoun ∧ (∃ e, FinMap.get L.code c = some e) ∧ Reach L.code k c ∧
      (c = k ∨ FinMap.get sc c = none) := by
  suffices H : ∀ a y, ScoReach (callsNoun L) (sccsNoun sc) a y → ∀ k : Bell, a = k.toNoun →
      (∃ e, FinMap.get L.code k = some e) →
      ∃ c : Bell, y = c.toNoun ∧ (∃ e, FinMap.get L.code c = some e) ∧ Reach L.code k c ∧
        (c = k ∨ FinMap.get sc c = none) from H _ _ h k rfl hk
  intro a y h
  induction h with
  | refl a => intro k hka hk; exact ⟨k, hka, hk, Reach.refl k, Or.inl rfl⟩
  | @step a a' y e _ ih =>
    intro k hka _
    obtain ⟨b', c', e', hx, hc, hb', hc', hs⟩ := (scoKids_enc a a').1 e
    have hbk : b' = k := sco_bell_inj (hx.symm.trans hka)
    subst hbk
    obtain ⟨e'', he''⟩ := (hC b' e' hb').1 c' hc'
    obtain ⟨c, hy, hck, hr, hor⟩ := ih c' hc ⟨e'', he''⟩
    refine ⟨c, hy, hck, Reach.step ⟨e', hb', hc', e'', he''⟩ hr, Or.inr ?_⟩
    rcases hor with rfl | h
    · exact hs
    · exact h

/-- **A `Reach` path inside `k`'s SCC** whose nodes have no `sc` entry is a
`ScoReach` path. -/
theorem reach_sco {k : Bell}
    (hfree : ∀ m, Reach L.code k m → Reach L.code m k → FinMap.get sc m = none) :
    ∀ {a c : Bell}, Reach L.code a c → Reach L.code k a → Reach L.code c k →
      ScoReach (callsNoun L) (sccsNoun sc) a.toNoun c.toNoun := by
  intro a c h
  induction h with
  | refl a => intro _ _; exact ScoReach.refl _
  | @step a a' c hE hr ih =>
    intro hka hck
    obtain ⟨e, he, hc', e', he'⟩ := hE
    have hka' : Reach L.code k a' := hka.trans (Reach.step ⟨e, he, hc', e', he'⟩ (Reach.refl a'))
    exact ScoReach.step ((scoKids_enc _ _).2 ⟨a, a', e, rfl, rfl, he, hc', hfree a' hka' (hr.trans hck)⟩)
      (ih hka' hck)

/-- **Mutual reachability in `sub` is the table's SCC**, for every node `k`
of `sub` (`ScoReach` from `b`), when `sc` holds whole SCCs. -/
theorem scoScc_iff (hC : CodeClosed L.code) (hs : SccsIs L.code sc) (hg : SccsGoodM sc) {b : Bell}
    (hb0 : ∃ e, FinMap.get L.code b = some e) (hb : sc.get b = none) {k : Bell}
    (hk : ScoReach (callsNoun L) (sccsNoun sc) b.toNoun k.toNoun) (x : Bell) :
    (ScoReach (callsNoun L) (sccsNoun sc) k.toNoun x.toNoun ∧ ScoReach (callsNoun L) (sccsNoun sc) x.toNoun k.toNoun) ↔
      InScc L.code k x := by
  obtain ⟨k', hkk, hkkey, -, hor⟩ := scoReach_key hC hb0 hk
  have hkk' : k = k' := sco_bell_inj hkk
  subst hkk'
  have hkn : FinMap.get sc k = none := by
    rcases hor with rfl | h
    · exact hb
    · exact h
  have hfree : ∀ m, Reach L.code k m → Reach L.code m k → FinMap.get sc m = none := by
    intro m h1 h2
    cases hm : FinMap.get sc m with
    | none => rfl
    | some S =>
      exfalso
      have hS := hs m S hm
      have hkS : FinMap.get S k = some () := by rw [hS]; exact sccSet_get.2 ⟨hkkey, h2, h1⟩
      have := (hg m S hm).2 k hkS
      rw [hkn] at this
      cases this
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨c, hxc, hckey, hr, -⟩ := scoReach_key hC hkkey h1
    have hxc' : x = c := sco_bell_inj hxc
    subst hxc'
    obtain ⟨c2, hkc2, -, hr2, -⟩ := scoReach_key hC hckey h2
    have hkc2' : k = c2 := sco_bell_inj hkc2
    subst hkc2'
    exact ⟨hckey, hr, hr2⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨reach_sco hfree h1 (Reach.refl k) h2, reach_sco hfree h2 h1 (Reach.refl k)⟩

/-- **The set the miss stores for a node `k` of `sub` is `sccSet T k`**: any
set of bells whose members are the mutual `ScoReach` of `k`. -/
theorem scoScc_set (hC : CodeClosed L.code) (hs : SccsIs L.code sc) (hg : SccsGoodM sc) {b : Bell}
    (hb0 : ∃ e, FinMap.get L.code b = some e) (hb : sc.get b = none) {k : Bell}
    (hk : ScoReach (callsNoun L) (sccsNoun sc) b.toNoun k.toNoun) (S : FinMap Bell Unit)
    (hS : ∀ x, FinMap.get S x = some () ↔
      (ScoReach (callsNoun L) (sccsNoun sc) k.toNoun x.toNoun ∧ ScoReach (callsNoun L) (sccsNoun sc) x.toNoun k.toNoun)) :
    S = sccSet L.code k := by
  apply Subtype.ext
  funext x
  exact opt_unit_ext ((hS x).trans ((scoScc_iff hC hs hg hb0 hb hk x).trans sccSet_get.symm))

/-- `sub` does not reach a bell with an `sc` entry (other than its start). -/
theorem scoReach_blocked {b m : Bell} (hbm : b ≠ m) (hm : FinMap.get sc m ≠ none) :
    ¬ ScoReach (callsNoun L) (sccsNoun sc) b.toNoun m.toNoun := by
  intro h
  rcases reach_last h with e | ⟨y, hy⟩
  · exact hbm (sco_bell_inj e).symm
  · obtain ⟨-, c', -, -, hc, -, -, hs⟩ := (scoKids_enc (L := L) y m.toNoun).1 hy
    have : m = c' := sco_bell_inj hc
    subst this
    exact hm hs

end Sub

/-! ## Why `SccOfIs` needs `b` a key and `SccsGoodM` -/

/-- Off the keys the SCC is empty. -/
theorem sccSet_nonkey {T : FinMap Bell (VarEntry FinMap)} {b : Bell} (h : FinMap.get T b = none) (x : Bell) :
    FinMap.get (sccSet T b) x = none := by
  cases e : FinMap.get (sccSet T b) x with
  | none => rfl
  | some u =>
    exfalso
    have hin : InScc T b x := sccSet_get.1 (by cases u; exact e)
    obtain ⟨⟨e', he'⟩, hr, -⟩ := hin
    cases hr with
    | refl => rw [h] at he'; cases he'
    | step hE _ => obtain ⟨e'', he'', -⟩ := hE; rw [h] at he''; cases he''

/-- **Witness (a)**: off the keys, `b` is in its own mutual-`ScoReach` set (the
set the miss stores for `b`, `scoMiss_spec`), and not in `sccSet T b`. -/
theorem sccOfIs_needs_key {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)} {b : Bell}
    (h : FinMap.get L.code b = none) :
    (ScoReach (callsNoun L) (sccsNoun sc) b.toNoun b.toNoun ∧ ScoReach (callsNoun L) (sccsNoun sc) b.toNoun b.toNoun) ∧
      FinMap.get (sccSet L.code b) b = none :=
  ⟨⟨ScoReach.refl _, ScoReach.refl _⟩, sccSet_nonkey h b⟩

/-- The table of the two-cycle `b ↔ m`. -/
def twoCyc (b m : Bell) (s : Cape) : FinMap Bell (VarEntry FinMap) :=
  (FinMap.empty.put b ⟨.n1 (A 0), FinMap.empty.put m (), s⟩).put m ⟨.n1 (A 0), FinMap.empty.put b (), s⟩

/-- The `sccs` with the one entry `m ↦ S`. -/
def scOne (m : Bell) (S : FinMap Bell Unit) : FinMap Bell (FinMap Bell Unit) := FinMap.empty.put m S

/-- **Witness (b)**: on the two-cycle `b ↔ m` with `sccs = {m ↦ sccSet T m}`,
the table is closed, `sccs` is `SccsIs` and has no entry for `b`, `m` is in
`b`'s SCC, but `sub` from `b` does not reach `m`, so the set the miss
stores for `b` is not `sccSet T b`; `SccsGoodM` fails on that `sccs`. -/
theorem sccOfIs_needs_good (b m : Bell) (hbm : b ≠ m) (s : Cape) (L : LongB FinMap) (hL : L.code = twoCyc b m s) :
    CodeClosed L.code ∧ SccsIs L.code (scOne m (sccSet L.code m)) ∧ FinMap.get (scOne m (sccSet L.code m)) b = none ∧
      InScc L.code b m ∧ ¬ ScoReach (callsNoun L) (sccsNoun (scOne m (sccSet L.code m))) b.toNoun m.toNoun ∧
      ¬ SccsGoodM (scOne m (sccSet L.code m)) := by
  have hmb : m ≠ b := Ne.symm hbm
  have gb : FinMap.get (twoCyc b m s) b = some ⟨.n1 (A 0), FinMap.empty.put m (), s⟩ := by
    simp [twoCyc, FinMap.get, FinMap.put, hbm]
  have gm : FinMap.get (twoCyc b m s) m = some ⟨.n1 (A 0), FinMap.empty.put b (), s⟩ := by
    simp [twoCyc, FinMap.get, FinMap.put]
  have go : ∀ c, c ≠ b → c ≠ m → FinMap.get (twoCyc b m s) c = none := by
    intro c h1 h2; simp [twoCyc, FinMap.get, FinMap.put, FinMap.empty, h1, h2]
  have one : ∀ (x c : Bell), FinMap.get (FinMap.empty.put x ()) c = some () ↔ c = x := by
    intro x c
    by_cases h : c = x
    · subst h; simp [FinMap.get, FinMap.put]
    · simp [FinMap.get, FinMap.put, FinMap.empty, h]
  have eBM : Edge (twoCyc b m s) b m := ⟨_, gb, (one m m).2 rfl, _, gm⟩
  have eMB : Edge (twoCyc b m s) m b := ⟨_, gm, (one b b).2 rfl, _, gb⟩
  have hin : InScc L.code b m := by
    rw [hL]; exact ⟨⟨_, gm⟩, Reach.step eBM (Reach.refl m), Reach.step eMB (Reach.refl b)⟩
  have hinmb : InScc L.code m b := by
    rw [hL]; exact ⟨⟨_, gb⟩, Reach.step eMB (Reach.refl b), Reach.step eBM (Reach.refl m)⟩
  have scm : FinMap.get (scOne m (sccSet L.code m)) m = some (sccSet L.code m) := by
    simp [scOne, FinMap.get, FinMap.put]
  have scb : FinMap.get (scOne m (sccSet L.code m)) b = none := by
    simp [scOne, FinMap.get, FinMap.put, FinMap.empty, hbm]
  refine ⟨?_, ?_, scb, hin, scoReach_blocked hbm (by rw [scm]; simp), ?_⟩
  · rw [hL]
    intro c e he
    by_cases h1 : c = b
    · subst h1
      rw [gb] at he
      cases he
      refine ⟨fun c' hc' => ?_, fun c' hc' => by simp [nommInfos] at hc'⟩
      rw [(one m c').1 hc']; exact ⟨_, gm⟩
    · by_cases h2 : c = m
      · subst h2
        rw [gm] at he
        cases he
        refine ⟨fun c' hc' => ?_, fun c' hc' => by simp [nommInfos] at hc'⟩
        rw [(one b c').1 hc']; exact ⟨_, gb⟩
      · rw [go c h1 h2] at he; cases he
  · intro k S hk
    by_cases h : k = m
    · subst h
      rw [scm] at hk
      exact (Option.some.inj hk).symm
    · simp [scOne, FinMap.get, FinMap.put, FinMap.empty, h] at hk
  · intro hg
    have := (hg m _ scm).2 b (sccSet_get.2 hinmb)
    rw [scb] at this
    cases this

end Compiler
end Formalization
