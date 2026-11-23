import lemmas.Ska.BakeImp

/-!
# The final pass of `+bake-graph` does not crash

`+know` with one `res` and with another that succeeds on every site the
first run lists gives the same products and sites (`knowGo_res`, which has
`knowGo_idc` of `BakeGraph.lean` as the case of `idc`).  With it, the final
pass of `+bake-graph` returns whenever the worklist ends
(`finalPass_some`): every bell with a bake was evaluated under its last
bake, so it has a datum and `+know` returned under it, `+pick` returned for
each of its sites, and a site that `+pick` sends to no variant has a bake
for its callee (`bakeLoop_sound`).
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

/-- `res` succeeds on every site of the list. -/
def ResAll (res : Bell → Sock → Option Bell) (l : List Site) : Prop := ∀ x ∈ l, (res x.1 x.2).isSome = true

theorem ResAll.sub {res : Bell → Sock → Option Bell} {a b : List Site} (h : ResAll res b) (hs : a <:+ b) :
    ResAll res a := fun x hx => h x (hs.subset hx)

/-- **`+know` with another `res`** that succeeds on the sites of a run gives
the same products and sites. -/
theorem knowGo_res (fold : Bool) (dat : Bell → Option Datum) (res res2 : Bell → Sock → Option Bell) :
    ∀ (nm : Nomm) (sub : Anno) (st : List Site) (r : (Nomm × Anno) × List Site),
      knowGo fold dat res nm sub st = some r → ResAll res2 r.2 →
      ∃ r', knowGo fold dat res2 nm sub st = some r' ∧ SameRun r r' := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro sub st r h hres
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, r1, hr1, h⟩ := h
    have e2 : r.2 = r1.2 := by split at h <;> (cases h; rfl)
    have hq : ResAll res2 r1.2 := e2 ▸ hres
    have hp : ResAll res2 l.2 := hq.sub (knowGo_suffix _ dat res q sub l.2 r1 hr1)
    obtain ⟨l', hl', el, pl, sl⟩ := ihp sub st l hl hp
    obtain ⟨r1', hr1', er, pr, sr⟩ := ihq sub l.2 r1 hr1 hq
    rw [← sl] at hr1'
    simp only [knowGo, hl', Option.bind_some, hr1']
    have e1 : lit l'.1.1 = lit l.1.1 := by rw [← lit_eraseN, el, lit_eraseN]
    have e2 : lit r1'.1.1 = lit r1.1.1 := by rw [← lit_eraseN, er, lit_eraseN]
    rw [e1, e2]
    split at h
    · cases h; exact ⟨_, rfl, rfl, rfl, sr⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, el, er], by simp only [pl, pr], sr⟩
  | n0 p =>
    intro sub st r h _
    exact ⟨r, by rw [← h]; rfl, rfl, rfl, rfl⟩
  | n1 p =>
    intro sub st r h _
    exact ⟨r, by rw [← h]; rfl, rfl, rfl, rfl⟩
  | n2 p q info ihp ihq =>
    intro sub st r h hres
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, f, hf, h⟩ := h
    have hf2 : ResAll res2 f.2 := by
      cases info with
      | none =>
        simp only [Option.some.injEq] at h
        subst h
        exact hres
      | some i =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨v, _, rfl⟩ := h
        exact fun x hx => hres x (List.mem_cons_of_mem _ hx)
    have hs2 : ResAll res2 s.2 := hf2.sub (knowGo_suffix _ dat res q sub s.2 f hf)
    obtain ⟨s', hs', es, ps, ss⟩ := ihp sub st s hs hs2
    obtain ⟨f', hf', ef, pf, sf⟩ := ihq sub s.2 f hf hf2
    rw [← ss] at hf'
    simp only [knowGo, hs', Option.bind_some, hf']
    cases info with
    | none =>
      simp only [Option.some.injEq] at h ⊢
      subst h
      exact ⟨_, rfl, by simp only [eraseN, es, ef, Option.map_none], rfl, sf⟩
    | some i =>
      obtain ⟨b, mk⟩ := i
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨v, _, rfl⟩ := h
      obtain ⟨v2, hv2⟩ := Option.isSome_iff_exists.mp (hres _ List.mem_cons_self)
      have hv2' : res2 b s'.1.2.sock = some v2 := by rw [ps]; exact hv2
      simp only [hv2', Option.map_some]
      exact ⟨_, rfl, by simp only [eraseN, es, ef, Option.map_some], by simp only [ps], by simp only [ps, sf]⟩
  | n3 p ih =>
    intro sub st r h hres
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    have e : r.2 = a.2 := by split at h <;> (cases h; rfl)
    obtain ⟨a', ha', ea, pa, sa⟩ := ih sub st a ha (e ▸ hres)
    simp only [knowGo, ha', Option.map_some]
    rw [pa, safeNomm_erase ea]
    split at h
    · cases h; exact ⟨_, rfl, rfl, rfl, sa⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea], rfl, sa⟩
  | n4 p ih =>
    intro sub st r h hres
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    have e : r.2 = a.2 := by split at h <;> (cases h; rfl)
    obtain ⟨a', ha', ea, pa, sa⟩ := ih sub st a ha (e ▸ hres)
    simp only [knowGo, ha', Option.map_some]
    rw [pa, safeNomm_erase ea]
    split at h
    · cases h; exact ⟨_, rfl, rfl, rfl, sa⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea], rfl, sa⟩
  | n5 p q ihp ihq =>
    intro sub st r h hres
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    have e : r.2 = b.2 := by split at h <;> (cases h; rfl)
    have hb2 : ResAll res2 b.2 := e ▸ hres
    have ha2 : ResAll res2 a.2 := hb2.sub (knowGo_suffix _ dat res q sub a.2 b hb)
    obtain ⟨a', ha', ea, pa, sa⟩ := ihp sub st a ha ha2
    obtain ⟨b', hb', eb, pb, sb⟩ := ihq sub a.2 b hb hb2
    rw [← sa] at hb'
    simp only [knowGo, ha', Option.bind_some, hb', Option.map_some]
    rw [pa, pb, safeNomm_erase ea, safeNomm_erase eb]
    split at h
    · cases h; exact ⟨_, rfl, rfl, rfl, sb⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea, eb], rfl, sb⟩
  | n6 p q r0 ihp ihq ihr =>
    intro sub st r h hres
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    have ha2 : ResAll res2 a.2 := by
      split at h
      · exact hres.sub (knowGo_suffix _ dat res q sub a.2 r h)
      · exact hres.sub (knowGo_suffix _ dat res r0 sub a.2 r h)
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
        obtain ⟨b, hb, c, hc, rfl⟩ := h
        exact (hres.sub (knowGo_suffix _ dat res r0 sub b.2 c hc)).sub (knowGo_suffix _ dat res q sub a.2 b hb)
    obtain ⟨a', ha', ea, pa, sa⟩ := ihp sub st a ha ha2
    simp only [knowGo, ha', Option.bind_some]
    rw [pa, safeNomm_erase ea, sa]
    split at h
    · exact ihq sub a.2 r h hres
    · exact ihr sub a.2 r h hres
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, c, hc, rfl⟩ := h
      have hc2 : ResAll res2 c.2 := hres
      have hb2 : ResAll res2 b.2 := hc2.sub (knowGo_suffix _ dat res r0 sub b.2 c hc)
      obtain ⟨b', hb', eb, pb, sb⟩ := ihq sub a.2 b hb hb2
      obtain ⟨c', hc', ec, pc, sc⟩ := ihr sub b.2 c hc hc2
      rw [← sb] at hc'
      simp only [hb', Option.bind_some, hc', Option.map_some]
      exact ⟨_, rfl, by simp only [eraseN, ea, eb, ec], by simp only [pb, pc], sc⟩
  | n7 p q ihp ihq =>
    intro sub st r h hres
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    have e : r.2 = b.2 := by split at h <;> (cases h; rfl)
    have hb2 : ResAll res2 b.2 := e ▸ hres
    have ha2 : ResAll res2 a.2 := hb2.sub (knowGo_suffix _ dat res q a.1.2 a.2 b hb)
    obtain ⟨a', ha', ea, pa, sa⟩ := ihp sub st a ha ha2
    obtain ⟨b', hb', eb, pb, sb⟩ := ihq a.1.2 a.2 b hb hb2
    rw [← sa, ← pa] at hb'
    simp only [knowGo, ha', Option.bind_some, hb', Option.map_some]
    have e2 : lit b'.1.1 = lit b.1.1 := by rw [← lit_eraseN, eb, lit_eraseN]
    rw [e2, safeNomm_erase ea]
    split at h
    · cases h; exact ⟨_, rfl, eb, rfl, sb⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea, eb], pb, sb⟩
  | n10 ax v q ihv ihq =>
    intro sub st r h hres
    simp only [knowGo, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    have e : r.2 = b.2 := by
      split at h
      · cases h; rfl
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨_, _, rfl⟩ := h
        rfl
    have hb2 : ResAll res2 b.2 := e ▸ hres
    have ha2 : ResAll res2 a.2 := hb2.sub (knowGo_suffix _ dat res q sub a.2 b hb)
    obtain ⟨a', ha', ea, pa, sa⟩ := ihv sub st a ha ha2
    obtain ⟨b', hb', eb, pb, sb⟩ := ihq sub a.2 b hb hb2
    rw [← sa] at hb'
    simp only [knowGo, ha', Option.bind_some, hb']
    have e1 : lit a'.1.1 = lit a.1.1 := by rw [← lit_eraseN, ea, lit_eraseN]
    have e2 : lit b'.1.1 = lit b.1.1 := by rw [← lit_eraseN, eb, lit_eraseN]
    rw [e1, e2, pa, pb]
    split at h
    · cases h; exact ⟨_, rfl, rfl, rfl, sb⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨s', hs', rfl⟩ := h
      simp only [hs', Option.map_some]
      exact ⟨_, rfl, by simp only [eraseN, ea, eb], rfl, sb⟩
  | n11s tag q body ih =>
    intro sub st r h hres
    simp only [knowGo, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    have e : r.2 = a.2 := by split at h <;> (cases h; rfl)
    obtain ⟨a', ha', ea, pa, sa⟩ := ih sub st a ha (e ▸ hres)
    simp only [knowGo, ha', Option.map_some]
    have e1 : lit a'.1.1 = lit a.1.1 := by rw [← lit_eraseN, ea, lit_eraseN]
    rw [e1]
    split at h
    · cases h; exact ⟨_, rfl, ea, rfl, sa⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea], pa, sa⟩
  | n11d tag hh q body ihh ihq =>
    intro sub st r h hres
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, h⟩ := h
    have e : r.2 = b.2 := by split at h <;> (cases h; rfl)
    have hb2 : ResAll res2 b.2 := e ▸ hres
    have ha2 : ResAll res2 a.2 := hb2.sub (knowGo_suffix _ dat res q sub a.2 b hb)
    obtain ⟨a', ha', ea, pa, sa⟩ := ihh sub st a ha ha2
    obtain ⟨b', hb', eb, pb, sb⟩ := ihq sub a.2 b hb hb2
    rw [← sa] at hb'
    simp only [knowGo, ha', Option.bind_some, hb', Option.map_some]
    have e2 : lit b'.1.1 = lit b.1.1 := by rw [← lit_eraseN, eb, lit_eraseN]
    rw [e2, safeNomm_erase ea]
    split at h
    · cases h; exact ⟨_, rfl, eb, rfl, sb⟩
    · cases h; exact ⟨_, rfl, by simp only [eraseN, ea, eb], pb, sb⟩
  | n12 p q ihp ihq =>
    intro sub st r h hres
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    have hb2 : ResAll res2 b.2 := hres
    have ha2 : ResAll res2 a.2 := hb2.sub (knowGo_suffix _ dat res q sub a.2 b hb)
    obtain ⟨a', ha', ea, pa, sa⟩ := ihp sub st a ha ha2
    obtain ⟨b', hb', eb, pb, sb⟩ := ihq sub a.2 b hb hb2
    rw [← sa] at hb'
    simp only [knowGo, ha', Option.bind_some, hb', Option.map_some]
    exact ⟨_, rfl, by simp only [eraseN, ea, eb], rfl, sb⟩
  | mean p b q body k ihp ihq =>
    intro sub st r h hres
    simp only [knowGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, v, hv, c, hc, rfl⟩ := h
    have hc2 : ResAll res2 c.2 := hres
    have hk2 : ResAll res2 ((b, a.1.2.sock) :: a.2) := hc2.sub (knowGo_suffix _ dat res q sub _ c hc)
    have ha2 : ResAll res2 a.2 := fun x hx => hk2 x (List.mem_cons_of_mem _ hx)
    obtain ⟨a', ha', ea, pa, sa⟩ := ihp sub st a ha ha2
    obtain ⟨c', hc', ec, pc, sc⟩ := ihq sub ((b, a.1.2.sock) :: a.2) c hc hc2
    rw [← sa, ← pa] at hc'
    obtain ⟨v2, hv2⟩ := Option.isSome_iff_exists.mp (hk2 _ List.mem_cons_self)
    have hv2' : res2 b a'.1.2.sock = some v2 := by rw [pa]; exact hv2
    simp only [knowGo, ha', Option.bind_some, hv2', hc', Option.map_some]
    exact ⟨_, rfl, by simp only [eraseN, ea, ec], pc, sc⟩

end Bake

end SkaModel
end Formalization
