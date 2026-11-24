import lemmas.Compiler.HeSock

/-!
# Toward: a `%he` turn of `resolve` moves to another identity

`+recursive-call` answers `%he` for the identity `[a f]` and a frame `[b f]`
when `(he-sock a b)` holds, and `resolve` goes on with `[(msg-sock a b) f]`.
The lemma wanted is `heSock a b → a ≠ b → msgSock a b ≠ some a`.  Proved
here: the two facts it rests on that are about one arm each, `knit_eq_cell`
(a knit that is a cell sock is the knit of its halves) and `heSock_size`
(`+he-sock` never grows the cape).  Left: `msgSock a b = some a` gives
`capeSize` of `b` at least that of `a` (by induction, the halves through
`knit_eq_cell`, a cape `|` through `capeSize_pos`), and then the main lemma
by induction: a couple of halves is equal by induction, `b` inside a half of
`a` has too large a cape by `heSock_size`, and a cape `|` embeds only itself.
-/

namespace Formalization
namespace SkaModel

open Nock Compiler

theorem knit_eq_cell {h t : Sock} {ah aT : Cape} {d1 d2 : Noun}
    (e : So.knit h t = Sock.mk (Cape.cell ah aT) (C d1 d2)) :
    h = Sock.mk ah d1 ∧ t = Sock.mk aT d2 := by
  cases h with
  | void => simp [So.knit] at e
  | mk l x1 =>
  cases t with
  | void => simp [So.knit] at e
  | mk r x2 =>
  have key : ∀ c : Cape, (if c = Cape.no then Sock.dunno else Sock.mk c (C x1 x2)) =
      Sock.mk (Cape.cell ah aT) (C d1 d2) → c = Cape.cell ah aT ∧ x1 = d1 ∧ x2 = d2 := by
    intro c hc
    by_cases h0 : c = Cape.no
    · rw [if_pos h0] at hc; simp [Sock.dunno] at hc
    · rw [if_neg h0] at hc
      simp only [Sock.mk.injEq, Noun.cell.injEq] at hc
      exact ⟨hc.1, hc.2.1, hc.2.2⟩
  simp only [So.knit] at e
  obtain ⟨hc, rfl, rfl⟩ := key _ e
  unfold Ca.con at hc
  split at hc
  · simp at hc
  · simp only [Cape.cell.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨rfl, rfl⟩

/-- **`+he-sock` never grows the cape**: if it holds of two different socks,
both are socks with capes and the second cape is no larger. -/
theorem heSock_size {x y : Sock} (h : heSock x y = true) (hne : x ≠ y) :
    ∃ cx dx cy dy, x = Sock.mk cx dx ∧ y = Sock.mk cy dy ∧ capeSize cy ≤ capeSize cx := by
  rw [heSock.eq_def, if_neg hne] at h
  cases x with
  | void => simp at h
  | mk cx dx =>
  cases y with
  | void => simp at h
  | mk cy dy =>
  refine ⟨cx, dx, cy, dy, rfl, rfl, ?_⟩
  simp only at h
  apply Classical.byContradiction
  intro hlt
  rw [if_pos (by omega)] at h
  simp at h

end SkaModel
end Formalization
