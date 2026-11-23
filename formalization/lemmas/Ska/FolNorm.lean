import lemmas.Ska.FolRel
import lemmas.Ska.SockNorm

/-!
# Normal products of `fol-loop`

On a subject sock with a normal cape (no `[| |]`, `NormSock`), with a table
whose answers on normal subject socks have normal products (`TabNorm`), every
product of `fol-loop` is normal (`folStep_norm`, `folR_norm`), as
`folStep_wf` and `folR_wf` show for well-formedness.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- The answers of a table on normal subject socks have normal products. -/
def TabNorm (tab : Tab) : Prop := ∀ s f a, NormSock s → tab s f = some a → NormSock a.prod

/-- A run of the recursion `go` on a normal subject sock has a normal
product. -/
def GoNorm (go : FolGo) : Prop :=
  ∀ fol sub mk bc df gen out gen', NormSock sub.sock → go fol sub mk bc df gen = some (out, gen') →
    NormSock out.prod.sock

theorem normSock_dunnoA : NormSock Anno.dunno.sock := normSock_dunno

theorem callStep_norm {tab : Tab} {go : FolGo} (htab : TabNorm tab) (IH : GoNorm go)
    {mk : Option Noun} {bc df : Bool} {s f out : FolOut} {gen gen' : Gen}
    (hs : NormSock s.prod.sock) (h : callStep tab go mk bc df s f gen = some (out, gen')) :
    NormSock out.prod.sock := by
  unfold callStep at h
  by_cases hv : s.prod.sock = Sock.void ∨ f.prod.sock = Sock.void
  · rw [if_pos hv] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact normSock_void
  rw [if_neg hv] at h
  have dflt : ∀ (o : FolOut) (g : Gen), some (o, g) = some (out, gen') → o.prod = Anno.dunno →
      NormSock out.prod.sock := by
    intro o g e hp
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rw [hp]; exact normSock_dunno
  cases hf : f.prod.sock with
  | void => exact absurd (Or.inr hf) hv
  | mk c d =>
  rw [hf] at h
  cases c with
  | no => exact dflt _ _ h rfl
  | cell _ _ => exact dflt _ _ h rfl
  | yes =>
  cases d with
  | atom _ => exact dflt _ _ h rfl
  | cell fa fb =>
  cases bc with
  | true => exact dflt _ _ h rfl
  | false =>
  simp only at h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨i, hi, rfl, rfl⟩ := h
    have := IH _ _ _ _ _ _ _ _ hs hi
    exact this
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨dd, hd, h⟩ := h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact htab _ _ _ hs hd

/-- **One level of `fol-loop` keeps normal products.** -/
theorem folStep_norm {tab : Tab} {go : FolGo} (htab : TabNorm tab) (IH : GoNorm go) :
    GoNorm (folStep tab go) := by
  intro fol sub mk bc df gen out gen' hsub h
  cases hs : shape fol with
  | cons a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
    exact normSock_consProd (IH _ _ _ _ _ _ _ _ hsub h1) (IH _ _ _ _ _ _ _ _ hsub h2)
  | op0 p =>
    simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨pr, hpr, rfl, rfl⟩ := h
    split at hpr
    · cases hpr; exact normSock_dunno
    · split at hpr
      · cases hpr; exact hsub
      · simp only [Option.map_eq_some_iff] at hpr
        obtain ⟨s', hs', rfl⟩ := hpr
        exact normSock_pull hsub hs'
  | op1 p =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact normSock_yes p
  | op2 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s1, g1⟩, h1, ⟨f1, g2⟩, h2, h3⟩ := h
    exact callStep_norm htab IH (IH _ _ _ _ _ _ _ _ hsub h1) h3
  | op3 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    exact normSock_dunno
  | op4 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    exact normSock_dunno
  | op5 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact normSock_dunno
  | op6 a b q r =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, ⟨r1, g3⟩, h3, rfl, rfl⟩ := h
    exact normSock_doubleInt (IH _ _ _ _ _ _ _ _ hsub h2) (IH _ _ _ _ _ _ _ _ hsub h3)
  | op7 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have := IH _ _ _ _ _ _ _ _ (IH _ _ _ _ _ _ _ _ hsub h1) h2
    exact this
  | op8 a b q =>
    simp only [folStep, hs] at h
    exact IH _ _ _ _ _ _ _ _ hsub h
  | op9 p a b =>
    simp only [folStep, hs] at h
    exact IH _ _ _ _ _ _ _ _ hsub h
  | op10 ax don r1 r2 =>
    simp only [folStep, hs] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact normSock_dunno
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, s', hd, rfl, rfl⟩ := h
      exact normSock_darn (IH _ _ _ _ _ _ _ _ hsub h2) (IH _ _ _ _ _ _ _ _ hsub h1) hd
  | op11s p a b =>
    simp only [folStep, hs] at h
    split at h
    · exact IH _ _ _ _ _ _ _ _ hsub h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨q1, g1⟩, h1, rfl, rfl⟩ := h
      have := IH _ _ _ _ _ _ _ _ hsub h1
      exact this
  | op11d tag h1 h2 f =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨hh, g1⟩, e1, h⟩ := h
    split at h
    · exact IH _ _ _ _ _ _ _ _ hsub h
    · simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨arm, harm, ⟨fr, g3⟩, h3, rfl, rfl⟩ := h
      have := IH _ _ _ _ _ _ _ _ hsub h3
      exact this
  | op12 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact normSock_dunno
  | other =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact normSock_dunno

section Rel

variable {P : Sock → Noun → TabEntry → Prop}

/-- **`FolR` keeps normal products**, for answers whose products are normal
on normal subject socks (the analogue of `folR_wf`). -/
theorem folR_norm (hP : ∀ tab, TabIn P tab → TabNorm tab) :
    ∀ (n : Nat) {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen}
      {out : FolOut}, NormSock sub.sock → FolR P n fol sub mk bc df gen out gen' →
      NormSock out.prod.sock
  | 0, _, _, _, _, _, _, _, _, _, h => h.elim
  | n + 1, _, _, _, _, _, _, _, _, hs, h => by
    obtain ⟨tab, go, g', ht, hgo, h, _⟩ := h
    have IH : GoNorm go := fun _ _ _ _ _ _ _ _ hs' hg => folR_norm hP n hs' (hgo _ _ _ _ _ _ _ _ hg)
    exact folStep_norm (hP tab ht) IH _ _ _ _ _ _ _ _ hs h

end Rel

end SkaModel
end Formalization
