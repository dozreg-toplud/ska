import lemmas.Compiler.PokeFrame
import lemmas.Compiler.EvalRend

/-!
# `+validate-ovum`, `+validate-bell`, `+validate-cape`

The inner `+poke` first slams `+validate-ovum` on its sample, under a `~_`
hint.  Here: `+validate-cape` returns its sample when `Cape.ofNoun?` accepts
it and crashes otherwise (`vcape_run`), `+validate-bell` likewise with
`Bell.ofNoun?` (`vbell_run`), `+validate-ovum` crashes on a `%dire` whose bell
`+validate-bell` rejects (`vovum_dire_bad`), and so does the poke of every
core with `CorIn` (`pokeDireBad`, the former hypothesis `PokeDireBad`).
The arms sit in the core at axis `15` of the compiler's core, `vcore`, which
every core with `CorIn` shares with `cor`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

def vcapeBat : Noun :=
  (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6))))))) (C (C (A 0) (A 6)) (C (A 0) (A 0))))) (C (A 11) (C (C (A 1869440365) (C (A 1) (A 0))) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))))))))))) (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6))))))

def vbellBat : Noun :=
  (C (A 8) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 3) (C (A 0) (A 13))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (C (C (A 8) (C (C (A 9) (C (A 84) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2)))))))) (C (A 0) (A 25))) (C (A 0) (A 13))) (C (A 0) (A 0))))) (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6))))))

def vovumBat : Noun :=
  (C (A 8) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 0) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1937007978)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1819047270)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 1953718630)) (C (A 0) (A 12)))))))))) (C (C (A 8) (C (C (A 9) (C (A 685) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1701996900)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1701996900)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 27)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 27))))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 343) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))) (C (A 0) (A 0))))) (C (A 11) (C (C (A 1936945012) (C (A 1) (A 0))) (C (A 0) (A 0))))))))))))) (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6))))))

def ipokeB : Noun :=
  (C (A 11) (C (C (A 1851876717) (C (C (A 1) (C (A 1) (A 2441013665125647850499502136360013400924842867))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 9) (C (A 170) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))))


def gateArm (bat : Noun) : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) bat) (C (A 0) (A 1))))

/-- The core of the validating arms: axis `15` of `cor`. -/
def vcore : Noun := (slot? 15 cor).getD (A 0)

theorem cor_vcore : slot? 15 cor = some vcore := by kernel_rfl
theorem vcore_cape : slot? 84 vcore = some (gateArm vcapeBat) := by kernel_rfl
theorem vcore_bell : slot? 343 vcore = some (gateArm vbellBat) := by kernel_rfl
theorem vcore_ovum : slot? 170 vcore = some (gateArm vovumBat) := by kernel_rfl

def ipokeR : Noun :=
  match ipokeBat with
  | Noun.cell _ (Noun.cell _ r) => r
  | _ => A 0

theorem ipokeBat_eq : ipokeBat = C (A 8) (C ipokeB ipokeR) := by kernel_rfl

@[nock_exec] theorem gateArm_run (bat c : Noun) : nock c (gateArm bat) = some (C bat (C (A 0) c)) := by
  unfold gateArm; simp [nock_exec]

/-! ## The runs -/

theorem vcape_run (c : Noun) : ∀ n : Noun,
    nock (C vcapeBat (C n c)) vcapeBat = (Cape.ofNoun? n).map Cape.toNoun
  | Noun.atom a => by
    nock_open vcapeBat
    rcases Nat.lt_or_ge a 2 with h | h
    · rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
        simp [nock_exec, Cape.ofNoun?, Cape.toNoun]
    · have h1 : ¬ (1 = a) := by omega
      have h0 : ¬ (0 = a) := by omega
      have h2 : Cape.ofNoun? (A a) = none := by
        match a, h with
        | a + 2, _ => rfl
      simp [nock_exec, h1, h0, h2]
  | Noun.cell h t => by
    have ih1 := vcape_run c h
    have ih2 := vcape_run c t
    nock_open vcapeBat
    simp only [nock_exec, ih1, ih2]
    cases e1 : Cape.ofNoun? h <;> cases e2 : Cape.ofNoun? t <;>
      simp [Cape.ofNoun?, e1, e2, Cape.toNoun, nock_exec]

theorem vbell_run (c : Noun) (hc : slot? 84 c = some (gateArm vcapeBat)) (n : Noun) :
    nock (C vbellBat (C n c)) vbellBat = (Bell.ofNoun? n).map Bell.toNoun := by
  nock_open vbellBat
  rcases n with a | ⟨hd | ⟨cp, d⟩, tl | ⟨f, g⟩⟩
  · simp [nock_exec, Bell.ofNoun?]
  · simp [nock_exec, Bell.ofNoun?]
  · simp [nock_exec, Bell.ofNoun?]
  · simp [nock_exec, Bell.ofNoun?]
  · simp only [nock_exec, hc, gateArm_run, vcape_run]
    cases e : Cape.ofNoun? cp <;> simp [Bell.ofNoun?, e, Bell.toNoun, Sock.toNoun, nock_exec]

theorem vovum_dire (c : Noun) (hc : slot? 84 c = some (gateArm vcapeBat))
    (hb : slot? 343 c = some (gateArm vbellBat)) (b : Noun) (m : Bool) :
    nock (C vovumBat (C (C (A Tag.dire) (C b (flag m))) c)) vovumBat =
      (Bell.ofNoun? b).map fun bb => C (A Tag.dire) (C bb.toNoun (flag m)) := by
  nock_open vovumBat
  cases m <;> cases e : Bell.ofNoun? b <;>
    simp [nock_exec, flag, Tag.dire, hb, gateArm_run, vbell_run c hc, e]

/-! ## In the poke -/

theorem pokeN_eq {cr : Noun} (hb : slot? 2 cr = slot? 2 cor) (ovo : Noun) :
    pokeN cr ovo = nock (C ipokeBat (C ovo cr)) ipokeBat := by
  have h23 : slot? Ska.axPoke cr = slot? Ska.axPoke cor :=
    slot_under (by decide) hb 3 _ (by decide)
  unfold pokeN
  rw [h23, cor_ipoke]
  simp only [nock_exec]

theorem nock_eight {s f b r : Noun} (hf : f = C (A 8) (C b r)) :
    nock s f = (nock s b).bind fun p => nock (C p s) r := by
  subst hf; simp only [nock_exec]

/-- The poke of a core with `CorIn` slams `+validate-ovum` of `vcore` on its
sample first: if the poke returns, so does `+validate-ovum`. -/
theorem pokeN_validates {cr ovo x : Noun} (hc : CorIn cr) (h : pokeN cr ovo = some x) :
    ∃ v, nock (C vovumBat (C ovo vcore)) vovumBat = some v := by
  obtain ⟨h2, -, h15⟩ := pokeReach_frame hc.2.2
  rw [pokeN_eq h2] at h
  rw [nock_eight ipokeBat_eq, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, -⟩ := h
  rw [cor_vcore] at h15
  refine ⟨v, ?_⟩
  unfold ipokeB at hv
  simp only [nock_exec, h15, vcore_ovum, gateArm_run] at hv
  simpa using hv

/-- **`PokeDireBad`**: the poke of every core with `CorIn` crashes on a `%dire`
whose bell `+validate-bell` rejects. -/
theorem pokeDireBad {cr : Noun} (hc : CorIn cr) : PokeDireBad cr := by
  intro n mono hn
  cases h : pokeN cr (C (A Tag.dire) (C n (flag mono))) with
  | none => rfl
  | some x =>
    obtain ⟨v, hv⟩ := pokeN_validates hc h
    rw [vovum_dire vcore vcore_cape vcore_bell, hn] at hv
    cases hv

end Compiler
end Formalization
