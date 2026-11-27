import lemmas.Compiler.CompSofNouns
import lemmas.Compiler.CompUnaryDir

/-!
# The push of `sof` (README Gaps 19, item (f))

```hoon
=/  sof=?
  ?&  ?=(~ key)
      !(sound (made p.nomm sup) b-ned)
      ?|  (need-soft b-ned b-sur less.b-callee)
          (hinted p.nomm code.long-ska)
          (hinted q.nomm code.long-ska)
  ==  ==
```

The push `crDKc6` returns when `+sound-far` (through `+sound`) and
`+need-soft` return loobeans: `+made` is `made_gate`, `+hinted` is
`hd_gateR` on callees with their code entries (`CallCode`, `hinted_code`).
So `SofRet` (`CompUnaryDir.lean`) comes down to two facts on the arms of
`K`, stated as `SoundFarRet` and `NeedSoftRet`.

* `snd_arm`, `sf_arm`, `ns_arm`: the arms build their gates.
* `snd_gate`: `+sound` is `+sound-far` on `code.long-ska` at depth `3`.
* **`sof_push`**: `SofRet` from `SoundFarRet`, `NeedSoftRet` and the code
  entries of the callees of `p` and `q`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

theorem snd_arm (d : Noun) :
    nock d sndArm = some (C sndBat (C (C (C (A 0) (A 0)) (C (A 0x656e6f6e) (A 0))) d)) := by
  unfold sndArm; simp only [nock_exec]

theorem sf_arm (d : Noun) :
    nock d sfArm = some (C sfBat (C (C (C (A 0) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (A 0)))) d)) := by
  unfold sfArm; simp only [nock_exec]

theorem ns_arm (d : Noun) :
    nock d nsArm = some (C nsBat (C (C (C (A 0x656e6f6e) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (C (A 1) (A 0)))) d)) := by
  unfold nsArm; simp only [nock_exec]

/-- **`+sound`** (door arm `13654`) is `+sound-far` on `[nom ned
code.long-ska 3]`. -/
theorem snd_gate (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (g : Gen (TreapMap mugF)) (x : GenRest) (nomN nedN : Noun) :
    nock (C sndBat (C (C nomN nedN) (compCore g x ctx))) sndBat
      = nock (C sfBat (C (C nomN (C nedN (C cod (A 3)))) compK)) sfBat := by
  have hK := compK_sf
  conv => lhs; arg 2; unfold sndBat
  simp [nock_exec, compCore, h7, hcode, hK, sf_arm]

/-- **`+sound-far` returns a loobean** on `[nom ned cod 3]`, the sample
`+sound` gives it (item (f), not linked: K arm `5467`). -/
def SoundFarRet (nom : Nomm) (ned : NeedOrd) (cod : Noun) : Prop :=
  ∃ s, nock (C sfBat (C (C nom.toNoun (C ned.toNoun (C cod (A 3)))) compK)) sfBat = some (loob s)

/-- **`+need-soft` returns a loobean** on `[ned sur k]` (item (f), not
linked: K arm `5466`). -/
def NeedSoftRet (ned sur : NeedOrd) (k : Sock) : Prop :=
  ∃ t, nock (C nsBat (C (C ned.toNoun (C sur.toNoun k.toNoun)) compK)) nsBat = some (loob t)

/-- **The push of `sof` returns** (`SofRet`) when `+sound-far` returns on
`(made p sup)` and `b-ned`, `+need-soft` returns on `b-ned`, `b-sur`,
`less.b-callee`, and the callees of `p` and `q` have their code entries
(`+hinted`, `hd_gateR`).  Its value is `!s && (t || hinted p || hinted q)`,
the same on every state. -/
theorem sof_push (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd) (x : GenRest)
    (hcp : CallCode cod env p) (hcq : CallCode cod env q)
    (hsf : SoundFarRet (made p msup) nb cod) (hns : NeedSoftRet nb (env.sure b) b.less) :
    SofRet env msup ctx p q b nb x := by
  obtain ⟨s, hs⟩ := hsf
  obtain ⟨t, ht⟩ := hns
  obtain ⟨hp, ehp⟩ := hinted_code p hcp
  obtain ⟨hq, ehq⟩ := hinted_code q hcq
  have hdp := hd_gateR cod env p hp hcp ehp
  have hdq := hd_gateR cod env q hq hcq ehq
  have hK := compK_hd
  have hN := compK_ns
  have hM := comp_made_at
  have hS := comp_sound_at
  refine ⟨loob (!s && (t || hp || hq)), fun g SV SN PV goalN regionN => ?_⟩
  have hsnd := snd_gate h7 hcode g x (made p msup).toNoun nb.toNoun
  have hmd := made_gate (compCore g x ctx) p msup
  rw [hs] at hsnd
  simp only [compCore] at hsnd hmd
  unfold crDKc6
  simp only [compCore]
  generalize comp.door = Dr at hM hS hsnd hmd ⊢
  cases s <;> cases t <;> cases hp <;> cases hq <;>
    simp [nock_exec, crSubj, Bell.toNoun, h7, hcode, hK, hN, hM, hS, hd_arm, ns_arm, snd_arm, madArm, hsnd,
      hmd, hdp, hdq, ht, loob]

/-! ## Every call -/

/-- **The two arm facts at every direct call of `n`**, each at the `msup`
its run gets: `+sound-far` on `(made p msup)` and the callee's need, and
`+need-soft` on the need, `env.sure b` and `less` of the callee. -/
def SofArms (env : CallEnv) (cod : Noun) : Option Nomm → Nomm → Prop
  | ms, Nomm.cons p q => SofArms env cod ms p ∧ SofArms env cod ms q
  | ms, Nomm.n2 p q Option.none => SofArms env cod ms p ∧ SofArms env cod ms q
  | ms, Nomm.n2 p q (some (b, _)) =>
      (∀ nb, env.need b = some nb → SoundFarRet (made p ms) nb cod ∧ NeedSoftRet nb (env.sure b) b.less) ∧
        SofArms env cod ms p ∧ SofArms env cod ms q
  | ms, Nomm.n3 p => SofArms env cod ms p
  | ms, Nomm.n4 p => SofArms env cod ms p
  | ms, Nomm.n5 p q => SofArms env cod ms p ∧ SofArms env cod ms q
  | ms, Nomm.n6 p q r => SofArms env cod ms p ∧ SofArms env cod ms q ∧ SofArms env cod ms r
  | ms, Nomm.n7 p q => SofArms env cod ms p ∧ SofArms env cod (some p) q
  | ms, Nomm.n10 _ v q => SofArms env cod ms v ∧ SofArms env cod ms q
  | _, _ => True

/-- `CallCode` of a nomm of `DirOk` whose callees have code entries, for an
environment of the samples. -/
theorem callCode_of_bells {env : CallEnv} {CODE COLE : Noun} (he : EnvFrom env CODE COLE) :
    ∀ (n : Nomm), DirOk n = true → (∀ b ∈ dirBells n, ∃ c, codeOf CODE b = some c) → CallCode CODE env n
  | Nomm.cons p q, h, hb => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨callCode_of_bells he p h.1 fun b m => hb b (Or.inl m), callCode_of_bells he q h.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n0 _, _, _ => trivial
  | Nomm.n1 _, _, _ => trivial
  | Nomm.n2 p q Option.none, h, hb => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨trivial, callCode_of_bells he p h.1 fun b m => hb b (Or.inl m),
      callCode_of_bells he q h.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n2 p q (some (b0, Option.none)), h, hb => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_cons, List.mem_append] at hb
    obtain ⟨c, hc⟩ := hb b0 (Or.inl rfl)
    exact ⟨codePure_of he hc, callCode_of_bells he p h.1 fun b m => hb b (Or.inr (Or.inl m)),
      callCode_of_bells he q h.2 fun b m => hb b (Or.inr (Or.inr m))⟩
  | Nomm.n2 _ _ (some (_, some _)), h, _ => by simp [DirOk] at h
  | Nomm.n3 p, h, hb => by simp only [DirOk] at h; exact callCode_of_bells he p h hb
  | Nomm.n4 p, h, hb => by simp only [DirOk] at h; exact callCode_of_bells he p h hb
  | Nomm.n5 p q, h, hb => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨callCode_of_bells he p h.1 fun b m => hb b (Or.inl m), callCode_of_bells he q h.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n6 p q r, h, hb => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨callCode_of_bells he p h.1.1 fun b m => hb b (Or.inl (Or.inl m)),
      callCode_of_bells he q h.1.2 fun b m => hb b (Or.inl (Or.inr m)),
      callCode_of_bells he r h.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n7 p q, h, hb => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨callCode_of_bells he p h.1 fun b m => hb b (Or.inl m), callCode_of_bells he q h.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n10 _ v q, h, hb => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨callCode_of_bells he v h.1.2 fun b m => hb b (Or.inl m),
      callCode_of_bells he q h.2 fun b m => hb b (Or.inr m)⟩
  | Nomm.n11s _ _ _, h, _ => by simp [DirOk] at h
  | Nomm.n11d _ _ _ _, h, _ => by simp [DirOk] at h
  | Nomm.n12 _ _, h, _ => by simp [DirOk] at h
  | Nomm.mean _ _ _ _ _, h, _ => by simp [DirOk] at h

/-- **`SofAll` from the two arm facts** (`sof_push` at every call). -/
theorem sofAll_of_arms (h7 : slot? 7 ctx = some compK) {CODE COLE : Noun} (hcode : slot? 52 ctx = some CODE)
    {env : CallEnv} (he : EnvFrom env CODE COLE) (x : GenRest) :
    ∀ (ms : Option Nomm) (n : Nomm), DirOk n = true → (∀ b ∈ dirBells n, ∃ c, codeOf CODE b = some c) →
      SofArms env CODE ms n → SofAll env ctx x ms n
  | ms, Nomm.cons p q, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAll_of_arms h7 hcode he x ms p h.1 (fun b m => hb b (Or.inl m)) hs.1,
      sofAll_of_arms h7 hcode he x ms q h.2 (fun b m => hb b (Or.inr m)) hs.2⟩
  | _, Nomm.n0 _, _, _, _ => trivial
  | _, Nomm.n1 _, _, _, _ => trivial
  | ms, Nomm.n2 p q Option.none, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAll_of_arms h7 hcode he x ms p h.1 (fun b m => hb b (Or.inl m)) hs.1,
      sofAll_of_arms h7 hcode he x ms q h.2 (fun b m => hb b (Or.inr m)) hs.2⟩
  | ms, Nomm.n2 p q (some (b0, Option.none)), h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_cons, List.mem_append] at hb
    have hbp : ∀ b ∈ dirBells p, ∃ c, codeOf CODE b = some c := fun b m => hb b (Or.inr (Or.inl m))
    have hbq : ∀ b ∈ dirBells q, ∃ c, codeOf CODE b = some c := fun b m => hb b (Or.inr (Or.inr m))
    exact ⟨fun nb hnb => sof_push h7 hcode env ms p q b0 nb x (callCode_of_bells he p h.1 hbp)
        (callCode_of_bells he q h.2 hbq) (hs.1 nb hnb).1 (hs.1 nb hnb).2,
      sofAll_of_arms h7 hcode he x ms p h.1 hbp hs.2.1, sofAll_of_arms h7 hcode he x ms q h.2 hbq hs.2.2⟩
  | _, Nomm.n2 _ _ (some (_, some _)), h, _, _ => by simp [DirOk] at h
  | ms, Nomm.n3 p, h, hb, hs => by simp only [DirOk] at h; exact sofAll_of_arms h7 hcode he x ms p h hb hs
  | ms, Nomm.n4 p, h, hb, hs => by simp only [DirOk] at h; exact sofAll_of_arms h7 hcode he x ms p h hb hs
  | ms, Nomm.n5 p q, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAll_of_arms h7 hcode he x ms p h.1 (fun b m => hb b (Or.inl m)) hs.1,
      sofAll_of_arms h7 hcode he x ms q h.2 (fun b m => hb b (Or.inr m)) hs.2⟩
  | ms, Nomm.n6 p q r, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAll_of_arms h7 hcode he x ms p h.1.1 (fun b m => hb b (Or.inl (Or.inl m))) hs.1,
      sofAll_of_arms h7 hcode he x ms q h.1.2 (fun b m => hb b (Or.inl (Or.inr m))) hs.2.1,
      sofAll_of_arms h7 hcode he x ms r h.2 (fun b m => hb b (Or.inr m)) hs.2.2⟩
  | ms, Nomm.n7 p q, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAll_of_arms h7 hcode he x ms p h.1 (fun b m => hb b (Or.inl m)) hs.1,
      sofAll_of_arms h7 hcode he x (some p) q h.2 (fun b m => hb b (Or.inr m)) hs.2⟩
  | ms, Nomm.n10 _ v q, h, hb, hs => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [dirBells, List.mem_append] at hb
    exact ⟨sofAll_of_arms h7 hcode he x ms v h.1.2 (fun b m => hb b (Or.inl m)) hs.1,
      sofAll_of_arms h7 hcode he x ms q h.2 (fun b m => hb b (Or.inr m)) hs.2⟩
  | _, Nomm.n11s _ _ _, h, _, _ => by simp [DirOk] at h
  | _, Nomm.n11d _ _ _ _, h, _, _ => by simp [DirOk] at h
  | _, Nomm.n12 _ _, h, _, _ => by simp [DirOk] at h
  | _, Nomm.mean _ _ _ _ _, h, _, _ => by simp [DirOk] at h

/-- **The gate of `+compile-unary` on `DirOk` with direct calls, `sof`
down to its two arms** (README Gaps 19): `cu_gate_dir_csi` with `SofAll`
from `SofArms` (`+sound-far` and `+need-soft` return at every call). -/
theorem cu_gate_dir_arms (FUNC SCC CODE LSR JH CACHE NM CA V COLE : Noun) (env : CallEnv) (n : Nomm)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 LSR = some COLE) (hcr : CodeNoRing CODE COLE n)
    (hn : DirOk n = true) (he : EnvFrom env CODE COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hneed : CsiNeeds env SCC NM CA n) (hsure : CsiSures env CA n)
    (harm : SofArms env CODE Option.none n) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA :=
  cu_gate_dir_csi FUNC SCC CODE LSR JH CACHE NM CA V COLE env n hgot hv hcl hcr hn he hcsi hneed hsure
    (sofAll_of_arms rfl (by simp [cuCtx, nock_exec]) he (cuRest CA) Option.none n hn (fun b m => (hcr b m).1) harm)

end Compiler
end Formalization
