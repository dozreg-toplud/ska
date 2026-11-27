import lemmas.Compiler.CompRunRTen
import lemmas.Compiler.CompRunRSixAll

/-!
# The run link at `mono` `&` on the plain class with direct calls (README Gaps 19)

`DirOk`: the plain class with `%6` (`%0`, `%1`, `%3`, `%4`, `%5`, `%6`, `%7`,
cons, `%10` with an axis not `0`, the indirect call), nested in any way, with the direct
call `[2 p q [~ b ~]]` (no memo key), with direct calls anywhere (also in
the subject `p` of a direct call: the case `%2` of `CompRunDirectMonoP.lean`
takes `+past` over `p` as `PastAt ctx env.cod p`, which the induction gives).  `DirCalls env cod ctx E msup n`: per direct
call in `n`, the callee's code entry (`CodePure`, `env.cod b = some (env.pure
b)`), no ring, its need `nb`, and `CallNounM` at `mono` `A 0` for every rest
with `E` (the `msup` of each call is the one the run gives it: `%7` hands
`some p` to `q`).

* `hinted_code`, `pastAt_code`: `+past` over a nomm whose callees have their
  code entries is `pastL env.cod` (`comp_pastR`).
* **`comp_run_dir`**: every nomm of `DirOk` with `DirCalls` is a `PartR` at
  `XM E msup`: the link against `runLCM env true msup` at `mono` `A 0` on
  every goal with `GInv`, its `GRes`, and `PastAt`; by induction, the call
  case by `comp_run_n2_directMM` / `res_n2_directMono`.
* **`comp_run_dirMM`**, `res_dir`: the same as `CompRunAtMM` and `ResForR`.
* `%6` (any part with direct calls, also the test) by `comp_run_n6_allR`
  (`CompRunRSixAll.lean`), its parts `SixPartsR` (`sixR_of`, `+past-fork` by
  `pastForkAt_code`), `Bake.NoAx0` from `DirOk` (`noAx0_of_dir`).
* `CallNounMR`, `callNounM_of_r`, `callOk_of_r`: `CallOk` with `+callee-need`
  and `+callee-sure` read-only (`NeedRead`, `SureNoun`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## `+past` with direct calls -/

theorem orB_ss (a b : Bool) : ∃ c, orB (some a) (some b) = some c := by
  cases a <;> simp [orB]

/-- With every callee's code entry, `+hinted` returns. -/
theorem hinted_code {cod : Noun} {env : CallEnv} : ∀ n : Nomm, CallCode cod env n → ∃ c, hinted env.cod n = some c := by
  intro n
  induction n with
  | n0 _ => intro _; exact ⟨_, rfl⟩
  | n1 _ => intro _; exact ⟨_, rfl⟩
  | n3 p ih => intro h; exact ih h
  | n4 p ih => intro h; exact ih h
  | n12 _ _ _ _ => intro _; exact ⟨_, rfl⟩
  | mean _ _ _ _ _ _ _ => intro _; exact ⟨_, rfl⟩
  | cons p q ihp ihq =>
    intro h; simp only [CallCode] at h
    obtain ⟨a, ha⟩ := ihp h.1; obtain ⟨b, hb⟩ := ihq h.2
    simp only [hinted, ha, hb]; exact orB_ss a b
  | n5 p q ihp ihq =>
    intro h; simp only [CallCode] at h
    obtain ⟨a, ha⟩ := ihp h.1; obtain ⟨b, hb⟩ := ihq h.2
    simp only [hinted, ha, hb]; exact orB_ss a b
  | n7 p q ihp ihq =>
    intro h; simp only [CallCode] at h
    obtain ⟨a, ha⟩ := ihp h.1; obtain ⟨b, hb⟩ := ihq h.2
    simp only [hinted, ha, hb]; exact orB_ss a b
  | n10 _ v q ihv ihq =>
    intro h; simp only [CallCode] at h
    obtain ⟨a, ha⟩ := ihv h.1; obtain ⟨b, hb⟩ := ihq h.2
    simp only [hinted, ha, hb]; exact orB_ss a b
  | n6 p q r ihp ihq ihr =>
    intro h; simp only [CallCode] at h
    obtain ⟨a, ha⟩ := ihp h.1; obtain ⟨b, hb⟩ := ihq h.2.1; obtain ⟨c, hc⟩ := ihr h.2.2
    obtain ⟨d, hd⟩ := orB_ss b c
    simp only [hinted, ha, hb, hc, hd]; exact orB_ss a d
  | n11s tag q _ ihq =>
    intro h; simp only [CallCode] at h
    obtain ⟨b, hb⟩ := ihq h
    simp only [hinted, hb]; exact orB_ss _ b
  | n11d tag hh q _ ihh ihq =>
    intro h; simp only [CallCode] at h
    obtain ⟨a, ha⟩ := ihh h.1; obtain ⟨b, hb⟩ := ihq h.2
    obtain ⟨d, hd⟩ := orB_ss a b
    simp only [hinted, ha, hb, hd]; exact orB_ss _ d
  | n2 p q info ihp ihq =>
    intro h
    rcases info with _ | ⟨bl, k⟩
    · exact ⟨_, rfl⟩
    · simp only [CallCode] at h
      obtain ⟨⟨-, hcb⟩, hp, hq⟩ := h
      obtain ⟨a, ha⟩ := ihp hp; obtain ⟨b, hb⟩ := ihq hq
      obtain ⟨d, hd⟩ := orB_ss a b
      simp only [hinted, ha, hb, hd, hcb, Option.map_some]; exact orB_ss _ d

/-- **`+past` over a nomm whose callees have their code entries** is `pastL
env.cod`. -/
theorem pastAt_code (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    {n : Nomm} (hcc : CallCode cod env n) : PastAt ctx env.cod n := by
  intro x g nex region
  obtain ⟨c, hc⟩ := hinted_code n hcc
  exact comp_pastR h7 hcode x g nex n region env hcc (by rw [hc]; simp)

/-- **`+past-fork` over a nomm whose callees have their code entries** is
`Lazy.pastFork env.cod`. -/
theorem pastForkAt_code (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) {n : Nomm} (hcc : CallCode cod env n) : PastForkAt ctx env.cod n := by
  intro G laz
  obtain ⟨c, hc⟩ := hinted_code n hcc
  exact comp_past_forkR h7 hcode G laz n env hcc (by rw [hc]; simp)

/-- A part of `%6` from its `PartR` and its callees' code entries. -/
theorem sixR_of (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    {env : CallEnv} {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop} {n : Nomm} {region : List Nat}
    (N : PartR env msup ctx X n region) (hcc : CallCode cod env n) : SixPartsR env msup ctx X n region :=
  ⟨N.link, N.res, pastForkAt_code h7 hcode env hcc⟩

/-! ## The class -/

/-- **The plain class with `%6` and direct calls** (no memo key), nested in
any way. -/
def DirOk : Nomm → Bool
  | Nomm.cons p q => DirOk p && DirOk q
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n2 p q Option.none => DirOk p && DirOk q
  | Nomm.n2 p q (some (_, Option.none)) => DirOk p && DirOk q
  | Nomm.n3 p => DirOk p
  | Nomm.n4 p => DirOk p
  | Nomm.n5 p q => DirOk p && DirOk q
  | Nomm.n6 p q r => DirOk p && DirOk q && DirOk r
  | Nomm.n7 p q => DirOk p && DirOk q
  | Nomm.n10 a v q => (a != 0 && DirOk v) && DirOk q
  | _ => false

/-- What one direct call takes of the rest of the compiler. -/
def CallOk (env : CallEnv) (cod ctx : Noun) (E : GenRest → Prop) (msup : Option Nomm) (p q : Nomm) (b : Bell) :
    Prop :=
  CodePure cod env b ∧ env.cod b = some (env.pure b) ∧ env.ring b = Option.none ∧
    ∃ nb, env.need b = some nb ∧ ∀ x, E x → ∃ sur SOF, CallNounM msup ctx p q b nb sur x (A 0) SOF

/-- `CallNounM` at `mono` `A 0` with `+callee-need` and `+callee-sure` in
their read-only cases (`NeedRead`, `SureNoun`, `CompRunDirectS.lean`): what
is left is the call's `cole` entry `~`, `jets-hot`, and that the push of `sof`
returns (any value: `mono` `&` does not read it). -/
structure CallNounMR (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (x : GenRest) (SOF : Noun) : Prop where
  cole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)
  hot : ∃ jh, slot? 54 ctx = some jh
  need : NeedRead ctx x b nb
  sure : SureNoun env b x
  sof : ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
    nock (C (env.sure b).toNoun (C SV (C SN (C nb.toNoun (C (A 0) (C PV (crSubj (A 0) (crdN p q b) goalN regionN
      (unitNoun Nomm.toNoun msup) (compCore g x ctx)))))))) crDKc6 = some SOF

theorem callNounM_of_r (h7 : slot? 7 ctx = some compK) {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {b : Bell}
    {nb : NeedOrd} {x : GenRest} {SOF : Noun} (h : CallNounMR env msup ctx p q b nb x SOF) :
    CallNounM msup ctx p q b nb (env.sure b).toNoun x (A 0) SOF :=
  ⟨h.cole, h.hot, cne_read h7 b nb x h.cole h.hot h.need, csu_gate (comp_ctx_pill ctx h7).1 env b x h.sure, h.sof⟩

/-- `CallOk` from the code entry, no ring, `env.need b = some nb`, and
`CallNounMR` for every rest with `E`. -/
theorem callOk_of_r (h7 : slot? 7 ctx = some compK) {env : CallEnv} {cod : Noun} {E : GenRest → Prop}
    {msup : Option Nomm} {p q : Nomm} {b : Bell} (hcd : CodePure cod env b) (hc : env.cod b = some (env.pure b))
    (hri : env.ring b = Option.none) {nb : NeedOrd} (hnb : env.need b = some nb)
    (hE : ∀ x, E x → ∃ SOF, CallNounMR env msup ctx p q b nb x SOF) : CallOk env cod ctx E msup p q b :=
  ⟨hcd, hc, hri, nb, hnb, fun x hx => by
    obtain ⟨SOF, h⟩ := hE x hx
    exact ⟨_, SOF, callNounM_of_r h7 h⟩⟩

/-- **`CallOk` of every direct call**, each at the `msup` its run gets. -/
def DirCalls (env : CallEnv) (cod ctx : Noun) (E : GenRest → Prop) : Option Nomm → Nomm → Prop
  | ms, Nomm.cons p q => DirCalls env cod ctx E ms p ∧ DirCalls env cod ctx E ms q
  | ms, Nomm.n2 p q Option.none => DirCalls env cod ctx E ms p ∧ DirCalls env cod ctx E ms q
  | ms, Nomm.n2 p q (some (b, _)) =>
      CallOk env cod ctx E ms p q b ∧ DirCalls env cod ctx E ms p ∧ DirCalls env cod ctx E ms q
  | ms, Nomm.n3 p => DirCalls env cod ctx E ms p
  | ms, Nomm.n4 p => DirCalls env cod ctx E ms p
  | ms, Nomm.n5 p q => DirCalls env cod ctx E ms p ∧ DirCalls env cod ctx E ms q
  | ms, Nomm.n6 p q r => DirCalls env cod ctx E ms p ∧ DirCalls env cod ctx E ms q ∧ DirCalls env cod ctx E ms r
  | ms, Nomm.n7 p q => DirCalls env cod ctx E ms p ∧ DirCalls env cod ctx E (some p) q
  | ms, Nomm.n10 _ v q => DirCalls env cod ctx E ms v ∧ DirCalls env cod ctx E ms q
  | _, _ => True

theorem callCode_of_dir {env : CallEnv} {cod : Noun} {E : GenRest → Prop} :
    ∀ (n : Nomm), DirOk n = true → ∀ (ms : Option Nomm), DirCalls env cod ctx E ms n → CallCode cod env n
  | Nomm.cons p q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_dir p h.1 ms hd.1, callCode_of_dir q h.2 ms hd.2⟩
  | Nomm.n0 _, _, _, _ => trivial
  | Nomm.n1 _, _, _, _ => trivial
  | Nomm.n2 p q Option.none, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd; simp only [CallCode]
    exact ⟨trivial, callCode_of_dir p h.1 ms hd.1, callCode_of_dir q h.2 ms hd.2⟩
  | Nomm.n2 p q (some (b, Option.none)), h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd; simp only [CallCode]
    exact ⟨⟨hd.1.1, hd.1.2.1⟩, callCode_of_dir p h.1 ms hd.2.1, callCode_of_dir q h.2 ms hd.2.2⟩
  | Nomm.n2 _ _ (some (_, some _)), h, _, _ => by simp [DirOk] at h
  | Nomm.n3 p, h, ms, hd => by
    simp only [DirOk] at h; simp only [DirCalls] at hd; simp only [CallCode]; exact callCode_of_dir p h ms hd
  | Nomm.n4 p, h, ms, hd => by
    simp only [DirOk] at h; simp only [DirCalls] at hd; simp only [CallCode]; exact callCode_of_dir p h ms hd
  | Nomm.n5 p q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_dir p h.1 ms hd.1, callCode_of_dir q h.2 ms hd.2⟩
  | Nomm.n7 p q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_dir p h.1 ms hd.1, callCode_of_dir q h.2 (some p) hd.2⟩
  | Nomm.n10 a v q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_dir v h.1.2 ms hd.1, callCode_of_dir q h.2 ms hd.2⟩
  | Nomm.n6 p q r, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd; simp only [CallCode]
    exact ⟨callCode_of_dir p h.1.1 ms hd.1, callCode_of_dir q h.1.2 ms hd.2.1, callCode_of_dir r h.2 ms hd.2.2⟩
  | Nomm.n11s _ _ _, h, _, _ => by simp [DirOk] at h
  | Nomm.n11d _ _ _ _, h, _, _ => by simp [DirOk] at h
  | Nomm.n12 _ _, h, _, _ => by simp [DirOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _ => by simp [DirOk] at h

/-- `DirOk` has no `%10` at axis `0`: `Bake.NoAx0`, which `%6` asks of its
branches. -/
theorem noAx0_of_dir : ∀ (n : Nomm), DirOk n = true → Bake.NoAx0 n
  | Nomm.cons p q, h => by
    simp only [DirOk, Bool.and_eq_true] at h; exact ⟨noAx0_of_dir p h.1, noAx0_of_dir q h.2⟩
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n2 p q Option.none, h => by
    simp only [DirOk, Bool.and_eq_true] at h; exact ⟨noAx0_of_dir p h.1, noAx0_of_dir q h.2⟩
  | Nomm.n2 p q (some (_, Option.none)), h => by
    simp only [DirOk, Bool.and_eq_true] at h; exact ⟨noAx0_of_dir p h.1, noAx0_of_dir q h.2⟩
  | Nomm.n2 _ _ (some (_, some _)), h => by simp [DirOk] at h
  | Nomm.n3 p, h => by simp only [DirOk] at h; exact noAx0_of_dir p h
  | Nomm.n4 p, h => by simp only [DirOk] at h; exact noAx0_of_dir p h
  | Nomm.n5 p q, h => by
    simp only [DirOk, Bool.and_eq_true] at h; exact ⟨noAx0_of_dir p h.1, noAx0_of_dir q h.2⟩
  | Nomm.n6 p q r, h => by
    simp only [DirOk, Bool.and_eq_true] at h
    exact ⟨noAx0_of_dir p h.1.1, noAx0_of_dir q h.1.2, noAx0_of_dir r h.2⟩
  | Nomm.n7 p q, h => by
    simp only [DirOk, Bool.and_eq_true] at h; exact ⟨noAx0_of_dir p h.1, noAx0_of_dir q h.2⟩
  | Nomm.n10 a v q, h => by
    simp only [DirOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨h.1.1, noAx0_of_dir v h.1.2, noAx0_of_dir q h.2⟩
  | Nomm.n11s _ _ _, h => by simp [DirOk] at h
  | Nomm.n11d _ _ _ _, h => by simp [DirOk] at h
  | Nomm.n12 _ _, h => by simp [DirOk] at h
  | Nomm.mean _ _ _ _ _, h => by simp [DirOk] at h

/-- `ResFor` of a nomm with no direct call is `ResForR (runLCM env true msup)`. -/
theorem resR_of_res {env : CallEnv} {msup : Option Nomm} {n : Nomm} {region : List Nat} (hn : n.noDirect = true)
    (h : ResFor env msup n region) : ResForR (runLCM env true msup) n region := by
  intro goal g g' nex hi e
  rw [runLCM_true env hn msup] at e
  exact h goal g g' nex hi e

/-- **The run link at `mono` `&` on the class with direct calls**: every
nomm of `DirOk` whose direct calls meet `CallOk` is a `PartR` at `XM E msup`
(link, result, `+past`), every `msup` and region. -/
theorem comp_run_dir (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (E : GenRest → Prop) : ∀ (n : Nomm), DirOk n = true → ∀ (msup : Option Nomm) (region : List Nat),
      DirCalls env cod ctx E msup n → PartR env msup ctx (XM E msup) n region
  | Nomm.cons p q, h, msup, region, hd => by
    have hc := callCode_of_dir (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd
    have P := comp_run_dir h7 hcode env E p h.1 msup region hd.1
    have Q := comp_run_dir h7 hcode env E q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_consLR h7 hcode env msup p q P Q goal g hi, res_consR P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n0 ax, _, msup, region, _ =>
    ⟨fun goal g hi => crx_of_runLC rfl (crc_of_pure env rfl (comp_run_n0L h7 ax goal region g hi) msup),
      resR_of_res rfl (res_n0 env msup ax region), pastAt_nd h7 hcode env.cod trivial⟩
  | Nomm.n1 k, _, msup, region, _ =>
    ⟨fun goal g hi => crx_of_runLC rfl (crc_of_pure env rfl (comp_run_n1L h7 k goal region g hi) msup),
      resR_of_res rfl (res_n1 env msup k region), pastAt_nd h7 hcode env.cod trivial⟩
  | Nomm.n2 p q Option.none, h, msup, region, hd => by
    have hc := callCode_of_dir (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd
    have P := comp_run_dir h7 hcode env E p h.1 msup region hd.1
    have Q := comp_run_dir h7 hcode env E q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n2LR h7 hcode env msup p q P Q goal g hi, res_n2R P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n2 p q (some (b, Option.none)), h, msup, region, hd => by
    have hc := callCode_of_dir (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd
    obtain ⟨⟨hcd, -, hri, nb, hnb, hE⟩, hdp, hdq⟩ := hd
    have P := comp_run_dir h7 hcode env E p h.1 msup region hdp
    have Q := comp_run_dir h7 hcode env E q h.2 msup region hdq
    exact ⟨fun goal g hi => crx_iff_mm.2 (comp_run_n2_directMM h7 hcode env msup p q P.past (partLM_of_partR P)
        (partLM_of_partR Q) b hcd nb hE hri hnb goal g hi),
      res_n2_directMono P.res Q.res hri hnb, pastAt_code h7 hcode env hc⟩
  | Nomm.n2 _ _ (some (_, some _)), h, _, _, _ => by simp [DirOk] at h
  | Nomm.n3 p, h, msup, region, hd => by
    have hc := callCode_of_dir (ctx := ctx) _ h msup hd
    simp only [DirOk] at h; simp only [DirCalls] at hd
    have P := comp_run_dir h7 hcode env E p h msup region hd
    exact ⟨fun goal g hi => comp_run_n3LR h7 env msup p goal region g hi P.link, res_n3R P.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n4 p, h, msup, region, hd => by
    have hc := callCode_of_dir (ctx := ctx) _ h msup hd
    simp only [DirOk] at h; simp only [DirCalls] at hd
    have P := comp_run_dir h7 hcode env E p h msup region hd
    exact ⟨fun goal g hi => comp_run_n4LR h7 env msup p goal region g hi P.link, res_n4R P.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n5 p q, h, msup, region, hd => by
    have hc := callCode_of_dir (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd
    have P := comp_run_dir h7 hcode env E p h.1 msup region hd.1
    have Q := comp_run_dir h7 hcode env E q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n5LR h7 hcode env msup p q P Q goal g hi, res_n5R P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n7 p q, h, msup, region, hd => by
    have hc := callCode_of_dir (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd
    have P := comp_run_dir h7 hcode env E p h.1 msup region hd.1
    have Q := comp_run_dir h7 hcode env E q h.2 (some p) region hd.2
    exact ⟨fun goal g hi => comp_run_n7CR env msup p q goal region g (Q.link goal g hi)
        (fun x mono sup hX => ⟨hX.1, hX.2.1, rfl⟩)
        (fun nex g1 e => P.link nex.goal g1 (Q.res goal g g1 nex hi e).2.2.1),
      res_n7R Q.res P.res, pastAt_code h7 hcode env hc⟩
  | Nomm.n10 a v q, h, msup, region, hd => by
    have hc := callCode_of_dir (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; simp only [DirCalls] at hd
    have V := comp_run_dir h7 hcode env E v h.1.2 msup region hd.1
    have Q := comp_run_dir h7 hcode env E q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n10LR h7 hcode env msup a h.1.1 v q V Q goal g hi, res_n10R h.1.1 V.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n6 p q r, h, msup, region, hd => by
    have hc := callCode_of_dir (ctx := ctx) _ h msup hd
    have ha := noAx0_of_dir _ h
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCalls] at hd; simp only [Bake.NoAx0] at ha
    have hc' := hc
    simp only [CallCode] at hc'
    have P := comp_run_dir h7 hcode env E p h.1.1 msup region hd.1
    have Q := fun rg => comp_run_dir h7 hcode env E q h.1.2 msup rg hd.2.1
    have R := fun rg => comp_run_dir h7 hcode env E r h.2 msup rg hd.2.2
    exact ⟨fun goal g hi => comp_run_n6_allR h7 hcode env msup p q r region (sixR_of h7 hcode P hc'.1)
        (sixR_of h7 hcode (Q region) hc'.2.1) (sixR_of h7 hcode (R region) hc'.2.2)
        (fun rid => sixR_of h7 hcode (Q (rid :: region)) hc'.2.1)
        (fun rid => sixR_of h7 hcode (R (rid :: region)) hc'.2.2) ha.2.1 ha.2.2 goal g hi,
      res_n6_allR P.res (Q region).res (R region).res (fun rid => (Q (rid :: region)).res)
        (fun rid => (R (rid :: region)).res) ha.2.1 ha.2.2,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n11s _ _ _, h, _, _, _ => by simp [DirOk] at h
  | Nomm.n11d _ _ _ _, h, _, _, _ => by simp [DirOk] at h
  | Nomm.n12 _ _, h, _, _, _ => by simp [DirOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _ => by simp [DirOk] at h

/-- **The run link at `mono` `&` on the class with direct calls**, as
`CompRunAtMM`: on every goal with `GInv`, against `runLCM env true msup`. -/
theorem comp_run_dirMM (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (E : GenRest → Prop) (n : Nomm) (hn : DirOk n = true) (msup : Option Nomm) (region : List Nat)
    (hd : DirCalls env cod ctx E msup n) (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtMM env msup ctx E n goal region g :=
  (partLM_of_partR (comp_run_dir h7 hcode env E n hn msup region hd)).link goal g hi

/-- What a run of the class returns. -/
theorem res_dir (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (E : GenRest → Prop) (n : Nomm) (hn : DirOk n = true) (msup : Option Nomm) (region : List Nat)
    (hd : DirCalls env cod ctx E msup n) : ResForR (runLCM env true msup) n region :=
  (comp_run_dir h7 hcode env E n hn msup region hd).res

/-- **An example**: a cons whose head is a direct call, `[[2 [0 1] [1 k] [~ b
~]] [0 1]]`, on every goal with `GInv`, given the call's `CallOk`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (E : GenRest → Prop) (msup : Option Nomm) (k : Noun) (b : Bell)
    (hb : CallOk env cod ctx E msup (Nomm.n0 1) (Nomm.n1 k) b) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtMM env msup ctx E (Nomm.cons (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none))) (Nomm.n0 1))
      goal region g :=
  comp_run_dirMM h7 hcode env E _ rfl msup region
    (by simp only [DirCalls]; exact ⟨⟨hb, trivial, trivial⟩, trivial⟩) goal g hi

/-- **An example**: two direct calls in a row, `[7 [2 [0 1] [1 k] [~ b ~]] [2
[0 1] [1 k'] [~ b' ~]]]` (the second runs on the product of the first), the
second's `CallOk` at `msup` `some` of the first call. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (E : GenRest → Prop) (msup : Option Nomm) (k k' : Noun) (b b' : Bell)
    (hb : CallOk env cod ctx E msup (Nomm.n0 1) (Nomm.n1 k) b)
    (hb' : CallOk env cod ctx E (some (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none)))) (Nomm.n0 1)
      (Nomm.n1 k') b')
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtMM env msup ctx E
      (Nomm.n7 (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none)))
        (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k') (some (b', Option.none)))) goal region g :=
  comp_run_dirMM h7 hcode env E _ rfl msup region
    (by simp only [DirCalls]; exact ⟨⟨hb, trivial, trivial⟩, ⟨hb', trivial, trivial⟩⟩) goal g hi

/-- **An example**: a direct call whose subject is a direct call, `[2 [2 [0
1] [1 k] [~ b ~]] [1 k'] [~ b' ~]]` (`+past` over the subject reads the code
entry of `b`), on every goal with `GInv`, given the two calls' `CallOk`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (E : GenRest → Prop) (msup : Option Nomm) (k k' : Noun) (b b' : Bell)
    (hb : CallOk env cod ctx E msup (Nomm.n0 1) (Nomm.n1 k) b)
    (hb' : CallOk env cod ctx E msup (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none))) (Nomm.n1 k') b')
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtMM env msup ctx E
      (Nomm.n2 (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none))) (Nomm.n1 k') (some (b', Option.none)))
      goal region g :=
  comp_run_dirMM h7 hcode env E _ rfl msup region
    (by simp only [DirCalls]; exact ⟨hb', ⟨hb, trivial, trivial⟩, trivial⟩) goal g hi

/-- **An example**: a direct call in a branch of a `%6`, `[6 [0 2] [2 [0 1]
[1 k] [~ b ~]] [1 0]]`, on every goal with `GInv`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (E : GenRest → Prop) (msup : Option Nomm) (k : Noun) (b : Bell)
    (hb : CallOk env cod ctx E msup (Nomm.n0 1) (Nomm.n1 k) b) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtMM env msup ctx E
      (Nomm.n6 (Nomm.n0 2) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none))) (Nomm.n1 (A 0)))
      goal region g :=
  comp_run_dirMM h7 hcode env E _ rfl msup region
    (by simp only [DirCalls]; exact ⟨trivial, ⟨hb, trivial, trivial⟩, trivial⟩) goal g hi

/-- **An example**: a direct call as the test of a `%6` (its run gets the
`%pick` goal, or the `%next` goal of the fork's condition register), `[6 [2
[0 1] [1 k] [~ b ~]] [1 0] [1 1]]`, on every goal with `GInv`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (E : GenRest → Prop) (msup : Option Nomm) (k : Noun) (b : Bell)
    (hb : CallOk env cod ctx E msup (Nomm.n0 1) (Nomm.n1 k) b) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtMM env msup ctx E
      (Nomm.n6 (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none))) (Nomm.n1 (A 0)) (Nomm.n1 (A 1)))
      goal region g :=
  comp_run_dirMM h7 hcode env E _ rfl msup region
    (by simp only [DirCalls]; exact ⟨⟨hb, trivial, trivial⟩, trivial, trivial⟩) goal g hi

end Compiler
end Formalization
