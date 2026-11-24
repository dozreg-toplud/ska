import lemmas.Compiler.FolLoopMono
import lemmas.Pill.Arm.Ska_analyze

/-!
# The loop `resolve` of `fol-loop`

The loop `resolve` (`fol_loop.resolve`) of the trap `nock-2-direct-non-inlined`
against one turn of a model, with its call to itself after a `%he` step and
`+analyze` as parameters (`resolve_step`).

The loop's subject is `[fol_loop.resolve [id-there D]]` with `D` the subject
of the trap (`dirSubj`): `id-there` at `6`, `fol-new` at `30`, `s` at `126`
(so `sock.prod.s` at `1012`) and the trap's subject `folSubj` at `127`, with
`gen` at `126` of it.  A `%he` step edits only `id-there` and kicks the loop
again (`[9 2 10 [6 0 11] 0 15]`), so `D` (and with it `fol-new`,
`sock.prod.s` and `gen`) is the same on every turn.

The loop reads nothing else of `D`: of `folSubj` it reads `gen` and the rest,
of `s` only `sock.prod.s`.  So `ResIs`, which quantifies over the whole
`dirSubj`, holds of any `res` that is a function of the identity and `gen`.

Found while linking: in the `%rec` branch the Hoon patches the product of the
function in progress with `sock.prod.s` (`(patch-prod [prod map]:d sock.prod.s)`,
the sample `[... 0 32756]` of the gate at `[9 22 0 0x7ffffff]`), the subject
sock the loop began with, not with the current `id-there`; `Ana.resolveStep`
patches with `idT.1`.  The two differ after a `%he` step.  `resolveStepH`
is `Ana.resolveStep` with `orig.1` there, which is what the pill computes.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- One turn of the loop `resolve` as the Hoon has it: `Ana.resolveStep`, except
that the `%rec` branch patches the product with the original subject sock
`orig.1`. -/
def resolveStepH (env : Env R) (resolve : ResGo M R) (analyze : AnaGo M R) (orig idT : Ident)
    (gen : GenS M R) : Option ((Ident × FDatum M) × GenS M R) :=
  match Treap.get gen.st.g idT with
  | some d =>
    match Treap.get gen.st.order idT with
    | none => some ((idT, d), gen)
    | some o => some ((idT, d), { gen with low := min gen.low o, back := true })
  | none =>
  match gitMi gen.st.done orig.2 orig.1 with
  | none => none
  | some (some m) => some (m, gen)
  | some none =>
  match recursiveCall env.he env.threshold idT gen.st.stk (gCore gen.st.g) with
  | none => none
  | some (some (false, i)) => resolve i gen
  | some (some (true, i)) =>
    let d := gitG gen.st.g i
    let m := patchProd d.prod d.map orig.1
    (Treap.get gen.st.order i).map fun o =>
      ((i, { d with prod := m.sock, map := m.src }), { gen with low := min gen.low o, back := true })
  | some none =>
    (analyze idT gen.st).map fun r =>
      ((idT, gitG r.2.g idT), { gen with st := r.2, low := min gen.low r.1 })

/-- On a turn whose current identity is the original one, the two steps agree. -/
theorem resolveStepH_self (env : Env R) (resolve : ResGo M R) (analyze : AnaGo M R) (i : Ident)
    (gen : GenS M R) :
    resolveStepH env resolve analyze i i gen = Ana.resolveStep env resolve analyze i i gen := rfl

/-- The subject of the loop `resolve` on the identity `idT`. -/
noncomputable def resSubj (regsNoun : R → Noun) (rest fol : Noun) (sub : Anno) (seat mk : Option Noun)
    (bc df : Bool) (gen : GenS FinMap R) (fa fb : Noun) (f s : FolOut) (idT : Ident) : Noun :=
  C fol_loop.resolve (C (identNoun idT)
    (dirSubj regsNoun rest fol sub seat mk bc df gen (C fa fb) f.toNoun s.toNoun))

/-- The gate `+analyze` in the context `K`, slammed by `c`, computes `an`, as
`[low st]`. -/
def AnaIsW (c : Noun → Noun → Option Noun) (regsNoun : R → Noun) (K : Noun) (an : AnaGo FinMap R) :
    Prop :=
  ∀ id st, c (C ska_analyze.battery (C (C (identNoun id) (st.toNoun regsNoun)) K)) ska_analyze.battery
    = (an id st).map fun r => C (A r.1) (r.2.toNoun regsNoun)

/-- The gate `+analyze` in the context `K` computes `an`, as `[low st]`. -/
abbrev AnaIs (regsNoun : R → Noun) (K : Noun) (an : AnaGo FinMap R) : Prop :=
  AnaIsW nock regsNoun K an

theorem rest_layer1 {rest : Noun} (h : slot? 511 rest = some ana) :
    slot? 4194303 rest = some layer1 := by
  have h' : slot? 511 rest = slot? 1 ana := by rw [h]; rfl
  have := slot_spine (by omega) (by omega) h' 13
  simp only [show 2 ^ 13 * (511 + 1) - 1 = 4194303 from rfl,
    show 2 ^ 13 * (1 + 1) - 1 = 16383 from rfl] at this
  rw [this]; exact ana_layer1

/-- The sample of the gate `+analyze` before it is slammed. -/
abbrev ska_analyze.bunt : Noun :=
  (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))))))))))

@[nock_exec] theorem ska_analyze_arm (c : Noun) :
    nock c ska_analyze.arm = some (C ska_analyze.battery (C ska_analyze.bunt c)) := by
  nock_open ska_analyze.arm; simp only [nock_exec]

/-- One turn of the loop `resolve`: given its call to itself on a `%he`
step (`rl`, on the same `D`, needed only at the identity that
`+recursive-call` gives) and `+analyze` (`an`, in the context `K` at axis `31`
of the rest), the loop computes `resolveStepH` with `orig` the call's own site
sock and formula. -/
theorem resolve_stepW (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (hhe : env.he = heSock)
    (hth : env.threshold = 32) (rest K : Noun) (hana : slot? 511 rest = some ana)
    (hK : slot? 31 rest = some K) (hKa : slot? 92 K = some ska_analyze.arm)
    (an : AnaGo FinMap R) (han : AnaIsW c regsNoun K an)
    (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R)
    (fa fb : Noun) (f s : FolOut) (rl : ResGo FinMap R)
    (idT : Ident)
    (hrl : ∀ i, Treap.get gen.st.g idT = none → gitMi gen.st.done (C fa fb) s.prod.sock = some none →
      recursiveCall heSock 32 idT gen.st.stk (gCore gen.st.g) = some (some (false, i)) →
      c (resSubj regsNoun rest fol sub seat mk bc df gen fa fb f s i) fol_loop.resolve
        = (rl i gen).map (resOutNoun regsNoun)) :
    nockW c (resSubj regsNoun rest fol sub seat mk bc df gen fa fb f s idT) fol_loop.resolve
      = (resolveStepH env rl an (s.prod.sock, C fa fb) idT gen).map (resOutNoun regsNoun) := by
  have hl1 := rest_layer1 hana
  have hl2 := rest_layer2 hana
  have hmin : ∀ a b : Nat, nock (C min.battery (C (C (A a) (A b)) layer1)) min.battery
      = some (A (min a b)) := min_gate layer1 arith_layer1.2.2.2.1
  unfold resSubj dirSubj folSubj at hrl ⊢
  obtain ⟨ms, ⟨ss, srcs⟩, fs⟩ := s
  obtain ⟨want, indi, seek, callees, area, low, back, st⟩ := gen
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  simp only [FolOut.toNoun, Anno.toNoun, GenS.toNoun, SkaState.toNoun] at hrl ⊢
  generalize flag df = n1 at hrl ⊢
  generalize flag bc = n2 at hrl ⊢
  generalize unitNoun id mk = n3 at hrl ⊢
  generalize unitNoun id seat = n4 at hrl ⊢
  generalize sub.toNoun = n6 at hrl ⊢
  generalize f.toNoun = nf at hrl ⊢
  generalize ms.toNoun = nms at hrl ⊢
  generalize flag fs = nfs at hrl ⊢
  generalize hwant : want.toNoun = nwant at hrl ⊢
  generalize hindi : indi.toNoun = nindi at hrl ⊢
  generalize hseek : seek.toNoun = nseek at hrl ⊢
  generalize hcal : Treap.setNoun callees = ncal at hrl ⊢
  generalize harea : unitNoun (fun x => x) area = narea at hrl ⊢
  generalize hback : flag back = nback at hrl ⊢
  generalize hnext : A next = nnext at hrl ⊢
  generalize hmoved : Treap.setNoun moved = nmoved at hrl ⊢
  generalize htick : A tick = ntick at hrl ⊢
  generalize hticks : Treap.toNoun (fun p => C (A p.1) (A p.2)) ticks = nticks at hrl ⊢
  generalize hregs : regsNoun regs = nregs at hrl ⊢
  generalize hstats : stats.toNoun = nstats at hrl ⊢
  have hg := FinMap.getF_toNoun FDatum.toNoun g idT
  have ho := FinMap.getF_toNoun A order idT
  have hsg : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hgg : nock (C by.get.battery (C (identNoun idT) (C by.battery (C (Treap.toNoun FDatum.toNoun g)
      layer2)))) by.get.battery = some (unitNoun FDatum.toNoun (Treap.get g idT)) :=
    get_gate layer2 hsg _ _ _ hg
  have hog : nock (C by.get.battery (C (identNoun idT) (C by.battery (C (Treap.toNoun A order)
      layer2)))) by.get.battery = some (unitNoun A (Treap.get order idT)) :=
    get_gate layer2 hsg _ _ _ ho
  have hgit := mi_git_pill done (C fa fb) ss
  have hrc := recursive_call_pill idT stk g
  have hu0 : ∀ {α : Type} (e : α → Noun), unitNoun e none = A 0 := fun _ => rfl
  have hus : ∀ {α : Type} (e : α → Noun) (x : α), unitNoun e (some x) = C (A 0) (e x) := fun _ _ => rfl
  nockW_open fol_loop.resolve
  cases eg : Treap.get g idT with
  | some d =>
    rw [eg, hus] at hgg
    cases eo : Treap.get order idT with
    | none =>
      rw [eo, hu0] at hog
      simp (disch := ffar_disch) [nock_exec, hcf, hl2, by_arm, by.get.arm_at, hgg, hog, resolveStepH, eg, eo, resOutNoun, entryNoun]
      subst hwant hindi hseek hcal harea hback hnext hmoved htick hticks hregs hstats
      simp [GenS.toNoun, SkaState.toNoun]
    | some o =>
      rw [eo, hus] at hog
      simp (disch := ffar_disch) [nock_exec, hcf, hl1, hl2, by_arm, by.get.arm_at, hgg, hog, resolveStepH, eg, eo, resOutNoun,
        entryNoun, min.arm_at, min_arm, hmin]
      subst hwant hindi hseek hcal harea hback hnext hmoved htick hticks hregs hstats
      simp [GenS.toNoun, SkaState.toNoun, flag]
  | none =>
    rw [eg, hu0] at hgg
    cases em : gitMi done (C fa fb) ss with
    | none =>
      rw [em] at hgit
      simp (disch := ffar_disch) [nock_exec, hcf, hl2, by_arm, by.get.arm_at, hgg, resolveStepH, eg, em, hana, mi.arm_at, mi_arm,
        mi.git.arm_at, mi_git_arm, hgit]
    | some mm =>
    cases mm with
    | some m =>
      rw [em] at hgit
      simp (disch := ffar_disch) [nock_exec, hcf, hl2, by_arm, by.get.arm_at, hgg, resolveStepH, eg, em, hana, mi.arm_at, mi_arm,
        mi.git.arm_at, mi_git_arm, hgit, resOutNoun, hus]
      subst hwant hindi hseek hcal harea hback hnext hmoved htick hticks hregs hstats
      simp [GenS.toNoun, SkaState.toNoun]
    | none =>
      rw [em] at hgit
      simp only [Option.map_some, hu0] at hgit
      cases er : recursiveCall heSock 32 idT stk (gCore g) with
      | none =>
        rw [er] at hrc
        simp (disch := ffar_disch) [nock_exec, hcf, hl2, by_arm, by.get.arm_at, hgg, resolveStepH, eg, em, hana, mi.arm_at, mi_arm,
          mi.git.arm_at, mi_git_arm, hgit, recursive_call.arm_at, recursive_call_arm, hrc, hhe, hth, er]
      | some rr =>
      cases rr with
      | none =>
        rw [er] at hrc
        simp only [Option.map_some, hu0] at hrc
        have ha := han idT ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩
        simp only [SkaState.toNoun] at ha
        rw [hnext, hmoved, htick, hticks, hregs, hstats] at ha
        cases ea : an idT ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ with
        | none =>
          rw [ea] at ha
          simp (disch := ffar_disch) [nock_exec, hcf, hl2, by_arm, by.get.arm_at, hgg, resolveStepH, eg, em, hana, mi.arm_at, mi_arm,
            mi.git.arm_at, mi_git_arm, hgit, recursive_call.arm_at, recursive_call_arm, hrc, hhe, hth, er,
            hK, hKa, ska_analyze_arm, ha, ea]
        | some r =>
          rw [ea] at ha
          obtain ⟨lowT, st'⟩ := r
          have hgg' := git_g_pill st'.g idT
          simp (disch := ffar_disch) [nock_exec, hcf, hl1, hl2, by_arm, by.get.arm_at, hgg, resolveStepH, eg, em, hana, mi.arm_at,
            mi_arm, mi.git.arm_at, mi_git_arm, hgit, recursive_call.arm_at, recursive_call_arm, hrc, hhe,
            hth, er, hK, hKa, ska_analyze_arm, ha, ea, SkaState.toNoun, git_g.arm_at, git_g_arm, hgg',
            min.arm_at, min_arm, hmin, resOutNoun, entryNoun]
          subst hwant hindi hseek hcal harea hback hnext hmoved htick hticks hregs hstats
          simp [GenS.toNoun, SkaState.toNoun]
      | some p =>
        obtain ⟨b, i⟩ := p
        rw [er] at hrc
        simp only [Option.map_some, hus] at hrc
        cases b with
        | false =>
          have h1 := hrl i eg em er
          simp (disch := ffar_disch) [nock_exec, hcf, hl2, by_arm, by.get.arm_at, hgg, resolveStepH, eg, em, hana, mi.arm_at, mi_arm,
            mi.git.arm_at, mi_git_arm, hgit, recursive_call.arm_at, recursive_call_arm, hrc, hhe, hth, er,
            rcNoun, h1]
        | true =>
          have hgi := git_g_pill g i
          have hoi : getF mugF (identNoun i) (Treap.toNoun A order)
              = some (unitNoun A (Treap.get order i)) := FinMap.getF_toNoun A order i
          have hpp := patch_prod_pill (gitG g i).prod (gitG g i).map ss
          have hnd : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 := ⟨need.arm_at, hsg⟩
          generalize hd : gitG g i = d at hgi hpp ⊢
          cases eo : Treap.get order i with
          | none =>
            rw [eo, hu0] at hoi
            have hgot := got_gate_nil layer2 hnd (identNoun i) (Treap.toNoun A order) hoi
            simp (disch := ffar_disch) [nock_exec, hcf, hl1, hl2, by_arm, by.get.arm_at, hgg, resolveStepH, eg, em, hana, mi.arm_at,
              mi_arm, mi.git.arm_at, mi_git_arm, hgit, recursive_call.arm_at, recursive_call_arm, hrc, hhe,
              hth, er, rcNoun, git_g.arm_at, git_g_arm, hgi, patch_prod.arm_at, patch_prod_arm, hpp,
              FDatum.toNoun, by.got.arm_at, hgot, hd, eo]
          | some o =>
            rw [eo, hus] at hoi
            have hgot := got_gate layer2 hnd (identNoun i) (Treap.toNoun A order) (A o) hoi
            simp (disch := ffar_disch) [nock_exec, hcf, hl1, hl2, by_arm, by.get.arm_at, hgg, resolveStepH, eg, em, hana, mi.arm_at,
              mi_arm, mi.git.arm_at, mi_git_arm, hgit, recursive_call.arm_at, recursive_call_arm, hrc, hhe,
              hth, er, rcNoun, git_g.arm_at, git_g_arm, hgi, patch_prod.arm_at, patch_prod_arm, hpp,
              FDatum.toNoun, by.got.arm_at, hgot, hd, min.arm_at, min_arm, hmin, resOutNoun, entryNoun, eo]
            subst hwant hindi hseek hcal harea hback hnext hmoved htick hticks hregs hstats
            simp [GenS.toNoun, SkaState.toNoun, flag]

/-- One turn of the loop `resolve` under `nock` (`resolve_stepW` with `c := nock`). -/
theorem resolve_step (regsNoun : R → Noun) (env : Env R) (hhe : env.he = heSock)
    (hth : env.threshold = 32) (rest K : Noun) (hana : slot? 511 rest = some ana)
    (hK : slot? 31 rest = some K) (hKa : slot? 92 K = some ska_analyze.arm)
    (an : AnaGo FinMap R) (han : AnaIs regsNoun K an)
    (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R)
    (fa fb : Noun) (f s : FolOut) (rl : ResGo FinMap R)
    (idT : Ident)
    (hrl : ∀ i, Treap.get gen.st.g idT = none → gitMi gen.st.done (C fa fb) s.prod.sock = some none →
      recursiveCall heSock 32 idT gen.st.stk (gCore gen.st.g) = some (some (false, i)) →
      nock (resSubj regsNoun rest fol sub seat mk bc df gen fa fb f s i) fol_loop.resolve
        = (rl i gen).map (resOutNoun regsNoun)) :
    nock (resSubj regsNoun rest fol sub seat mk bc df gen fa fb f s idT) fol_loop.resolve
      = (resolveStepH env rl an (s.prod.sock, C fa fb) idT gen).map (resOutNoun regsNoun) := by
  rw [nock_eq_nockW]
  exact resolve_stepW nock (fun _ _ _ => rfl) regsNoun env hhe hth rest K hana hK hKa an han fol sub seat
    mk bc df gen fa fb f s rl idT hrl

/-- The loop `resolve` as the Hoon has it, fuelled, with `+analyze` a fixed
function `an` (the pill's gate). -/
def resolveH (env : Env R) (an : AnaGo M R) : Nat → Ident → ResGo M R
  | 0 => fun _ _ _ => none
  | n + 1 => fun orig => resolveStepH env (resolveH env an n orig) an orig

/-- What the loop `resolveH` returns at any fuel, the pill's loop returns, on
every identity, given `+analyze` (`AnaIs`).  With `idT = orig` this is the
loop as the trap enters it. -/
theorem resolve_le (regsNoun : R → Noun) (env : Env R) (hhe : env.he = heSock)
    (hth : env.threshold = 32) (rest K : Noun) (hana : slot? 511 rest = some ana)
    (hK : slot? 31 rest = some K) (hKa : slot? 92 K = some ska_analyze.arm)
    (an : AnaGo FinMap R) (han : AnaIs regsNoun K an)
    (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R)
    (fa fb : Noun) (f s : FolOut) :
    ∀ n idT r, resolveH env an n (s.prod.sock, C fa fb) idT gen = some r →
      nock (resSubj regsNoun rest fol sub seat mk bc df gen fa fb f s idT) fol_loop.resolve
        = some (resOutNoun regsNoun r) := by
  intro n
  induction n with
  | zero => intro _ _ h; simp [resolveH] at h
  | succ n ih =>
    intro idT r h
    have hst := resolve_step regsNoun env hhe hth rest K hana hK hKa an han fol sub seat mk bc df gen
      fa fb f s (resolveH env an n (s.prod.sock, C fa fb)) idT
    simp only [resolveH] at h
    by_cases hp : ∃ i, Treap.get gen.st.g idT = none ∧ gitMi gen.st.done (C fa fb) s.prod.sock = some none ∧
        recursiveCall heSock 32 idT gen.st.stk (gCore gen.st.g) = some (some (false, i))
    · obtain ⟨i, hg, hm, hi⟩ := hp
      -- a `%he` turn: the model's result is the loop's result at `i`
      have hr : resolveH env an n (s.prod.sock, C fa fb) i gen = some r := by
        unfold resolveStepH at h
        simp only [hg, hm, hhe, hth, hi] at h
        exact h
      rw [hst (fun j _ _ hj => by
        rw [hi] at hj; cases hj; rw [hr]; exact ih i r hr), h]
      rfl
    · rw [hst (fun j hg hm hj => absurd ⟨j, hg, hm, hj⟩ hp), h]
      rfl

/-- `ResIs` in one direction: what `res` returns, the pill's loop returns. -/
def ResLe (regsNoun : R → Noun) (rest : Noun) (res : ResGo FinMap R) : Prop :=
  ∀ (s f : FolOut) (fa fb fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) r, res (s.prod.sock, C fa fb) gen = some r →
    nock (C fol_loop.resolve (C (identNoun (s.prod.sock, C fa fb))
        (dirSubj regsNoun rest fol sub seat mk bc df gen (C fa fb) f.toNoun s.toNoun)))
        fol_loop.resolve
      = some (resOutNoun regsNoun r)

/-- The loop begun at the call's own identity, at any fuel, is below the
pill's loop entered from the trap. -/
theorem resLe_resolveH (regsNoun : R → Noun) (env : Env R) (hhe : env.he = heSock)
    (hth : env.threshold = 32) (rest K : Noun) (hana : slot? 511 rest = some ana)
    (hK : slot? 31 rest = some K) (hKa : slot? 92 K = some ska_analyze.arm)
    (an : AnaGo FinMap R) (han : AnaIs regsNoun K an) (n : Nat) :
    ResLe regsNoun rest (fun i gen => resolveH env an n i i gen) :=
  fun s f fa fb fol sub seat mk bc df gen r h =>
    resolve_le regsNoun env hhe hth rest K hana hK hKa an han fol sub seat mk bc df gen fa fb f s n
      (s.prod.sock, C fa fb) r h

end Compiler
end Formalization
