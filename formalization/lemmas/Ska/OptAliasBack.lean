import lemmas.Ska.OptAliasFwd

/-!
# The simulation of `+alias`, backward

The normal form (`ANorm`, `AliasN`): `AliasI` where the code before stands at
a pending pass, at an op the walk keeps (and no dead fill), at the end of a
live block, or at the end of a dead block.  **`alias_norm`**: the code before
reaches the normal form by running the ops the walk drops (`alive_drop_exec`)
and the `%imm` ops of the dead mode.  **`alias_bwd_step`**: out of the normal
form, a step of the code after is matched by a step of the code before (the
pass before goes on by `ArgsOK` and the check of `PassOK`, `apass_some`; a
kept op before runs as the op after, `XRel`; the end before takes a jump when
the end after does, `afn_jump_back`).  **`alias_bwd`**: on paths.  At the
normal form, an end after is an end before (`alias_bwd_end`), a real read
after reads a value (`alias_reads`, through `aop_rename`: a kept op reads the
renamed registers of the op before), an op that `+get-reg-safe-assignment`
names goes on (`alias_local`), and a pending argument after is present
(`alias_args`).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

set_option linter.unusedSectionVars false

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-! ## The ops the walk keeps -/

/-- An op with the registers it reads renamed by `f`. -/
def renameP (f : Nat → Nat) : Pole → Pole
  | Pole.imm n d => Pole.imm n d
  | Pole.mov s d => Pole.mov (f s) d
  | Pole.inc s d => Pole.inc (f s) d
  | Pole.con h t d => Pole.con (f h) (f t) d
  | Pole.hed s d => Pole.hed (f s) d
  | Pole.tal s d => Pole.tal (f s) d
  | Pole.cel p => Pole.cel (f p)
  | Pole.lob p => Pole.lob (f p)
  | Pole.equ l r => Pole.equ (f l) (f r)
  | Pole.hsp n g => Pole.hsp n g
  | Pole.hse n g => Pole.hse n g
  | Pole.hdp n p g => Pole.hdp n (f p) g
  | Pole.hde n p g => Pole.hde n (f p) g
  | Pole.hmp a v g => Pole.hmp a (v.map f) g
  | Pole.hme a v g => Pole.hme a (v.map f) g
  | Pole.hcp n g => Pole.hcp n g
  | Pole.hce n g => Pole.hce n g
  | Pole.spy e p d => Pole.spy (f e) (f p) d
  | Pole.nok u g d => Pole.nok (f u) (f g) d
  | Pole.cal a v d => Pole.cal a (v.map f) d
  | Pole.caf a v d n => Pole.caf a (v.map f) d n
  | Pole.cam a v d k => Pole.cam a (v.map f) d k
  | Pole.csl a s d => Pole.csl a (f s) d
  | Pole.csf a s d n => Pole.csf a (f s) d n
  | Pole.csm a s d k => Pole.csm a (f s) d k

/-- **An op the walk keeps is the op before with its reads renamed by
`old`.** -/
theorem aop_rename {pick : List Nat → Nat} {st st2 : ABody} {op op' : Pole}
    (h : aliasOp pick st op = some (some op', st2)) : op' = renameP st.old op := by
  cases op with
  | imm n d =>
    simp only [aliasOp] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | mov s d => simp [aliasOp] at h
  | inc s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | con h0 t0 d =>
    simp only [aliasOp] at h
    obtain ⟨hi, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ti, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨l1, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l2, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | hed s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | tal s d =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | cel p =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | lob p =>
    simp only [aliasOp] at h
    obtain ⟨ai, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · obtain ⟨loc, -, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq, Option.some.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | equ l r =>
    simp only [aliasOp] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | hsp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | hse => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | hdp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | hde => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | hmp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | hme => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | hcp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | hce => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | spy => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | nok => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | cal => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | caf => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | cam => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | csl => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | csf => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl
  | csm => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; rfl

theorem poleReads_rename (gul : Noun) (f : Nat → Nat) (op : Pole) :
    Path.poleReads gul (renameP f op) = (Path.poleReads gul op).map f := by
  cases op <;> simp only [renameP, Path.poleReads, List.map_cons, List.map_nil]
  · split <;> rfl
  · split <;> rfl

theorem safeAssign_rename (f : Nat → Nat) (op : Pole) : safeAssign (renameP f op) = safeAssign op := by
  cases op <;> rfl

/-- A real read of an op is a read of `aliasReads`. -/
theorem poleReads_alias {gul : Noun} {op : Pole} {y : Nat} (h : y ∈ Path.poleReads gul op) : y ∈ aliasReads op := by
  cases op with
  | inc s d => exact akx_reads_dst (l := [s]) rfl rfl h
  | con h0 t0 d => exact akx_reads_dst (l := [h0, t0]) rfl rfl h
  | hed s d => exact akx_reads_dst (l := [s]) rfl rfl h
  | tal s d => exact akx_reads_dst (l := [s]) rfl rfl h
  | cel p => exact akx_reads_none rfl h
  | lob p => exact akx_reads_none rfl h
  | equ l r => exact akx_reads_none rfl h
  | hdp n p f =>
    simp only [Path.poleReads] at h
    split at h
    · exact akx_reads_none rfl h
    · cases h
  | hmp a v f => exact akx_reads_none rfl h
  | spy e p d =>
    simp only [Path.poleReads] at h
    split at h
    · cases h
    · exact akx_reads_dst (l := [e, p]) rfl rfl h
  | nok u f d => exact akx_reads_dst (l := [u, f]) rfl rfl h
  | cal a v d => exact akx_reads_call rfl rfl h
  | caf a v d n => exact akx_reads_call rfl rfl h
  | cam a v d k => exact akx_reads_call rfl rfl h
  | csl a s d => exact akx_reads_dst (l := [s]) rfl rfl h
  | csf a s d n => exact akx_reads_dst (l := [s]) rfl rfl h
  | csm a s d k => exact akx_reads_dst (l := [s]) rfl rfl h
  | _ => simp [Path.poleReads] at h

/-! ## The end after jumps only where the end before jumps -/

/-- **When the end after takes a jump, the end before takes one**, on a file
where the facts at the end hold, the reads before hold values and read
through `old` what they hold. -/
theorem afn_jump_back {old : Nat → Nat} {loc : AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat} {fin : Termin}
    {r : Termin × (Nat → List Nat) × Bool} {R : Nat → Option Noun} {j' : Jmp}
    (h : aliasFin old loc rev f o fin = some r) (hf : FactsOK R loc)
    (hold : ∀ x ∈ Path.finReads fin, R (old x) = R x) (hnl : ∀ n s z o', fin ≠ Termin.lti n s z o')
    (hval : ∀ x ∈ Path.finReads fin, (R x).isSome) (ht : takenR R r.1 = some j') :
    ∃ j, takenR R fin = some j := by
  cases fin with
  | clq s z o' =>
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hval s (by simp [Path.finReads]))
    simp only [takenR, hv, Option.map_some]; exact ⟨_, rfl⟩
  | eqq l r0 z o' =>
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hval l (by simp [Path.finReads]))
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hval r0 (by simp [Path.finReads]))
    simp only [takenR, hv, hw, Option.bind_some, Option.map_some]; exact ⟨_, rfl⟩
  | brz s z o' =>
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hval s (by simp [Path.finReads]))
    simp only [takenR, hv, Option.map_some]; exact ⟨_, rfl⟩
  | hop t => exact ⟨t, rfl⟩
  | brn s z o' =>
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hval s (by simp [Path.finReads]))
    have hs := hold s (by simp [Path.finReads])
    by_cases hl : v = A 0 ∨ v = A 1
    · rcases hl with rfl | rfl
      · exact ⟨z, by simp [takenR, hv]⟩
      · exact ⟨o', by simp [takenR, hv, A]⟩
    · exfalso
      simp only [aliasFin] at h
      split at h
      · cases h
      obtain ⟨ic, hic, e⟩ := Option.map_eq_some_iff.mp h
      have hI := hf _ ic v hic (by rw [hs, hv])
      split at e
      · split at e
        · rename_i hlb
          rcases hI.2.1 hlb with e1 | e1
          · exact hl (Or.inl e1)
          · exact hl (Or.inr e1)
        · subst e
          simp only [takenR, hs, hv, Option.bind_some] at ht
          by_cases h0 : v = A 0
          · exact hl (Or.inl h0)
          · by_cases h1 : v = A 1
            · exact hl (Or.inr h1)
            · simp [h0, h1] at ht
      · rename_i hm; exact hl (Or.inl (hI.2.2.1 _ hm))
      · rename_i hm; exact hl (Or.inr (hI.2.2.1 _ hm))
      · subst e; simp [takenR] at ht
  | lti n s z o' => exact absurd rfl (hnl n s z o')
  | jmp => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [takenR] at ht
  | jmf => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [takenR] at ht
  | jsp => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [takenR] at ht
  | jsf => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [takenR] at ht
  | don => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [takenR] at ht
  | bom => simp only [aliasFin, Option.some.injEq] at h; subst h; simp [takenR] at ht

/-! ## The pass before goes on -/

/-- A pass loop that goes on has as many arguments as parameters. -/
theorem passLoop_len : ∀ (args : List (Option Nat)) (par : List Nat) (R R2 : Map (Option Noun)),
    evalPassLoop args par R = some R2 → args.length = par.length
  | [], par, R, R2, h => by
    simp only [evalPassLoop] at h
    split at h
    · rename_i e; subst e; rfl
    · cases h
  | _ :: _, [], _, _, h => by simp [evalPassLoop] at h
  | a :: args, p :: par, R, R2, h => by
    simp only [evalPassLoop] at h
    obtain ⟨R1, -, h2⟩ := Option.bind_eq_some_iff.mp h
    simp only [List.length_cons, passLoop_len args par R1 R2 h2]

/-- **A pass loop goes on** when it has as many arguments as parameters and
every argument register is in the file. -/
theorem apass_some : ∀ (args : List (Option Nat)) (par : List Nat) (R : Map (Option Noun)),
    args.length = par.length → (∀ u, some u ∈ args → (HoonMap.get R u).isSome) →
    ∃ R2, evalPassLoop args par R = some R2
  | [], [], R, _, _ => ⟨R, by simp [evalPassLoop]⟩
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | a :: args, p :: par, R, hl, hu => by
    have hl' : args.length = par.length := by simpa using hl
    have keep : ∀ w, ∀ u, some u ∈ args → (HoonMap.get (HoonMap.put R p w) u).isSome := fun w u hm =>
      get_put_isSome (hu u (List.mem_cons_of_mem _ hm))
    cases a with
    | none =>
      obtain ⟨R2, h2⟩ := apass_some args par _ hl' (keep none)
      exact ⟨R2, by simp only [evalPassLoop, Option.bind_some]; exact h2⟩
    | some r =>
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hu r List.mem_cons_self)
      obtain ⟨R2, h2⟩ := apass_some args par _ hl' (keep w)
      exact ⟨R2, by simp only [evalPassLoop, move, hw, Option.map_some, Option.bind_some]; exact h2⟩

/-! ## The normal form -/

section
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c c' : Straight Map} {gul : Noun}
  {pick : List Nat → Nat} {nargs : Nat} {topo : List Nat} {rev : Map (List Nat)} {g : AGen Map}
  {S0 : σ} {V0 : List Noun} {T0 : Trace}

/-- **The normal form**: the pending mode, the live mode at the end of the
body or at an op the walk keeps that is no dead fill, the dead mode at the
end of the body. -/
def ANorm (pick : List Nat → Nat) (nargs : Nat) (c : Straight Map) (topo : List Nat) (rev : Map (List Nat))
    (es : List (Nat × Nat)) (x x' : Path.Cfg σ Map) : Prop :=
  APend pick nargs c topo rev es x x' ∨
  (∃ s, ALive pick nargs c topo rev es x x' s ∧
    (x.b.body = [] ∨ ((∀ r, ¬ DeadFill c.blocks r x.lab s.k) ∧
      ∃ op rest op' st2, x.b.body = op :: rest ∧ aliasOp pick s.sta op = some (some op', st2)))) ∨
  (ADead x x' ∧ x.b.body = [])

/-- `AliasI` in the normal form. -/
def AliasN (pick : List Nat → Nat) (nargs : Nat) (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun)
    (topo : List Nat) (rev : Map (List Nat)) (S0 : σ) (V0 : List Noun) (T0 : Trace) (x x' : Path.Cfg σ Map) :
    Prop :=
  ∃ es, Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) S0 V0 T0 es x ∧
    x'.lab = x.lab ∧ x'.t = x.t ∧ x'.st = x.st ∧ ANorm pick nargs c topo rev es x x'

theorem apend_ne {es : List (Nat × Nat)} {x x' : Path.Cfg σ Map} (hp : APend pick nargs c topo rev es x x') :
    x'.params ≠ [] ∨ x'.b.par ≠ [] := by
  obtain ⟨hne, hpar, -, f, hargs, -⟩ := hp
  rcases hne with h | h
  · left; rw [hargs]; intro e; exact h (List.map_eq_nil_iff.mp e)
  · right; rw [hpar]; exact h

/-- **The normal form**: the code before runs the ops the walk drops and the
`%imm` ops of the dead mode. -/
theorem alias_norm (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS c.blocks)
    (hT : TopoInvR c.blocks topo rev) (hE : EntryOK lib O c gul S0 V0 T0) :
    ∀ (l : List Pole) {x x' : Path.Cfg σ Map}, x.b.body = l →
      AliasI pick nargs lib O c gul topo rev S0 V0 T0 x x' →
      ∃ es z, Path.Steps lib O c gul x es z ∧ AliasN pick nargs lib O c gul topo rev S0 V0 T0 z x'
  | [], x, x', hl0, hr => by
    obtain ⟨es, hfe, hlab, ht, hst, hm⟩ := hr
    refine ⟨[], x, Path.Steps.refl _, es, hfe, hlab, ht, hst, ?_⟩
    rcases hm with hp | ⟨s, hl⟩ | hd
    · exact Or.inl hp
    · exact Or.inr (Or.inl ⟨s, hl, Or.inl hl0⟩)
    · exact Or.inr (Or.inr ⟨hd, hl0⟩)
  | op :: l, x, x', hl0, hr => by
    obtain ⟨es, hfe, hlab, ht, hst, hm⟩ := hr
    have dead : ADead x x' →
        ∃ es z, Path.Steps lib O c gul x es z ∧ AliasN pick nargs lib O c gul topo rev S0 V0 T0 z x' := by
      intro hd
      obtain ⟨n0, d, rfl⟩ := hd.imm op (by rw [hl0]; exact List.mem_cons_self)
      have hpole : execPole lib O gul x.st (Pole.imm n0 d) x.regs x.t =
          some (Tone.zero (A 0), store d n0 x.regs, x.t, x.st) := rfl
      have hs := Path.Step.op (c := c) hd.px hd.qx hl0 hpole
      obtain ⟨-, -, -, -, hd'⟩ := adead_step hd hs
      have hfe' := fe_step hfe hs
      obtain ⟨es2, z, hz, hn⟩ := alias_norm hpick hD hT hE l rfl ⟨es ++ [], hfe', hlab, ht, hst, Or.inr (Or.inr hd')⟩
      exact ⟨[] ++ es2, z, Path.Steps.step hs hz, hn⟩
    rcases hm with hp | ⟨s, hl⟩ | hd
    · exact ⟨[], x, Path.Steps.refl _, es, hfe, hlab, ht, hst, Or.inl hp⟩
    · by_cases hdf : ∃ r, DeadFill c.blocks r x.lab s.k
      · obtain ⟨r, hdf⟩ := hdf
        exact dead (alive_dead hl hdf)
      · have hnd : ∀ r, ¬ DeadFill c.blocks r x.lab s.k := fun r hr => hdf ⟨r, hr⟩
        obtain ⟨res, st2, outb2, h1, -, -, -⟩ := alive_next hpick hD hT hfe hl hl0
        cases res with
        | some op' =>
          exact ⟨[], x, Path.Steps.refl _, es, hfe, hlab, ht, hst,
            Or.inr (Or.inl ⟨s, hl, Or.inr ⟨hnd, op, l, op', st2, hl0, h1⟩⟩)⟩
        | none =>
          obtain ⟨R2, hR2⟩ := alive_drop_exec hpick hD hT hE hfe hl hl0 h1
          obtain ⟨res', st2', s', h1', -, hdrop⟩ := alive_op hpick hD hT hE hfe hl hl0 hnd hR2
          rw [h1] at h1'
          cases h1'
          obtain ⟨-, -, -, hl'⟩ := hdrop rfl
          have hs := Path.Step.op (c := c) hl.px (by rw [hl.bx]) hl0 hR2
          have hfe' := fe_step hfe hs
          rw [List.append_nil] at hfe'
          obtain ⟨es2, z, hz, hn⟩ := alias_norm hpick hD hT hE l rfl
            ⟨es, hfe', hlab, ht, hst, Or.inr (Or.inl ⟨s', hl'⟩)⟩
          exact ⟨[] ++ es2, z, Path.Steps.step hs hz, hn⟩
    · exact dead hd

/-! ## Backward -/

/-- **Backward**: out of the normal form, a step of the code after is matched
by one step of the code before. -/
theorem alias_bwd_step (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS c.blocks)
    (hT : TopoInvR c.blocks topo rev) (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g)
    (hc' : c'.blocks = g.new) (hE : EntryOK lib O c gul S0 V0 T0)
    {x x' y' : Path.Cfg σ Map} {e' : List (Nat × Nat)} (hs : Path.Step lib O c' gul x' e' y')
    (hn : AliasN pick nargs lib O c gul topo rev S0 V0 T0 x x') :
    ∃ es y, Path.Steps lib O c gul x es y ∧ AliasI pick nargs lib O c gul topo rev S0 V0 T0 y y' := by
  obtain ⟨es, hfe, hlab, ht, hst, hm⟩ := hn
  rcases hm with hp | ⟨s, hl, hnf⟩ | ⟨hd, hbd⟩
  · have hne' := apend_ne hp
    obtain ⟨hne, hpar, hchk, f, hargs, hpr, hpass⟩ := hp
    cases hs with
    | @pass Rp' _ hR' =>
      have hlen : x.params.length = x.b.par.length := by
        obtain ⟨-, hloop⟩ := evalPass_check hR'
        have := passLoop_len _ _ _ _ hloop
        rw [hargs, hpar, List.length_map] at this; exact this
      obtain ⟨Rp, hRp⟩ := apass_some x.params x.b.par x.regs hlen (fun u hu => hE.2.1 es x u hfe hu)
      have hR : evalPass x.params x.b.par x.regs = some Rp := by
        rw [evalPass_ok (fun a ha k e => by subst e; exact hchk k ha)]; exact hRp
      obtain ⟨Rp'', hR'', s', hl'⟩ := hpass Rp hR
      rw [hR'] at hR''
      cases hR''
      have hsx := Path.Step.pass (c := c) (lib := lib) (O := O) (gul := gul) hne hR
      have hfe' := fe_step hfe hsx
      rw [List.append_nil] at hfe'
      exact ⟨_, _, Path.Steps.step hsx (Path.Steps.refl _), es, hfe', hlab, ht, hst, Or.inr (Or.inl ⟨s', hl'⟩)⟩
    | op hp' hq' _ _ => exact absurd hne' (by simp [hp', hq'])
    | jump hp' hq' _ _ _ => exact absurd hne' (by simp [hp', hq'])
  · have hq0 : x.b.par = [] := by rw [hl.bx]
    have hq0' : x'.b.par = [] := by rw [hl.bx']
    rcases hnf with hbd | ⟨hnd, op, rest, op', st2, hbd, h1⟩
    · obtain ⟨-, hout, hst', hf, hfr, hrr⟩ := alive_end hpick hD hT hfe hl hbd
      have hb' : x'.b.body = [] := by rw [hl.bx', hout]
      cases hs with
      | pass hne' _ => exact absurd hne' (by simp [hl.px', hq0'])
      | op _ _ hb'' _ => rw [hb'] at hb''; cases hb''
      | @jump j' b2' _ _ _ htk' hb2' =>
        have hfin : x.b.fin = s.b.fin := by rw [hl.bx]
        have hfin' : x'.b.fin = s.rf.1 := by rw [hl.bx']
        have hrf := hl.ok.fin
        rw [hst'] at hrf
        have htkR : takenR (fun y => read y x.regs) s.rf.1 = some j' := by
          rw [← afn_taken_congr hrr, ← afn_taken, ← hfin']; exact htk'
        obtain ⟨j, hjR⟩ := afn_jump_back hrf hf (fun y hy => (hfr y hy).1) (hD.2.2 _ s.b hl.ok.hb)
          (fun y hy => by
            obtain ⟨v, hv⟩ := hE.1 es x y hfe ⟨hl.px, hq0, Or.inr ⟨hbd, by rw [hfin]; exact hy⟩⟩
            rw [hv]; rfl) htkR
        have htk : Path.taken x.regs x.b.fin = some j := by rw [afn_taken, hfin]; exact hjR
        obtain ⟨hπ, -, -, -, -, -⟩ := alive_at hpick hD hT hfe hl
        have hxT : x.lab ∈ topo := hT.1.1.2.2.2.1 _ (ssk_bpath_reach hπ _ List.mem_cons_self)
        have hjT := (awi_fwd hT.1.1 hxT hl.ok.hb (by rw [← hfin]; exact taken_mem htk)).1
        obtain ⟨bo, hbo⟩ := Option.isSome_iff_exists.mp (hT.1.1.2.2.1 _ hjT)
        have hsx := Path.Step.jump (c := c) (lib := lib) (O := O) (gul := gul) hl.px hq0 hbd htk hbo
        obtain ⟨j'', pbo, htk'', hj''o, hgo, -, -, hmode⟩ := alive_jump hpick hD hT h hfe hl hbd htk hbo
        rw [htk'] at htk''
        cases htk''
        rw [hc', hj''o, hgo] at hb2'
        cases hb2'
        have e : (⟨j'.there, b2', j'.args, x'.regs, x'.t, x'.st⟩ : Path.Cfg σ Map) =
            ⟨j.there, b2', j'.args, x'.regs, x'.t, x'.st⟩ := by rw [hj''o]
        rw [e]
        refine ⟨_, _, Path.Steps.step hsx (Path.Steps.refl _), es ++ [(x.lab, j.there)], fe_step hfe hsx, rfl, ht,
          hst, ?_⟩
        rcases hmode with hm | ⟨s', hm⟩
        · exact Or.inl hm
        · exact Or.inr (Or.inl ⟨s', hm⟩)
    · obtain ⟨res, st3, outb2, h1', hout, -, hx⟩ := alive_next hpick hD hT hfe hl hbd
      rw [h1] at h1'
      cases h1'
      have hb' : x'.b.body = op' :: outb2 := by rw [hl.bx', hout]; rfl
      cases hs with
      | pass hne' _ => exact absurd hne' (by simp [hl.px', hq0'])
      | jump _ _ hb'' _ _ => rw [hb'] at hb''; cases hb''
      | @op p' rest' n R2' t2 s2 _ _ hb'' hpole' =>
        rw [hb'] at hb''
        simp only [List.cons.injEq] at hb''
        obtain ⟨rfl, rfl⟩ := hb''
        rw [hst, ht] at hpole'
        rcases hx op' rfl with ⟨-, e2⟩ | ⟨ton, t3, s3, W, e1, e2, -, -⟩
        · rw [e2] at hpole'; cases hpole'
        · rw [e2] at hpole'
          simp only [Option.some.injEq, Prod.mk.injEq] at hpole'
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hpole'
          obtain ⟨res, st4, s', h1'', hkept', -⟩ := alive_op hpick hD hT hE hfe hl hbd hnd e1
          rw [h1] at h1''
          cases h1''
          obtain ⟨R2'', hout', hx'', hl'⟩ := hkept' op' rfl
          rw [e2] at hx''
          simp only [Option.some.injEq, Prod.mk.injEq] at hx''
          obtain ⟨-, rfl, -, -⟩ := hx''
          have hob : s'.outb = outb2 := by
            rw [hout] at hout'; simp only [Option.toList_some, List.singleton_append, List.cons.injEq] at hout'
            exact hout'.2.symm
          rw [hob] at hl'
          have hsx := Path.Step.op (c := c) (lib := lib) (O := O) (gul := gul) hl.px hq0 hbd e1
          have hfe' := fe_step hfe hsx
          rw [List.append_nil] at hfe'
          exact ⟨_, _, Path.Steps.step hsx (Path.Steps.refl _), es, hfe', hlab, rfl, rfl, Or.inr (Or.inl ⟨s', hl'⟩)⟩
  · cases hs with
    | pass hne' _ => exact absurd hne' (by simp [hd.px', hd.qx'])
    | jump _ _ _ htk' _ =>
      obtain ⟨u, hu⟩ := hd.bom'
      rw [hu] at htk'; simp [Path.taken] at htk'
    | @op p' rest' n R2' t2 s2 _ _ hb'' hpole' =>
      obtain ⟨n0, d, rfl⟩ := hd.imm' p' (by rw [hb'']; exact List.mem_cons_self)
      simp only [execPole, localPole, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpole'
      obtain ⟨-, -, rfl, rfl⟩ := hpole'
      exact ⟨[], x, Path.Steps.refl _, es, hfe, hlab, ht, hst, Or.inr (Or.inr ⟨hd.px, hd.qx, hd.px', hd.qx', hd.imm,
        fun op hop => hd.imm' op (by rw [hb'']; exact List.mem_cons_of_mem _ hop), hd.bom, hd.bom'⟩)⟩

/-- **Backward, on paths**, to the normal form. -/
theorem alias_bwd (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS c.blocks)
    (hT : TopoInvR c.blocks topo rev) (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g)
    (hc' : c'.blocks = g.new) (hE : EntryOK lib O c gul S0 V0 T0)
    {x' z' : Path.Cfg σ Map} {es' : List (Nat × Nat)} (hs : Path.Steps lib O c' gul x' es' z') :
    ∀ {x : Path.Cfg σ Map}, AliasI pick nargs lib O c gul topo rev S0 V0 T0 x x' →
      ∃ es z, Path.Steps lib O c gul x es z ∧ AliasN pick nargs lib O c gul topo rev S0 V0 T0 z z' := by
  induction hs with
  | refl => intro x hr; exact alias_norm hpick hD hT hE _ rfl hr
  | step s _ ih =>
    intro x hr
    obtain ⟨es1, x1, hs1, hn1⟩ := alias_norm hpick hD hT hE _ rfl hr
    obtain ⟨es2, y, hs2, hr2⟩ := alias_bwd_step hpick hD hT h hc' hE s hn1
    obtain ⟨es3, z, hs3, hn3⟩ := ih hr2
    exact ⟨_, z, Path.steps_trans (Path.steps_trans hs1 hs2) hs3, hn3⟩

/-! ## At the normal form -/

/-- **An end after, at the normal form, is the same end before.** -/
theorem alias_bwd_end (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS c.blocks)
    (hT : TopoInvR c.blocks topo rev) (hE : EntryOK lib O c gul S0 V0 T0)
    {x x' : Path.Cfg σ Map} (hn : AliasN pick nargs lib O c gul topo rev S0 V0 T0 x x') {r : Tone × σ}
    (he : Path.endOf lib O gul x' = some r) : Path.endOf lib O gul x = some r := by
  obtain ⟨es, hfe, hlab, ht, hst, hm⟩ := hn
  rcases hm with hp | ⟨s, hl, hnf⟩ | ⟨hd, hbd⟩
  · unfold Path.endOf at he
    rw [if_pos (apend_ne hp)] at he
    cases he
  · have hq0 : x.b.par = [] := by rw [hl.bx]
    have hq0' : x'.b.par = [] := by rw [hl.bx']
    rcases hnf with hbd | ⟨-, op, rest, op', st2, hbd, h1⟩
    · obtain ⟨-, hout, hst', hf, hfr, hrr⟩ := alive_end hpick hD hT hfe hl hbd
      have hb' : x'.b.body = [] := by rw [hl.bx', hout]
      have hfin : x.b.fin = s.b.fin := by rw [hl.bx]
      have hfin' : x'.b.fin = s.rf.1 := by rw [hl.bx']
      have hrf := hl.ok.fin
      rw [hst'] at hrf
      rw [afn_endOf hl.px' hq0' hb', hfin', hst, ht, endR_congr hrr,
        afn_end O gul x.st x.t hrf hf (fun y hy => (hfr y hy).1) (hD.2.2 _ s.b hl.ok.hb) (fun s0 z o' e => ?_)] at he
      · rw [afn_endOf hl.px hq0 hbd, hfin]; exact he
      · obtain ⟨v, hv⟩ := hE.1 es x s0 hfe ⟨hl.px, hq0, Or.inr ⟨hbd, by rw [hfin, e]; simp [Path.finReads]⟩⟩
        rw [hv]; rfl
    · obtain ⟨res, st3, outb2, h1', hout, -, hx⟩ := alive_next hpick hD hT hfe hl hbd
      rw [h1] at h1'
      cases h1'
      have hb' : x'.b.body = op' :: outb2 := by rw [hl.bx', hout]; rfl
      rw [endOf_op hl.px' hq0' hb', hst, ht, endPole_xrel (hx op' rfl)] at he
      rw [endOf_op hl.px hq0 hbd]; exact he
  · obtain ⟨u, hu⟩ := hd.bom
    obtain ⟨u', hu'⟩ := hd.bom'
    rw [afn_endOf hd.px hd.qx hbd, hu]
    cases hb' : x'.b.body with
    | cons p rest =>
      obtain ⟨n0, d, rfl⟩ := hd.imm' p (by rw [hb']; exact List.mem_cons_self)
      rw [endOf_op hd.px' hd.qx' hb'] at he
      cases he
    | nil =>
      rw [afn_endOf hd.px' hd.qx' hb', hu', ht, hst] at he
      exact he

/-- **A real read after, at the normal form, reads a value**, given
`ReadsOK` before. -/
theorem alias_reads (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS c.blocks)
    (hT : TopoInvR c.blocks topo rev) (hE : EntryOK lib O c gul S0 V0 T0)
    {x x' : Path.Cfg σ Map} (hn : AliasN pick nargs lib O c gul topo rev S0 V0 T0 x x') {k : Nat}
    (hk : Path.ReadsAt gul x' k) : ∃ v, read k x'.regs = some v := by
  obtain ⟨es, hfe, hlab, ht, hst, hm⟩ := hn
  obtain ⟨hp', hq', hk⟩ := hk
  rcases hm with hp | ⟨s, hl, hnf⟩ | ⟨hd, hbd⟩
  · exact absurd (apend_ne hp) (by simp [hp', hq'])
  · have hq0 : x.b.par = [] := by rw [hl.bx]
    rcases hnf with hbd | ⟨-, op, rest, op', st2, hbd, h1⟩
    · obtain ⟨-, hout, hst', -, hfr, hrr⟩ := alive_end hpick hD hT hfe hl hbd
      have hfin : x.b.fin = s.b.fin := by rw [hl.bx]
      have hfin' : x'.b.fin = s.rf.1 := by rw [hl.bx']
      have hb' : x'.b.body = [] := by rw [hl.bx', hout]
      rcases hk with ⟨p, rest, hb'', -⟩ | ⟨-, hk⟩
      · rw [hb'] at hb''; cases hb''
      · rw [hfin'] at hk
        have hrf := hl.ok.fin
        rw [hst'] at hrf
        obtain ⟨z, hz, rfl⟩ := awa_fin_reads hrf (hD.2.2 _ s.b hl.ok.hb) k hk
        obtain ⟨v, hv⟩ := hE.1 es x z hfe ⟨hl.px, hq0, Or.inr ⟨hbd, by rw [hfin]; exact hz⟩⟩
        exact ⟨v, by rw [hrr _ hk, (hfr z hz).1, hv]⟩
    · obtain ⟨res, st3, outb2, h1', hout, hrd, -⟩ := alive_next hpick hD hT hfe hl hbd
      rw [h1] at h1'
      cases h1'
      have hb' : x'.b.body = op' :: outb2 := by rw [hl.bx', hout]; rfl
      rcases hk with ⟨p, rest', hb'', hk⟩ | ⟨hb'', -⟩
      · rw [hb'] at hb''
        simp only [List.cons.injEq] at hb''
        obtain ⟨rfl, -⟩ := hb''
        rw [aop_rename h1, poleReads_rename] at hk
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hk
        obtain ⟨v, hv⟩ := hE.1 es x y hfe ⟨hl.px, hq0, Or.inl ⟨op, rest, hbd, hy⟩⟩
        exact ⟨v, by rw [hrd y (poleReads_alias hy), hv]⟩
      · rw [hb'] at hb''; cases hb''
  · rcases hk with ⟨p, rest, hb'', hk⟩ | ⟨-, hk⟩
    · obtain ⟨n0, d, rfl⟩ := hd.imm' p (by rw [hb'']; exact List.mem_cons_self)
      simp [Path.poleReads] at hk
    · obtain ⟨u, hu⟩ := hd.bom'
      rw [hu] at hk; simp [Path.finReads] at hk

/-- **An op after that `+get-reg-safe-assignment` names goes on, at the
normal form**, given `LocalOK` before. -/
theorem alias_local (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS c.blocks)
    (hT : TopoInvR c.blocks topo rev) (hE : EntryOK lib O c gul S0 V0 T0)
    {x x' : Path.Cfg σ Map} (hn : AliasN pick nargs lib O c gul topo rev S0 V0 T0 x x') {p : Pole}
    {rest : List Pole} (hp' : x'.params = []) (hq' : x'.b.par = []) (hb : x'.b.body = p :: rest)
    (hsa : (safeAssign p).isSome) : (execPole lib O gul x'.st p x'.regs x'.t).isSome := by
  obtain ⟨es, hfe, hlab, ht, hst, hm⟩ := hn
  rcases hm with hpe | ⟨s, hl, hnf⟩ | ⟨hd, -⟩
  · exact absurd (apend_ne hpe) (by simp [hp', hq'])
  · have hq0 : x.b.par = [] := by rw [hl.bx]
    rcases hnf with hbd | ⟨-, op, rest0, op', st2, hbd, h1⟩
    · obtain ⟨-, hout, -⟩ := alive_end hpick hD hT hfe hl hbd
      rw [hl.bx', hout] at hb; cases hb
    · obtain ⟨res, st3, outb2, h1', hout, -, hx⟩ := alive_next hpick hD hT hfe hl hbd
      rw [h1] at h1'
      cases h1'
      rw [hl.bx', hout] at hb
      simp only [Option.toList_some, List.singleton_append, List.cons.injEq] at hb
      obtain ⟨rfl, -⟩ := hb
      have hsa' : (safeAssign op).isSome := by rw [aop_rename h1, safeAssign_rename] at hsa; exact hsa
      have hloc := hE.2.2 es x op rest0 hfe hl.px hq0 hbd hsa'
      rw [hst, ht]
      rcases hx _ rfl with ⟨e1, -⟩ | ⟨ton, t3, s3, W, -, e2, -, -⟩
      · rw [e1] at hloc; cases hloc
      · rw [e2]; rfl
  · obtain ⟨n0, d, rfl⟩ := hd.imm' p (by rw [hb]; exact List.mem_cons_self)
    rfl

/-- **A pending argument after is present**, given `ArgsOK` before. -/
theorem alias_args (hE : EntryOK lib O c gul S0 V0 T0)
    {x x' : Path.Cfg σ Map} (hn : AliasN pick nargs lib O c gul topo rev S0 V0 T0 x x') {k : Nat}
    (hk : some k ∈ x'.params) : (HoonMap.get x'.regs k).isSome := by
  obtain ⟨es, hfe, -, -, -, hm⟩ := hn
  rcases hm with ⟨-, -, -, f, hargs, hpr, -⟩ | ⟨s, hl, -⟩ | ⟨hd, -⟩
  · rw [hargs] at hk
    obtain ⟨a, ha, e⟩ := List.mem_map.mp hk
    cases a with
    | none => cases e
    | some u =>
      simp only [Option.map_some, Option.some.injEq] at e
      subst e
      exact hpr u ha (hE.2.1 es x u hfe ha)
  · rw [hl.px'] at hk; cases hk
  · rw [hd.px'] at hk; cases hk

end

end Opt
end SkaModel
end Formalization
