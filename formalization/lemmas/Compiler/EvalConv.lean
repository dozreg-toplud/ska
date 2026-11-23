import lemmas.Compiler.EvalCall

/-!
# What the pill's `+eval-top` returns, the model returns

The converse of `eval_top_of_model`.  The pill's run is cut by the depth of
its calls (`iterN`), and the induction follows the calls of the three gates
that call each other: `+eval-top`, `+eval-blob` and `+eval-pole` (`InR`).

A run at depth `k + 1` is a run of `nockW (hyb k)`: the calls of the three
gates go to `iterN k`, where the hypothesis of the induction applies, and
every other call to `nock`, where the theorems about the other arms apply.
One gate of `+eval-blob` is let through: the gate `hop` that `+eval-blob`
builds to jump to a block, whose battery `hopB` calls `+eval-blob` again.  It
runs inline, with `hyb0 k`.

The model's side is "from some level on" (`Ev`): the model's `k` is both the
depth of the interpreter's calls and the fuel of `+mink`, and the value comes
from the other direction (`interp_le`) and the determinism of Nock.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- The batteries whose calls the induction follows. -/
def InR (f : Noun) : Prop := f = eval_top.battery ∨ f = eval_blob.battery ∨ f = eval_pole.battery

instance : DecidablePred InR := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The battery of the gate `hop` of `+eval-blob`: `+got:by` of the block,
then `+eval-blob` on it. -/
def hopB : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 110) (C (A 0) (A 12))) (C (A 10) (C (C (A 26) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 2011))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 0) (A 7))))))))

/-- Calls of the three gates at most `k` deep, other calls in full. -/
def hyb0 (k : Nat) (s f : Noun) : Option Noun := if InR f then iterN k s f else nock s f

/-- `hyb0`, with the gate `hop` run inline. -/
def hyb (k : Nat) (s f : Noun) : Option Noun :=
  if InR f then iterN k s f else if f = hopB then nockW (hyb0 k) s f else nock s f

theorem hyb0_le (k : Nat) (s f : Noun) : Below? (hyb0 k s f) (nock s f) := by
  unfold hyb0; split
  · exact iterN_sound k s f
  · exact Below?.refl _

theorem hyb_le (k : Nat) (s f : Noun) : Below? (hyb k s f) (nock s f) := by
  unfold hyb; split
  · exact iterN_sound k s f
  · split
    · rw [nock_eq_nockW]; exact nockW_mono (hyb0_le k) s f
    · exact Below?.refl _

theorem iterN_le_hyb0 (k : Nat) (s f : Noun) : Below? (iterN k s f) (hyb0 k s f) := by
  unfold hyb0; split
  · exact Below?.refl _
  · exact iterN_sound k s f

theorem iterN_le_hyb (k : Nat) (s f : Noun) : Below? (iterN k s f) (hyb k s f) := by
  unfold hyb; split
  · exact Below?.refl _
  · split
    · cases k with
      | zero => intro x h; simp [iterN] at h
      | succ j =>
        rw [iterN_succ]
        exact nockW_mono (fun s f x h => iterN_le_hyb0 (j + 1) s f x (iterN_mono_succ j s f x h)) s f
    · exact iterN_sound k s f

/-- A run at depth `k + 1` is a run of `nockW (hyb k)`. -/
theorem iterN_succ_hyb {k : Nat} {s f x : Noun} (h : iterN (k + 1) s f = some x) :
    nockW (hyb k) s f = some x :=
  nockW_mono (iterN_le_hyb k) s f x h

theorem hyb_in {k : Nat} {s f : Noun} (h : InR f) : hyb k s f = iterN k s f := if_pos h

theorem hyb_hop {k : Nat} {s f : Noun} (h : f = hopB) : hyb k s f = nockW (hyb0 k) s f := by
  subst h; unfold hyb; rw [if_neg (by decide), if_pos rfl]

theorem hyb_out {k : Nat} {s f : Noun} (h : ¬ InR f ∧ ¬ f = hopB) : hyb k s f = nock s f := by
  unfold hyb; rw [if_neg h.1, if_neg h.2]

theorem hyb0_in {k : Nat} {s f : Noun} (h : InR f) : hyb0 k s f = iterN k s f := if_pos h

theorem hyb0_out {k : Nat} {s f : Noun} (h : ¬ InR f) : hyb0 k s f = nock s f := if_neg h

/-! ## From some level on -/

/-- `g m` is `some a` for every `m` from some `m0` on. -/
def Ev {α : Type} (g : Nat → Option α) (a : α) : Prop := ∃ m0, ∀ m, m0 ≤ m → g m = some a

theorem Ev.at {α : Type} {g : Nat → Option α} {a : α} (h : Ev g a) : ∃ m, g m = some a :=
  let ⟨m0, hm⟩ := h; ⟨m0, hm m0 (Nat.le_refl _)⟩

section
variable (lib : Lib) (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))

/-- What the pill's `+eval-top` returns at depth `k`, the model returns from
some level on. -/
def TopGe (k : Nat) : Prop :=
  ∀ cr, CorIn cr → ∀ s f scry x, iterN k (topS cr s f scry) eval_top.battery = some x →
    ∃ r, Ev (fun m => (SkaModel.interp lib pk m).nok cr s f scry) r

/-- The same for `+eval-blob`. -/
def BlobGe (k : Nat) : Prop :=
  ∀ cr, CorIn cr → ∀ regs trace b s params scry x,
    iterN k (blobS cr regs trace b s params scry) eval_blob.battery = some x →
    ∃ r, Ev (fun m => execBlob lib (SkaModel.interp lib pk m) s scry cr regs trace b params) r

/-- The same for `+eval-pole`. -/
def PoleGe (k : Nat) : Prop :=
  ∀ cr, CorIn cr → ∀ pole regs trace scry x,
    iterN k (poleS cr pole regs trace scry) eval_pole.battery = some x →
    ∃ r, Ev (fun m => execPole lib (SkaModel.interp lib pk m) scry cr pole regs trace) r

theorem topGe_zero : TopGe lib pk 0 := fun _ _ _ _ _ _ h => by simp [iterN] at h
theorem blobGe_zero : BlobGe lib pk 0 := fun _ _ _ _ _ _ _ _ _ h => by simp [iterN] at h
theorem poleGe_zero : PoleGe lib pk 0 := fun _ _ _ _ _ _ _ h => by simp [iterN] at h

theorem blobGe_mono {k k' : Nat} (hk : k ≤ k') (h : BlobGe lib pk k') : BlobGe lib pk k :=
  fun cr hc regs trace b s params scry x e =>
    h cr hc regs trace b s params scry x (iterN_mono hk _ _ x e)

end

/-! ## The poke under a call function below `nock` -/

/-- `pokeN` with its two calls made by `c`. -/
def pokeW (c : Noun → Noun → Option Noun) (cr ovo : Noun) : Option Noun :=
  ((slot? poke.axis cr).bind fun a => c cr a).bind fun g =>
    (edit? 6 ovo g).bind fun g' => (slot? 2 g').bind fun f => c g' f

theorem pokeW_le {c : Noun → Noun → Option Noun} (hc : ∀ s f, Below? (c s f) (nock s f))
    (cr ovo : Noun) : Below? (pokeW c cr ovo) (pokeN cr ovo) :=
  Below?.bind (Below?.bind (Below?.refl _) fun a => hc cr a) fun _ =>
    Below?.bind (Below?.refl _) fun g' => Below?.bind (Below?.refl _) fun f => hc g' f

/-- Under `hyb k`, the poke crashes or returns what the model `pk` says. -/
theorem pokeW_cases {pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)}
    {cr : Noun} (hpk : PokeIs pk cr) (k : Nat) (ov : Ovum) :
    pokeW (hyb k) cr ov.toNoun = none ∨
      ∃ p cr', pk cr ov = some (p, cr') ∧ pokeW (hyb k) cr ov.toNoun = some (C p.toNoun cr') := by
  cases e : pokeW (hyb k) cr ov.toNoun with
  | none => exact Or.inl rfl
  | some y =>
    right
    have h1 := pokeW_le (hyb_le k) cr ov.toNoun y e
    rw [hpk.1 ov] at h1
    obtain ⟨⟨p, cr'⟩, e1, rfl⟩ := Option.map_eq_some_iff.1 h1
    exact ⟨p, cr', e1, rfl⟩

/-! ## The values, from the other direction -/

section
variable (lib : Lib) (hslam : SlamIsNock lib)
  (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
  (hpk : ∀ cr, CorIn cr → PokeIs pk cr)
include hslam hpk

theorem interp_call_le (m : Nat) : CallLe lib pk (SkaModel.interp lib pk m) := by
  cases m with
  | zero => intro _ _ _ _ _ _ _ h; simp [SkaModel.interp] at h
  | succ m =>
    exact fun _ _ _ _ _ _ _ h => ⟨SkaModel.interp lib pk m, (interp_le lib hslam pk hpk m).1, h⟩

theorem top_val {k : Nat} {cr s f scry x : Noun} {r : Tone × Noun} (hc : CorIn cr)
    (hr : Ev (fun m => (SkaModel.interp lib pk m).nok cr s f scry) r)
    (h : iterN k (topS cr s f scry) eval_top.battery = some x) : x = resN r ∧ CorIn r.2 := by
  obtain ⟨m, hm⟩ := hr.at
  obtain ⟨h1, h2⟩ := (interp_le lib hslam pk hpk m).2 cr hc s f scry r hm
  have h3 := iterN_sound k _ _ x h
  rw [h1] at h3
  exact ⟨(Option.some.inj h3).symm, h2⟩

theorem blob_val {k : Nat} {cr : Noun} {regs : TreapMap mugF Noun} {trace : Trace} {b : Blob}
    {s : Straight (TreapMap mugF)} {params : List (Option Nat)} {scry x : Noun} {r : Tone × Noun}
    (hc : CorIn cr)
    (hr : Ev (fun m => execBlob lib (SkaModel.interp lib pk m) s scry cr regs trace b params) r)
    (h : iterN k (blobS cr regs trace b s params scry) eval_blob.battery = some x) :
    x = resN r ∧ CorIn r.2 := by
  obtain ⟨m, hm⟩ := hr.at
  obtain ⟨h1, h2⟩ := (interp_le lib hslam pk hpk m).1 cr hc regs trace b s params scry r hm
  have h3 := iterN_sound k _ _ x h
  rw [h1] at h3
  exact ⟨(Option.some.inj h3).symm, h2⟩

theorem pole_val {k : Nat} {cr : Noun} {pole : Pole} {regs : TreapMap mugF Noun} {trace : Trace}
    {scry x : Noun} {r : Tone × TreapMap mugF Noun × Trace × Noun} (hc : CorIn cr)
    (hr : Ev (fun m => execPole lib (SkaModel.interp lib pk m) scry cr pole regs trace) r)
    (h : iterN k (poleS cr pole regs trace scry) eval_pole.battery = some x) :
    x = poleOutS r ∧ CorIn r.2.2.2 := by
  obtain ⟨m, hm⟩ := hr.at
  obtain ⟨h1, h2⟩ := eval_pole_le cr hc lib hslam pk (hpk cr hc) _ (interp_call_le lib hslam pk hpk m)
    (interp_le lib hslam pk hpk m).2 scry pole regs trace r hm
  have h3 := iterN_sound k _ _ x h
  rw [h1] at h3
  exact ⟨(Option.some.inj h3).symm, h2⟩

end

/-- The ends of `+eval-top`, run on a hypothesis under `hyb k`. -/
macro "top_simp_at" h:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (conv at $h:ident => { lhs; arg 3; unfold eval_top.battery }
   simp (disch := decide) [nock_exec, hyb_in, hyb_hop, hyb_out, hyb0_in, hyb0_out, $ts,*] at $h:ident))

/-- The same, on a hypothesis whose formula is already open. -/
macro "hyb_simp_at" h:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (disch := decide) [nock_exec, hyb_in, hyb_hop, hyb_out, hyb0_in, hyb0_out, $ts,*] at $h:ident)

theorem needOrd_this {n : NeedOrd} (h : ¬ n = NeedOrd.this) :
    ¬ C (A Tag.this) (A 0) = n.toNoun := by
  cases n with
  | pair p q => cases p <;> simp [NeedOrd.toNoun]
  | both _ _ => simp [NeedOrd.toNoun, Tag.this, Tag.both]
  | this => exact absurd rfl h
  | none => simp [NeedOrd.toNoun, Tag.this, Tag.none]

/-- The model at level `m + 1` from level `m`. -/
theorem Ev.succ {α : Type} {g : Nat → Option α} {a : α} (h : ∃ m0, ∀ m, m0 ≤ m → g (m + 1) = some a) :
    Ev g a := by
  obtain ⟨m0, hm⟩ := h
  refine ⟨m0 + 1, fun m hm' => ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact hm m' (by omega)

section
variable (lib : Lib) (hslam : SlamIsNock lib)
  (pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun))
  (hpk : ∀ cr, CorIn cr → PokeIs pk cr)
include hslam hpk

set_option maxHeartbeats 16000000 in
/-- `+eval-top` at depth `k + 1`: an atom formula, a `%bare` one by `+mink`, and
any other by the poke and `+eval-blob` at depth `k`. -/
theorem top_step (k : Nat) (hB : BlobGe lib pk k) : TopGe lib pk (k + 1) := by
  intro cr hc s f scry x h
  have h' := iterN_succ_hyb h
  have hl4 : slot? (read.layer2.axis / 4) (icore cr) = some layer4 := hc.2
  simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec] at hl4
  rcases f with fa | ⟨fh, ft⟩
  · exact ⟨(Tone.two [], cr), Ev.succ ⟨0, fun m _ => by simp [SkaModel.interp, topBody]⟩⟩
  rcases isBare_cases (C fh ft) with ⟨rest, e⟩ | hb
  · simp only [Noun.cell.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    by_cases hM : ∃ t, Mink lib scry [] s (C (A 11) (C (A Tag.bare) rest)) t
    · obtain ⟨t, n, hn⟩ := hM
      refine ⟨(t, cr), Ev.succ ⟨n, fun m hm => ?_⟩⟩
      simp [SkaModel.interp, topBody, isBare, minkF_le lib scry hm _ _ _ _ hn]
    · exfalso
      have hn : nock (C mink.battery (C (C (C s (C (A 11) (C (A Tag.bare) rest))) scry) layer4))
          mink.battery = none := by
        cases e : nock (C mink.battery (C (C (C s (C (A 11) (C (A Tag.bare) rest))) scry) layer4))
          mink.battery with
        | none => rfl
        | some y =>
          obtain ⟨t, -, ht⟩ := (mink_pill_iff lib hslam _ _ _ y).1 e
          exact absurd ⟨t, ht⟩ hM
      simp only [Tag.bare] at hn
      top_simp_at h' [hl4, mink.arm_at, mink_arm, hn, Tag.bare]
  · have hdisp : ¬ A 11 = fh ∨ (fh = A 11 ∧ ∃ t, ft = A t) ∨
        (fh = A 11 ∧ ∃ th tt, ft = C th tt ∧ ¬ A Tag.bare = th) := by
      by_cases h11 : fh = A 11
      · subst h11
        rcases ft with t | ⟨th, tt⟩
        · exact Or.inr (Or.inl ⟨rfl, t, rfl⟩)
        · refine Or.inr (Or.inr ⟨rfl, th, tt, rfl, fun e => ?_⟩)
          subst e; simp [isBare] at hb
      · exact Or.inl fun e => h11 e.symm
    rcases pokeW_cases (hpk cr hc) k (Ovum.full s (C fh ft)) with hw | ⟨p, cr', e1, hw⟩
    · exfalso
      simp only [pokeW, poke.axis, Ovum.toNoun, Tag.full] at hw
      rcases hdisp with hd | ⟨rfl, t, rfl⟩ | ⟨rfl, th, tt, rfl, hd⟩
      · top_simp_at h' [hw, hd]
      · top_simp_at h' [hw]
      · simp only [Tag.bare] at hd
        top_simp_at h' [hw, hd]
    · simp only [pokeW, poke.axis, Ovum.toNoun, Tag.full] at hw
      have hc' := (hpk cr hc).2 _ _ e1
      have hl2 : slot? read.layer2.axis (icore cr') = some layer2 := hc'.1
      simp only [read.layer2.axis, icore, nock_exec] at hl2
      have hnd : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
        ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
      have hreg : HoonMap.toNoun id (regsOf [s] : TreapMap mugF Noun)
          = C (C (A 0) s) (C (A 0) (A 0)) := rfl
      rcases hdisp with hd | ⟨rfl, t, rfl⟩ | ⟨rfl, th, tt, rfl, hd⟩
      all_goals (try simp only [Tag.bare] at hd)
      all_goals first | top_simp_at h' [hw, hd] | top_simp_at h' [hw]
      all_goals
        rcases p with _ | ⟨b, c, new⟩ | ps
        · hyb_simp_at h' []
        rotate_left
        · hyb_simp_at h' [Tag.ir, Tag.drop]
        by_cases h1 : c.nargs = 1
        rotate_left
        · have h1' : ¬ 1 = c.nargs := fun e => h1 e.symm
          hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, h1']
        by_cases h2 : c.need = NeedOrd.this
        rotate_left
        · have h2' := needOrd_this h2
          simp only [Tag.this] at h2'
          hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, h1, h2']
        have hg := getF_hoonMap Blob.toNoun c.blocks 0
        cases e2 : HoonMap.get c.blocks 0 with
        | none =>
          rw [e2] at hg
          simp only [unitNoun] at hg
          hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, h1, h2, NeedOrd.toNoun,
            Tag.this, hl2, by.arm_at, by_arm, by.got.arm_at, got_arm, got_gate_nil layer2 hnd _ _ hg]
        | some b0 =>
        rw [e2] at hg
        obtain ⟨par0, body0, fin0⟩ := b0
        simp only [unitNoun, Blob.toNoun] at hg
        by_cases hp0 : par0 = []
        rotate_left
        · obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil hp0
          hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, h1, h2, NeedOrd.toNoun,
            Tag.this, hl2, by.arm_at, by_arm, by.got.arm_at, got_arm, got_gate layer2 hnd _ _ _ hg,
            listNoun]
        subst hp0
        cases eB : iterN k (blobS cr' (regsOf [s]) [] ⟨[], body0, fin0⟩ c [] scry)
          eval_blob.battery with
        | none =>
          simp only [blobS, icore, Straight.toNoun, argsN, listNoun, hreg, Blob.toNoun, h1, h2,
            NeedOrd.toNoun, Tag.this] at eB
          hyb_simp_at h' [SkaModel.Prod.toNoun, Tag.ir, Straight.toNoun, h1, h2, NeedOrd.toNoun,
            Tag.this, hl2, by.arm_at, by_arm, by.got.arm_at, got_arm, got_gate layer2 hnd _ _ _ hg,
            eval_blob.arm, eB, hreg, listNoun]
        | some y =>
          obtain ⟨r, m0, hm⟩ := hB cr' hc' _ _ _ _ _ _ _ eB
          refine ⟨r, Ev.succ ⟨m0, fun m hm' => ?_⟩⟩
          simp [SkaModel.interp, topBody, hb, e1, h1, h2, e2, hm m hm']

end

end Compiler
end Formalization
