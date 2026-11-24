import lemmas.Ska.WellFormedFacts

/-!
# `+run` after `fol-loop`, the graph's invariants, and convergence on the graph

A model of the datum construction at the end of `+run:ska-callgraph` (the
`=;` after `fol-loop`): `runDatum`.  The entry it writes satisfies `RunEntryM`
for the table of the run (`runDatum_entryM`), and keeps the product well
formed (`runDatum_wf`).

The graph's invariant `GraphWF` (every identity's subject sock and every
product is well formed) is kept by every write of `+ska-callgraph` to the
graph `g` (`GStep`): the `*datum` that `+analyze` puts under a new identity,
the datum of a run (`+run`), the `|+~` that `+pop` puts for a `%void`
product, a deletion (`+cull`), and a memo hit of `+analyze` patched for the
identity.  The identities that `+analyze` is called on are well formed:
the root `[&+sub fol]` of a `%dire` poke (`wf_yes`), a call read by a run
(`folLoopTop_wf`: a run reads the table only at well-formed subject socks),
and a `%he` generalization against a function in progress (`wf_msgSock`).

`AnswersS` is `Answers` with the `%he` partner a graph entry, as it is in
`+recursive-call`; from a well-formed graph its answers have well-formed
products (`answersS_wf`), which is what `folLoopTop_wf` asks of the table.

`codeOf` is the code table as `+ska-poke` builds it, a `put` per entry in
the order of `~(rep by pruned)`; it satisfies `CodeIs` and `CodeHas`.
`ConvergedGraph` says what the final graph gives, and
`agree_converged_graph` is `agree_at_convergence` from it.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## `+run` after `fol-loop` -/

/-- `+msg-ca`: where two capes disagree, `&`.  The cell is not normalized. -/
def msgCa : Cape → Cape → Cape
  | a, b =>
    if a = b then a else
    match a, b with
    | Cape.cell ah aT, Cape.cell bh bT => Cape.cell (msgCa ah bh) (msgCa aT bT)
    | _, _ => Cape.yes

/-- `dark` in `+run`: `?@(bus | cape.bus)`. -/
def darkOf : Sock → Cape
  | Sock.void => Cape.no
  | Sock.mk c _ => c

/-- What `+run` makes of the result of `fol-loop`, from the old datum `old`
of the identity `[bus fol]` and whether the identity is in `moved`: the new
datum, whether it joins `moved`, and `changed`.  `callees` and `area` are not
in `Datum`.  The code requirement is `want` united with the old entry's cape
before the mask (`(app:ca (uni:ca want old) bus)` with
`old=?@(less-code.data | cape.less-code.data)`, that is `darkOf old.less`),
so it only grows across the passes of a loop. -/
def runDatum (moved : Bool) (bus : Sock) (out : FolOut) (gen' : Gen) (old : Datum) :
    Datum × Bool × Bool :=
  let less := Ca.app (Ca.uni gen'.want (darkOf old.less)) bus
  let dark := darkOf bus
  let indi := Ca.lack gen'.indi dark
  let pm := mergeProd moved out.prod ⟨old.prod, old.map⟩
  let moved' := moved || (decide (old.prod ≠ Sock.void) && decide (pm ≠ ⟨old.prod, old.map⟩))
  let indi' :=
    if (less, pm.sock, pm.src) = (old.less, old.prod, old.map) ∧ indi ≠ old.indi then
      Ca.lack (msgCa indi old.indi) dark
    else indi
  let seek' :=
    if (less, pm.sock, pm.src, indi') = (old.less, old.prod, old.map, old.indi) ∧ gen'.seek ≠ old.seek then
      msgCa gen'.seek old.seek
    else gen'.seek
  let d : Datum := ⟨out.nomm, less, indi', seek', pm.sock, pm.src⟩
  (d, moved', decide ((d.less, d.prod, d.map, d.indi, d.seek) ≠ (old.less, old.prod, old.map, old.indi, old.seek)))

/-- **The entry that `+run` writes satisfies `RunEntryM`** for the table of
the run. -/
theorem runDatum_entryM {tab : Tab} {n : Nat} {bus : Sock} {fol : Noun} {out : FolOut} {gen' : Gen}
    (h : folLoopTop tab n bus fol = some (out, gen')) (moved : Bool) (old : Datum) :
    RunEntryM tab ⟨bus, fol, (runDatum moved bus out gen' old).1⟩ :=
  ⟨n, out, gen', moved, ⟨old.prod, old.map⟩, h, rfl, ⟨darkOf old.less, rfl⟩, rfl⟩

/-- **`+run` keeps the product well formed.** -/
theorem runDatum_wf {moved : Bool} {bus : Sock} {out : FolOut} {gen' : Gen} {old : Datum}
    (ho : WellFormed out.prod.sock) (hd : WellFormed old.prod) :
    WellFormed (runDatum moved bus out gen' old).1.prod :=
  wf_mergeProd moved (b := ⟨old.prod, old.map⟩) ho hd

/-! ## The graph and its writes -/

/-- The call graph `g`, as `+git-g` reads it. -/
abbrev Graph := Sock × Noun → Option Datum

/-- **The construction invariant**: every identity's subject sock and every
product in the graph is well formed. -/
def GraphWF (g : Graph) : Prop := ∀ i d, g i = some d → WellFormed i.1 ∧ WellFormed d.prod

/-- The graph with `i` set to `d`, as `~(put by g)`. -/
def Graph.put (g : Graph) (i : Sock × Noun) (d : Datum) : Graph :=
  fun j => if j = i then some d else g j

/-- The graph without `i`, as `~(del by g)`. -/
def Graph.del (g : Graph) (i : Sock × Noun) : Graph :=
  fun j => if j = i then none else g j

/-- The writes of `+ska-callgraph` to the graph, with what each needs:

* `start`: `+analyze` puts `*datum` under a new identity;
* `run`: `+run` puts the datum it makes from a run of `fol-loop` on the
  identity with the table `tab` of the run, whose answers at well-formed
  subject socks have well-formed products, from the identity's old datum;
* `pop`: `+pop` turns a `%void` product into `|+~`;
* `cull`: `+cull` deletes an identity;
* `memo`: `+analyze` puts a memo hit of `+git:mi`, patched for the
  identity, from a memo entry with a well-formed product. -/
inductive GStep : Graph → Graph → Prop where
  | start {g : Graph} {i : Sock × Noun} : WellFormed i.1 → GStep g (g.put i Datum.bunt)
  | run {g : Graph} {i : Sock × Noun} {tab : Tab} {n : Nat} {out : FolOut} {gen' : Gen}
      {moved : Bool} {old : Datum} :
      TabWF tab → folLoopTop tab n i.1 i.2 = some (out, gen') → g i = some old →
      GStep g (g.put i (runDatum moved i.1 out gen' old).1)
  | pop {g : Graph} {i : Sock × Noun} {d : Datum} : g i = some d →
      GStep g (g.put i (if d.prod = Sock.void then { d with prod := Sock.dunno } else d))
  | cull {g : Graph} {i : Sock × Noun} : GStep g (g.del i)
  | memo {g : Graph} {i : Sock × Noun} {d : Datum} : WellFormed i.1 → WellFormed d.prod →
      GStep g (g.put i (patchDatum d i.1))

theorem graphWF_put {g : Graph} {i : Sock × Noun} {d : Datum} (hg : GraphWF g) (hi : WellFormed i.1)
    (hd : WellFormed d.prod) : GraphWF (g.put i d) := by
  intro j e hj
  unfold Graph.put at hj
  split at hj
  · rename_i h; subst h; cases hj; exact ⟨hi, hd⟩
  · exact hg j e hj

/-- **Every write of `+ska-callgraph` keeps the construction invariant.** -/
theorem GStep.wf {g g' : Graph} (hs : GStep g g') (hg : GraphWF g) : GraphWF g' := by
  cases hs with
  | start hi => exact graphWF_put hg hi wf_void
  | run htab h ho =>
    obtain ⟨hi, hd⟩ := hg _ _ ho
    exact graphWF_put hg hi (runDatum_wf (folLoopTop_wf htab hi h).1 hd)
  | pop ho =>
    obtain ⟨hi, hd⟩ := hg _ _ ho
    refine graphWF_put hg hi ?_
    split
    · exact wf_dunno
    · exact hd
  | cull =>
    intro j e hj
    unfold Graph.del at hj
    split at hj
    · cases hj
    · exact hg j e hj
  | memo hi hd => exact graphWF_put hg hi (wf_patchDatum hd hi)

/-- A sequence of writes. -/
inductive GSteps : Graph → Graph → Prop where
  | refl (g : Graph) : GSteps g g
  | tail {g g' g'' : Graph} : GSteps g g' → GStep g' g'' → GSteps g g''

/-- **The invariant along any sequence of writes**, from a graph that keeps
it: the empty graph of a poke does. -/
theorem graphWF_steps {g g' : Graph} (hs : GSteps g g') (hg : GraphWF g) : GraphWF g' := by
  induction hs with
  | refl => exact hg
  | tail _ h ih => exact h.wf ih

theorem graphWF_empty : GraphWF (fun _ => none) := fun _ _ h => by cases h

/-- The root of a `%dire` poke, `[&+sub fol]`, is well formed. -/
theorem wf_root (sub : Noun) : WellFormed (Sock.mk Cape.yes sub) := wf_yes sub

/-! ## The answers of a run, from the graph -/

/-- `Answers` with the `%he` partner a graph entry, as in `+recursive-call`,
which generalizes against a function in progress (`i.stk`, in the graph). -/
inductive AnswersS (G : Entry → Prop) : Sock → Noun → TabEntry → Prop where
  | exact {e : Entry} : G e → AnswersS G e.more e.fol e.d.tab
  | hit {e : Entry} {s : Sock} : G e → hitTest e s = some true →
      AnswersS G s e.fol (patchDatum e.d s).tab
  | gen {s m : Sock} {e : Entry} {f : Noun} {a : TabEntry} : G e → msgSock s e.more = some m →
      AnswersS G m f a → AnswersS G s f a

theorem AnswersS.toAnswers {G : Entry → Prop} {s : Sock} {f : Noun} {a : TabEntry}
    (h : AnswersS G s f a) : Answers G s f a := by
  induction h with
  | exact he => exact Answers.exact he
  | hit he ht => exact Answers.hit he ht
  | gen _ hm _ ih => exact Answers.gen hm ih

/-- **From a well-formed graph, the answers at a well-formed subject sock
have well-formed products.** -/
theorem answersS_wf {G : Entry → Prop} (hG : ∀ e, G e → WellFormed e.more ∧ WellFormed e.d.prod)
    {s : Sock} {f : Noun} {a : TabEntry} (h : AnswersS G s f a) : WellFormed s → WellFormed a.prod := by
  induction h with
  | exact he => exact fun _ => (hG _ he).2
  | hit he _ => exact fun hs => wf_patchDatum (hG _ he).2 hs
  | gen he hm _ ih => exact fun hs => ih (wf_msgSock hs (hG _ he).1 hm)

theorem tabWF_of_answersS {G : Entry → Prop} {tab : Tab}
    (hG : ∀ e, G e → WellFormed e.more ∧ WellFormed e.d.prod)
    (hans : ∀ s f a, tab s f = some a → AnswersS G s f a) : TabWF tab :=
  fun s f a hs h => answersS_wf hG (hans s f a h) hs

/-! ## The code table of a poke -/

/-- The code table as `+ska-poke` builds `dats` from the graph: a `put`
under the bell `[less-code fol]` per entry, in the order of the list (that
of `~(rep by pruned)`), a later one replacing an earlier one. -/
def codeOf : List Entry → Bell → Option Nomm
  | [] => fun _ => none
  | e :: es => fun bl => if bl = ⟨e.d.less, e.fol⟩ then some e.d.nomm else codeOf es bl

theorem codeOf_is : ∀ (es : List Entry), CodeIs (codeOf es) (· ∈ es)
  | [], _, _, h => by cases h
  | e :: es, bl, nb, h => by
    unfold codeOf at h
    split at h
    · rename_i hb; cases h; exact ⟨e, by simp, hb, rfl⟩
    · obtain ⟨e', he', hb, hn⟩ := codeOf_is es bl nb h
      exact ⟨e', by simp [he'], hb, hn⟩

theorem codeOf_has : ∀ (es : List Entry), CodeHas (codeOf es) (· ∈ es)
  | [], _, h => by cases h
  | e :: es, e', h => by
    unfold codeOf
    split
    · exact ⟨_, rfl⟩
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · rename_i hb; exact absurd rfl hb
      · exact codeOf_has es e' h

/-! ## Convergence on the graph -/

/-- **What the final graph gives.**  `G` holds the entries of the final
graph, and also the version of a member of a component from before `+pop`
turned its `%void` product into `|+~` (its callers in the component read
that version in their last runs; `RunEntryM` holds of both, since a run
whose product is `%void` merges to whatever was there).  Every entry is
written by the last run on its identity (`runDatum_entryM`), with a table
whose every answer comes from `G`: the entry of the identity, a memo or
`%rec` hit patched for the call's subject sock, or a `%he` generalization
against an entry. -/
def ConvergedGraph (G : Entry → Prop) : Prop :=
  ∀ e, G e → ∃ tab, (∀ s f a, tab s f = some a → AnswersS G s f a) ∧ RunEntryM tab e

end SkaModel
end Formalization
