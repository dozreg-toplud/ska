import lemmas.Compiler.CompMapRegs
import lemmas.Compiler.SkaCull
import lemmas.Hoon.Ju
import lemmas.Ska.OptDriver

/-!
# The pill link of the optimizer: the core, the keys, the nouns

The optimizer's arms are those of the `|%` core `optC` at axis `31` of `cor`
(`optC_at`): its battery `nh58984ad6cdbd` on the payload `compK`, the core
of the compiler.  The small helpers (`+get-jmps`, `+get-regs`, ...) are arms
of `compTypes`, at axis `7` of `optC` (`optC_types`).  `layer2`, the library
core with `+by`, `+in`, `+roll`, ..., is at axis `0x1ffff` of `optC`
(`optC_layer2`).

* `Opt.MapKeys (TreapMap mugF)`: the keys in the order in which `+rep:by`
  visits them (`TreapMap.rap`, pre-order), with `nodup` from the strict
  `+gor` order of `TreapMap.tap` (`tap_pairwise`), of which `rap` is a
  permutation (`Tr.pre_perm`).  Every `+rep:by` of a pass is a fold over
  these keys in its model.
* The nouns of the IR are injective (`blob_toNoun_inj`, `termin_toNoun_inj`,
  `pole_toNoun_inj`, `jmp_toNoun_inj`), by decoders that undo them
  (`blobDec_toNoun`, ...).  The Hoon compares blobs and terminators as nouns
  (`=(nex-z nex-o)` and `!=(new-fin fin.b)` of `+remove-useless-branching`),
  the models as values.
* `NoLti bl`: no block ends in `%lti`.  `+get-jmps` and `+get-regs` give `~`
  on `%lti` where `getJmps` and `finRegs` do not, so the links of the passes
  that run them on terminators take it; every pass before `+switch-chains`
  meets only blocks without `%lti`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The core -/

/-- The optimizer's core: its battery on `compK`. -/
def optC : Noun := C nh58984ad6cdbd compK

/-- `optC` is at axis `31` of `cor`. -/
theorem optC_at : slot? 31 cor = some optC := by kernel_rfl

theorem optC_compK : slot? 3 optC = some compK := rfl

theorem optC_types : slot? 7 optC = some compTypes := rfl

theorem optC_layer2 : slot? 0x1ffff optC = some layer2 := by
  have h : slot? 3 optC = slot? 1 compK := rfl
  have := slot_spine (by omega) (by omega) h 15
  simp only [show 2 ^ 15 * (3 + 1) - 1 = 0x1ffff from rfl,
    show 2 ^ 15 * (1 + 1) - 1 = 65535 from rfl] at this
  rw [this]
  exact compK_layer2

/-! ## The keys of a treap in the order of `+rep:by` -/

namespace Tr

variable {ν : Type}

/-- The pre-order of `+rep` is a permutation of the order of `+tap`. -/
theorem pre_perm : ∀ t : Tr ν, (t.pre).Perm t.tapL
  | nil => List.Perm.nil
  | node k v l r => by
    simp only [pre, tapL]
    have hl := pre_perm l
    have hr := pre_perm r
    refine List.Perm.trans (List.Perm.cons _ (List.Perm.append hl hr)) ?_
    refine List.Perm.trans (List.Perm.cons _ List.perm_append_comm) ?_
    exact List.perm_middle.symm

end Tr

theorem rap_keys_nodup {ν : Type} (m : TreapMap mugF ν) : ((TreapMap.rap m).map Prod.fst).Nodup := by
  have hp : ((TreapMap.rap m).map Prod.fst).Perm ((TreapMap.tap m).map Prod.fst) :=
    (Tr.pre_perm m.1).map Prod.fst
  rw [hp.nodup_iff, List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (TreapMap.tap_pairwise m).imp fun h => h.1

/-- **The keys of the optimizer's models on treaps**: those of `rap`, the
order of `+rep:by`. -/
instance optMapKeys : Opt.MapKeys (TreapMap mugF) where
  keys m := (TreapMap.rap m).map Prod.fst
  mem_keys m k := by
    constructor
    · intro hk
      obtain ⟨⟨k', v⟩, hm, rfl⟩ := List.mem_map.1 hk
      show (TreapMap.get m k').isSome = true
      rw [(TreapMap.mem_rap m k' v).1 hm]
      rfl
    · intro hk
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hk
      exact List.mem_map.2 ⟨(k, v), (TreapMap.mem_rap m k v).2 hv, rfl⟩
  nodup m := rap_keys_nodup m

theorem optKeys_eq {ν : Type} (m : TreapMap mugF ν) :
    Opt.MapKeys.keys m = (TreapMap.rap m).map Prod.fst := rfl

/-- A fold over the keys that looks each key up is a fold over the pairs of
`rap`. -/
theorem foldl_keys_rap {ν σ : Type} (m : TreapMap mugF ν) (g : σ → Nat → ν → Option σ) :
    ∀ (L : List (Nat × ν)), (∀ p ∈ L, HoonMap.get m p.1 = some p.2) → ∀ (acc : Option σ),
    (L.map Prod.fst).foldl (fun acc k => acc.bind fun s => (HoonMap.get m k).bind fun v => g s k v) acc
      = acc.bind fun s => L.foldlM (fun s p => g s p.1 p.2) s
  | [], _, acc => by cases acc <;> rfl
  | p :: L, hL, acc => by
    have hp := hL p (by simp)
    have ih := foldl_keys_rap m g L (fun q hq => hL q (by simp [hq]))
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    cases acc with
    | none => rfl
    | some a => simp only [Option.bind_some, hp, List.foldlM_cons]; cases g a p.1 p.2 <;> rfl

theorem rap_get {ν : Type} (m : TreapMap mugF ν) : ∀ p ∈ TreapMap.rap m, HoonMap.get m p.1 = some p.2 :=
  fun p hp => by rw [hoonMap_get]; exact (TreapMap.mem_rap m p.1 p.2).1 hp

/-! ## Decoders of the nouns of the IR -/

namespace OptDec

/-- The atom of an atom, `0` of a cell. -/
def atomOf : Noun → Nat
  | Noun.atom n => n
  | _ => 0

/-- The head of a cell. -/
def hd : Noun → Noun
  | Noun.cell h _ => h
  | x => x

/-- The tail of a cell. -/
def tl : Noun → Noun
  | Noun.cell _ t => t
  | x => x

def listDec {α : Type} (f : Noun → α) : Noun → List α
  | Noun.cell h t => f h :: listDec f t
  | _ => []

theorem listDec_listNoun {α : Type} (f : Noun → α) (g : α → Noun) (h : ∀ x, f (g x) = x) :
    ∀ l : List α, listDec f (listNoun g l) = l
  | [] => rfl
  | x :: l => by simp [listNoun, listDec, h, listDec_listNoun f g h l]

def unitDec {α : Type} (f : Noun → α) : Noun → Option α
  | Noun.cell _ v => some (f v)
  | _ => Option.none

theorem unitDec_unitNoun {α : Type} (f : Noun → α) (g : α → Noun) (h : ∀ x, f (g x) = x) :
    ∀ u : Option α, unitDec f (unitNoun g u) = u
  | Option.none => rfl
  | Option.some x => by simp [unitNoun, unitDec, h]

def capeDec : Noun → Cape
  | Noun.atom 1 => Cape.no
  | Noun.cell h t => Cape.cell (capeDec h) (capeDec t)
  | _ => Cape.yes

theorem capeDec_toNoun : ∀ c : Cape, capeDec c.toNoun = c
  | Cape.yes => rfl
  | Cape.no => rfl
  | Cape.cell h t => by simp [Cape.toNoun, capeDec, capeDec_toNoun h, capeDec_toNoun t]

def sockDec : Noun → Sock
  | Noun.cell c d => Sock.mk (capeDec c) d
  | _ => Sock.void

theorem sockDec_toNoun : ∀ s : Sock, sockDec s.toNoun = s
  | Sock.void => rfl
  | Sock.mk c d => by simp [Sock.toNoun, sockDec, capeDec_toNoun]

def bellDec (n : Noun) : Bell := ⟨sockDec (hd n), tl n⟩

theorem bellDec_toNoun (b : Bell) : bellDec b.toNoun = b := by
  simp [bellDec, Bell.toNoun, hd, tl, sockDec_toNoun]

def ringDec (n : Noun) : Ring := ⟨listDec atomOf (hd n), atomOf (tl n)⟩

theorem ringDec_toNoun (r : Ring) : ringDec r.toNoun = r := by
  simp [ringDec, Ring.toNoun, hd, tl, atomOf, listDec_listNoun atomOf A (fun _ => rfl)]

def jmpDec (n : Noun) : Jmp := ⟨listDec (unitDec atomOf) (hd n), atomOf (tl n)⟩

theorem jmpDec_toNoun (j : Jmp) : jmpDec j.toNoun = j := by
  simp [jmpDec, Jmp.toNoun, hd, tl, atomOf,
    listDec_listNoun (unitDec atomOf) (unitNoun A) (unitDec_unitNoun atomOf A (fun _ => rfl))]

/-- The op of a noun, by its tag. -/
def poleDec (n : Noun) : Pole :=
  let t := atomOf (hd n)
  let r := tl n
  if t = Tag.imm then Pole.imm (hd r) (atomOf (tl r))
  else if t = Tag.mov then Pole.mov (atomOf (hd r)) (atomOf (tl r))
  else if t = Tag.inc then Pole.inc (atomOf (hd r)) (atomOf (tl r))
  else if t = Tag.con then Pole.con (atomOf (hd r)) (atomOf (hd (tl r))) (atomOf (tl (tl r)))
  else if t = Tag.hed then Pole.hed (atomOf (hd r)) (atomOf (tl r))
  else if t = Tag.tal then Pole.tal (atomOf (hd r)) (atomOf (tl r))
  else if t = Tag.cel then Pole.cel (atomOf r)
  else if t = Tag.lob then Pole.lob (atomOf r)
  else if t = Tag.equ then Pole.equ (atomOf (hd r)) (atomOf (tl r))
  else if t = Tag.hsp then Pole.hsp (atomOf (hd r)) (tl r)
  else if t = Tag.hse then Pole.hse (atomOf (hd r)) (tl r)
  else if t = Tag.hdp then Pole.hdp (atomOf (hd r)) (atomOf (hd (tl r))) (tl (tl r))
  else if t = Tag.hde then Pole.hde (atomOf (hd r)) (atomOf (hd (tl r))) (tl (tl r))
  else if t = Tag.hmp then Pole.hmp (bellDec (hd r)) (listDec atomOf (hd (tl r))) (tl (tl r))
  else if t = Tag.hme then Pole.hme (bellDec (hd r)) (listDec atomOf (hd (tl r))) (tl (tl r))
  else if t = Tag.hcp then Pole.hcp (hd r) (tl r)
  else if t = Tag.hce then Pole.hce (hd r) (tl r)
  else if t = Tag.spy then Pole.spy (atomOf (hd r)) (atomOf (hd (tl r))) (atomOf (tl (tl r)))
  else if t = Tag.nok then Pole.nok (atomOf (hd r)) (atomOf (hd (tl r))) (atomOf (tl (tl r)))
  else if t = Tag.cal then Pole.cal (bellDec (hd r)) (listDec atomOf (hd (tl r))) (atomOf (tl (tl r)))
  else if t = Tag.caf then Pole.caf (bellDec (hd r)) (listDec atomOf (hd (tl r)))
    (atomOf (hd (tl (tl r)))) (ringDec (tl (tl (tl r))))
  else if t = Tag.cam then Pole.cam (bellDec (hd r)) (listDec atomOf (hd (tl r)))
    (atomOf (hd (tl (tl r)))) (tl (tl (tl r)))
  else if t = Tag.csl then Pole.csl (bellDec (hd r)) (atomOf (hd (tl r))) (atomOf (tl (tl r)))
  else if t = Tag.csf then Pole.csf (bellDec (hd r)) (atomOf (hd (tl r))) (atomOf (hd (tl (tl r))))
    (ringDec (tl (tl (tl r))))
  else Pole.csm (bellDec (hd r)) (atomOf (hd (tl r))) (atomOf (hd (tl (tl r)))) (tl (tl (tl r)))

theorem poleDec_toNoun (p : Pole) : poleDec p.toNoun = p := by
  have hl := listDec_listNoun atomOf A (fun _ => rfl)
  cases p <;> simp [poleDec, Pole.toNoun, hd, tl, atomOf, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed,
    Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp,
    Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm, bellDec_toNoun,
    ringDec_toNoun, hl]

/-- The terminator of a noun, by its tag. -/
def terminDec (n : Noun) : Termin :=
  let t := atomOf (hd n)
  let r := tl n
  if t = Tag.clq then Termin.clq (atomOf (hd r)) (jmpDec (hd (tl r))) (jmpDec (tl (tl r)))
  else if t = Tag.eqq then Termin.eqq (atomOf (hd r)) (atomOf (hd (tl r))) (jmpDec (hd (tl (tl r))))
    (jmpDec (tl (tl (tl r))))
  else if t = Tag.brn then Termin.brn (atomOf (hd r)) (jmpDec (hd (tl r))) (jmpDec (tl (tl r)))
  else if t = Tag.brz then Termin.brz (atomOf (hd r)) (jmpDec (hd (tl r))) (jmpDec (tl (tl r)))
  else if t = Tag.hop then Termin.hop (jmpDec r)
  else if t = Tag.jmp then Termin.jmp (bellDec (hd r)) (listDec atomOf (tl r))
  else if t = Tag.jmf then Termin.jmf (bellDec (hd r)) (listDec atomOf (hd (tl r))) (ringDec (tl (tl r)))
  else if t = Tag.jsp then Termin.jsp (bellDec (hd r)) (atomOf (tl r))
  else if t = Tag.jsf then Termin.jsf (bellDec (hd r)) (atomOf (hd (tl r))) (ringDec (tl (tl r)))
  else if t = Tag.don then Termin.don (atomOf r)
  else if t = Tag.bom then Termin.bom (unitDec atomOf r)
  else Termin.lti (atomOf (hd r)) (atomOf (hd (tl r))) (jmpDec (hd (tl (tl r)))) (jmpDec (tl (tl (tl r))))

theorem terminDec_toNoun (t : Termin) : terminDec t.toNoun = t := by
  have hl := listDec_listNoun atomOf A (fun _ => rfl)
  have hu := unitDec_unitNoun atomOf A (fun _ => rfl)
  cases t <;> simp [terminDec, Termin.toNoun, hd, tl, atomOf, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop,
    Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, bellDec_toNoun, ringDec_toNoun,
    jmpDec_toNoun, hl, hu]

def blobDec (n : Noun) : Blob := ⟨listDec atomOf (hd n), listDec poleDec (hd (tl n)), terminDec (tl (tl n))⟩

theorem blobDec_toNoun (b : Blob) : blobDec b.toNoun = b := by
  simp [blobDec, Blob.toNoun, hd, tl, listDec_listNoun atomOf A (fun _ => rfl),
    listDec_listNoun poleDec Pole.toNoun poleDec_toNoun, terminDec_toNoun]

end OptDec

open OptDec

theorem jmp_toNoun_inj {a b : Jmp} : a.toNoun = b.toNoun ↔ a = b :=
  ⟨fun h => by rw [← jmpDec_toNoun a, h, jmpDec_toNoun], fun h => h ▸ rfl⟩

theorem pole_toNoun_inj {a b : Pole} : a.toNoun = b.toNoun ↔ a = b :=
  ⟨fun h => by rw [← poleDec_toNoun a, h, poleDec_toNoun], fun h => h ▸ rfl⟩

theorem termin_toNoun_inj {a b : Termin} : a.toNoun = b.toNoun ↔ a = b :=
  ⟨fun h => by rw [← terminDec_toNoun a, h, terminDec_toNoun], fun h => h ▸ rfl⟩

theorem blob_toNoun_inj {a b : Blob} : a.toNoun = b.toNoun ↔ a = b :=
  ⟨fun h => by rw [← blobDec_toNoun a, h, blobDec_toNoun], fun h => h ▸ rfl⟩

/-! ## Sets of registers or labels -/

/-- The noun `S` is a set of atoms, the members of `l`. -/
def SawRel (S : Noun) (l : List Nat) : Prop := IsSet mugF S ∧ ∀ k, Has S k ↔ ∃ n ∈ l, k = A n

theorem SawRel.has_atom {S : Noun} {l : List Nat} (h : SawRel S l) (k : Nat) : Has S (A k) ↔ k ∈ l := by
  rw [h.2]
  constructor
  · rintro ⟨n, hn, e⟩; cases e; exact hn
  · intro hk; exact ⟨k, hk, rfl⟩

theorem sawRel_nil : SawRel (A 0) [] := ⟨isSet_nil, fun k => by simp [uni_has_nil]⟩

/-- A set of atoms is `~` exactly when it has no member. -/
theorem SawRel.eq_nil {S : Noun} {l : List Nat} (h : SawRel S l) : S = A 0 ↔ l = [] := by
  constructor
  · rintro rfl
    cases l with
    | nil => rfl
    | cons n l => exact absurd ((h.has_atom n).2 (by simp)) not_has_atom
  · rintro rfl
    exact isSet_ext h.1 isSet_nil (fun k => by rw [h.2]; simp [uni_has_nil])

/-- `+has:in` of a register on `saw`. -/
theorem saw_has {S : Noun} {l : List Nat} (h : SawRel S l) (d : Nat) :
    nock (C in.has.battery (C (A d) (C in.battery (C S layer2)))) in.has.battery
      = some (loob (decide (d ∈ l))) := by
  obtain ⟨t, ht, hiff⟩ := hasInF_spec mugF S (A d) h.1
  rw [has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 (A d) S t ht]
  congr 2
  rw [h.has_atom d] at hiff
  cases t <;> simp_all

/-- `+gas:in` of a list of registers on `saw`. -/
theorem saw_gas {S : Noun} {l : List Nat} (h : SawRel S l) (regs : List Nat) :
    ∃ S', nock (C in.gas.battery (C (listNoun A regs) (C in.battery (C S layer2)))) in.gas.battery = some S' ∧
      SawRel S' (regs ++ l) := by
  obtain ⟨out, ho, hs, hh⟩ := gasInF_spec (mug := mugF) (regs.map A) S h.1
  refine ⟨out, ?_, hs, fun k => ?_⟩
  · rw [listNoun_map_listN]; exact gas_in_gate _ S out ho
  · rw [hh, h.2 k]
    constructor
    · rintro (hk | ⟨n, hn, rfl⟩)
      · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hk
        exact ⟨n, List.mem_append_left _ hn, rfl⟩
      · exact ⟨n, List.mem_append_right _ hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      rcases List.mem_append.1 hn with hn | hn
      · exact Or.inl (List.mem_map.2 ⟨n, hn, rfl⟩)
      · exact Or.inr ⟨n, hn, rfl⟩

/-- `+put:in` of a label on `saw`. -/
theorem saw_put {S : Noun} {l : List Nat} (h : SawRel S l) (o : Nat) :
    ∃ S', nock (C in.put.battery (C (A o) (C in.battery (C S layer2)))) in.put.battery = some S' ∧
      SawRel S' (o :: l) := by
  obtain ⟨out, hp, hs, hh⟩ := putInF_spec mugF S (A o) h.1
  refine ⟨out, put_in_gate layer2 gorIn_morIn_layer2 (A o) S out hp, hs, fun k => ?_⟩
  rw [hh, h.2 k]
  constructor
  · rintro (rfl | ⟨n, hn, rfl⟩)
    · exact ⟨o, List.mem_cons_self, rfl⟩
    · exact ⟨n, List.mem_cons_of_mem _ hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    rcases List.mem_cons.1 hn with rfl | hn
    · exact Or.inl rfl
    · exact Or.inr ⟨n, hn, rfl⟩

/-! ## Folds -/

/-- A fold over the keys of a treap, each looked up, is a fold over `rap`. -/
theorem foldl_keys_rap' {ν σ : Type} (st : σ → Nat → σ) (g : σ → Nat → ν → σ) :
    ∀ (L : List (Nat × ν)), (∀ p ∈ L, ∀ acc, st acc p.1 = g acc p.1 p.2) → ∀ acc : σ,
    (L.map Prod.fst).foldl st acc = L.foldl (fun acc p => g acc p.1 p.2) acc
  | [], _, _ => rfl
  | p :: L, h, acc => by
    simp only [List.map_cons, List.foldl_cons]
    rw [h p (by simp) acc]
    exact foldl_keys_rap' st g L (fun q hq => h q (by simp [hq])) _

theorem foldlM_some {α σ : Type} (f : σ → α → σ) : ∀ (L : List α) (s : σ),
    L.foldlM (fun s p => some (f s p)) s = some (L.foldl f s)
  | [], _ => rfl
  | p :: L, s => by simp only [List.foldlM_cons, List.foldl_cons, Option.bind_some]; exact foldlM_some f L _

/-- **`+roll` with a gate that may crash, over a list of values**: the loop
on `listN (L.map pn)` from the accumulator `toN s`, where the gate on `pn p`
and `toN s` is `(gf p s).map toN`, is `foldlM` of `gf`. -/
theorem roll_loop_list {α σ : Type} (pn : α → Noun) (toN : σ → Noun) (gf : α → σ → Option σ)
    (c bp e bc : Noun) : ∀ (L : List α) (s : σ),
    (∀ p ∈ L, ∀ s, nock (C bp (C (C (pn p) (toN s)) bc)) bp = (gf p s).map toN) →
    nock (C roll.loop (C roll.battery (C (C (listN (L.map pn)) (C bp (C (C e (toN s)) bc))) c))) roll.loop
      = (L.foldlM (fun s p => gf p s) s).map toN := by
  intro L
  induction L with
  | nil =>
    intro s _
    nock_open roll.loop
    simp [nock_exec]
  | cons p L ih =>
    intro s hf
    have hp := hf p (by simp) s
    nock_open roll.loop
    cases e1 : gf p s with
    | none => simp [nock_exec, hp, e1]
    | some s' =>
      have hl := ih s' (fun q hq => hf q (by simp [hq]))
      simp [nock_exec, hp, e1, hl]

theorem roll_gate_list {α σ : Type} (pn : α → Noun) (toN : σ → Noun) (gf : α → σ → Option σ)
    (c bp e bc : Noun) (L : List α) (s : σ)
    (hf : ∀ p ∈ L, ∀ s, nock (C bp (C (C (pn p) (toN s)) bc)) bp = (gf p s).map toN) :
    nock (C roll.battery (C (C (listN (L.map pn)) (C bp (C (C e (toN s)) bc))) c)) roll.battery
      = (L.foldlM (fun s p => gf p s) s).map toN := by
  nock_open roll.battery
  simp only [nock_exec, roll_loop_list pn toN gf c bp e bc L s hf]

/-- **`+roll` with a gate that may crash, against a relation**: the noun
of the accumulator is related to the model's state by `R`, and the gate on
`pn p` and a related noun returns a noun related to `gf p s`.  For loops
whose accumulator holds a set, whose noun the model does not fix. -/
theorem roll_loop_rel {α σ : Type} (pn : α → Noun) (R : Noun → σ → Prop) (gf : α → σ → Option σ)
    (c bp e bc : Noun) : ∀ (L : List α) (s : σ) (N : Noun) (r : σ),
    (∀ p ∈ L, ∀ s N s', R N s → gf p s = some s' →
      ∃ N', nock (C bp (C (C (pn p) N) bc)) bp = some N' ∧ R N' s') →
    R N s → L.foldlM (fun s p => gf p s) s = some r →
    ∃ N', nock (C roll.loop (C roll.battery (C (C (listN (L.map pn)) (C bp (C (C e N) bc))) c))) roll.loop
      = some N' ∧ R N' r := by
  intro L
  induction L with
  | nil =>
    intro s N r _ hR hr
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hr
    subst hr
    refine ⟨N, ?_, hR⟩
    nock_open roll.loop
    simp [nock_exec]
  | cons p L ih =>
    intro s N r hf hR hr
    simp only [List.foldlM_cons] at hr
    cases e1 : gf p s with
    | none => rw [e1] at hr; cases hr
    | some s1 =>
      rw [e1] at hr
      change L.foldlM (fun s p => gf p s) s1 = some r at hr
      obtain ⟨N1, h1, hR1⟩ := hf p (by simp) s N s1 hR e1
      obtain ⟨N2, h2, hR2⟩ := ih s1 N1 r (fun q hq => hf q (by simp [hq])) hR1 hr
      refine ⟨N2, ?_, hR2⟩
      nock_open roll.loop
      simp [nock_exec, h1, h2]

theorem roll_gate_rel {α σ : Type} (pn : α → Noun) (R : Noun → σ → Prop) (gf : α → σ → Option σ)
    (c bp e bc : Noun) (L : List α) (s : σ) (N : Noun) (r : σ)
    (hf : ∀ p ∈ L, ∀ s N s', R N s → gf p s = some s' →
      ∃ N', nock (C bp (C (C (pn p) N) bc)) bp = some N' ∧ R N' s')
    (hR : R N s) (hr : L.foldlM (fun s p => gf p s) s = some r) :
    ∃ N', nock (C roll.battery (C (C (listN (L.map pn)) (C bp (C (C e N) bc))) c)) roll.battery
      = some N' ∧ R N' r := by
  obtain ⟨N', h, hR'⟩ := roll_loop_rel pn R gf c bp e bc L s N r hf hR hr
  refine ⟨N', ?_, hR'⟩
  nock_open roll.battery
  simp only [nock_exec, h]

/-! ## Jars -/

theorem juIn_layer2' : JuIn mugF layer2 :=
  ⟨by.arm_at, in.arm_at, someIn_layer2, gorIn_morIn_layer2.1, gorIn_morIn_layer2.2⟩

/-- `+add:ja` on the noun of a jar of labels: `addJa`. -/
theorem jar_add (m : TreapMap mugF (List Nat)) (k o : Nat) :
    nock (C ja.add.battery (C (C (A k) (A o)) (C ja.battery (C (HoonMap.toNoun (listNoun A) m) layer2))))
      ja.add.battery = some (HoonMap.toNoun (listNoun A) (Opt.addJa m k o)) := by
  apply ja_add_gate layer2 juIn_layer2'
  have hg := getF_hoonMap (listNoun A) m k
  have hp := putF_hoonMap (listNoun A) m k (o :: (HoonMap.get m k).getD [])
  unfold jaAddF juGetF Opt.addJa
  rw [hg]
  cases e : HoonMap.get m k with
  | none => rw [e] at hp; simpa [unitNoun, unUnit, listNoun] using hp
  | some l => rw [e] at hp; simpa [unitNoun, unUnit, listNoun] using hp

/-- `+get:ja` on the noun of a jar of labels: `getJa`. -/
theorem jar_get (m : TreapMap mugF (List Nat)) (k : Nat) :
    nock (C ju.get.battery (C (A k) (C ja.battery (C (HoonMap.toNoun (listNoun A) m) layer2))))
      ju.get.battery = some (listNoun A (Opt.getJa m k)) := by
  have hg := getF_hoonMap (listNoun A) m k
  rw [ju_get_gate layer2 juIn_layer2' ja.battery (A k) _ _ hg]
  unfold Opt.getJa
  cases HoonMap.get m k <;> rfl

/-! ## `+got:by` on blocks -/

/-- `+got:by` on the noun of a treap of blocks: the noun of the block, and a
crash where there is none. -/
theorem blocks_got (bl : TreapMap mugF Blob) (k : Nat) :
    nock (C by.got.battery (C (A k) (C by.battery (C (HoonMap.toNoun Blob.toNoun bl) layer2)))) by.got.battery
      = (HoonMap.get bl k).map Blob.toNoun := by
  have hg := getF_hoonMap Blob.toNoun bl k
  cases e : HoonMap.get bl k with
  | none =>
    rw [e] at hg
    exact got_gate_nil (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ hg
  | some v =>
    rw [e] at hg
    exact got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ _ hg

/-! ## No `%lti` -/

/-- A terminator other than `%lti`, the terminators of `termin`. -/
def finPlain : Termin → Bool
  | Termin.lti _ _ _ _ => false
  | _ => true

/-- No block ends in `%lti`: blocks of the type `blob`. -/
def NoLti {Map : Type → Type} [HoonMap Map] (bl : Map Blob) : Prop :=
  ∀ o b, HoonMap.get bl o = some b → finPlain b.fin = true

end Compiler
end Formalization
