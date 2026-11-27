import lemmas.Compiler.PokeLinkRestSeek

/-!
# The tail of `spRest` up to the jets

Pushes 10 to 13 and the end (`srK10`): `new-cores` (`srCores`), the edit of
`jets.lon` (`srJets = [10 [0x7fff4 srJetsF] [0 1]]`), the writes of `seek`
and `calls` (linked, `srSeek_run`, `srCalls_run`), and `srEnd`
(`[root-bell (flop new.regs)]` and `+ska-cole-update`).  `srK10_run`: the
tail is `srEnd` on the subject with the new jets `jE`, `calls` and `seek` of
`addCode code nc`.  `tailLinkAt_of`: **`TailLinkAt`** from the leaf
`TailEndAt` (the jets: `new-cores`, `srJetsF` and `srEnd` return the read
back `j'` with the rest of `lon` unchanged), on a subject whose `calls` and
`seek` are the old table's.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-- The value pushed at `jets.lon` by push 11: root, core, batt, arms from
`regs`, `pend` by `+uni-ju` with `new-cores`. -/
def srJetsF : Noun :=
  C (A 10) (C (C (A 62) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 1404) (C (A 0) (A 0xffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fffe9e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 30) (C (A 0) (A 0x1ffde))) (C (A 10) (C (C (A 14) (C (A 0) (A 0xffee))) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ff6))) (C (A 10) (C (C (A 2) (C (A 0) (A 0x3ffa))) (C (A 0) (A 0x7fff4)))))))))))

theorem srJets_eq : srJets = C (A 10) (C (C (A 0x7fff4) srJetsF) (C (A 0) (A 1))) := rfl

/-- The subject of push 10: `[sccs [new-code [baked spine]]]`. -/
noncomputable def srT10 (q ncN bkN g0 rN a b c d e e0 J mN cN caN vN sN hN : Noun) : Noun :=
  C q (C ncN (C bkN (srS3x g0 (srSk a b c d e (srSam e0 J mN cN caN vN sN hN)) rN)))

set_option maxHeartbeats 2000000 in
/-- **The tail up to `srEnd`**: once `new-cores` and the new jets are pushed,
the writes of `seek` and `calls` are those of `addCode code nc`. -/
theorem srK10_run (q bkN g0 rN a b c d e e0 J mN cN vN hN nco jE : Noun) (code nc : FinMap Bell (VarEntry FinMap))
    (hc : nock (srT10 q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN
      (code.toNoun fun e => FinMap.setNoun e.calls) vN (code.toNoun fun e => e.seek.toNoun) hN) srCores = some nco)
    (hj : nock (srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN
      (code.toNoun fun e => FinMap.setNoun e.calls) vN (code.toNoun fun e => e.seek.toNoun) hN) srJetsF = some jE) :
    nock (srT10 q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN
      (code.toNoun fun e => FinMap.setNoun e.calls) vN (code.toNoun fun e => e.seek.toNoun) hN) srK10 =
    nock (srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 jE mN cN
      ((addCode code nc).toNoun fun e => FinMap.setNoun e.calls) vN ((addCode code nc).toNoun fun e => e.seek.toNoun) hN)
      srEnd := by
  have h11 : nock (srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN
      (code.toNoun fun e => FinMap.setNoun e.calls) vN (code.toNoun fun e => e.seek.toNoun) hN) srJets =
      some (srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 jE mN cN
      (code.toNoun fun e => FinMap.setNoun e.calls) vN (code.toNoun fun e => e.seek.toNoun) hN) := by
    rw [srJets_eq]
    simp only [nock_exec, hj, Option.bind_some]
    simp [srTS, srS3x, srSk, srSam, nock_exec]
  have hs := srSeek_run nco q bkN g0 rN a b c d e e0 jE mN cN (code.toNoun fun e => FinMap.setNoun e.calls) vN
    (code.toNoun fun e => e.seek.toNoun) hN code nc rfl
  have hca := srCalls_run nco q bkN g0 rN a b c d e e0 jE mN cN (code.toNoun fun e => FinMap.setNoun e.calls) vN
    ((addCode code nc).toNoun fun e => e.seek.toNoun) hN code nc rfl
  simp only [srK10, srK11, srK12, srK13, srK14, nock_exec, hc, Option.bind_some]
  show ((nock (C nco _) srJets).bind fun s => (nock s srSeek).bind fun s' => (nock s' srCalls).bind fun s'' =>
    nock s'' srEnd) = _
  have e11 : C nco (srT10 q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN
      (code.toNoun fun e => FinMap.setNoun e.calls) vN (code.toNoun fun e => e.seek.toNoun) hN) =
      srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN
      (code.toNoun fun e => FinMap.setNoun e.calls) vN (code.toNoun fun e => e.seek.toNoun) hN := rfl
  rw [e11, h11, Option.bind_some, hs, Option.bind_some, hca, Option.bind_some]

section Parts

variable (root : Ident) (r1 r2 r3 r4 jRest codeN varsN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

/-- The tail's subject at `srK10` in the form of `TailLinkAt`, laid out. -/
noncomputable def srT10At (code : FinMap Bell (VarEntry FinMap)) (q ncN bkN c v : Noun) : Noun :=
  srT10 q ncN bkN
    (srS0 root r1 r2 r3 r4 jRest codeN (code.toNoun fun e => FinMap.setNoun e.calls) varsN
      (code.toNoun fun e => e.seek.toNoun) hotN gr r) (srRootN root r)
    (Treap.toNoun FDatum.toNoun r.2.1) r.2.2.2.1.toNoun (Treap.toNoun FDatum.toNoun r.1)
    (C (Treap.toNoun FDatum.toNoun gr.1) gr.2) (identNoun root) (identNoun root) (C r1 (C r2 (C r3 (C r4 jRest))))
    (memoNoun r.2.2.1) c (code.toNoun fun e => FinMap.setNoun e.calls) v (code.toNoun fun e => e.seek.toNoun) hotN

/-- **The leaf of the tail: the jets** (open; `new-cores` 54 cells with
`+turn` and `+gas:ju`, the edit `srJetsF` 45 cells with `+uni-ju`, and `srEnd`
45 cells with `+flop` and `+ska-cole-update`): on every `sccs` noun `q`,
`new-cores` and the new jets `jE` are pushed, and `srEnd` returns
`[[root-bell newN] [j' rest]]` with `rest` the `lon` it was given past its
jets.  `j'` is the read back of the jets. -/
def TailEndAt (fl : Flags) (code nc : FinMap Bell (VarEntry FinMap)) (bkN vr j' newN : Noun) : Prop :=
  ∀ q, ∃ nco jE,
    nock (srT10At root r1 r2 r3 r4 jRest codeN varsN hotN gr r code q (nc.toNoun varEntryNoun) bkN
      (codeNoun fl (addCode code nc)) vr) srCores = some nco ∧
    nock (C nco (srT10At root r1 r2 r3 r4 jRest codeN varsN hotN gr r code q (nc.toNoun varEntryNoun) bkN
      (codeNoun fl (addCode code nc)) vr)) srJetsF = some jE ∧
    nock (srTS nco q (nc.toNoun varEntryNoun) bkN
      (srS0 root r1 r2 r3 r4 jRest codeN (code.toNoun fun e => FinMap.setNoun e.calls) varsN
        (code.toNoun fun e => e.seek.toNoun) hotN gr r) (srRootN root r)
      (Treap.toNoun FDatum.toNoun r.2.1) r.2.2.2.1.toNoun (Treap.toNoun FDatum.toNoun r.1)
      (C (Treap.toNoun FDatum.toNoun gr.1) gr.2) (identNoun root) (identNoun root) jE
      (memoNoun r.2.2.1) (codeNoun fl (addCode code nc)) ((addCode code nc).toNoun fun e => FinMap.setNoun e.calls) vr
      ((addCode code nc).toNoun fun e => e.seek.toNoun) hotN) srEnd =
    some (C (C (srRootN root r) newN) (C j' (C (memoNoun r.2.2.1) (C (codeNoun fl (addCode code nc))
      (C ((addCode code nc).toNoun fun e => FinMap.setNoun e.calls)
        (C vr ((addCode code nc).toNoun fun e => e.seek.toNoun)))))))

/-- **`TailLinkAt` from the leaf of the jets**, on a subject whose `calls`
and `seek` are the nouns of the old table `code` (as in `enc`). -/
theorem tailLinkAt_of (fl : Flags) (code nc baked : FinMap Bell (VarEntry FinMap)) (vr j' newN : Noun)
    (hE : TailEndAt root r1 r2 r3 r4 jRest codeN varsN hotN gr r fl code nc (baked.toNoun varEntryNoun) vr j' newN) :
    TailLinkAt root r1 r2 r3 r4 jRest codeN (code.toNoun fun e => FinMap.setNoun e.calls) varsN
      (code.toNoun fun e => e.seek.toNoun) hotN gr r fl code nc baked vr j' newN := by
  intro q
  obtain ⟨nco, jE, h1, h2, h3⟩ := hE q
  have e : C q (C (nc.toNoun varEntryNoun) (C (baked.toNoun varEntryNoun)
      (srSp root r1 r2 r3 r4 jRest codeN (code.toNoun fun e => FinMap.setNoun e.calls) varsN
        (code.toNoun fun e => e.seek.toNoun) hotN gr r (codeNoun fl (addCode code nc)) vr))) =
      srT10At root r1 r2 r3 r4 jRest codeN varsN hotN gr r code q (nc.toNoun varEntryNoun) (baked.toNoun varEntryNoun)
        (codeNoun fl (addCode code nc)) vr := rfl
  rw [e]
  unfold srT10At at h1 h2 ⊢
  rw [srK10_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ code nc h1 h2]
  exact h3

end Parts

end Compiler
end Formalization
