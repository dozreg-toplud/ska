  · -- the copy block
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [kc3])
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
    have hcf0 : ∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>
      (hcf1 k (by omega)).trans ((hq.cfr.get_lt hk).trans (by rw [hcnd]))
    have agC : Agree c g2 g3 := fun k h0 h1 => by
      rw [(ag st).1 k (by omega) h1 (fun hm => by have := labN k hm; omega)]
      exact fixC cf hcf k h0 h1
    obtain ⟨R1, hs1, hs1', u1, e1⟩ := CB d2 c agC lib σ O st regs t gul s hh
    have hned2 : ∀ r, NMem ned r → g2.re ≤ r := fun r hr => by have := hned r hr; omega
    have hned1 : ∀ r, NMem ned r → g1.re ≤ r := fun r hr => by have := hned r hr; omega
    have hn1 : HoldsN ned R1 s0 := HoldsN.agree _ (fun r hr => u1 r (fun hm => by
      have := lowP r hm; have := hned r hr; omega) (fun hm => by have := lowQ r hm; have := hned r hr; omega)) hn
    have agP : ∀ st' : σ, AgreeU lib O c gul st' t cf ned g1 g2 nexp.laz s0 s := fun st' =>
      (ag st').part (by omega) hp3 (fun e he => (memN e).mpr (Or.inl he))
        (fun k h0 h1 hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          rcases (memN e).mp he with a | a
          · exact List.mem_map_of_mem a
          · have := lq' e a; omega)
        (fun e he => (lp' e he).2)
    have agQ : ∀ st' : σ, AgreeU lib O c gul st' t cf ned g' g1 nexq.laz s0 s := fun st' =>
      (ag st').part bo01 Eq3 (fun e he => (memN e).mpr (Or.inr he))
        (fun k h0 h1 hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          rcases (memN e).mp he with a | a
          · have := lp' e a; omega
          · exact List.mem_map_of_mem a)
        (fun e he => (lq' e he).2)
    have agQ0 : Agree c g0 g' := fun k h0 h1 => by
      rw [(ag st).1 k h0 (by omega) (fun hm => by have := labN k hm; omega), E'3.2.2.2 k h1]
      exact hfix cf hcf0 k h0 h1
    -- the kept registers
    have nlpK : ∀ r, (r < g0.re ∨ NMem ned r) → ¬ NMem sur.ned r → ¬ NMem lp.ned r := fun r k1 k2 hm => by
      rcases hlp r hm with b | ⟨b, b'⟩
      · exact k2 b
      · rcases k1 with k1 | k1
        · omega
        · have := hned r k1; omega
    have keep1 : ∀ r, (r < g0.re ∨ NMem ned r) → ¬ NMem sur.ned r →
        SkaModel.read r R1 = SkaModel.read r regs := by
      intro r k1 k2
      refine u1 r (fun hm => ?_) (fun hm => ?_)
      · rcases mp r hm with a | ⟨a, a'⟩
        · exact nlpK r k1 k2 a
        · rcases k1 with k1 | k1
          · omega
          · have := hned r k1; omega
      · rcases mq r hm with a | ⟨a, a'⟩
        · rcases hlq r a with b | ⟨b, b'⟩
          · exact k2 b
          · rcases k1 with k1 | k1
            · omega
            · have := hned r k1; omega
        · rcases k1 with k1 | k1
          · omega
          · have := hned r k1; omega
    -- the head runs first
    obtain ⟨n', rh, hn', hmh, hr⟩ := minkF_consC hfh Mq hs hm
    have Hp := hp.sem cf hcf2 c ned σ Inv ν O n' gul hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm
      s0 s rh hI htr hs hmh agP hned2 R1 hs1 hn1
    rcases hr with ⟨hnz, rfl⟩ | ⟨x, rfl, hq'⟩
    · exact goalSemCM_ret _ _ hnz (returnsC_step (Needs.le_refl _) e1 (returnsC_of_goalSemCM _ _ hnz Hp))
    by_cases fx : FitsS lp x
    · obtain ⟨st', R2, hI', hν, hl2, k2, e2⟩ := Hp.1 fx
      have htr' := frames_mono hν htr
      have hq2 : HoldsS nexq.laz.sure R2 s := by
        refine ⟨HoldsN.agree _ (fun r hr => k2 r ⟨Or.inl (lowQ r hr), ?_⟩) hs1'.1, hs1'.2⟩
        intro hm
        rcases mq r hr with a | ⟨a, _⟩
        · exact hpq r hm a
        · have := lpl r hm; omega
      have hn2 : HoldsN ned R2 s0 := HoldsN.agree _ (fun r hr => k2 r ⟨Or.inr hr, fun hm => by
        have := lpl r hm; have := hned r hr; omega⟩) hn1
      have keep2 : ∀ r, (r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r →
          SkaModel.read r R2 = SkaModel.read r regs := fun r hk => by
        obtain ⟨k1, k2'⟩ := hk
        rw [k2 r ⟨k1.imp (fun h => by omega) id, nlpK r k1 k2'⟩, keep1 r k1 k2']
      have Hq := hq.sem cf hcf1 c ned σ O st' t gul s0 s (agQ st') hned1 R2 hq2 hn2
      rcases hq' with ⟨eq, rfl⟩ | ⟨y, eq, rfl⟩
      · rw [eq] at Hq
        exact ⟨Tone.two t, st', hI', hν, e1.trans (e2.trans Hq), ToneRel.two htr'⟩
      rw [eq] at Hq
      by_cases fy : FitsS lq y
      · obtain ⟨R3, hq3, k3, e3⟩ := Hq.1 fy
        have hl3 : HoldsN lp.ned R3 x :=
          HoldsN.agree _ (fun r hr => k3 r ⟨Or.inl (lpl r hr), hpq r hr⟩) hl2
        have B := hblk c agQ0 σ O st' R3 t gul x y fx fy hl3 hq3
        have G : GoalSem lib O c gul st' (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) R2 t nexq.th
            (CGoal.next sur th) (some (C x y)) := by
          refine GoalSem.transfer e3 (fun r hk => ?_)
            (GoalSem.mono (fun r ⟨k1, k2⟩ => ⟨k1.imp id (fun h => by have := hned r h; omega), k2⟩) B)
          obtain ⟨k1, k2'⟩ := hk
          have nlq : ¬ NMem lq.ned r := fun hm => by
            rcases hlq r hm with b | ⟨b, b'⟩
            · exact k2' b
            · rcases k1 with k1 | k1
              · omega
              · have := hned r k1; omega
          exact k3 r ⟨k1.imp (fun h => by omega) id, nlq⟩
        exact goalSemCM_step hν keep2 (e1.trans e2) _ _ (goalSemC_of_goalSem hI' htr' _ _ G)
      · exact ⟨fun hf => absurd hf (hnot x y (Or.inr fy)),
          fun _ => ⟨Tone.two t, st', hI', hν, e1.trans (e2.trans (Hq.2 fy)), ToneRel.two htr'⟩⟩
    · have Rc := returnsC_step (Needs.le_refl _) e1 (Hp.2 fx)
      rcases hq' with ⟨_, rfl⟩ | ⟨y, _, rfl⟩
      · exact Rc
      · exact ⟨fun hf => absurd hf (hnot x y (Or.inl fx)), fun _ => Rc⟩
