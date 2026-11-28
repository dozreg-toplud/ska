import lemmas.Glue.Assemble13
import lemmas.Glue.NskProxy
import lemmas.Compiler.CompSccLoopSoftLoop
import lemmas.Compiler.CompRunShapeTen
import lemmas.Ska.TarjanSound
import lemmas.Compiler.CompTarjanLeaf
import lemmas.Compiler.CompInlinedL4
import lemmas.Ska.CompGenTop
import lemmas.Ska.CompGenConsK
import lemmas.Ska.CompHintTenEx
import lemmas.Ska.PassGrow
import lemmas.Compiler.OptLinkTotalAvail
import lemmas.Ska.RawInvCLSABase
import lemmas.Ska.AnnotSDet

/-!
# Audit of the thirteenth pass (track G)

The assembly `gap13` and its records (`Glue/Assemble13.lean`), and the names
of other tracks that the LEDGER's thirteenth pass cites from digest [306] to
[315] (those in the tree at e4345c23).  A separate file from `AuditGlue.lean`
so that neither exceeds the 3500M cap of a single target.
-/

namespace Formalization

-- thirteenth pass, track G: THE ASSEMBLY
#check @SkaModel.Glue.Route13
#check @SkaModel.Glue.PokeLeaves13
#check @SkaModel.Glue.CompLeaves13
#check @SkaModel.Glue.ClassLeaves13
#check @SkaModel.Glue.HaltLeaves13
#check @SkaModel.Glue.FormatLeaves13
#check @Compiler.PokeOther13
#check @SkaModel.Glue.PlainCallsM
#check @SkaModel.Glue.PlainCallsN
#print axioms SkaModel.Glue.gap13
#print axioms SkaModel.Glue.full13
#print axioms SkaModel.Glue.gap13_fragX
#print axioms SkaModel.Glue.gap13_fragXPlain
#print axioms SkaModel.Glue.compHyp13
#print axioms SkaModel.Glue.classLeaves_or
#print axioms SkaModel.Glue.classLeaves_fragX
#print axioms SkaModel.Glue.classLeaves_plain
#print axioms Compiler.pokeModel_of_fullOther
#print axioms Compiler.monoLinkGood6_of_rest5
#print axioms Compiler.pokeModel_fullReachP6K
#print axioms Compiler.unaryFinish_of_rest5

-- thirteenth pass, track G: toward `NskEndC`
#check @SkaModel.Glue.SDW
#check @SkaModel.Glue.SDWEndC
#print axioms SkaModel.Glue.sdw_of_sds
#print axioms SkaModel.Glue.nsk_of_sdw
#print axioms SkaModel.Glue.nskEndC_of
#print axioms SkaModel.Glue.entryMono_noSixW
#print axioms SkaModel.Glue.proxy_fresh
#print axioms SkaModel.Glue.sdw_proxy

-- other tracks, digest [306] to [315], in the tree at e4345c23
#check @Compiler.pokeModel_fullReachP6L
#check @Compiler.pokeModel_fullReachP5S
#check @Compiler.GateRest5
#check @Compiler.cu_gate_dir_sccDS
#check @Compiler.csi_gate_ranked_soft
#check @Compiler.rs_cls8
#check @Compiler.rs_done8
#check @Compiler.sccsLeafAt_of_tarjan
#check @Compiler.inl_pill_gate
#check @Compiler.optimize_total_finishLFX
#check @SkaModel.AnnotSF.InvBSR
#check @SkaModel.AnnotSF.inlAnnot_of_inv
#check @Tarjan.tarjanM_spec
#check @SkaModel.Comp.exCons_contract
#check @SkaModel.Comp.finishLUC_contractGD
#check @SkaModel.Comp.runOKGen_cons00
#check @SkaModel.Comp.contract_spotArm
#check @SkaModel.Ana.passLoop_returns_k
#check @SkaModel.Raw.liveRun_plain
#check @SkaModel.AnnotSF.sffOn_of_detK

end Formalization
