-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.Mean.PathDecomposition
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeFluxOrderBound

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVenhance AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean

/-! The weak transfer reads the finer native source coefficients. The appended
child has the history geometry of the recentered native family on the whole
availability interval. The carried finer-history invariant and native source
covariance then give the coefficient equality used by transfer collapse. -/

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window GenSem QuietAtlas
open AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The supplied carrier start also controls one unit of temporal padding. -/
theorem Case.carrierOne (x : Case plan R) :
    IsCarrierStart x.c.D.α x.c.D.q x.c.D.Λ A.bw 1 1 x.c.j₀ := by
  obtain ⟨hΛ0, hq, _, _⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hc : IsCarrierStart x.c.D.α x.c.D.q x.c.D.Λ A.bw 1 400 x.c.j₀ := by
    rw [x.c.alpha, x.c.q_eq, x.c.base_eq]
    exact x.c.carrier
  exact IsCarrierStart.mono (fun j => (Applications.ocA_pos _ _ hq _ j hΛ0).le)
    (fun j => (Construction.Stream.ocTauPP_pos (m := j) hΛ).le)
    le_rfl (by norm_num) zero_le_one zero_le_one hc

/-- Only the observed coarse pulse acts during the complete availability history of an
active finer pulse. This is a support statement, not fast independence. -/
theorem Case.transferPulse (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (p : ℤ) (hp : Odd p) (k : ℤ) (t : ℝ)
    (hcp : ocCutoff x.c.D.α x.c.D.q x.c.D.Λ (x.c.stage (x.i - 1)).level p t ≠ 0)
    (hck : ocCutoff x.c.D.α x.c.D.q x.c.D.Λ ((x.c.stage (x.i - 1)).level + 1) k t ≠ 0) :
    ∀ u ∈ availInterval x.c.D (x.c.M + A.Jw) ((x.c.stage (x.i - 1)).level + 1) k,
      SinglePulseAt x.c.D (x.c.stage (x.i - 1)).level p u := by
  have hlevel : (x.c.stage (x.i - 1)).level = x.i - 1 := by
    rw [(x.c.construction.2.2 x.i x.lower x.upper).1.2.1,
      (cd_stage_inv x.c x.i x.lower x.upper).1]
  have hf := x.startFloor hcommon
  have hm : 1 ≤ (x.c.stage (x.i - 1)).level := by rw [hlevel]; have := x.lower; omega
  have hj : x.c.j₀ ≤ (x.c.stage (x.i - 1)).level := by rw [hlevel]; have := x.lower; omega
  obtain ⟨hΛ0, _, hζ, _⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hstreams : IsOCStreamSeq x.c.D.α x.c.D.q x.c.D.Λ x.c.D.ζ x.c.D.Φ := by
    rw [x.c.alpha, x.c.q_eq, x.c.base_eq, x.c.profile_eq]
    exact x.c.streams
  exact tc_single_pulse_avail hstreams hζ hΛ x.carrierOne (x.c.M + A.Jw) hm hj hp hcp hck

/-- At nonzero coarse and fine cutoffs, the weak child coefficient is its native coefficient
at the changed label. No quiet-time premise is used. -/
theorem Case.childCoefficient (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (v u : CompIn (x.c.stage (x.i - 1)).comps)
    (γ : (x.c.stage (x.i - 1)).fam.Γ v u)
    (p : ℤ) (hp : Odd p) (k : ℤ) (hk : Odd k) (t : ℝ)
    (hcp : ocCutoff x.c.D.α x.c.D.q x.c.D.Λ (x.c.stage (x.i - 1)).level p t ≠ 0)
    (hck : ocCutoff x.c.D.α x.c.D.q x.c.D.Λ ((x.c.stage (x.i - 1)).level + 1) k t ≠ 0)
    (y : Vec 2) (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    let m := (x.c.stage (x.i - 1)).level
    let s := (x.witness.e v u γ).1
    fluxCoeff (s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
        ((⟨m - 1, [p], y, []⟩ : RealChain).appendChild x.c.D k t ((x.c.D.eps m)⁻¹ • y)))
        d I 0 =
      fluxCoeff (s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
        (nativeChain (x.c.stage x.i).level k)) d I
        (labelChange x.c.D m p k t y) := by
  classical
  let G := x.c.stage x.i
  let G' := x.c.stage (x.i - 1)
  let m := G'.level
  let s := (x.witness.e v u γ).1
  have hlev : G.level = x.i := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hpw := (x.c.construction.2.2 x.i x.lower x.upper).1
  have hG' : G'.level = x.i - 1 := by
    rw [hpw.2.1, hlev]
  have hL : G.level = m + 1 := by
    dsimp only [m]
    rw [hlev, hG']
    have := x.lower
    omega
  have hf := x.startFloor hcommon
  have hm1 : 1 ≤ m := by
    change 1 ≤ G'.level
    rw [hG']
    have := x.lower
    omega
  have hjm : x.c.j₀ ≤ m := by
    change x.c.j₀ ≤ G'.level
    rw [hG']
    have := x.lower
    omega
  have hji : x.c.j₀ ≤ G.level := by
    rw [hlev]
    have := x.lower
    omega
  obtain ⟨hΛ0, _, hζ, hband⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by rw [hlev]
  have hε : x.c.D.eps m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hstart := x.carrierOne
  have hsp := x.transferPulse hcommon p hp k t hcp hck
  have hτk : 0 < ocTau x.c.D.α x.c.D.q x.c.D.Λ (m + 1) := Construction.Stream.ocTau_pos hΛ
  have htk := mem_ocPulseWindow_of_ocCutoff_ne_zero hτk hck
  have htav := mem_availInterval_of_ocCutoff x.c.D hΛ hck (Mtop := x.c.M + A.Jw)
  have hsav := slotAnchor_mem_availInterval x.c.D (x.c.M + A.Jw) (m + 1) k
  have hh := tc_appendChild_histEq hζ hm1 hε p k t y
    (I := availInterval x.c.D (x.c.M + A.Jw) (m + 1) k)
    (fun z hz w hw => hsp w (uIcc_subset_availInterval x.c.D (x.c.M + A.Jw) (m + 1) k hsav hz hw))
    (fun w hw => hsp w (uIcc_subset_availInterval x.c.D (x.c.M + A.Jw) (m + 1) k htav hsav hw))
  have hch := nativeChain_isCarrier x.c.D A.bw x.c.j₀ m p 2 hm1 hjm hp y
  have hsch : IsScheduledIn x.c.D m k p :=
    ⟨t, Function.mem_support.mpr hck,
      mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hΛ) hcp⟩
  have hA := appendChild_admissible x.c.D hΛ hζ A.bw_pos
    (startBound_of_carrierStart hΛ le_rfl le_rfl hstart) m p _ hch k hk hsch t hck
    ((x.c.D.eps m)⁻¹ • y)
  have hB := nativeChain_isCarrier x.c.D A.bw x.c.j₀ (m + 1) k 2 (by omega) (by omega) hk
    (labelChange x.c.D m p k t y)
  have hsame := (histEq_iff_sameHistory x.c.D _ _ hh.1).mp hh
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos x.c.D hΛ hζ hband G.level
  have hF := weakPassage_finerHistory hζ hΛ x.witness hL hc x.history.2 x.history.1
  have hgerm (f : Vec 2 → ℝ) := hF v u γ 0 (by
    simp only [weakPassagePresentation, QuietSource.degrees, mem_singleton_iff])
    ⟨k, hk⟩ ⟨_, hA⟩ ⟨_, hB⟩ hsame t htk f
  have hcoef : fluxCoeff (s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
      ((⟨m - 1, [p], y, []⟩ : RealChain).appendChild x.c.D k t ((x.c.D.eps m)⁻¹ • y))) d I 0 =
      fluxCoeff (s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
        ⟨m, [k], labelChange x.c.D m p k t y, []⟩) d I 0 := by
    unfold fluxCoeff
    apply congrArg (fun z : Vec 2 => ((d - 1).factorial : ℝ)⁻¹ • z)
    simpa only [weakPassagePresentation, QuietSource.finer, Nat.add_sub_cancel, s, heps]
      using (hgerm (fun Y => ∏ j, (Y - 0) (I j))).eq_of_nhds
  refine hcoef.trans ?_
  have hBeq : (⟨m, [k], labelChange x.c.D m p k t y, []⟩ : RealChain) =
      (nativeChain G.level k).recenter x.c.D (labelChange x.c.D m p k t y) := by
    rw [hL, nativeChain_recenter]
    rfl
  rw [hBeq]
  exact fluxCoeff_recenter (fun f => x.sourceRecenter hcommon s k hk hji
    (labelChange x.c.D m p k t y) t (by rwa [hL]) f) d I

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
end

section
open Homogenization MeasureTheory Set AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean

/-! Finite order of the weak native path means. Native joint smoothness and the
box reserve give the existing `LiftRegular` array hypotheses directly;
no quantitative certificate or ambient-cap price is charged here. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window GenSem
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Providers.PathDecomp

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The native path data and any of their lifts satisfy the finite array reserve. -/
theorem Case.pathRegular (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    {g : ℕ} (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) g)
    (τ : ℝ) (hτ : τ ∈ Icc (x.left k) (x.right k))
    (Cc : ℕ → ℕ → LiftCoeff (Fin (g + 1)) (fun _ => ℝ))
    (hseq : IsLiftSequence (x.pathData π k hk (x.native k hk hj))
      R.sX R.sZ (x.left k) (x.right k) A.Nw g Cc) (n : ℕ) :
    LiftRegular (x.pathData π k hk (x.native k hk hj)) Cc (0 : Fin (g + 1))
      τ g n (x.cap + 2) := by
  classical
  have H := x.pathSetting hcommon k hk hj hX hZ
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by
    rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hh hhh p _hp m α v
    have hb := ((hseq.2.2.2.2.2.1 hh hhh p m α v 0 τ hτ).1).map_clm
      (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
    exact hb.contDiff_uncurry (by have := A.Nw_pos; omega) (by have := A.Nw_pos; omega)
  · intro a b
    exact ((EntryWeakProofs.familyLiftData_metric_entry_smooth x.c.D
      (x.c.stage x.i).level k (nativeChain (x.c.stage x.i).level k) rfl
      (x.c.D.eps ((x.c.stage x.i).level - 1))
      (pathEdges (weakWindowStage x.c x.i x.lower x.upper) π ⟨k, hk⟩
        (x.native k hk hj)) τ a b).comp contDiff_fst).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro j
    exact ((hl_familyLiftData_drift_smooth x.c.D (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) (x.c.D.eps ((x.c.stage x.i).level - 1))
      (pathEdges (weakWindowStage x.c x.i x.lower x.upper) π ⟨k, hk⟩
        (x.native k hk hj)) τ j).comp contDiff_snd).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro v u d γ hγ α j
    simp only [Case.pathData, familyLiftData, liftEdges, List.mem_map] at hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    unfold pathEdges at hγ₀
    split_ifs at hγ₀ with hvu hd
    · rw [List.mem_singleton] at hγ₀
      subst γ₀
      have hdD : d.1 ≤ x.cap := (Finset.mem_Icc.mp d.2).2
      have hg := H.goodDat_path π ⟨u, hvu.2⟩ τ hτ d.1 α j
      simp only [pathDat, stageDat, hdD, ite_true] at hg
      have hr := hg.1.of_le (m := ((x.cap + 2 : ℕ) : WithTop ℕ∞)) (WithTop.coe_le_coe.mpr (by exact_mod_cast
          (show x.cap + 2 ≤ A.Nw + 1 + x.cap by have := A.Nw_pos; omega)))
      simp only [Case.native, heps] at hr ⊢
      with_unfolding_all exact hr
    · simp only [List.not_mem_nil] at hγ₀
    · simp only [List.not_mem_nil] at hγ₀

/-- An array formula at a label gives its symmetric-coefficient expansion there. -/
theorem weakMean_finiteOrderAtLabel_of_arr {n : ℕ} (hn : 1 ≤ n)
    (Arr : Fin 2 → CArr) (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) (y : Vec 2)
    (hL : ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → ∀ j,
      L f y j = applyArr (n - 1) (Arr j) f y 0) :
    ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      L f y = ∑ d ∈ Finset.Icc 1 n, ∑ I : DerivativeWord2 (d - 1),
        orderedDerivative I f y • fluxCoeff L d I y := by
  let L' : (Vec 2 → ℝ) → Vec 2 → Vec 2 := fun f z => L (fun X => f (X - y)) (y + z)
  let Arr' : Fin 2 → CArr := fun j r α _ _ => Arr j r α y 0
  have hfo : FiniteOrderAt n L' := by
    refine finiteOrderAt_of_arr hn Arr' L' ?_
    intro f hf j
    have hp := hL (fun X => f (X - y)) (hf.comp (contDiff_id.sub contDiff_const)) j
    dsimp only [L']
    rw [add_zero, hp]
    simp only [applyArr, Arr', sub_eq_add_neg,
      CycleComparison.LiftMeanEntrywise.orderedDerivative_slowShift, add_neg_cancel]
  have hshift (f : Vec 2 → ℝ) : L' (fun z => f (y + z)) 0 = L f y := by
    dsimp only [L']
    rw [add_zero]
    congr 1
    funext X
    congr 1
    abel
  intro f hf
  exact finiteOrder_of_recenter hshift hfo hf

/-- A native path mean has precisely the finite order recorded by its mean degree. -/
theorem Case.pathFiniteOrder (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    {g : ℕ} (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) g)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (g + 1)) (fun _ => ℝ))
    (hseq : IsLiftSequence (x.pathData π k hk (x.native k hk hj))
      R.sX R.sZ (x.left k) (x.right k) A.Nw g Cc)
    (t : ℝ) (ht : (x.c.D.cellScaleSq (x.c.stage x.i).level)⁻¹ * t ∈
      Icc (x.left k) (x.right k)) (n : ℕ) (hn : 1 ≤ n) (y : Vec 2 := 0) :
    ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      pathMeanFlux x.c.D (x.c.stage x.i).level x.length
        (x.pathData π k hk (x.native k hk hj)) Cc n t f y =
      ∑ d ∈ Finset.Icc 1 n, ∑ I : DerivativeWord2 (d - 1), orderedDerivative I f y •
        fluxCoeff (pathMeanFlux x.c.D (x.c.stage x.i).level x.length
          (x.pathData π k hk (x.native k hk hj)) Cc n t) d I y := by
  have hreg := x.pathRegular hcommon k hk hj hX hZ π _ ht Cc hseq n
  refine weakMean_finiteOrderAtLabel_of_arr hn
    (fun j => pmArr x.c.D (x.c.stage x.i).level x.length
      (x.pathData π k hk (x.native k hk hj)) Cc n t j) _ y ?_
  intro f hf j
  rw [pathMeanFlux_applyArr x.c.D (x.c.stage x.i).level (x.scales hcommon).2.ne'
    (x.pathData π k hk (x.native k hk hj)) Cc n t hreg
    (hf.of_le (by exact_mod_cast le_top)) y j]
  exact congrFun (congrFun (applyArr_eq_of_supp (K := n - 1) (K' := n) (by omega)
    (arrSupp_pmArr x.c.D (x.c.stage x.i).level x.length _ Cc n t j) f) y) 0
end

/-! The scalar eddy flux has finite order equal to its recorded degree. Only
continuity of the scalar lift arrays is used. Its empty-edge lift restricts to
the fixed weak cap without changing its coefficients. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window GenSem
open AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-- Finite order of the drift part of the scalar mean, by its existing coefficient array. -/
theorem weakMean_eddyFiniteOrder {Dm : ℕ} (D : OCData) (m : ℕ) (ρ : ℝ) (hρ : ρ ≠ 0)
    (Q : LiftOperatorData (Fin 1) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hreg : LiftRegular Q Cc (0 : Fin 1) ((D.cellScaleSq m)⁻¹ * t) 0 n 0) (y : Vec 2 := 0) :
    ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      weakEddyFlux D m ρ Q Cc n t f y =
        ∑ d ∈ Finset.Icc 1 n, ∑ I : DerivativeWord2 (d - 1),
          orderedDerivative I f y • fluxCoeff (weakEddyFlux D m ρ Q Cc n t) d I y := by
  classical
  let τ := (D.cellScaleSq m)⁻¹ * t
  let P := -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ)
  let Arr : Fin 2 → CArr := fun j r α Y z =>
    P * ρ ^ r * meanArr (fluxXA Q Cc 0 0 n τ 0 j) r α (ρ⁻¹ • Y) z
  refine weakMean_finiteOrderAtLabel_of_arr hn Arr _ y ?_
  intro f hf j
  let b : Vec 2 → ℝ := fun X => f (ρ • X)
  have hb : ContDiff ℝ ((n - 1 : ℕ) : WithTop ℕ∞) b :=
    (hf.comp (contDiff_const_smul ρ)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hψ (z : Vec 2) (v : Fin 1) :
      ((Real.sqrt Q.η * Q.v τ z j) • liftApply (n - 1) (Cc 0 (n - 1))
        (fun _ X => (Pi.single (0 : Fin 1) (b X) : Fin 1 → ℝ)) τ (ρ⁻¹ • y) z) v =
      applyArr (n - 1) (fluxXA Q Cc 0 0 n τ v j) b (ρ⁻¹ • y) z := by
    rw [liftApply_single_fun Cc (0 : Fin 1) (a := b) 0 (n - 1) τ hb]
    simp only [Pi.smul_apply, smul_eq_mul, fluxXA, applyArr_mulArr]
  have hsm (v : Fin 1) : ArrSmooth 0 (fluxXA Q Cc 0 0 n τ v j) := by
    unfold fluxXA
    exact arrSmooth_mulArr (contDiff_const.mul (hreg.drift j))
      (arrSmooth_entryArr _ _ _ _ _ fun r α =>
        hreg.coeff 0 le_rfl (n - 1) (by omega) r α v)
  have hcont : Continuous fun z => (Real.sqrt Q.η * Q.v τ z j) •
      liftApply (n - 1) (Cc 0 (n - 1))
        (fun _ X => (Pi.single (0 : Fin 1) (b X) : Fin 1 → ℝ)) τ (ρ⁻¹ • y) z := by
    apply continuous_pi
    intro v
    simp_rw [hψ]
    exact continuous_applyArr_z (hsm v) b (ρ⁻¹ • y)
  change P * fieldCellMean (fun z => (Real.sqrt Q.η * Q.v τ z j) •
    liftApply (n - 1) (Cc 0 (n - 1))
      (fun _ X => (Pi.single (0 : Fin 1) (b X) : Fin 1 → ℝ)) τ (ρ⁻¹ • y) z) 0 = _
  rw [hl_mean_eval hcont 0]
  simp_rw [hψ]
  rw [fieldCellMean_applyArr (n - 1) _ b (ρ⁻¹ • y) 0 (fun r α =>
    integrableOn_unitCube_of_continuous
      (((hsm 0).continuous r α).comp (continuous_const.prodMk continuous_id)))]
  unfold applyArr Arr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _hr => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hd := GenSem.orderedDerivative_comp_smul (g := f) ρ α
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)) (ρ⁻¹ • y)
  rw [smul_inv_smul₀ hρ] at hd
  dsimp only [b]
  rw [hd]
  ring

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The native empty-edge data at the fixed weak cap. -/
abbrev Case.scalarData (x : Case plan R) (k : ℤ) :=
  familyLiftData (Dm := x.cap) (hv := fun _ : Fin 1 => ℝ) x.c.D
    (x.c.stage x.i).level k (nativeChain (x.c.stage x.i).level k) x.length (fun _ _ _ => [])

/-- The source witness's scalar lift, at the cap and on the original closed native window. -/
theorem Case.scalarSequence (x : Case plan R) (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) :
    IsLiftSequence (x.scalarData k) R.sX R.sZ (x.left k) (x.right k) A.Nw 0
      (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) := by
  let Q : LiftOperatorData (Fin 1) (fun _ => ℝ) x.c.Dm :=
    familyLiftData x.c.D (x.c.stage x.i).level k (nativeChain (x.c.stage x.i).level k)
      (x.c.D.eps ((x.c.stage x.i).level - 1)) (fun _ _ _ => [])
  let Cc := x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)
  have hch : IsAdmissibleChain x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) := (x.native k hk hj).2
  have hL : IsLiftSequence Q R.sX R.sZ
      (x.c.D.slotStart (x.c.stage x.i).level k / x.c.D.cellScaleSq (x.c.stage x.i).level)
      ((((k : ℝ) + 61 / 48) * ocTau x.c.D.α x.c.D.q x.c.D.Λ (x.c.stage x.i).level) /
        x.c.D.cellScaleSq (x.c.stage x.i).level) A.Nw 0 Cc :=
    x.witness.lifts0 k _ hk hch
  have hE : EdgesBelow x.cap Q.edge := by
    intro v u d _
    simp only [Q, familyLiftData, liftEdges, List.map_nil]
  have hN : A.Nw ≤ x.cap :=
    (Nat.le_mul_of_pos_left A.Nw A.Jw_pos).trans (Nat.le_add_left _ _)
  have hs := isLiftSequence_restrict (N := x.cap) x.c.order_ge hE Cc hN hL
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by
    rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
  have he : restrictData x.c.order_ge Q = x.scalarData k := by
    rw [familyLiftData_empty_restrict, heps]
  rw [he] at hs
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  simp only [Case.left, Case.right, weakSlotLeft, weakSlotRight, Cc, hlevel] at hs ⊢
  with_unfolding_all exact hs

/-- The scalar source arrays need only continuity for their finite-order formula. -/
theorem Case.scalarRegular (x : Case plan R) (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) (τ : ℝ)
    (hτ : τ ∈ Icc (x.left k) (x.right k)) (n : ℕ) :
    LiftRegular (x.scalarData k)
      (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) (0 : Fin 1) τ 0 n 0 := by
  have hs := x.scalarSequence k hk hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hh hhh p _hp m α v
    have hb := ((hs.2.2.2.2.2.1 hh hhh p m α v 0 τ hτ).1).map_clm
      (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
    exact hb.contDiff_uncurry (Nat.zero_le _) (Nat.zero_le _)
  · intro a b
    exact ((EntryWeakProofs.familyLiftData_metric_entry_smooth x.c.D
      (x.c.stage x.i).level k (nativeChain (x.c.stage x.i).level k) rfl x.length
      (fun _ _ _ => []) τ a b).comp contDiff_fst).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro j
    exact ((hl_familyLiftData_drift_smooth x.c.D (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) x.length
      (fun _ _ _ => []) τ j).comp contDiff_snd).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro v u d γ hγ
    simp only [Case.scalarData, familyLiftData, liftEdges, List.map_nil, List.not_mem_nil] at hγ
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
end
end
end

section
@[expose] public noncomputable section
section
open Homogenization MeasureTheory Set AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean

/-! The actual weak finer source has finite order at most its recorded degree.
Every retained inherited degree is at most the fixed weak cap; restriction of
its data therefore preserves the physical mean flux. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window GenSem
open AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- All degrees produced at a passage are retained at the weak cap. -/
theorem Case.validDegree (x : Case plan R) (s : WeakSource (x.c.stage x.i))
    (hs : s.Valid A.Nw A.Rw x.incomingOrder) : 2 ≤ s.degree ∧ s.degree ≤ x.cap := by
  have hN : A.Nw ≤ A.Jw * A.Nw := Nat.le_mul_of_pos_left A.Nw A.Jw_pos
  cases s with
  | eddy v w n =>
    dsimp only [WeakSource.degree]
    exact ⟨hs.2.2.1, hs.2.2.2.trans (by dsimp only [Case.cap]; omega)⟩
  | inherited w h π n =>
    refine ⟨hs.2.2.1, hs.2.2.2.trans ?_⟩
    have hh : x.c.M + A.Jw - x.i + 1 ≤ A.Jw := by have := x.lower; have := A.Jw_pos; omega
    change A.Nw + (1 + (x.c.M + A.Jw - x.i) * A.Nw) ≤ 1 + A.Jw * A.Nw
    calc
      _ = 1 + (x.c.M + A.Jw - x.i + 1) * A.Nw := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right A.Nw hh) 1

/-- Finite-order production for every valid weak source at its native chart. -/
theorem Case.sourceFiniteOrder (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (s : WeakSource (x.c.stage x.i)) (hs : s.Valid A.Nw A.Rw x.incomingOrder)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (t : ℝ) (ht : (x.c.D.cellScaleSq (x.c.stage x.i).level)⁻¹ * t ∈
      Icc (x.left k) (x.right k)) (y : Vec 2 := 0) :
    ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
        (nativeChain (x.c.stage x.i).level k) f y =
      ∑ d ∈ Finset.Icc 1 s.degree, ∑ I : DerivativeWord2 (d - 1), orderedDerivative I f y •
        fluxCoeff (s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
          (nativeChain (x.c.stage x.i).level k)) d I y := by
  classical
  let ctx := x.native k hk hj
  have hc : IsAdmissibleChain x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) ∧ Odd k := ⟨ctx.2, hk⟩
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by
    rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hn := x.validDegree s hs
  cases s with
  | inherited w h π n =>
    simp only [WeakSource.degree] at hn ⊢
    let πc : StagePath (weakWindowStage x.c x.i x.lower x.upper) h := π.recap
    let Cc := x.witness.Cc (.inherited w h π n) k (nativeChain (x.c.stage x.i).level k)
    let Q := familyLiftData x.c.D (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) x.length (pathEdges (x.c.stage x.i) π ⟨k, hk⟩ ctx)
    have hπ : x.originalPath πc = π := by cases π; rfl
    have hl := x.pathSequenceOn πc k hk ctx w n
    dsimp only [Case.pathCoefficients] at hl
    rw [hπ, heps, show ctx.1 = nativeChain (x.c.stage x.i).level k from rfl,
      x.nativeLadder_univ k hk hj] at hl
    have hseq : IsLiftSequence (x.pathData πc k hk ctx) R.sX R.sZ (x.left k) (x.right k)
        A.Nw h Cc := by
      have h := liftSequence_of_on_univ _ _ _ _ _ _ _ _ hl
      simpa only [Case.left, Case.right, weakSlotLeft, weakSlotRight, hlevel, ctx, Case.native, Cc] using h
    have heQ : x.pathData πc k hk ctx = restrictData x.c.order_ge Q := by
      have he := familyLiftData_recap (hN := weakStage_maxOrder_le x.c x.i x.lower x.upper)
        (𝒮 := (x.c.stage x.i).exports) x.c.order_ge π ⟨k, hk⟩ ctx k ctx.1
        (x.c.D.eps ((x.c.stage x.i).level - 1))
      simp only [Case.pathData, Case.native, heps, ctx, Q] at he ⊢
      with_unfolding_all exact he
    have hE : EdgesBelow x.cap Q.edge :=
      edgesBelow_liftEdges (edgesBelow_pathEdges
        (weakStage_maxOrder_le x.c x.i x.lower x.upper) π ⟨k, hk⟩ ctx) _ _
    have heF : pathMeanFlux x.c.D (x.c.stage x.i).level x.length
        (x.pathData πc k hk ctx) Cc n t =
        pathMeanFlux x.c.D (x.c.stage x.i).level x.length Q Cc n t := by
      rw [heQ]
      exact pathMeanFlux_restrict x.c.order_ge x.c.D (x.c.stage x.i).level x.length hE Cc hn.2 t
    simp only [WeakSource.fluxOp, dite_eq_left hc]
    have hp := x.pathFiniteOrder hcommon k hk hj hX hZ πc Cc hseq t ht n (by omega) y
    rw [heF] at hp
    simpa only [Q, Cc, ctx, Case.native] using hp
  | eddy v w n =>
    simp only [WeakSource.degree] at hn ⊢
    simp only [WeakSource.fluxOp, dite_eq_left hc]
    have he : weakEddyFlux x.c.D (x.c.stage x.i).level x.length
        (familyLiftData (Dm := x.c.Dm) (hv := fun _ : Fin 1 => ℝ) x.c.D
          (x.c.stage x.i).level k (nativeChain (x.c.stage x.i).level k) x.length (fun _ _ _ => []))
        (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) n t =
        weakEddyFlux x.c.D (x.c.stage x.i).level x.length (x.scalarData k)
          (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) n t := rfl
    rw [he]
    exact weakMean_eddyFiniteOrder x.c.D (x.c.stage x.i).level x.length (x.scales hcommon).2.ne'
      (x.scalarData k) _ n (by omega) t (x.scalarRegular k hk hj _ ht n) y

/-- Every valid native source annihilates constants on the original closed pulse window. -/
theorem Case.sourceConstZero (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (s : WeakSource (x.c.stage x.i)) (hs : s.Valid A.Nw A.Rw x.incomingOrder)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (t : ℝ) (ht : (x.c.D.cellScaleSq (x.c.stage x.i).level)⁻¹ * t ∈
      Icc (x.left k) (x.right k)) (c₀ : ℝ) (y : Vec 2) :
    s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
      (nativeChain (x.c.stage x.i).level k) (fun _ => c₀) y = 0 := by
  classical
  let ctx := x.native k hk hj
  have hc : IsAdmissibleChain x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) ∧ Odd k := ⟨ctx.2, hk⟩
  have H := x.pathSetting hcommon k hk hj hX hZ
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by
    rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  cases s with
  | inherited w h π n =>
    let Q := familyLiftData x.c.D (x.c.stage x.i).level k ctx.1 x.length
      (pathEdges (x.c.stage x.i) π ⟨k, hk⟩ ctx)
    let Cc := x.witness.Cc (.inherited w h π n) k ctx.1
    have hl := x.witness.lifts (.inherited w h π n) k ctx.1 hc
    dsimp only [WeakSource.IsLiftFamily] at hl
    rw [heps] at hl
    have hΩ : ladderOmega x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k ctx.1 x.length =
        Set.univ := x.nativeLadder_univ k hk hj
    rw [hΩ] at hl
    have hseq : IsLiftSequenceOn Set.univ Q R.sX R.sZ (x.left k) (x.right k) A.Nw h Cc := by
      simp only [Case.left, Case.right, weakSlotLeft, weakSlotRight, Q, Cc, hlevel, ctx,
        Case.native] at hl ⊢
      with_unfolding_all exact hl
    have hW : ∀ X ∈ (Set.univ : Set (Vec 2)), ∃ lo hi Mv : ℝ,
        Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v
          (x.left k) (x.right k) lo hi Mv := fun X _ => H.windowData X
    have hz := pcc_order_zero_vanish Q (x.left k) (x.right k) H.window isOpen_univ hW
      R.sX R.sZ A.Nw h Cc hseq
    have he := pcc_pathMeanFlux_const_zero x.c.D (x.c.stage x.i).level x.length hs.2.1
      isOpen_univ hseq hz n t ht c₀ y (Set.mem_univ _)
    simpa only [WeakSource.fluxOp, dite_eq_left hc, Q, Cc, ctx, Case.native] using he
  | eddy v w n =>
    have hseq := x.scalarSequence k hk hj
    have hζ := (Comparison.weakPassageInstance_base x.c).2.2.1
    have hz := fsc_diag_hZ x.c.D hζ (x.c.stage x.i).level hk _ x.length H.window hseq
    have hn : n - 1 ≠ 0 := by have := hs.2.2.1; omega
    have hcst := pcc_liftApply_constOn (hz (n - 1) hn)
      (Pi.single (0 : Fin 1) c₀) ht
    simp only [WeakSource.fluxOp, dite_eq_left hc]
    change weakEddyFlux x.c.D (x.c.stage x.i).level x.length (x.scalarData k)
      (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) n t (fun _ => c₀) y = 0
    funext j
    have hfield : (fun z =>
        (Real.sqrt (x.scalarData k).η * (x.scalarData k).v
          ((x.c.D.cellScaleSq (x.c.stage x.i).level)⁻¹ * t) z j) •
        liftApply (n - 1) (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k) 0 (n - 1))
          (fun _ _ => Pi.single (0 : Fin 1) c₀)
          ((x.c.D.cellScaleSq (x.c.stage x.i).level)⁻¹ * t) (x.length⁻¹ • y) z) = 0 := by
      funext z
      rw [hcst _ (Set.mem_univ _) z, smul_zero]
      rfl
    unfold weakEddyFlux
    rw [hfield]
    simp [fieldCellMean]

/-- Native sources have no zeroth-order term in their finite expansion. -/
theorem Case.sourceFiniteOrderFromTwo (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (s : WeakSource (x.c.stage x.i)) (hs : s.Valid A.Nw A.Rw x.incomingOrder)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (t : ℝ) (ht : (x.c.D.cellScaleSq (x.c.stage x.i).level)⁻¹ * t ∈
      Icc (x.left k) (x.right k)) (y : Vec 2) :
    ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
        (nativeChain (x.c.stage x.i).level k) f y =
      ∑ d ∈ Finset.Icc 2 s.degree, ∑ I : DerivativeWord2 (d - 1), orderedDerivative I f y •
        fluxCoeff (s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
          (nativeChain (x.c.stage x.i).level k)) d I y := by
  intro f hf
  rw [x.sourceFiniteOrder hcommon hX hZ s hs k hk hj t ht y f hf]
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun d hd hnd => ?_).symm
  have hd1 : d = 1 := by
    have hmem := Finset.mem_Icc.mp hd
    by_contra hne
    exact hnd (Finset.mem_Icc.mpr ⟨by omega, hmem.2⟩)
  subst d
  refine Finset.sum_eq_zero fun I _ => ?_
  have hz := x.sourceConstZero hcommon hX hZ s hs k hk hj t ht 1 y
  have hcoeff : fluxCoeff (s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
      (nativeChain (x.c.stage x.i).level k)) 1 I y = 0 := by
    unfold fluxCoeff
    have he : (fun Y : Vec 2 => ∏ j, (Y - y) (I j)) = fun _ => 1 := by
      rfl
    rw [he, hz, smul_zero]
  rw [hcoeff, smul_zero]
end

/-! Grade zero of the incoming native fibre is the scalar diagonal lift. This
uses the generic grade-zero uniqueness calculation on the native closed window,
without the terminal-level premise of the successor-specific wrapper. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window GenSem
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open HLZero

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Scalarization of the full native grade-zero mean at a component. -/
theorem Case.nativeZeroMean (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (τ : ℝ) (hτ : τ ∈ Icc (x.left k) (x.right k))
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a τ)) (n : ℕ) (X : Vec 2) (j : Fin 2)
    (v : CompIn (x.c.stage x.i).comps) (ℓ : ScalarH v.1.root →L[ℝ] ℝ) :
    ℓ (fieldCellMean (fun z => liftFluxX (x.nativeData k hk hj)
        (x.input.CcR x.i k) a 0 n τ X z j) v) =
      fieldCellMean (fun z => liftFluxX (x.scalarData k)
        (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k))
        (hlScal (hs := fun v : CompIn (x.c.stage x.i).comps => ScalarH v.1.root) ℓ a) 0 n τ X z j) 0 := by
  classical
  let Q : LiftOperatorData (CompIn (x.c.stage x.i).comps)
      (fun v => ScalarH v.1.root) x.cap := x.nativeData k hk hj
  let Q0 := x.scalarData k
  let C0 := x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)
  let hs := fun v : CompIn (x.c.stage x.i).comps => ScalarH v.1.root
  have H := x.pathSetting hcommon k hk hj hX hZ
  have hseq := x.nativeSequence k hk hj
  have hseq0 := x.scalarSequence k hk hj
  have hN := A.Nw_pos
  have hcap : 2 ≤ x.cap := by
    dsimp only [Case.cap]
    have := Nat.mul_pos A.Jw_pos A.Nw_pos; omega
  have hη : Q0.η = Q.η := rfl
  have hG : Q0.G = Q.G := rfl
  have hv : Q0.v = Q.v := rfl
  have hGs : ∀ t i j, ContDiff ℝ (⊤ : ℕ∞) (fun X => Q.G t X i j) :=
    fun t i j => EntryWeakProofs.familyLiftData_metric_entry_smooth x.c.D
      (x.c.stage x.i).level k (nativeChain (x.c.stage x.i).level k) rfl x.length
      ((weakWindowStage x.c x.i x.lower x.upper).fam.fiber ⟨k, hk⟩ (x.native k hk hj)) t i j
  have hvs : ∀ t j, ContDiff ℝ (⊤ : ℕ∞) (fun z => Q.v t z j) :=
    fun t j => hl_familyLiftData_drift_smooth x.c.D (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) x.length
      ((weakWindowStage x.c x.i x.lower x.upper).fam.fiber ⟨k, hk⟩ (x.native k hk hj)) t j
  have hD := hlDiag_isLiftSequence (hs := hs) C0 Q Q0 hη hG hv hseq0 H.window
    (by omega) (by omega) (by omega) hGs hvs
  have huniq := Uniqueness.lift_sequence_unique_window Q (x.left k) (x.right k)
    H.window H.windowData R.sX R.sZ A.Nw 0 (x.input.CcR x.i k)
    (hlDiagCoeff hs C0) (hl_isLiftSequence_grade_zero hseq) hD
  have hF : ∀ n', liftApply n' (x.input.CcR x.i k 0 n') a τ =
      liftApply n' (hlDiagCoeff hs C0 0 n') a τ := by
    intro n'
    refine Uniqueness.liftApply_congr (fun m _ α => ?_) rfl
    funext X' z' v' u'
    exact huniq 0 le_rfl n' m α τ hτ X' z' v' u'
  have hflux : liftFluxX Q (x.input.CcR x.i k) a 0 n τ =
      liftFluxX Q (hlDiagCoeff hs C0) a 0 n τ := by
    funext X' z' j'
    rw [liftFluxX_zero_formula, liftFluxX_zero_formula, hF (n - 1), hF (n - 2)]
  have he := hl_fluxMean_transfer (hs := hs) C0 Q Q0 hη hG hv ℓ a n τ X j
    (fun i j => (hGs τ i j).of_le (WithTop.coe_le_coe.mpr le_top))
    (fun j => (hvs τ j).of_le (WithTop.coe_le_coe.mpr le_top))
    (ha.of_le (WithTop.coe_le_coe.mpr le_top))
    (fun n' m α v' u' => (hD.2.2.2.2.2.1 0 le_rfl n' m α v' u' τ hτ).1.mono
      (by omega) (by omega))
    (fun n' m α v' u' => (hseq0.2.2.2.2.2.1 0 le_rfl n' m α v' u' τ hτ).1.mono
      (by omega) (by omega))
  rw [← hflux] at he
  exact he

/-- At grade zero only the drift mean and the degree-two molecular flux survive. -/
theorem weakMean_gradeZeroFlux {ι : Type*} [Fintype ι] {hs : ι → Type*}
    [∀ v, NormedAddCommGroup (hs v)] [∀ v, NormedSpace ℝ (hs v)]
    [∀ v, FiniteDimensional ℝ (hs v)] [∀ v, CompleteSpace (hs v)] {Dm : ℕ}
    (Q : LiftOperatorData ι hs Dm) {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    (Cc : ℕ → ℕ → LiftCoeff ι hs) (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (hX : 1 ≤ sX) (hZ : 1 ≤ sZ) (f : Vec 2 → ∀ v, hs v)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (hn : 2 ≤ n)
    (t : ℝ) (ht : t ∈ Icc t₀ t₁) (X : Vec 2) (j : Fin 2)
    (hv : Continuous (fun z => Q.v t z j)) :
    fieldCellMean (fun z => liftFluxX Q Cc (fun _ => f) 0 n t X z j) =
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z j) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t X z) -
      if n = 2 then Q.η • ∑ k : Fin 2, Q.G t X j k • fderiv ℝ f X (basisVec k) else 0 := by
  let Φ := liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t
  let Ψ := liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t
  have hΦ : GoodField 1 Φ := liftApply_goodField_of_seq Q hseq hX hZ (Nat.zero_le H) _ hf ht
  have hΨ : GoodField 1 Ψ := liftApply_goodField_of_seq Q hseq hX hZ (Nat.zero_le H) _ hf ht
  have hm : ∀ Y, fieldCellMean (Ψ Y) = if n = 2 then f Y else 0 := by
    intro Y
    by_cases hn2 : n = 2
    · subst n
      have hid : Ψ Y = fun _ => f Y := funext fun z => hseq.1 f hf t ht Y z
      rw [hid, fieldCellMean_const, ite_eq_left rfl]
    · have hn0 : 1 ≤ n - 2 := by omega
      have hc := liftApply_centField_of_seq Q hseq hX hZ (Nat.zero_le H)
        (n := n - 2) (Or.inl hn0) hf ht
      rw [ite_eq_right hn2]
      exact hc.2 trivial Y
  have hfast (k : Fin 2) : fieldCellMean (fun z => fastPartial k Φ X z) = 0 :=
    fieldCellMean_fastPartial_eq_zero (Φ X) (hΦ.1.comp (contDiff_const.prodMk contDiff_id))
      (hΦ.2 X) k
  have hslow (k : Fin 2) : fieldCellMean (fun z => slowPartial k Ψ X z) =
      if n = 2 then fderiv ℝ f X (basisVec k) else 0 := by
    rw [fieldCellMean_slowPartial hΨ.1, funext hm]
    by_cases hn2 : n = 2
    · simp only [hn2, ite_true]
    · simp only [hn2, ite_false, fderiv_const_apply, zero_apply]
  have hF (k : Fin 2) : Continuous (fun z => fastPartial k Φ X z) :=
    (hΦ.fastPartial (r := 0) k).continuous_slice X
  have hS (k : Fin 2) : Continuous (fun z => slowPartial k Ψ X z) :=
    (hΨ.slowPartial (r := 0) k).continuous_slice X
  have hd : Continuous (fun z => (Real.sqrt Q.η * Q.v t z j) • Φ X z) :=
    (continuous_const.mul hv).smul (hΦ.continuous_slice X)
  have hfs : Continuous (fun z => Real.sqrt Q.η • ∑ k : Fin 2,
      Q.G t X j k • fastPartial k Φ X z) :=
    (continuous_finsetSum Finset.univ fun k _ => (hF k).const_smul (Q.G t X j k)).const_smul
      (Real.sqrt Q.η)
  have hss : Continuous (fun z => Q.η • ∑ k : Fin 2,
      Q.G t X j k • slowPartial k Ψ X z) :=
    (continuous_finsetSum Finset.univ fun k _ => (hS k).const_smul (Q.G t X j k)).const_smul Q.η
  simp only [liftFluxX_zero_formula, hn, ite_true]
  change fieldCellMean (fun z =>
      ((Real.sqrt Q.η * Q.v t z j) • Φ X z -
        Real.sqrt Q.η • ∑ k : Fin 2, Q.G t X j k • fastPartial k Φ X z) +
        -(Q.η • ∑ k : Fin 2, Q.G t X j k • slowPartial k Ψ X z)) =
    fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z j) • Φ X z) - _
  have hadd := fieldCellMean_add (hd.sub hfs) hss.neg
  simp only [Pi.sub_apply, Pi.neg_apply] at hadd
  rw [hadd]
  change fieldCellMean (fun z => (Real.sqrt Q.η * Q.v t z j) • Φ X z -
      Real.sqrt Q.η • ∑ k : Fin 2, Q.G t X j k • fastPartial k Φ X z) +
      fieldCellMean (fun z => -(Q.η • ∑ k : Fin 2, Q.G t X j k • slowPartial k Ψ X z)) = _
  rw [fieldCellMean_sub hd hfs,
    fieldCellMean_neg, fieldCellMean_smul, fieldCellMean_smul,
    fieldCellMean_sum Finset.univ (f := fun k z => Q.G t X j k • fastPartial k Φ X z)
      (fun k _ => (hF k).const_smul (Q.G t X j k)),
    fieldCellMean_sum Finset.univ (f := fun k z => Q.G t X j k • slowPartial k Ψ X z)
      (fun k _ => (hS k).const_smul (Q.G t X j k))]
  simp only [fieldCellMean_smul, hfast, smul_zero, Finset.sum_const_zero, sub_zero, hslow]
  by_cases hn2 : n = 2
  · simp only [hn2, ite_true, sub_eq_add_neg]
  · simp only [hn2, ite_false, smul_zero, Finset.sum_const_zero, neg_zero, add_zero, sub_zero]
end

/-! Dimensional weak transfers on the native charts. The source's finer native
coefficient is supplied by the carried history calculation; the dimensional
normalization and the change-of-chart Jacobian are the existing transfer APIs. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window GenSem QuietAtlas
open AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The dimensional coefficient of a stored weak edge on a native coarse chart. -/
theorem Case.dimFluxNative (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (v u : CompIn (x.c.stage (x.i - 1)).comps)
    (γ : (x.c.stage (x.i - 1)).fam.Γ v u) (p : OddSlot) (t : ℝ)
    (hcp : ocCutoff x.c.D.α x.c.D.q x.c.D.Λ (x.c.stage (x.i - 1)).level p.1 t ≠ 0)
    (y : Vec 2) (d : ℕ) (hd : 2 ≤ d) (I : DerivativeWord2 (d - 1)) :
    let G := x.c.stage x.i
    let G' := x.c.stage (x.i - 1)
    let s := (x.witness.e v u γ).1
    G'.fam.dimFlux (x.c.D.kap G'.level) (x.c.D.eps G'.level)
      (x.c.D.eps (G'.level - 1)) p (G'.actual p) v u γ d I t y
      ((x.c.D.eps G'.level)⁻¹ • y) =
    s.lam G.level A.η₀ • ∑ k ∈ activeSlots x.c.D
      (by have := (Comparison.weakPassageInstance_base x.c).1; omega) G'.level t,
      ocCutoff x.c.D.α x.c.D.q x.c.D.Λ (G'.level + 1) k.1 t •
        transportedCoeff (fun h => chartInvJacobian
          (labelChange x.c.D G'.level p.1 k.1 t) (y + h)) s.degree
          (fun e J => fluxCoeff (s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0
            k.1 t (nativeChain G.level k.1)) e J
              (labelChange x.c.D G'.level p.1 k.1 t y)) (d - 1) I 0 := by
  classical
  let G := x.c.stage x.i
  let G' := x.c.stage (x.i - 1)
  let s := (x.witness.e v u γ).1
  let F := s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0
  have hlevel : G.level = x.i := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hpw := (x.c.construction.2.2 x.i x.lower x.upper).1
  have hG' : G'.level = x.i - 1 := by rw [hpw.2.1, hlevel]
  have hL : G.level = G'.level + 1 := by rw [hlevel, hG']; have := x.lower; omega
  have hnat : G'.IsNatural (x.c.M + A.Jw) := hpw.2.2.2.2.1
  have hf := x.startFloor hcommon
  have hm : 1 ≤ G'.level := by rw [hG']; have := x.lower; omega
  have hj : x.c.j₀ ≤ G'.level := by rw [hG']; have := x.lower; omega
  obtain ⟨hΛ0, _, hζ, hband⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hε : x.c.D.eps G'.level ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hεc : x.c.D.eps (G'.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hκ : x.c.D.kap G'.level ≠ 0 :=
    (EntryWeakProofs.weakData_kap_pos x.c.D hΛ hζ hband G'.level).ne'
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by rw [hlevel]
  have htp := mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hΛ) hcp
  have hlv : transferAt x.c.D G.level p.1 = transferAt x.c.D (G'.level + 1) p.1 := by rw [hL]
  have he := dim_transferAt x.c.D hΛ hκ htp (s.lam G.level A.η₀) s.degree F
    (⟨G'.level - 1, [p.1], y, []⟩ : RealChain) ((x.c.D.eps G'.level)⁻¹ • y) d I
  simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux]
  rw [x.witness.flux v u γ p (G'.actual p) d I t _ _ hd, smul_inv_smul₀ hεc,
    hnat.2.2.1 p, ite_eq_left (isAdmissibleChain_nativeChain_recenter hm hj p y),
    heps, hlv, nativeChain_recenter, he]
  refine congrArg (fun z => s.lam G.level A.η₀ • z) (Finset.sum_congr rfl fun k hk => ?_)
  have hck : ocCutoff x.c.D.α x.c.D.q x.c.D.Λ (G'.level + 1) k.1 t ≠ 0 := by
    simpa [activeSlots] using hk
  have hsp := x.transferPulse hcommon p.1 p.2 k.1 t hcp hck
  have htav := mem_availInterval_of_ocCutoff x.c.D hΛ hck (Mtop := x.c.M + A.Jw)
  have hsav := slotAnchor_mem_availInterval x.c.D (x.c.M + A.Jw) (G'.level + 1) k.1
  have hco : (fun e J => fluxCoeff (F k.1 t
        ((⟨G'.level - 1, [p.1], y, []⟩ : RealChain).appendChild x.c.D k.1 t
          ((x.c.D.eps G'.level)⁻¹ • y))) e J 0) =
      fun e J => fluxCoeff (F k.1 t (nativeChain G.level k.1)) e J
        (labelChange x.c.D G'.level p.1 k.1 t y) := by
    funext e J
    exact x.childCoefficient hcommon v u γ p.1 p.2 k.1 k.2 t hcp hck y e J
  rw [tc_slot_jacobian hζ hm hε p.1 k.1 t y
    (fun w hw => hsp w (uIcc_subset_availInterval x.c.D (x.c.M + A.Jw)
      (G'.level + 1) k.1 htav hsav hw)), hco]

/-- The finer native operator glued in physical space for the actual source of an edge. -/
abbrev Case.sourceEuler (x : Case plan R)
    {v u : CompIn (x.c.stage (x.i - 1)).comps}
    (γ : (x.c.stage (x.i - 1)).fam.Γ v u) (t : ℝ) :=
  let s := (x.witness.e v u γ).1
  gluedFluxOp x.c.D (x.c.stage x.i).level
    (fun k => s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
      (nativeChain (x.c.stage x.i).level k)) t

/-- One coarse chart gives the symmetric coefficients of the glued native source. -/
theorem Case.pieceFlux (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (v u : CompIn (x.c.stage (x.i - 1)).comps)
    (γ : (x.c.stage (x.i - 1)).fam.Γ v u) (p : OddSlot) (t : ℝ)
    (hcp : ocCutoff x.c.D.α x.c.D.q x.c.D.Λ (x.c.stage (x.i - 1)).level p.1 t ≠ 0)
    (Dc : ℕ) (f : Vec 2 → ScalarH u.1.root) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (y : Vec 2) (j : Fin 2) :
    let G' := x.c.stage (x.i - 1)
    let s := (x.witness.e v u γ).1
    ∑ d ∈ Finset.Icc 2 Dc, ∑ α : DerivativeWord2 (d - 1),
      transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
        (G'.fam.identity v u γ).maxOrder
        (fun e I => G'.fam.dimFlux (x.c.D.kap G'.level) (x.c.D.eps G'.level)
          (x.c.D.eps (G'.level - 1)) p (G'.actual p) v u γ e I t
          (((G'.fam.piece p).material t).symm y)
          ((x.c.D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm y))
        (d - 1) α y j • (G'.fam.identity v u γ).map (orderedDerivative α f y) =
    s.lam (x.c.stage x.i).level A.η₀ •
      ∑ d ∈ Finset.Icc 2 Dc, ∑ I : DerivativeWord2 (d - 1),
        fluxCoeff (x.sourceEuler γ t) d I y j •
          (G'.fam.identity v u γ).map (orderedDerivative I f y) := by
  classical
  dsimp only
  let G := x.c.stage x.i
  let G' := x.c.stage (x.i - 1)
  let s := (x.witness.e v u γ).1
  let L := fun k => s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0
    k t (nativeChain G.level k)
  have hlevel : G.level = x.i := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hpw := (x.c.construction.2.2 x.i x.lower x.upper).1
  have hG' : G'.level = x.i - 1 := by rw [hpw.2.1, hlevel]
  have hL : G.level = G'.level + 1 := by rw [hlevel, hG']; have := x.lower; omega
  have hnat : G'.IsNatural (x.c.M + A.Jw) := hpw.2.2.2.2.1
  have hmax : (G'.fam.identity v u γ).maxOrder = s.degree := by
    change _ = (x.witness.e v u γ).1.degree
    rw [x.witness_edge v u]
    exact cd_maxOrder_eq_degree x.c x.i x.lower x.upper v u γ
  have hsrc : x.sourceEuler γ t = gluedFluxOp x.c.D (G'.level + 1) L t := by
    change gluedFluxOp x.c.D G.level L t = gluedFluxOp x.c.D (G'.level + 1) L t
    exact congrArg (fun m => gluedFluxOp x.c.D m L t) hL
  obtain ⟨hΛ0, _, hζ, hband⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hcell := EntryWeakProofs.weakData_cellScaleSq_pos x.c.D hΛ hζ hband G.level
  have hstart := x.startFloor hcommon
  have hj : x.c.j₀ ≤ G.level := by rw [hlevel]; have := x.lower; omega
  have hs : s.Valid A.Nw A.Rw x.incomingOrder := (x.witness.e v u γ).2.1
  have hfo : ∀ k ∈ activeSlots x.c.D hΛ G'.level t,
      ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
        L k.1 g (x.c.D.flowOf G'.level (x.c.D.slotAnchor (G'.level + 1) k.1) y t) =
        ∑ d ∈ Finset.Icc 1 s.degree, ∑ I : DerivativeWord2 (d - 1),
          orderedDerivative I g (x.c.D.flowOf G'.level
            (x.c.D.slotAnchor (G'.level + 1) k.1) y t) •
          fluxCoeff (L k.1) d I (x.c.D.flowOf G'.level
            (x.c.D.slotAnchor (G'.level + 1) k.1) y t) := by
    intro k hk g hg
    have hck : ocCutoff x.c.D.α x.c.D.q x.c.D.Λ (G'.level + 1) k.1 t ≠ 0 := by
      simpa [activeSlots] using hk
    have htk := mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hΛ) hck
    rw [← hL] at htk
    have ht' := inv_mul_mem_liftWindowOf hcell htk
    have hwin : (x.c.D.cellScaleSq G.level)⁻¹ * t ∈ Icc (x.left k.1) (x.right k.1) := by
      simpa only [Case.left, Case.right, weakSlotLeft, weakSlotRight, liftWindowOf, hlevel] using ht'
    exact x.sourceFiniteOrder hcommon hX hZ s hs k.1 k.2 hj t hwin _ g hg
  have key := tc_piece_eulerian x.c.D hΛ G'.level p.1 t y (s.lam G.level A.η₀)
    s.degree L hfo (G'.fam.identity v u γ).map Dc
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)) j
  rw [tc_material_symm hnat p t, hmax, hsrc]
  refine Eq.trans ?_ key
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun α _ => ?_
  have hd2 := (Finset.mem_Icc.mp hd).1
  refine congrArg (fun z : Vec 2 => z j • (G'.fam.identity v u γ).map
    (orderedDerivative α f y)) ?_
  exact transportedCoeff_congr _ _ (fun e he _ I =>
    x.dimFluxNative hcommon v u γ p t hcp _ e (by omega) I) α y

/-- A glued actual source is the differential operator of its coefficients from order two. -/
theorem Case.sourceEulerExpansion (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    {v u : CompIn (x.c.stage (x.i - 1)).comps}
    (γ : (x.c.stage (x.i - 1)).fam.Γ v u) (t : ℝ) (Dc : ℕ)
    (hDc : (x.witness.e v u γ).1.degree ≤ Dc)
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : Vec 2) (j : Fin 2) :
    x.sourceEuler γ t f y j =
      ∑ d ∈ Finset.Icc 2 Dc, ∑ I : DerivativeWord2 (d - 1),
        fluxCoeff (x.sourceEuler γ t) d I y j * orderedDerivative I f y := by
  let G := x.c.stage x.i
  let s := (x.witness.e v u γ).1
  let L := fun k => s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
    (nativeChain G.level k)
  have hlevel : G.level = x.i := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hpos : 1 ≤ G.level := by rw [hlevel]; have := x.lower; omega
  have hlev : G.level - 1 + 1 = G.level := Nat.sub_add_cancel hpos
  have he : x.sourceEuler γ t = gluedFluxOp x.c.D (G.level - 1 + 1) L t := by
    change gluedFluxOp x.c.D G.level L t = gluedFluxOp x.c.D (G.level - 1 + 1) L t
    rw [hlev]
  have hj : x.c.j₀ ≤ G.level := by
    rw [hlevel]; have := x.startFloor hcommon; have := x.lower; omega
  obtain ⟨hΛ0, _, hζ, hband⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hcell := EntryWeakProofs.weakData_cellScaleSq_pos x.c.D hΛ hζ hband G.level
  rw [he]
  refine sml_glued_expansion x.c.D hΛ (G.level - 1) t y s.degree Dc hDc L ?_ hf j
  intro k hk g hg
  have hck : ocCutoff x.c.D.α x.c.D.q x.c.D.Λ G.level k.1 t ≠ 0 := by
    have hck : ocCutoff x.c.D.α x.c.D.q x.c.D.Λ (G.level - 1 + 1) k.1 t ≠ 0 := by
      simpa [activeSlots] using hk
    simpa only [hlev] using hck
  have htk := mem_ocPulseWindow_of_ocCutoff_ne_zero (Construction.Stream.ocTau_pos hΛ) hck
  have ht' := inv_mul_mem_liftWindowOf hcell htk
  have hwin : (x.c.D.cellScaleSq G.level)⁻¹ * t ∈ Icc (x.left k.1) (x.right k.1) := by
    simpa only [Case.left, Case.right, weakSlotLeft, weakSlotRight, liftWindowOf, hlevel] using ht'
  exact x.sourceFiniteOrderFromTwo hcommon hX hZ s (x.witness.e v u γ).2.1
    k.1 k.2 hj t hwin _ g hg

/-- The physical stored edge contracts to the native glued source, at any finite order cap. -/
theorem Case.edgePhysicalFlux (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (v u : CompIn (x.c.stage (x.i - 1)).comps)
    (γ : (x.c.stage (x.i - 1)).fam.Γ v u) (t : ℝ) (Dc : ℕ)
    (f : Vec 2 → ScalarH u.1.root) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (y : Vec 2) (j : Fin 2) :
    let G' := x.c.stage (x.i - 1)
    let s := (x.witness.e v u γ).1
    ∑ d ∈ Finset.Icc 2 Dc, G'.physCoeff v u γ d t y
        (WithLp.toLp 2 (fun I => orderedDerivative I f y)) j =
      (s.lam (x.c.stage x.i).level A.η₀ •
        fluxOpApply Dc (x.sourceEuler γ t) (G'.fam.identity v u γ).map f y) j := by
  classical
  dsimp only
  let G' := x.c.stage (x.i - 1)
  have hpw := (x.c.construction.2.2 x.i x.lower x.upper).1
  have hnat : G'.IsNatural (x.c.M + A.Jw) := hpw.2.2.2.2.1
  have hΛ : 1 ≤ x.c.D.Λ := by
    have := (Comparison.weakPassageInstance_base x.c).1; omega
  simp only [tc_physCoeff_apply]
  rw [Finset.sum_comm]
  have hpiece : ∀ p ∈ (G'.fam.locally_finite t t).toFinset,
      (∑ d ∈ Finset.Icc 2 Dc, G'.fam.weight p t •
        ∑ I : DerivativeWord2 (d - 1),
          transportedCoeff (chartInvJacobian ⇑((G'.fam.piece p).material t).symm)
            (G'.fam.identity v u γ).maxOrder
            (fun e J => G'.fam.dimFlux (x.c.D.kap G'.level) (x.c.D.eps G'.level)
              (x.c.D.eps (G'.level - 1)) p (G'.actual p) v u γ e J t
              (((G'.fam.piece p).material t).symm y)
              ((x.c.D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm y))
            (d - 1) I y j • (G'.fam.identity v u γ).map (orderedDerivative I f y)) =
        G'.fam.weight p t • (((x.witness.e v u γ).1.lam (x.c.stage x.i).level A.η₀ •
          fluxOpApply Dc (x.sourceEuler γ t) (G'.fam.identity v u γ).map f y) j) := by
    intro p _
    rw [← Finset.smul_sum]
    by_cases hw : G'.fam.weight p t = 0
    · rw [hw, zero_smul, zero_smul]
    · rw [x.pieceFlux hcommon hX hZ v u γ p t
        (by rw [← hnat.2.1 p t]; exact hw) Dc f hf y j]
      rfl
  rw [Finset.sum_congr rfl hpiece, ← Finset.sum_smul, tc_weight_sum_one G' hnat hΛ t,
    one_smul]
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
end
end
end
