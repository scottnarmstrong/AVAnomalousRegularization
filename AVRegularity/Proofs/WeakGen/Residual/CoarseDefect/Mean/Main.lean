-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.Mean.LetterSums
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeFluxOrderBound
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.MacroSwapLettersReg
import AVRegularity.CycleReference.ChartTestTransport

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean

/-! Identification of the literal weak pulse data with the incoming native
fibre on the original closed pulse window. This is the existing data agreement
used by the lift sequence, now read by the slow mean flux. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window GenSem
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.EntryTerminal.Ingredients.Recon

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The native fibre is the restricted ambient lift data `weakCapData`. -/
theorem Case.nativeData_eq_cap (x : Case plan R) (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) :
    x.nativeData k hk hj = weakCapData x.c x.i k hk := by
  have hctx : x.native k hk hj = (x.c.stage x.i).actual ⟨k, hk⟩ :=
    Subtype.ext (x.natural.2.2.1 ⟨k, hk⟩).symm
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  dsimp only [Case.nativeData]
  rw [hctx, hlevel]
  rfl

/-- The actual pulse and the raw native fibre agree throughout their closed native window. -/
theorem Case.nativeData_agree (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (τ : ℝ) (hτ : τ ∈ Icc (x.left k) (x.right k)) :
    (x.nativeData k hk hj).η = (x.data k).η ∧
      Seq.SeqAgreeAt (x.nativeData k hk hj) (x.data k) τ := by
  have hclock : x.clock = x.c.D.cellScaleSq x.i :=
    weakWindow_cellTime x.c x.i x.lower (Reduction.weakPassageRawSetting x.c).kappa_pos
  have hpos : 0 < x.c.D.cellScaleSq x.i := hclock ▸ (x.scales hcommon).1
  have hp : x.c.D.cellScaleSq x.i * τ ∈
      ocPulseWindow x.c.D.α x.c.D.q x.c.D.Λ x.i k :=
    Residual.weakNativeQuietMemWindow hpos hτ
  have he : x.data k = wLiftData x.c x.i x.lower x.upper k := rfl
  rw [x.nativeData_eq_cap k hk hj, he]
  have hg := weakSeqAgree_of x.c x.i x.lower x.upper k hk
  exact ⟨hg.1, hg.2 τ hp⟩

/-- The literal pulse mean flux may be read on the unmasked incoming native data. -/
theorem Case.pulseMean_native (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : k ∈ x.pulses) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (n : ℕ) (t : ℝ) (ht : t ∈ x.interval) (hne : x.weight k t ≠ 0)
    (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) :
    pulseMeanFluxEuler x.clock x.length x.contrast n x.grade
      (x.data k) (x.input.CcR x.i k) (x.chart k) (x.label k) a t y v =
    pulseMeanFluxEuler x.clock x.length x.contrast n x.grade
      (x.nativeData k (CycleComparison.LiftSetting.obsPulse_odd hk) hj) (x.input.CcR x.i k)
      (x.chart k) (x.label k) a t y v := by
  have hwin := (weakCoarsePulseGeometry hcommon x).support k hk t ht hne
  have hag := x.nativeData_agree hcommon k (CycleComparison.LiftSetting.obsPulse_odd hk) hj _ hwin
  let Q : LiftOperatorData (CompIn (x.c.stage x.i).comps)
      (fun v => ScalarH v.1.root) x.cap :=
    x.nativeData k (CycleComparison.LiftSetting.obsPulse_odd hk) hj
  let Q' : LiftOperatorData (CompIn (x.c.stage x.i).comps)
      (fun v => ScalarH v.1.root) x.cap := x.data k
  let b : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root :=
    fun s X => a (x.clock * s) (x.chart k (x.clock * s) (x.length • X))
  have he := liftFluxX_congr_data Q Q' hag.1 (x.input.CcR x.i k) b x.grade n hag.2
  change pulseMeanFluxEuler x.clock x.length x.contrast n x.grade Q' (x.input.CcR x.i k)
      (x.chart k) (x.label k) a t y v =
    pulseMeanFluxEuler x.clock x.length x.contrast n x.grade Q (x.input.CcR x.i k)
      (x.chart k) (x.label k) a t y v
  unfold pulseMeanFluxEuler
  change (fun j => ∑ l : Fin 2, jacMatrix (x.chart k t) (x.label k t y) j l •
      ((-(x.clock⁻¹ * x.contrast ^ n * x.length)) •
        fieldCellMean (fun z => liftFluxX Q' (x.input.CcR x.i k) b x.grade n
          (x.clock⁻¹ * t) (x.length⁻¹ • x.label k t y) z l) v)) =
    fun j => ∑ l : Fin 2, jacMatrix (x.chart k t) (x.label k t y) j l •
      ((-(x.clock⁻¹ * x.contrast ^ n * x.length)) •
        fieldCellMean (fun z => liftFluxX Q (x.input.CcR x.i k) b x.grade n
          (x.clock⁻¹ * t) (x.length⁻¹ • x.label k t y) z l) v)
  rw [← he]

/-- A retained inherited source uses exactly the capped native path mean selected by the
full-fibre decomposition, independently of its degree. -/
theorem Case.inheritedNative (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    {g : ℕ} (hg : 1 ≤ g) (π : StagePath (x.c.stage x.i) g)
    (n : ℕ) (hn : n ∈ Finset.Icc 2 (A.Nw + x.incomingOrder))
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (t : ℝ) (ht : (x.c.D.cellScaleSq (x.c.stage x.i).level)⁻¹ * t ∈ Icc (x.left k) (x.right k)) :
    (WeakSource.inherited [] g π n).fluxOp x.length
      (x.witness.Cc (.inherited [] g π n)) x.witness.Cc0 k t
        (nativeChain (x.c.stage x.i).level k) =
      pathMeanFlux x.c.D (x.c.stage x.i).level x.length
        (x.pathData π.recap k hk (x.native k hk hj))
        (x.pathCoefficients π.recap k hk (x.native k hk hj)) n t := by
  classical
  let ctx := x.native k hk hj
  let πc : StagePath (weakWindowStage x.c x.i x.lower x.upper) g := π.recap
  let Q := familyLiftData x.c.D (x.c.stage x.i).level k ctx.1 x.length
    (pathEdges (x.c.stage x.i) π ⟨k, hk⟩ ctx)
  let Cc := x.witness.Cc (.inherited [] g π n) k ctx.1
  have hc : IsAdmissibleChain x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) ∧ Odd k := ⟨ctx.2, hk⟩
  have hs : (WeakSource.inherited [] g π n).Valid A.Nw A.Rw x.incomingOrder :=
    ⟨Or.inl rfl, hg, (Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2⟩
  have hncap := (x.validDegree (.inherited [] g π n) hs).2
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by
    rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
  have heQ : x.pathData πc k hk ctx = restrictData x.c.order_ge Q := by
    have he := familyLiftData_recap (hN := weakStage_maxOrder_le x.c x.i x.lower x.upper)
      (𝒮 := (x.c.stage x.i).exports) x.c.order_ge π ⟨k, hk⟩ ctx k ctx.1
      (x.c.D.eps ((x.c.stage x.i).level - 1))
    simp only [Case.pathData, heps, πc, Q] at he ⊢
    with_unfolding_all exact he
  have hE : EdgesBelow x.cap Q.edge :=
    edgesBelow_liftEdges (edgesBelow_pathEdges (weakStage_maxOrder_le x.c x.i x.lower x.upper)
      π ⟨k, hk⟩ ctx) _ _
  have hr := pathMeanFlux_restrict x.c.order_ge x.c.D (x.c.stage x.i).level x.length hE Cc hncap t
  rw [← heQ] at hr
  have hCc : Cc = x.pathCoefficients πc k hk ctx [] n := by
    have he : x.originalPath πc = π := by cases π; rfl
    dsimp only [Case.pathCoefficients]
    change x.witness.Cc (.inherited [] g π n) k ctx.1 =
      x.witness.Cc (.inherited [] g (x.originalPath πc) n) k ctx.1
    rw [he]
  have hchoice := x.pathMeanChoice hcommon hX hZ πc k hk hj [] n n t ht
  rw [← hCc] at hchoice
  simp only [WeakSource.fluxOp, dite_eq_left hc]
  exact hr.symm.trans hchoice

/-- An incoming positive path cannot produce a mean above its actual retained order. -/
theorem Case.pathHighZero (x : Case plan R) {g : ℕ} (hg : 1 ≤ g)
    (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) g)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (hX : x.cap ≤ R.sX) (hZ : x.cap ≤ R.sZ)
    (t : ℝ) (ht : (x.c.D.cellScaleSq (x.c.stage x.i).level)⁻¹ * t ∈ Icc (x.left k) (x.right k))
    (n : ℕ) (hn : A.Nw + x.incomingOrder < n)
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : Vec 2) :
    pathMeanFlux x.c.D (x.c.stage x.i).level x.length
      (x.pathData π k hk (x.native k hk hj))
      (x.pathCoefficients π k hk (x.native k hk hj)) n t f y = 0 := by
  let G := weakWindowStage x.c x.i x.lower x.upper
  let ctx := x.native k hk hj
  let Q := x.pathData π k hk ctx
  let Cc := x.pathCoefficients π k hk ctx
  have hbound : G.maxOrderBound x.incomingOrder :=
    (x.c.construction.2.2 x.i x.lower x.upper).1.2.2.1
  have hE : 2 ≤ x.incomingOrder :=
    ((G.fam.identity _ _ (π.step ⟨0, hg⟩).2.2).two_le).trans
      (hbound _ _ (π.step ⟨0, hg⟩).2.2)
  have hev : ∀ j, OrderBound.EdgeVanish G x.incomingOrder (π.step j).2.2 := by
    intro j p c d I _ hd
    exact G.fam.flux_zero p c _ _ (π.step j).2.2 d I (fun h =>
      (Nat.not_le_of_lt hd) (h.2.trans (hbound _ _ _)))
  have hs := x.selectedPathSequence π k hk hj [] 2
  have hseq := WeakEntryProofs.liftSequenceOn_of_global Set.univ Q R.sX R.sZ
    (x.left k) (x.right k) A.Nw g Cc hs
  refine OrderBound.pathMeanFlux_eq_zero_of_degree x.c.D (x.c.stage x.i).level x.length
    Q Cc isOpen_univ hseq hX hZ hE ht ?_ hn hf (Set.mem_univ _)
  intro v u d hd γ hγ I X z j
  have he := OrderBound.pathEdges_coeff_eq_zero π ⟨k, hk⟩ ctx hev
    (x.c.D.cellScaleSq (x.c.stage x.i).level)
    (x.c.D.eps ((x.c.stage x.i).level - 1) /
      x.c.D.eps ((x.c.stage x.i).level - 1)) v u d
    (by rw [max_eq_right hE]; exact hd) γ hγ I
    ((x.c.D.cellScaleSq (x.c.stage x.i).level)⁻¹ * t) X z j
  exact he

/-- Pushing a native scalar path mean gives the literal Eulerian pulse mean. -/
theorem Case.pathPulseEuler (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    {g : ℕ} (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) g)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (n : ℕ) (t : ℝ) (f : Vec 2 → ℝ) (y : Vec 2) (j : Fin 2) :
    pushFlux (x.chart k t) (x.label k t)
      (pathMeanFlux x.c.D (x.c.stage x.i).level x.length
        (x.pathData π k hk (x.native k hk hj))
        (x.pathCoefficients π k hk (x.native k hk hj)) n t) f y j =
      pulseMeanFluxEuler x.clock x.length x.contrast n g
        (x.pathData π k hk (x.native k hk hj))
        (x.pathCoefficients π k hk (x.native k hk hj)) (x.chart k) (x.label k)
        (fun _ z => (Pi.single (0 : Fin (g + 1)) (f z) : Fin (g + 1) → ℝ))
        t y (Fin.last g) j := by
  let Q := x.pathData π k hk (x.native k hk hj)
  let Cc := x.pathCoefficients π k hk (x.native k hk hj)
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hclock : x.c.D.cellScaleSq (x.c.stage x.i).level = x.clock := by
    rw [hlevel]
    exact (weakWindow_cellTime x.c x.i x.lower
      (Reduction.weakPassageRawSetting x.c).kappa_pos).symm
  have hcontrast : ocDStar x.c.D.q x.c.D.Λ (x.c.stage x.i).level
      (x.c.D.kap (x.c.stage x.i).level) (x.c.D.kap ((x.c.stage x.i).level - 1)) /
      x.length = x.contrast := by
    rw [hlevel, wSetting_kap x.c x.i x.lower, wSetting_kap_pred x.c x.i x.lower]
  have hclk : x.clock * (x.clock⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ (x.scales hcommon).1.ne', one_mul]
  have he := right_liftFluxX_time_congr Q Cc
    (fun _ X => (Pi.single (0 : Fin (g + 1))
      (f (x.chart k t (x.length • X))) : Fin (g + 1) → ℝ))
    (fun τ X => (Pi.single (0 : Fin (g + 1))
      (f (x.chart k (x.clock * τ) (x.length • X))) : Fin (g + 1) → ℝ))
    g n (x.clock⁻¹ * t) (by rw [hclk])
  unfold pushFlux pulseMeanFluxEuler pathMeanFlux
  simp only [hclock, hcontrast, Matrix.mulVec, dotProduct, Function.comp_apply]
  rw [he]
  rfl

/-- The positive native pulse mean is the sum of the pushed scalar path means. -/
theorem Case.positivePulseMean (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (g : ℕ) (hg : g + 1 ≤ A.Jw * A.Rw)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (n : ℕ) (t : ℝ)
    (ht : x.clock⁻¹ * t ∈ Icc (x.left k) (x.right k))
    (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (j : Fin 2) :
    pulseMeanFluxEuler x.clock x.length x.contrast n (g + 1)
      (x.nativeData k hk hj) (x.input.CcR x.i k) (x.chart k) (x.label k)
      (fun _ => a) t y v j =
      ∑ᶠ π : StagePath (weakWindowStage x.c x.i x.lower x.upper) (g + 1),
        if hπ : π.tgt = v.1 ∧ π.src ∈ (x.c.stage x.i).comps then
          pushFlux (x.chart k t) (x.label k t)
            (pathMeanFlux x.c.D (x.c.stage x.i).level x.length
              (x.pathData π k hk (x.native k hk hj))
              (x.pathCoefficients π k hk (x.native k hk hj)) n t)
            (fun z => a z ⟨π.src, hπ.2⟩) y j else 0 := by
  classical
  let G := weakWindowStage x.c x.i x.lower x.upper
  let : Fintype (StagePath G (g + 1)) := Fintype.ofFinite _
  let b := fun τ X => a (x.chart k (x.clock * τ) (x.length • X))
  have hclk : x.clock * (x.clock⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ (x.scales hcommon).1.ne', one_mul]
  have hchart : ContDiff ℝ (⊤ : ℕ∞) (x.chart k t) := by
    exact ((CycleComparison.Charts.contDiff_ocChart_joint (x.c.D.hΦ (x.i - 1))
      x.c.D.α x.c.D.q x.c.D.Λ x.i
      (ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k)).comp
      (contDiff_const.prodMk contDiff_id))
  have hb : ContDiff ℝ (⊤ : ℕ∞) (b (x.clock⁻¹ * t)) := by
    simp only [b, hclk]
    exact ha.comp (hchart.comp (contDiff_const_smul _))
  have hm (l : Fin 2) := x.nativePositiveMean hcommon k hk hj hX hZ g hg
    (x.clock⁻¹ * t) ht b hb n
    (x.length⁻¹ • x.label k t y) l v (ContinuousLinearMap.id ℝ ℝ)
  have hpath (π : StagePath G (g + 1))
      (hπ : π.tgt = v.1 ∧ π.src ∈ (x.c.stage x.i).comps) :
      hlIn G π (r := v.1.root) (ContinuousLinearMap.id ℝ ℝ) b =
        fun τ X => (Pi.single (0 : Fin (g + 2))
          (a (x.chart k (x.clock * τ) (x.length • X)) ⟨π.src, hπ.2⟩) : Fin (g + 2) → ℝ) := by
    funext τ X
    unfold hlIn
    have hmem : π.src ∈ G.comps := hπ.2
    rw [dite_eq_left hmem]
    have he : rootPathMap ScalarH π.src.root π.mapList v.1.root =
        ContinuousLinearMap.id ℝ ℝ := by
      rw [← hπ.1]
      exact x.pathMap π
    rw [he]
    rfl
  have hterm (π : StagePath G (g + 1))
      (hπ : π.tgt = v.1 ∧ π.src ∈ (x.c.stage x.i).comps) :
      pushFlux (x.chart k t) (x.label k t)
          (pathMeanFlux x.c.D (x.c.stage x.i).level x.length
            (x.pathData π k hk (x.native k hk hj))
            (x.pathCoefficients π k hk (x.native k hk hj)) n t)
          (fun z => a z ⟨π.src, hπ.2⟩) y j =
        ∑ l : Fin 2, jacMatrix (x.chart k t) (x.label k t y) j l *
          (-(x.clock⁻¹ * x.contrast ^ n * x.length) *
            fieldCellMean (fun z => liftFluxX (x.pathData π k hk (x.native k hk hj))
              (x.pathCoefficients π k hk (x.native k hk hj))
              (hlIn G π (r := v.1.root) (ContinuousLinearMap.id ℝ ℝ) b) (g + 1) n (x.clock⁻¹ * t)
              (x.length⁻¹ • x.label k t y) z l) (Fin.last (g + 1))) := by
    rw [x.pathPulseEuler hcommon π k hk hj n t _ y j]
    unfold pulseMeanFluxEuler
    rw [hpath π hπ]
    rfl
  simp only [ContinuousLinearMap.id_apply] at hm
  dsimp only [b] at hm
  unfold pulseMeanFluxEuler
  simp only [smul_eq_mul, hm, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases hπ : π.tgt = v.1 ∧ π.src ∈ (x.c.stage x.i).comps
  · simp only [hπ]
    exact (hterm π hπ).symm
  · simp only [hπ, ite_false, dite_false, mul_zero, Finset.sum_const_zero]

private theorem weakMean_metric_cancel (J : Matrix (Fin 2) (Fin 2) ℝ)
    (hJ : IsUnit J.det) (u : Vec 2) :
    J.mulVec ((J⁻¹ * J⁻¹.transpose).mulVec (J.transpose.mulVec u)) = u := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv J hJ, Matrix.one_mul, Matrix.transpose_nonsing_inv J,
    Matrix.nonsing_inv_mul J.transpose (by rwa [Matrix.det_transpose]), Matrix.one_mulVec]

/-- The native metric removes both chart Jacobians from the molecular flux. -/
theorem Case.molecularMetric (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ)
    (t : ℝ) (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : Vec 2) (j : Fin 2) :
    (∑ l : Fin 2, jacMatrix (x.chart k t) (x.label k t y) j l *
      ∑ q : Fin 2, (x.scalarData k).G (x.clock⁻¹ * t)
        (x.length⁻¹ • x.label k t y) l q *
        fderiv ℝ (fun X => f (x.chart k t (x.length • X)))
          (x.length⁻¹ • x.label k t y) (basisVec q)) =
      x.length * fderiv ℝ f y (basisVec j) := by
  let J := jacMatrix (x.chart k t) (x.label k t y)
  let u : Vec 2 := fun p => fderiv ℝ f y (basisVec p)
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hc : x.c.D.cellScaleSq (x.c.stage x.i).level = x.clock := by
    rw [hlevel]
    exact (weakWindow_cellTime x.c x.i x.lower
      (Reduction.weakPassageRawSetting x.c).kappa_pos).symm
  have hclk : x.clock * (x.clock⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ (x.scales hcommon).1.ne', one_mul]
  have hρ : x.length • (x.length⁻¹ • x.label k t y) = x.label k t y :=
    smul_inv_smul₀ (x.scales hcommon).2.ne' _
  have hchart : x.chart k = fun t y =>
      x.c.D.flowOf ((x.c.stage x.i).level - 1) t y
        (x.c.D.slotAnchor (x.c.stage x.i).level k) := by
    funext t y
    simp only [Case.chart, hlevel]
    unfold ocChart OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k
      (Construction.Stream.ocTauPP_pos (by
        have := (Comparison.weakPassageInstance_base x.c).1; omega))]
  have hG : (x.scalarData k).G (x.clock⁻¹ * t)
      (x.length⁻¹ • x.label k t y) = J⁻¹ * J⁻¹.transpose := by
    have he := EntryWeakProofs.native_familyLiftData_metric x.c.D
      (x.c.stage x.i).level (by rw [hlevel]; have := x.lower; omega) k x.length
      (Dm := x.cap) (h := fun _ : Fin 1 => ℝ) (fun _ _ _ => [])
      (x.clock⁻¹ * t) (x.length⁻¹ • x.label k t y)
    rw [hc, hclk, hρ] at he
    rw [← congrFun hchart t] at he
    exact he
  have hdiff : Differentiable ℝ (x.chart k t) :=
    ((CycleComparison.Charts.contDiff_ocChart_joint (x.c.D.hΦ (x.i - 1))
      x.c.D.α x.c.D.q x.c.D.Λ x.i
      (ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k)).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hinv : x.chart k t (x.label k t y) = y :=
    CycleComparison.Charts.ocChart_ocChartInv _ _ _ _ _ _ _ _ y
  have hder (q : Fin 2) :
      fderiv ℝ (fun X => f (x.chart k t (x.length • X)))
        (x.length⁻¹ • x.label k t y) (basisVec q) = x.length * (J.transpose.mulVec u) q := by
    have hd := fderiv_comp_smul (f := fun Z => f (x.chart k t Z))
      (x := x.length⁻¹ • x.label k t y) x.length
    rw [hd, smul_apply, hρ]
    change x.length * fderiv ℝ (f ∘ x.chart k t) (x.label k t y) (basisVec q) = _
    rw [fderiv_comp (x.label k t y) (hf.differentiable (by simp) _) (hdiff _),
      ContinuousLinearMap.comp_apply, CycleComparison.ActualMeans.fderiv_basisVec_eq_sum,
      map_sum, hinv]
    simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.transpose_apply, J, u]
  rw [hG]
  simp_rw [hder]
  have hunit : IsUnit J.det := by
    rw [show J.det = 1 from CycleComparison.Charts.ocChart_det
      (x.c.D.hΦ (x.i - 1)) _ _ _ _ _ t _]
    exact isUnit_one
  have he := congrFun (weakMean_metric_cancel J hunit u) j
  change (∑ l : Fin 2, J j l * ∑ q : Fin 2,
    (J⁻¹ * J⁻¹.transpose) l q * (J.transpose.mulVec u) q) = u j at he
  calc
    _ = x.length * (∑ l : Fin 2, J j l *
        ∑ q : Fin 2, (J⁻¹ * J⁻¹.transpose) l q * (J.transpose.mulVec u) q) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ => ?_
      dsimp only [J]
      ring
    _ = _ := by rw [he]

/-- The diagonal native pulse is the scalar diagonal pulse on the selected component. -/
theorem Case.zeroPulseScalar (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (n : ℕ) (t : ℝ)
    (ht : x.clock⁻¹ * t ∈ Icc (x.left k) (x.right k))
    (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (j : Fin 2) :
    pulseMeanFluxEuler x.clock x.length x.contrast n 0
      (x.nativeData k hk hj) (x.input.CcR x.i k) (x.chart k) (x.label k)
      (fun _ => a) t y v j =
    pulseMeanFluxEuler x.clock x.length x.contrast n 0
      (x.scalarData k) (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k))
      (x.chart k) (x.label k) (fun _ z (_ : Fin 1) => a z v) t y 0 j := by
  let b := fun τ X => a (x.chart k (x.clock * τ) (x.length • X))
  have hchart : ContDiff ℝ (⊤ : ℕ∞) (x.chart k (x.clock * (x.clock⁻¹ * t))) :=
    ((CycleComparison.Charts.contDiff_ocChart_joint (x.c.D.hΦ (x.i - 1))
      x.c.D.α x.c.D.q x.c.D.Λ x.i
      (ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k)).comp
      (contDiff_const.prodMk contDiff_id))
  have hb : ContDiff ℝ (⊤ : ℕ∞) (b (x.clock⁻¹ * t)) :=
    ha.comp (hchart.comp (contDiff_const_smul _))
  have hm (l : Fin 2) := x.nativeZeroMean hcommon k hk hj hX hZ
    (x.clock⁻¹ * t) ht b hb n (x.length⁻¹ • x.label k t y) l v
    (ContinuousLinearMap.id ℝ ℝ)
  simp only [ContinuousLinearMap.id_apply] at hm
  dsimp only [b] at hm
  unfold pulseMeanFluxEuler
  simp only [hm]
  rfl

private theorem weakMean_singleFinOne (z : ℝ) :
    (Pi.single (0 : Fin 1) z : Fin 1 → ℝ) = fun _ => z := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact Pi.single_eq_same (M := fun _ : Fin 1 => ℝ) 0 z

/-- The scalar diagonal pulse splits into the eddy mean and its degree-two molecular term. -/
theorem Case.scalarPulseSplit (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : 1 ≤ R.sX) (hZ : 1 ≤ R.sZ)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : x.clock⁻¹ * t ∈ Icc (x.left k) (x.right k))
    (y : Vec 2) (j : Fin 2) :
    pulseMeanFluxEuler x.clock x.length x.contrast n 0
      (x.scalarData k) (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k))
      (x.chart k) (x.label k) (fun _ z (_ : Fin 1) => f z) t y 0 j =
    pushFlux (x.chart k t) (x.label k t)
      (weakEddyFlux x.c.D (x.c.stage x.i).level x.length (x.scalarData k)
        (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) n t) f y j +
      if n = 2 then
        x.clock⁻¹ * x.contrast ^ 2 * x.length ^ 2 * fderiv ℝ f y (basisVec j) else 0 := by
  classical
  let Q := x.scalarData k
  let Cc := x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)
  let F : Vec 2 → ℝ := fun X => f (x.chart k t (x.length • X))
  let b : Vec 2 → Fin 1 → ℝ := fun X _ => F X
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hc : x.c.D.cellScaleSq (x.c.stage x.i).level = x.clock := by
    rw [hlevel]
    exact (weakWindow_cellTime x.c x.i x.lower
      (Reduction.weakPassageRawSetting x.c).kappa_pos).symm
  have hcontrast : ocDStar x.c.D.q x.c.D.Λ (x.c.stage x.i).level
      (x.c.D.kap (x.c.stage x.i).level) (x.c.D.kap ((x.c.stage x.i).level - 1)) /
      x.length = x.contrast := by
    rw [hlevel, wSetting_kap x.c x.i x.lower, wSetting_kap_pred x.c x.i x.lower]
  have hclk : x.clock * (x.clock⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ (x.scales hcommon).1.ne', one_mul]
  have hη : Q.η = 1 := by
    change x.c.D.kap (x.c.stage x.i).level / x.c.D.kap ((x.c.stage x.i).level - 1) = 1
    rw [hlevel, wSetting_kap x.c x.i x.lower, wSetting_kap_pred x.c x.i x.lower,
      div_self (Reduction.weakPassageRawSetting x.c).kappa_pos.ne']
  have hchart : ContDiff ℝ (⊤ : ℕ∞) (x.chart k t) :=
    ((CycleComparison.Charts.contDiff_ocChart_joint (x.c.D.hΦ (x.i - 1))
      x.c.D.α x.c.D.q x.c.D.Λ x.i
      (ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k)).comp
      (contDiff_const.prodMk contDiff_id))
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hf.comp (hchart.comp (contDiff_const_smul _))
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := contDiff_pi.mpr fun _ => hF
  have htime := right_liftFluxX_time_congr Q Cc
    (fun τ X (_ : Fin 1) => f (x.chart k (x.clock * τ) (x.length • X)))
    (fun _ => b) 0 n (x.clock⁻¹ * t) (by funext X i; rw [hclk])
  have hm (l : Fin 2) := weakMean_gradeZeroFlux Q Cc (x.scalarSequence k hk hj)
    hX hZ b hb n hn (x.clock⁻¹ * t) ht (x.length⁻¹ • x.label k t y) l
    ((hl_familyLiftData_drift_smooth x.c.D (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) x.length
      (fun (_ _ : Fin 1) _ => []) (x.clock⁻¹ * t) l).continuous)
  have hder (q : Fin 2) :
      (fderiv ℝ b (x.length⁻¹ • x.label k t y) (basisVec q)) 0 =
        fderiv ℝ F (x.length⁻¹ • x.label k t y) (basisVec q) := by
    rw [fderiv_pi (fun (_ : Fin 1) => hF.differentiable (by simp) _)]
    rfl
  have hη0 : (x.scalarData k).η = 1 := hη
  unfold pulseMeanFluxEuler pushFlux weakEddyFlux
  simp only [hc, hcontrast, Matrix.mulVec, dotProduct, Function.comp_apply,
    weakMean_singleFinOne]
  rw [htime]
  simp_rw [hm]
  simp only [Pi.sub_apply, apply_ite, hη, hη0]
  by_cases hn2 : n = 2
  · subst n
    simp only [ite_true, one_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hder,
      mul_sub, Finset.sum_sub_distrib]
    have hmetric := x.molecularMetric hcommon k t f hf y j
    change _ - ∑ l : Fin 2, jacMatrix (x.chart k t) (x.label k t y) j l *
        (-(x.clock⁻¹ * x.contrast ^ 2 * x.length) *
          ∑ q : Fin 2, Q.G (x.clock⁻¹ * t) (x.length⁻¹ • x.label k t y) l q *
            fderiv ℝ F (x.length⁻¹ • x.label k t y) (basisVec q)) = _
    have hscale : (∑ l : Fin 2, jacMatrix (x.chart k t) (x.label k t y) j l *
        (-(x.clock⁻¹ * x.contrast ^ 2 * x.length) *
          ∑ q : Fin 2, Q.G (x.clock⁻¹ * t) (x.length⁻¹ • x.label k t y) l q *
            fderiv ℝ F (x.length⁻¹ • x.label k t y) (basisVec q))) =
        -(x.clock⁻¹ * x.contrast ^ 2 * x.length) *
          (x.length * fderiv ℝ f y (basisVec j)) := by
      rw [← hmetric, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hscale]
    ring
  · simp only [hn2, ite_false, Pi.zero_apply, sub_zero, add_zero]
    rfl

/-- The degree-two molecular normalization is exactly the reference diffusivity. -/
theorem Case.molecularScale (hcommon : WeakPassageCommonOK plan) (x : Case plan R) :
    x.clock⁻¹ * x.contrast ^ 2 * x.length ^ 2 = x.c.D.κ x.c.M := by
  have hκ := (Reduction.weakPassageRawSetting x.c).kappa_pos
  have hΛ : 1 ≤ x.c.D.Λ := by
    have := (Comparison.weakPassageInstance_base x.c).1; omega
  have hε : ocEpsilon x.c.D.q x.c.D.Λ x.i ≠ 0 :=
    (Construction.Stream.ocEpsilon_pos hΛ).ne'
  change (ocEll x.c.D.q x.c.D.Λ x.i (x.c.D.κ x.c.M) ^ 2)⁻¹ *
    (ocDStar x.c.D.q x.c.D.Λ x.i (x.c.D.κ x.c.M) (x.c.D.κ x.c.M) / x.length) ^ 2 *
      x.length ^ 2 = _
  rw [CycleReference.ocEll_sq_eq hκ, weakWindow_dStar x.c x.i hκ]
  field_simp [hε, (x.scales hcommon).2.ne']

/-- The diagonal native degree sum consists of the retained eddy degrees and reference flux. -/
theorem Case.zeroPulseDegrees (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (t : ℝ)
    (ht : x.clock⁻¹ * t ∈ Icc (x.left k) (x.right k))
    (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (j : Fin 2) :
    (∑ n ∈ Finset.Icc 2 (A.Nw + x.cap),
      pulseMeanFluxEuler x.clock x.length x.contrast n 0
        (x.nativeData k hk hj) (x.input.CcR x.i k) (x.chart k) (x.label k)
        (fun _ => a) t y v j) =
      (∑ n ∈ Finset.Icc 2 (A.Nw + 1),
        pushFlux (x.chart k t) (x.label k t)
          (weakEddyFlux x.c.D (x.c.stage x.i).level x.length (x.scalarData k)
            (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) n t)
          (fun z => a z v) y j) + x.c.D.κ x.c.M * fderiv ℝ (fun z => a z v) y (basisVec j) := by
  classical
  have hX1 : 1 ≤ R.sX := by omega
  have hZ1 : 1 ≤ R.sZ := by omega
  have hcap : 1 ≤ x.cap := by change 1 ≤ 1 + A.Jw * A.Nw; omega
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun z => a z v) := contDiff_pi.mp ha v
  have hchart : ContDiff ℝ (⊤ : ℕ∞) (x.chart k t) :=
    ((CycleComparison.Charts.contDiff_ocChart_joint (x.c.D.hΦ (x.i - 1))
      x.c.D.α x.c.D.q x.c.D.Λ x.i
      (ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k)).comp
      (contDiff_const.prodMk contDiff_id))
  rw [Finset.sum_congr rfl fun n _ => x.zeroPulseScalar hcommon hX hZ k hk hj a ha n t ht y v j]
  have hsmall : (∑ n ∈ Finset.Icc 2 (A.Nw + x.cap),
      pulseMeanFluxEuler x.clock x.length x.contrast n 0
        (x.scalarData k) (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k))
        (x.chart k) (x.label k) (fun _ z (_ : Fin 1) => a z v) t y 0 j) =
      ∑ n ∈ Finset.Icc 2 (A.Nw + 1),
        pulseMeanFluxEuler x.clock x.length x.contrast n 0
          (x.scalarData k) (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k))
          (x.chart k) (x.label k) (fun _ z (_ : Fin 1) => a z v) t y 0 j := by
    symm
    refine Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans (Nat.add_le_add_left hcap _)⟩)
      fun n hn hnot => ?_
    have hn' : A.Nw + 2 ≤ n := by
      have hn2 := (Finset.mem_Icc.mp hn).1
      have hnot' : ¬ (2 ≤ n ∧ n ≤ A.Nw + 1) := by
        simpa only [Finset.mem_Icc] using hnot
      omega
    have hz := pulseMeanFluxEuler_zero (x.scalarData k) (x.scalarData k) R.sX R.sZ
      (x.left k) (x.right k) A.Nw 0 _ (x.scalarSequence k hk hj) hX1 hZ1 A.Nw_pos
      x.clock x.length x.contrast (x.scales hcommon).1.ne' n hn'
      (x.chart k) (x.label k) (fun _ z (_ : Fin 1) => a z v) t y
      (contDiff_pi.mpr fun _ => hv) hchart ht 0
    exact congrFun hz j
  rw [hsmall]
  rw [Finset.sum_congr rfl fun n hn => x.scalarPulseSplit hcommon hX1 hZ1 k hk hj
    (fun z => a z v) hv n (Finset.mem_Icc.mp hn).1 t ht y j]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  have h2 : 2 ∈ Finset.Icc 2 (A.Nw + 1) := Finset.mem_Icc.mpr ⟨le_rfl, by have := A.Nw_pos; omega⟩
  rw [ite_eq_left h2, x.molecularScale hcommon]

/-- High positive pulse means vanish above the order present in the inherited registry. -/
theorem Case.positivePulseHighZero (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (g : ℕ) (hg : g + 1 ≤ A.Jw * A.Rw)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (n : ℕ) (hn : A.Nw + x.incomingOrder < n)
    (t : ℝ) (ht : x.clock⁻¹ * t ∈ Icc (x.left k) (x.right k))
    (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (j : Fin 2) :
    pulseMeanFluxEuler x.clock x.length x.contrast n (g + 1)
      (x.nativeData k hk hj) (x.input.CcR x.i k) (x.chart k) (x.label k)
      (fun _ => a) t y v j = 0 := by
  classical
  rw [x.positivePulseMean hcommon hX hZ g hg k hk hj a ha n t ht y v j]
  refine finsum_eq_zero_of_forall_eq_zero fun π => ?_
  split_ifs with hπ
  · have hchart : ContDiff ℝ (⊤ : ℕ∞) (x.chart k t) :=
      ((CycleComparison.Charts.contDiff_ocChart_joint (x.c.D.hΦ (x.i - 1))
        x.c.D.α x.c.D.q x.c.D.Λ x.i
        (ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k)).comp
        (contDiff_const.prodMk contDiff_id))
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun z => a (x.chart k t z) ⟨π.src, hπ.2⟩) :=
      (contDiff_pi.mp ha ⟨π.src, hπ.2⟩).comp hchart
    have hc : x.c.D.cellScaleSq (x.c.stage x.i).level = x.clock := by
      rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
      exact (weakWindow_cellTime x.c x.i x.lower
        (Reduction.weakPassageRawSetting x.c).kappa_pos).symm
    have he := x.pathHighZero (Nat.succ_le_succ (Nat.zero_le g)) π k hk hj
      (by omega) (by omega) t (by rwa [hc]) n hn
      (fun z => a (x.chart k t z) ⟨π.src, hπ.2⟩) hf (x.label k t y)
    change ((jacMatrix (x.chart k t) (x.label k t y)).mulVec _) j = 0
    dsimp only [Function.comp_def]
    rw [he, Matrix.mulVec_zero]
    rfl
  · rfl

/-- Every eddy source uses the same capped scalar native lift. -/
theorem Case.eddyNative (x : Case plan R) (v : CompIn (x.c.stage x.i).comps)
    (w : List WordLetter) (n : ℕ) (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) (t : ℝ) :
    (WeakSource.eddy v w n).fluxOp x.length (x.witness.Cc (.eddy v w n)) x.witness.Cc0 k t
      (nativeChain (x.c.stage x.i).level k) =
      weakEddyFlux x.c.D (x.c.stage x.i).level x.length (x.scalarData k)
        (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) n t := by
  have hc : IsAdmissibleChain x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) ∧ Odd k := ⟨(x.native k hk hj).2, hk⟩
  simp only [WeakSource.fluxOp, dite_eq_left hc]
  rfl

/-- The scalar eddy source glue may be read on the fixed observation pulses. -/
theorem Case.eddyEulerFixed (x : Case plan R)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) (n : ℕ)
    (t : ℝ) (ht : t ∈ x.interval) (f : Vec 2 → ℝ) (y : Vec 2) (j : Fin 2) :
    x.sourceEulerOf (.eddy x.v₀ [] n) t f y j =
      ∑ k ∈ x.pulses, x.weight k t *
        pushFlux (x.chart k t) (x.label k t)
          (weakEddyFlux x.c.D (x.c.stage x.i).level x.length (x.scalarData k)
            (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) n t) f y j := by
  rw [x.sourceEulerFixed (.eddy x.v₀ [] n) t ht f y j]
  exact Finset.sum_congr rfl fun k hk => by
    rw [x.eddyNative x.v₀ [] n k (CycleComparison.LiftSetting.obsPulse_odd hk) hj t]

/-- A retained inherited source is the fixed pulse glue of its capped native path means. -/
theorem Case.inheritedEulerFixed (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    {g : ℕ} (hg : 1 ≤ g) (π : StagePath (x.c.stage x.i) g)
    (n : ℕ) (hn : n ∈ Finset.Icc 2 (A.Nw + x.incomingOrder))
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (t : ℝ) (ht : t ∈ x.interval) (f : Vec 2 → ℝ) (y : Vec 2) (j : Fin 2) :
    x.sourceEulerOf (.inherited [] g π n) t f y j =
      ∑ k : x.pulses, x.weight k.1 t *
        pushFlux (x.chart k.1 t) (x.label k.1 t)
          (pathMeanFlux x.c.D (x.c.stage x.i).level x.length
            (x.pathData π.recap k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2)
              (x.native k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2) hj))
            (x.pathCoefficients π.recap k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2)
              (x.native k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2) hj)) n t) f y j := by
  classical
  rw [x.sourceEulerFixed (.inherited [] g π n) t ht f y j]
  rw [← Finset.sum_coe_sort x.pulses (fun k : ℤ => x.weight k t *
    pushFlux (x.chart k t) (x.label k t)
      ((WeakSource.inherited [] g π n).fluxOp x.length
        (x.witness.Cc (.inherited [] g π n)) x.witness.Cc0 k t
        (nativeChain (x.c.stage x.i).level k)) f y j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hw : x.weight k.1 t = 0
  · rw [hw, zero_mul, zero_mul]
  · have hc : x.clock = x.c.D.cellScaleSq (x.c.stage x.i).level := by
      rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
      exact weakWindow_cellTime x.c x.i x.lower (Reduction.weakPassageRawSetting x.c).kappa_pos
    have hwin := (weakCoarsePulseGeometry hcommon x).support k.1 k.2 t ht hw
    rw [hc] at hwin
    rw [x.inheritedNative hcommon hX hZ hg π n hn k.1
      (CycleComparison.LiftSetting.obsPulse_odd k.2) hj t hwin]

/-- The native positive pulse may be indexed by the original paths used by stored sources. -/
theorem Case.positivePulseRegistry (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (g : ℕ) (hg : g + 1 ≤ A.Jw * A.Rw)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (n : ℕ) (t : ℝ)
    (ht : x.clock⁻¹ * t ∈ Icc (x.left k) (x.right k))
    (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (j : Fin 2) :
    (∑ᶠ π : StagePath (x.c.stage x.i) (g + 1), if π.tgt = v.1 then
      pushFlux (x.chart k t) (x.label k t)
        (pathMeanFlux x.c.D (x.c.stage x.i).level x.length
          (x.pathData π.recap k hk (x.native k hk hj))
          (x.pathCoefficients π.recap k hk (x.native k hk hj)) n t)
        (fun z => a z ⟨π.src, (cd_stagePath_mem x.c x.i π (by omega)).1⟩) y j else 0) =
    pulseMeanFluxEuler x.clock x.length x.contrast n (g + 1)
      (x.nativeData k hk hj) (x.input.CcR x.i k) (x.chart k) (x.label k)
      (fun _ => a) t y v j := by
  classical
  let G := weakWindowStage x.c x.i x.lower x.upper
  let : Fintype (StagePath G (g + 1)) := Fintype.ofFinite _
  let : Fintype (StagePath (x.c.stage x.i) (g + 1)) := Fintype.ofFinite _
  let H := fun π : StagePath G (g + 1) =>
    if hπ : π.tgt = v.1 ∧ π.src ∈ (x.c.stage x.i).comps then
      pushFlux (x.chart k t) (x.label k t)
        (pathMeanFlux x.c.D (x.c.stage x.i).level x.length
          (x.pathData π k hk (x.native k hk hj))
          (x.pathCoefficients π k hk (x.native k hk hj)) n t)
        (fun z => a z ⟨π.src, hπ.2⟩) y j else 0
  have hp := x.positivePulseMean hcommon hX hZ g hg k hk hj a ha n t ht y v j
  change pulseMeanFluxEuler x.clock x.length x.contrast n (g + 1)
    (x.nativeData k hk hj) (x.input.CcR x.i k) (x.chart k) (x.label k)
    (fun _ => a) t y v j = ∑ᶠ π : StagePath G (g + 1), H π at hp
  rw [hp, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← (x.pathCapEquiv (g + 1)).sum_comp H]
  refine Finset.sum_congr rfl fun π _ => ?_
  change (if π.tgt = v.1 then _ else 0) = H π.recap
  dsimp only [H]
  by_cases hπ : π.tgt = v.1
  · rw [ite_eq_left hπ]
    split
    · rfl
    · next h => exact (h ⟨hπ, (cd_stagePath_mem x.c x.i π (by omega)).1⟩).elim
  · rw [ite_eq_right hπ]
    split
    · next h => exact (hπ h.1).elim
    · rfl

/-- One retained positive degree glues to its full native pulse mean. -/
theorem Case.sourceDegreePulse (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (g : ℕ) (hg : g + 1 ≤ A.Jw * A.Rw)
    (n : ℕ) (hn : n ∈ Finset.Icc 2 (A.Nw + x.incomingOrder))
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (t : ℝ) (ht : t ∈ x.interval)
    (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (j : Fin 2) :
    (∑ᶠ π : StagePath (x.c.stage x.i) (g + 1), if π.tgt = v.1 then
      x.sourceEulerOf (.inherited [] (g + 1) π n) t
        (fun z => a z ⟨π.src, (cd_stagePath_mem x.c x.i π (by omega)).1⟩) y j else 0) =
      ∑ k : x.pulses, x.weight k.1 t *
        pulseMeanFluxEuler x.clock x.length x.contrast n (g + 1)
          (x.nativeData k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2) hj)
          (x.input.CcR x.i k.1) (x.chart k.1) (x.label k.1) (fun _ => a) t y v j := by
  classical
  let : Fintype (StagePath (x.c.stage x.i) (g + 1)) := Fintype.ofFinite _
  let P := fun (π : StagePath (x.c.stage x.i) (g + 1)) (k : x.pulses) =>
    pushFlux (x.chart k.1 t) (x.label k.1 t)
      (pathMeanFlux x.c.D (x.c.stage x.i).level x.length
        (x.pathData π.recap k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2)
          (x.native k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2) hj))
        (x.pathCoefficients π.recap k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2)
          (x.native k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2) hj)) n t)
      (fun z => a z ⟨π.src, (cd_stagePath_mem x.c x.i π (by omega)).1⟩) y j
  have hterm (π : StagePath (x.c.stage x.i) (g + 1)) :
      (if π.tgt = v.1 then x.sourceEulerOf (.inherited [] (g + 1) π n) t
        (fun z => a z ⟨π.src, (cd_stagePath_mem x.c x.i π (by omega)).1⟩) y j else 0) =
      ∑ k : x.pulses, x.weight k.1 t * (if π.tgt = v.1 then P π k else 0) := by
    by_cases hπ : π.tgt = v.1
    · simp only [hπ, ite_true]
      exact x.inheritedEulerFixed hcommon hX hZ (by omega) π n hn hj t ht _ y j
    · simp only [hπ, ite_false, mul_zero, Finset.sum_const_zero]
  simp only [finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl fun π _ => hterm π, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  by_cases hw : x.weight k.1 t = 0
  · rw [hw, zero_mul, zero_mul]
  · have hwin := (weakCoarsePulseGeometry hcommon x).support k.1 k.2 t ht hw
    have he := x.positivePulseRegistry hcommon hX hZ g hg k.1
      (CycleComparison.LiftSetting.obsPulse_odd k.2) hj a ha n t hwin y v j
    rw [finsum_eq_sum_of_fintype] at he
    exact congrArg (fun z => x.weight k.1 t * z) he

/-- The positive native degree sum stops at the inherited registry's retained order. -/
theorem Case.positivePulseDegrees (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (g : ℕ) (hg : g + 1 ≤ A.Jw * A.Rw)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (t : ℝ)
    (ht : x.clock⁻¹ * t ∈ Icc (x.left k) (x.right k))
    (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (j : Fin 2) :
    (∑ n ∈ Finset.Icc 2 (A.Nw + x.cap),
      pulseMeanFluxEuler x.clock x.length x.contrast n (g + 1)
        (x.nativeData k hk hj) (x.input.CcR x.i k) (x.chart k) (x.label k)
        (fun _ => a) t y v j) =
    ∑ n ∈ Finset.Icc 2 (A.Nw + x.incomingOrder),
      pulseMeanFluxEuler x.clock x.length x.contrast n (g + 1)
        (x.nativeData k hk hj) (x.input.CcR x.i k) (x.chart k) (x.label k)
        (fun _ => a) t y v j := by
  classical
  have hinc : x.incomingOrder ≤ x.cap := by
    change 1 + (x.c.M + A.Jw - x.i) * A.Nw ≤ 1 + A.Jw * A.Nw
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have := x.lower; omega)) _
  symm
  refine Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans (Nat.add_le_add_left hinc _)⟩)
    fun n hn hnot => ?_
  have hn' : A.Nw + x.incomingOrder < n := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hnot' : ¬ (2 ≤ n ∧ n ≤ A.Nw + x.incomingOrder) := by
      simpa only [Finset.mem_Icc] using hnot
    omega
  exact x.positivePulseHighZero hcommon hX hZ g hg k hk hj a ha n hn' t ht y v j

/-- The stored positive block is exactly the glued full native degree sum. -/
theorem Case.positiveGluedAction (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (g : ℕ) (hg : g + 1 ≤ A.Jw * A.Rw)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (t : ℝ) (ht : t ∈ x.interval)
    (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (j : Fin 2) :
    (∑ u : CompIn (x.c.stage x.i).comps, ∑ d : Finset.Icc 2 (A.Nw + x.cap),
      cdCE x.c (A.Nw + x.cap) x.i x.lower x.upper (g + 1) v u d t y
        (WithLp.toLp 2 (fun I => orderedDerivative I (fun z => a z u) y)) j) =
      ∑ k : x.pulses, x.weight k.1 t *
        ∑ n ∈ Finset.Icc 2 (A.Nw + x.cap),
          pulseMeanFluxEuler x.clock x.length x.contrast n (g + 1)
            (x.nativeData k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2) hj)
            (x.input.CcR x.i k.1) (x.chart k.1) (x.label k.1) (fun _ => a) t y v j := by
  classical
  rw [x.cePathAction hcommon hX hZ (by omega) v (A.Nw + x.cap) (Nat.le_add_left _ _)
    a ha t y j]
  rw [Finset.sum_congr rfl fun n hn =>
    x.sourceDegreePulse hcommon hX hZ g hg n hn hj a ha t ht y v j]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  by_cases hw : x.weight k.1 t = 0
  · rw [hw, zero_mul, zero_mul]
  · have hwin := (weakCoarsePulseGeometry hcommon x).support k.1 k.2 t ht hw
    rw [x.positivePulseDegrees hcommon hX hZ g hg k.1
      (CycleComparison.LiftSetting.obsPulse_odd k.2) hj a ha t hwin y v j]

/-- The stored diagonal block and reference diffusion reproduce the glued native degree sum. -/
theorem Case.zeroGluedAction (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (t : ℝ) (ht : t ∈ x.interval)
    (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (j : Fin 2) :
    (∑ d : Finset.Icc 2 (A.Nw + x.cap), cdAD x.c (A.Nw + x.cap) x.i x.v₀ d t y
      (WithLp.toLp 2 (fun I => orderedDerivative I (fun z => a z v) y)) j) +
      x.c.D.κ x.c.M * fderiv ℝ (fun z => a z v) y (basisVec j) =
      ∑ k : x.pulses, x.weight k.1 t *
        ∑ n ∈ Finset.Icc 2 (A.Nw + x.cap),
          pulseMeanFluxEuler x.clock x.length x.contrast n 0
            (x.nativeData k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2) hj)
            (x.input.CcR x.i k.1) (x.chart k.1) (x.label k.1) (fun _ => a) t y v j := by
  classical
  let E := fun k : ℤ => ∑ n ∈ Finset.Icc 2 (A.Nw + 1),
    pushFlux (x.chart k t) (x.label k t)
      (weakEddyFlux x.c.D (x.c.stage x.i).level x.length (x.scalarData k)
        (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) n t) (fun z => a z v) y j
  let ref := x.c.D.κ x.c.M * fderiv ℝ (fun z => a z v) y (basisVec j)
  have heddy : (∑ d : Finset.Icc 2 (A.Nw + x.cap),
      cdAD x.c (A.Nw + x.cap) x.i x.v₀ d t y
        (WithLp.toLp 2 (fun I => orderedDerivative I (fun z => a z v) y)) j) =
      ∑ k : x.pulses, x.weight k.1 t * E k.1 := by
    rw [x.adPhysicalAction hcommon hX hZ (A.Nw + x.cap) (Nat.le_add_left _ _)
      (fun z => a z v) (contDiff_pi.mp ha v) t y j]
    rw [Finset.sum_coe_sort x.pulses (fun k : ℤ => x.weight k t * E k)]
    rw [Finset.sum_congr rfl fun n _ => x.eddyEulerFixed hj n t ht (fun z => a z v) y j,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [← Finset.mul_sum]
  rw [heddy]
  have hterm (k : x.pulses) :
      x.weight k.1 t * (∑ n ∈ Finset.Icc 2 (A.Nw + x.cap),
        pulseMeanFluxEuler x.clock x.length x.contrast n 0
          (x.nativeData k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2) hj)
          (x.input.CcR x.i k.1) (x.chart k.1) (x.label k.1) (fun _ => a) t y v j) =
      x.weight k.1 t * E k.1 + x.weight k.1 t * ref := by
    by_cases hw : x.weight k.1 t = 0
    · rw [hw, zero_mul, zero_mul, zero_mul, add_zero]
    · have hwin := (weakCoarsePulseGeometry hcommon x).support k.1 k.2 t ht hw
      rw [x.zeroPulseDegrees hcommon hX hZ k.1
        (CycleComparison.LiftSetting.obsPulse_odd k.2) hj a ha t hwin y v j]
      exact mul_add _ _ _
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
    ← Finset.sum_mul, x.pulseWeights t ht, one_mul]
end

/-! The weak window's literal mean presentation. All native source sums and the
molecular term are proved in NativeFlux; this module transfers them back to the
actual pulse data and the classical flux notation. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window GenSem

private theorem weakMean_pulse_freeze {ι : Type*} [Fintype ι] {hs : ι → Type*}
    [∀ v, NormedAddCommGroup (hs v)] [∀ v, NormedSpace ℝ (hs v)] {Dm : ℕ}
    (c ρ ε : ℝ) (hc : c ≠ 0) (n g : ℕ) (Q : LiftOperatorData ι hs Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι hs) (chart label : ℝ → Vec 2 → Vec 2)
    (a : ℝ → Vec 2 → ∀ v, hs v) (t : ℝ) (y : Vec 2) (v : ι) :
    pulseMeanFluxEuler c ρ ε n g Q Cc chart label a t y v =
      pulseMeanFluxEuler c ρ ε n g Q Cc chart label (fun _ => a t) t y v := by
  have hclk : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have he := Construction.Preservation.Residual.FluxCancellation.right_liftFluxX_time_congr Q Cc
    (fun τ X => a (c * τ) (chart (c * τ) (ρ • X)))
    (fun τ X => a t (chart (c * τ) (ρ • X))) g n (c⁻¹ * t)
    (by rw [hclk])
  unfold pulseMeanFluxEuler
  rw [he]

private theorem weakMean_clm_jet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : PiLp 2 (fun _ : ι => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (a : ι → ℝ) (j : Fin 2) :
    (∑ I : ι, L (WithLp.toLp 2 (Pi.single I (1 : ℝ))) j * a I) =
      L (WithLp.toLp 2 a) j := by
  classical
  have he : WithLp.toLp 2 a = ∑ I : ι, a I • WithLp.toLp 2 (Pi.single I (1 : ℝ)) := by
    apply PiLp.ext
    intro k
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [he, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The literal glued mean can be evaluated on the unmasked incoming native data. -/
theorem Case.gluedNative (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (t : ℝ) (ht : t ∈ x.interval) (y : Vec 2)
    (v : CompIn (x.c.stage x.i).comps) (j : Fin 2) :
    x.gluedFlux a t y v j =
      ∑ k : x.pulses, x.weight k.1 t *
        ∑ n ∈ Finset.Icc 2 (A.Nw + x.cap),
          pulseMeanFluxEuler x.clock x.length x.contrast n x.grade
            (x.nativeData k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2) hj)
            (x.input.CcR x.i k.1) (x.chart k.1) (x.label k.1) (fun _ => a t) t y v j := by
  classical
  unfold Case.gluedFlux
  rw [← Finset.sum_coe_sort x.pulses (fun k : ℤ => x.weight k t • x.pulseFlux a k t y v j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hw : x.weight k.1 t = 0
  · rw [hw, zero_smul, zero_mul]
  · unfold Case.pulseFlux
    simp only [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => congrArg (fun z => x.weight k.1 t * z) ?_
    rw [congrFun (x.pulseMean_native hcommon k.1 k.2 hj a n t ht hw y v) j]
    exact congrFun (weakMean_pulse_freeze x.clock x.length x.contrast (x.scales hcommon).1.ne'
      n x.grade (x.nativeData k.1 (CycleComparison.LiftSetting.obsPulse_odd k.2) hj)
      (x.input.CcR x.i k.1) (x.chart k.1) (x.label k.1) a t y v) j

/-- The physical stored-letter identity at the fixed weak reserve cap. -/
theorem weakCoarsePhysicalFlux (hcommon : WeakPassageCommonOK plan)
    (horder : ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
      A.Nw + 1 + (1 + A.Jw * A.Nw) ≤ plan.liftFloor A) :
    WeakCoarsePhysicalFluxStatement plan := by
  intro B A R x a ha t ht y v j
  have hX : A.Nw + 1 + x.cap ≤ R.sX := (horder A).trans x.input.sX_ge
  have hZ : A.Nw + 1 + x.cap ≤ R.sZ := (horder A).trans x.input.sZ_ge
  have hj : x.c.j₀ ≤ (x.c.stage x.i).level := by
    rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
    have := x.startFloor hcommon
    have := x.lower
    omega
  rw [x.gluedNative hcommon hj a t ht y v j]
  unfold classicalGradeFlux
  by_cases h0 : x.grade = 0
  · simp only [h0, ite_true]
    have hdiag := x.zeroGluedAction hcommon hX hZ hj (a t) (ha t) t ht y v j
    rw [← hdiag]
    have href : (∑ l : Fin 2, ((x.c.D.κ x.c.M) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j l •
        fderiv ℝ (fun z => a t z v) y (basisVec l)) =
        x.c.D.κ x.c.M * fderiv ℝ (fun z => a t z v) y (basisVec j) := by
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [href]
    simp only [smul_eq_mul]
    rw [Finset.sum_congr rfl fun d _ => weakMean_clm_jet
      (cdAD x.c (A.Nw + x.cap) x.i x.v₀ d t y)
      (fun I => orderedDerivative I (fun z => a t z v) y) j]
    exact add_comm _ _
  · obtain ⟨g, hg⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hgle : g + 1 ≤ A.Jw * A.Rw := by
      have he := x.grade_le
      rw [hg] at he
      exact he
    rw [ite_eq_right h0, hg]
    exact x.positiveGluedAction hcommon hX hZ g hgle hj (a t) (ha t) t ht y v j

/-- The stored-letter identity consumed directly by the weak reconstruction window. -/
theorem weakCoarseStoredMeanFlux (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseMeanPlanOK plan)
    (horder : ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
      A.Nw + 1 + (1 + A.Jw * A.Nw) ≤ plan.liftFloor A) :
    WeakCoarseStoredMeanFluxStatement plan := by
  apply weakCoarseStoredMeanFlux_of_physical hcommon hok
  · intro B A
    exact (Nat.le_add_left _ _).trans (horder A)
  · exact weakCoarsePhysicalFlux hcommon horder
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
end
