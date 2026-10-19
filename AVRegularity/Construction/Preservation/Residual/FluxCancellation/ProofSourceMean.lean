-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeFluxOrderBound
import AVRegularity.Construction.StageSuccessor.StageOfFields
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofTransferCollapseMain
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMeanEdges
import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofSourceMeanDirect
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

section
section
/-! `CascadeSplitInputStatement` from the weak order bound (`cascadeSplitInput_of_weakOrderBound`,
with `CascadeFluxOrderBoundWeak`), using `2 ≤ D_H` (`1 ≤ H`, `2 ≤ N`, `1 ≤ p` of the schedule).

`CascadeFluxOrderBoundWeak` takes the stream data of the cascade (`1 ≤ D.Λ`, the
fast profile, the band chain), passed here from the prefix, and is proved
(`OrderBound.cascadeFluxOrderBoundWeak`): `cascadeSplitInput` is unconditional. The
fields `alpha_pos`, `q_gt` of `SplitInput` follow from the hypotheses `0 < α`, `1 < q` (namely
`hα₀`, and `1 < q` from `IsAdmissibleQ α s q`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual
open FluxCancellation CovarianceTransport

/-- **The cascade supplies the split input** (conditional on the order bound of the cascade). -/
theorem cascadeSplitInput_of_weakOrderBound (α s q : ℝ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hα : 0 < α) (hq : 1 < q) (hord : OrderBound.CascadeFluxOrderBoundWeak) :
    CascadeSplitInputStatement α s q ζ := by
  obtain ⟨Λ₀, hΛ₀, hc⟩ := StageSuccessor.cascade_successor_inputs α s q ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ?_⟩
  obtain ⟨c₀max, hc₀, hc⟩ := hc Λ hΛ
  refine ⟨c₀max, hc₀, ?_⟩
  intro φ₀ hφ₀ h1 h2 h3 h4 bw hbw hbw' Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀' hc₀u hcr hcru
    hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout
    halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ h1 h2 h3 h4 bw hbw hbw' Q T₀ hQ hT₀ Ce τe kS
    r₀ D₀ hCe hτe hc₀' hc₀u hcr hcru hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX
    sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, max Υ 1, hCH, lt_of_lt_of_le hΥ (le_max_left _ _), ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨hstart', hstart1⟩ := cascadeSplitInput_carrierStart (by omega : 1 ≤ Λ) hCH hΥ hstart
  obtain ⟨mStar, hc⟩ := hc CI Cw j₀ hledger hstart'
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow _hT G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hf Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  have hin := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh
    seed n tS tf hseed m hm hn hnM G hcascade hlevel ⟨tA, htA, hG⟩
  subst hlevel
  have haux := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rfl, rfl, rfl, rfl, by dsimp only; omega, ?_⟩
  refine ⟨hin, hactual, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hDα]; exact hα, by rw [hDq]; exact hq⟩
  · exact (isMenuLiftedField_cascade
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) rfl rfl G (G'.retained G.level H J)
      G.level p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) tp tf Y CcT PZ aRep û).2 hlift |>.1
  swap
  · obtain ⟨_hc0I, _hcrI, hprod⟩ := Buffer.invariantAdmissible_molecular_parameters hkI
    exact ⟨kI, hG.2.2.2.2.2.1, hG.2.2.2.2.1, fun v =>
      ⟨(Buffer.cascade_component_reserve_pos hseed.2.1 hcascade kI hprod v).le,
        (Buffer.compReserve_le_one kI v.1).trans (by norm_num)⟩⟩
  · have hbound := hord (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) D₀ (succSchedR r₀ J H) npad
      seed G rfl rfl rfl hseed.2.1 (fun v u γ => (hseed.2.2.2.2.2.1 v u γ).1)
      (by rw [hDΛ]; exact_mod_cast (by omega : 1 ≤ Λ)) (by rw [hDζ]; exact hζ)
      (by rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband)
      (by simp only [succMenu]; omega) (by simp only [succMenu]; omega) hcascade
    have hgr := (InitialValue.cascade_invariant hseed.2.1 hcascade)
    have hH1 : 1 ≤ H := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hN2 : 2 ≤ N := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hDH : 2 ≤ succSchedD D₀ N p H := by
      rw [succSchedD_eq]
      have := Nat.mul_le_mul_right (2 * N + 4 * p + 4) hH1
      omega
    refine ⟨succSchedD D₀ N p H, N + succSchedD D₀ N p H, succSchedR r₀ J H, npad, rfl, le_rfl,
      hDH, ?_, ?_, hsX, hsZ⟩
    · intro p' c v u γ d I hd
      refine hbound p' c v u γ d I (lt_of_le_of_lt hDH hd) (lt_of_le_of_lt ?_ hd)
      exact cascadeSplitInput_succSchedD_mono D₀ N p (hgr v.1 v.2).2
    · intro h π
      have hh := Providers.CascadeInvariants.cascade_path_length_le_of_generatedSeed hseed hcascade π
      exact ⟨hh, hh⟩
  · rw [hDα, hDq, hDΛ, hDζ]
    exact hseq
  · exact ⟨Mnat, hG.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · rw [hDα, hDq, hDΛ]
    exact hstart1

/-- **The cascade supplies the split input.** -/
theorem cascadeSplitInput (α s q : ℝ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hα : 0 < α)
    (hq : 1 < q) : CascadeSplitInputStatement α s q ζ :=
  cascadeSplitInput_of_weakOrderBound α s q ζ hζ hα hq OrderBound.cascadeFluxOrderBoundWeak

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! The first-source-flux step: **`FSPiolaConstant`**, the label operator of the first source kills constants.

The commutator part vanishes because the gradient of a constant does, the covariance operator
kills constants (`pcc_covOperator_const_iterate`), and the diagonal part vanishes by
`fsc_diagMeanFluxCtx_const_zero`. -/
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Uniqueness Providers Providers.GenSem

/-- The gradient of a constant field vanishes. -/
theorem fsc_gradField_const (c : ℝ) : gradField (fun _ : Vec 2 => c) = fun _ => 0 := by
  funext x k
  simp [gradField]

/-- The diagonal flux of a constant vanishes. -/
theorem fsc_diagFluxCtx_const_zero {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (D : OCData) (Mn : SuccMenu)
    (m : ℕ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hc : 0 < D.cellScaleSq m)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hdiag : IsDiagLifts D Dm b j₀ Mn m Cc0) (t : ℝ) (ch : RealChain) (ζ : Vec 2) (c : ℝ)
    (x : Vec 2) :
    diagFluxCtx D b j₀ Dm m (Mn.lenFactor * liftLength D m) Mn.N Cc0 t ch ζ (fun _ => c) x = 0 := by
  unfold diagFluxCtx
  rw [fsc_diagMeanFluxCtx_const_zero D Mn m hΛ hζ hc Cc0 hdiag t ch ζ le_rfl c x,
    fsc_gradField_const, Finset.sum_eq_zero fun n hn => fsc_diagMeanFluxCtx_const_zero D Mn m hΛ hζ
      hc Cc0 hdiag t ch ζ (by have := (Finset.mem_Icc.mp hn).1; omega) c x]
  simp

/-- The covariance polynomial `P_p` of a constant is a constant. -/
theorem fsc_covPolyP_const (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) :
    ∃ c : ℝ, covPolyP H p (fun _ : Vec 2 => (1 : ℝ)) = fun _ => c := by
  choose c hc using fun l : ℕ => pcc_covOperator_const_iterate H l
  refine ⟨∑ l ∈ Finset.range (p + 1), ((l.factorial : ℝ)⁻¹) * c l, ?_⟩
  funext x
  unfold covPolyP
  simp [Finset.sum_apply, hc]

/-- The covariance polynomial `Q_p` of the zero function is zero. -/
theorem fsc_covPolyQ_zero (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) :
    covPolyQ H p (fun _ : Vec 2 => (0 : Vec 2)) = fun _ => 0 := by
  funext x
  unfold covPolyQ
  simp [ccfo_covOperator_iterate_zero]

/-- `Q_p` kills a function vanishing everywhere. -/
theorem fsc_covPolyQ_of_zero (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {F : Vec 2 → Vec 2}
    (hF : ∀ x, F x = 0) : covPolyQ H p F = fun _ => 0 := by
  have : F = fun _ => 0 := funext hF
  rw [this]
  exact fsc_covPolyQ_zero H p

open scoped Classical in
/-- The first-source flux of the constant `1` vanishes everywhere. -/
theorem fsc_firstSourceFlux_const_zero {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (D : OCData) (Mn : SuccMenu)
    (m : ℕ) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hc : 0 < D.cellScaleSq m)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hdiag : IsDiagLifts D Dm b j₀ Mn m Cc0) (t : ℝ) (ch : RealChain) (ζ : Vec 2) (y : Vec 2) :
    firstSourceFlux D b j₀ Dm m (Mn.lenFactor * liftLength D m) Mn.N Mn.p Mn.anchor Cc0 t ch ζ
      (fun _ => 1) y = 0 := by
  unfold firstSourceFlux pullFlux
  set Hc := ocCovariance D.α D.q D.Λ D.ζ m (D.κ m) (D.κ (m - 1)) Mn.anchor t with hHc
  obtain ⟨c1, hc1⟩ := fsc_covPolyP_const Hc Mn.p
  choose cl hcl using fun l : ℕ => pcc_covOperator_const_iterate Hc l
  beta_reduce
  rw [fsc_covPolyQ_of_zero Hc Mn.p (F := _) (fun x' => ?_)]
  · simp
  · simp only [Function.comp_def, hc1, hcl, fsc_gradField_const, Matrix.mulVec_zero, neg_zero,
      ccfo_covOperator_iterate_zero, Finset.sum_const_zero, smul_zero,
      fsc_diagFluxCtx_const_zero D Mn m hΛ hζ hc Cc0 hdiag t ch ζ]
    simp

/-- **Lemma Piola-B.** The label operator kills constants. -/
theorem fsPiolaConstant : FSPiolaConstant := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W p t hp x I
  have hΛ := hin.stage.base
  have hζ := hin.stage.profile
  have hκ := hin.stage.band
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  unfold fluxCoeff fsLabelOp
  have h1 : (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) = fun _ => 1 := by
    funext Y
    simp
  rw [h1]
  simp only [smul_eq_zero]
  right
  exact fsc_firstSourceFlux_const_zero D Mn G.level hΛ hζ hc W.Cc0 W.diag t _ _ 0

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The first-source-flux step, sub-step Algebra: the scalar reading of the temporal flux, the translation of
the commutator sum, and the assembly of the algebra sub-step (`FSStepAlgebraConcl`) from the strain
step and the diagonal step `FSStepDiagShift`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport CovFluxReg

section Scalar
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fsAlg_JH_eq_commFluxE (bv : Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (g : Vec 2 → ℝ) : commutatorFluxJH bv Hc g = commFluxE bv Hc g := by
  funext z j
  simp only [commutatorFluxJH, commFluxE, gradField, gradE, Pi.neg_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, smul_eq_mul]

/-- A continuous linear map commutes with `𝒥_H` on differentiable fields. -/
theorem fsAlg_commFluxE_clm (bv : Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (ℓ : E →L[ℝ] F) {B : Vec 2 → E} (hB : Differentiable ℝ B) (z : Vec 2) (j : Fin 2) :
    ℓ (commFluxE bv Hc B z j) = commFluxE bv Hc (fun y => ℓ (B y)) z j := by
  have h1 : fderiv ℝ (fun y => ℓ (B y)) z = ℓ.comp (fderiv ℝ B z) :=
    (ℓ.hasFDerivAt.comp z (hB z).hasFDerivAt).fderiv
  simp only [commFluxE, gradE, h1, map_neg, map_sum, map_smul]
  rfl

/-- The commutator flux of the translated velocity on a translated field. -/
theorem fsAlg_JH_shift (bv : Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (x : Vec 2)
    (B : Vec 2 → ℝ) :
    commutatorFluxJH (fun y => bv (x + y)) Hc (fun y => B (x + y)) =
      fun z => commutatorFluxJH bv Hc B (x + z) := by
  funext z
  have hj : jacMatrix (fun y => bv (x + y)) z = jacMatrix bv (x + z) := by
    unfold jacMatrix
    ext a c
    simp only [Matrix.of_apply, fderiv_comp_add_left (f := bv)]
  have hg : gradField (fun y => B (x + y)) z = gradField B (x + z) := by
    funext k
    simp only [gradField, fderiv_comp_add_left (f := B)]
  simp only [commutatorFluxJH, hj, hg]

/-- The commutator sum of a translated field. -/
theorem fsAlg_sum_shift (bv : Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (x : Vec 2)
    (f : Vec 2 → ℝ) (z : Vec 2) :
    fsAlgSum Hc p (commutatorFluxJH (fun y => bv (x + y)) Hc) (fun y => f (x + y)) z =
      fsAlgSum Hc p (commutatorFluxJH bv Hc) f (x + z) := by
  unfold fsAlgSum
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fsAlg_covOperator_iterate_shift, fsAlg_JH_shift, fsAlg_covOperator_iterate_shift]

/-- One term of the commutator sum, read through a functional and a coordinate. -/
theorem fsAlg_scalar_term (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p K : ℕ) (hK : 4 * p ≤ K) {A : Vec 2 → E}
    (hA : ContDiff ℝ (K : ℕ∞) A) (ℓ : E →L[ℝ] ℝ) (κ : Fin 2) {l a : ℕ} (hl : l ≤ p)
    (ha : a < l) (y : Vec 2) :
    ℓ ((covOperator Hc)^[a] (commFluxE bv Hc ((covOperator Hc)^[l - 1 - a] A)) y κ) =
      (covOperator Hc)^[a] (commutatorFluxJH bv Hc ((covOperator Hc)^[l - 1 - a]
        (fun y => ℓ (A y)))) y κ := by
  set b := l - 1 - a with hb
  have hCovB : ContDiff ℝ ((2 * a + 1 : ℕ) : ℕ∞) ((covOperator Hc)^[b] A) :=
    Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc b (2 * a + 1) A
      (hA.of_le (by exact_mod_cast (by omega : 2 * a + 1 + 2 * b ≤ K)))
  have hA' : ContDiff ℝ (K : ℕ∞) (fun y => ℓ (A y)) := ℓ.contDiff.comp hA
  have hCovB' : ContDiff ℝ ((2 * a + 1 : ℕ) : ℕ∞) ((covOperator Hc)^[b] (fun y => ℓ (A y))) :=
    Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc b (2 * a + 1) _
      (hA'.of_le (by exact_mod_cast (by omega : 2 * a + 1 + 2 * b ≤ K)))
  have hH : ContDiff ℝ ((2 * a : ℕ) : ℕ∞) (commFluxE bv Hc ((covOperator Hc)^[b] A)) :=
    commFluxE_contDiff bv hbv Hc (2 * a) hCovB
  have hJ : ContDiff ℝ ((2 * a : ℕ) : ℕ∞)
      (commutatorFluxJH bv Hc ((covOperator Hc)^[b] (fun y => ℓ (A y)))) := by
    rw [fsAlg_JH_eq_commFluxE]
    exact commFluxE_contDiff bv hbv Hc (2 * a) hCovB'
  have hcomm : (fun z => ℓ (commFluxE bv Hc ((covOperator Hc)^[b] A) z κ)) =
      fun z => commutatorFluxJH bv Hc ((covOperator Hc)^[b] (fun y => ℓ (A y))) z κ := by
    funext z
    rw [fsAlg_commFluxE_clm bv Hc ℓ (hCovB.differentiable (by simp)), fsAlg_JH_eq_commFluxE,
      fsAlg_covOperator_iterate_clm Hc ℓ b (hA.of_le (by exact_mod_cast (by omega : 2 * b ≤ K)))]
  have e1 := congrFun (fsAlg_covOperator_iterate_clm Hc (ℓ.comp (ContinuousLinearMap.proj κ)) a
    hH) y
  have e2 := congrFun (fsAlg_covOperator_iterate_clm Hc
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) κ) a hJ) y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at e1 e2
  rw [← e1, ← e2]
  have : (fun z => ℓ (commFluxE bv Hc ((covOperator Hc)^[b] A) z κ)) = _ := hcomm
  rw [this]

/-- The commutator part of the temporal flux, read through a functional and a coordinate. -/
theorem fsAlg_scalar_sum (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p K : ℕ) (hK : 4 * p ≤ K) {A : Vec 2 → E}
    (hA : ContDiff ℝ (K : ℕ∞) A) (ℓ : E →L[ℝ] ℝ) (κ : Fin 2) (y : Vec 2) :
    ℓ ((∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a' ∈ Finset.range l,
        (covOperator Hc)^[a'] (commFluxE bv Hc ((covOperator Hc)^[l - 1 - a'] A)) y) κ) =
      fsAlgSum Hc p (commutatorFluxJH bv Hc) (fun y => ℓ (A y)) y κ := by
  unfold fsAlgSum
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_Icc.mp hl
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  exact fsAlg_scalar_term bv hbv Hc p K hK hA ℓ κ hl'.2 (Finset.mem_range.mp ha) y

end Scalar

/-- **Sub-step Diagonal.** At a time of nonzero weight, `diagFluxCtx` at the
recentred actual context of the piece at `x`, applied to the field translated to the centre `x`,
at the relative point `x'`, is the physical diagonal flux at the point `x + x'`, componentwise.
The translation makes both sides read the field at the same physical point. The regularity (class
`C^{N+Dm}`, the order read by the grade-zero means of orders `≤ N+1`) is only needed at the time
`t`. -/
def FSStepDiagShift : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (p : OddSlot) (t : ℝ), G'.fam.weight p t ≠ 0 →
    ∀ (x : Vec 2) (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a t y v)) →
    ∀ (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (x' : Vec 2) (j : Fin 2),
      diagFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N W.Cc0 t
          (fsCtx G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)
          (fun y => ℓ (a t (x + y) v)) x' j =
        ℓ (menuDiagFluxPhys Mn G G.level Mn.N CcT a t (x + x') v j)

/-- The conclusion of sub-step Algebra, without its two hypotheses (the strain and diagonal
sub-steps). -/
def FSStepAlgebraConcl : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (W : SplitWitness P Mn G G') (K : ℕ) (ta tb : ℝ)
      (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root), FSField Mn G K ta tb g →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc ta tb, ∀ x : Vec 2, ∀ p : OddSlot,
      G'.fam.weight p t ≠ 0 → ∀ (ℓ : hr v.1.root →L[ℝ] ℝ) (κ : Fin 2),
      fsEulerRead Mn G G' W.Cc0 p t x (fun y => ℓ (g t y v)) κ =
        -ℓ (covTemporalAt Mn G G.level Mn.N Mn.p CcT g v t x κ)

/-- **Sub-step Algebra from the strain step and the diagonal step.** -/
theorem fs_algebra_of_steps (SS : FSStepStrain) (SD : FSStepDiagShift) : FSStepAlgebraConcl := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W K ta tb g hg v t ht x p hp ℓ κ
  have hSS := SS P Mn G G' depth CcT hin p t hp
  have hK := (hg).1
  have hgt : ∀ w, ContDiff ℝ (K : ℕ∞) (fun y => g t y w) := fun w => by
    exact_mod_cast ((hg).2 w t ht).1
  have hDm : 1 ≤ Dm := hin.stage.order
  have hbv : ContDiff ℝ (⊤ : ℕ∞) (streamVel (D.Φ (G.level - 1)) t) :=
    ((AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (G.level - 1))).smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have hT := CovFluxReg.menuTemporalFlux_contDiff P Mn G G' depth CcT hin K hK g t hgt v
  -- the diagonal field and its regularity
  set Hc := menuCovPrimitive D Mn G.level t with hHc
  set a' : ℝ → Vec 2 → ∀ w : CompIn G.comps, hr w.1.root := fun s y w =>
    covPolyP (menuCovPrimitive D Mn G.level s) Mn.p (fun y' => g s y' w) y with ha'
  have hreg : ∀ w, ContDiff ℝ ((Mn.N + Dm : ℕ) : ℕ∞) (fun y => a' t y w) := fun w =>
    CovFluxReg.covPolyP_contDiff Hc Mn.p (Mn.N + Dm)
      ((hgt w).of_le (by exact_mod_cast (by omega : Mn.N + Dm + 2 * Mn.p ≤ K)))
  have hAp : ContDiff ℝ ((2 * Mn.p : ℕ) : ℕ∞) (fun y => g t y v) :=
    (hgt v).of_le (by exact_mod_cast (by omega : 2 * Mn.p ≤ K))
  -- the functional
  set Λ : (Fin 2 → hr v.1.root) →L[ℝ] ℝ := -(ℓ.comp (ContinuousLinearMap.proj κ)) with hΛ
  have hΛ' : ∀ κ' : Fin 2, ∀ y, -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y κ') =
      (-(ℓ.comp (ContinuousLinearMap.proj κ'))) (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y) :=
    fun κ' y => rfl
  -- the unfolded left-hand side
  rw [fsAlg_unfold hin p t x hSS W.Cc0 (fun y => ℓ (g t y v))]
  have hfun : (fun x' => -(fsAlgSum Hc Mn.p
          (commutatorFluxJH (fun y => streamVel (D.Φ (G.level - 1)) t (x + y)) Hc)
          (fun y => ℓ (g t (x + y) v)) x') +
        diagFluxCtx D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level) Mn.N W.Cc0 t
          (fsCtx G' p t x) ((D.eps G'.level)⁻¹ • ((G'.fam.piece p).material t).symm x)
          (covPolyP Hc Mn.p (fun y => ℓ (g t (x + y) v))) x') =
      fun x' => fun κ' => -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v (x + x') κ') := by
    funext x' κ'
    have hd := SD P Mn G G' depth CcT hin W p t hp x a' hreg v ℓ x' κ'
    have hpP : (fun y => ℓ (a' t (x + y) v)) = covPolyP Hc Mn.p (fun y => ℓ (g t (x + y) v)) := by
      funext y
      simp only [ha']
      rw [← hHc]
      rw [← fsAlg_covPolyP_clm Hc ℓ Mn.p hAp (x + y),
        ← fsAlg_covPolyP_shift Hc Mn.p (fun y => ℓ (g t y v)) x y]
    rw [hpP] at hd
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [hd, fsAlg_sum_shift (streamVel (D.Φ (G.level - 1)) t) Hc Mn.p x (fun y => ℓ (g t y v)) x']
    have hsc := fsAlg_scalar_sum (streamVel (D.Φ (G.level - 1)) t) hbv Hc Mn.p K (by omega)
      (hgt v) ℓ κ' (x + x')
    unfold menuTemporalFlux
    simp only [Pi.sub_apply, map_sub]
    rw [hsc]
    ring
  have hsh : covPolyQ Hc Mn.p
      (fun x' κ' => -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v (x + x') κ')) 0 =
      covPolyQ Hc Mn.p
        (fun y κ' => -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y κ')) (x + 0) :=
    fsAlg_covPolyQ_shift Hc Mn.p
      (fun y κ' => -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y κ')) x 0
  rw [hfun, hsh, add_zero]
  have hZ : ContDiff ℝ ((2 * Mn.p : ℕ) : ℕ∞)
      (fun y => fun κ' => -ℓ (menuTemporalFlux Mn G G.level Mn.N Mn.p CcT g t v y κ')) := by
    refine contDiff_pi.mpr fun κ' => ?_
    simp only [hΛ']
    exact (ContinuousLinearMap.contDiff _).comp hT
  have h1 := fsAlg_covPolyQ_clm Hc (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) κ)
    Mn.p hZ x
  have h2 := fsAlg_covPolyQ_clm Hc Λ Mn.p hT x
  simp only [ContinuousLinearMap.proj_apply] at h1
  rw [← h1]
  simp only [hΛ', hΛ] at h2 ⊢
  rw [h2]
  simp [covTemporalAt, toFluxL, hHc, menuCovPrimitive]

/-- **The piece statement from the sub-steps, with the diagonal step translated to the centre**. -/
theorem firstSourcePiece_of_steps' (SP : FSStepPiola) (SS : FSStepStrain) (SD : FSStepDiagShift) :
    FirstSourcePieceStatement := by
  intro _ _ _ hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W K ta tb g hg v t ht x p hp
  ext κ
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ => ?_
  rw [SP P Mn G G' depth CcT hin W K ta tb g hg v t ht x p hp ℓ κ,
    fs_algebra_of_steps SS SD P Mn G G' depth CcT hin W K ta tb g hg v t ht x p hp ℓ κ]
  simp

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end

section
section
/-! **Source mean, Left: the reading of a transferred identity**.

`sml_root_linear`, `sml_dep_eq`, `sml_read_fluxOpApply`: reading the differential operator
`fluxOpApply` through the cast of the roots, `ℓ` and a component equals the same operator on the
scalar field `ℓ ∘ C ∘ f` (the cast and `ℓ` are continuous linear, so they commute with the
ordered derivatives, `orderedDerivative_clm_comp`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- A functional on the space of the root `r'` is, along the equality of the roots, a functional
on the space of the root `r`, and it reads the path maps the same way. -/
theorem sml_root_linear {r r' : ℕ} (h : r = r') (ℓ : hr r' →L[ℝ] ℝ) :
    ∃ ℓ0 : hr r →L[ℝ] ℝ, (∀ w : hr r, ℓ (cast (congrArg hr h) w) = ℓ0 w) ∧
      ∀ (a : ℕ) (maps : List (Σ (a c : ℕ), hr a →L[ℝ] hr c)) (z : hr a),
        ℓ (rootPathMap hr a maps r' z) = ℓ0 (rootPathMap hr a maps r z) := by
  subst h
  exact ⟨ℓ, fun _ => rfl, fun _ _ _ => rfl⟩

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The path map from equal source components reads the field at equal points. -/
theorem sml_dep_eq {S : Finset Comp} (F : ∀ c : CompIn S, hr c.1.root) (c₁ c₂ : Comp)
    (h₁ : c₁ ∈ S) (h₂ : c₂ ∈ S) (e : c₁ = c₂)
    (maps : List (Σ (a c : ℕ), hr a →L[ℝ] hr c)) (r : ℕ) :
    rootPathMap hr c₁.root maps r (F ⟨c₁, h₁⟩) = rootPathMap hr c₂.root maps r (F ⟨c₂, h₂⟩) := by
  subst e
  rfl

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **Reading `fluxOpApply`** through the cast, `ℓ` and the component `j`. -/
theorem sml_read_fluxOpApply {r r' a : ℕ} (h : r = r') (c lam : ℝ) (ℓ : hr r' →L[ℝ] ℝ)
    (ℓ0 : hr r →L[ℝ] ℝ) (hℓ0 : ∀ w : hr r, ℓ (cast (congrArg hr h) w) = ℓ0 w) (j : Fin 2)
    (K : ℕ) (L : (Vec 2 → ℝ) → Vec 2 → Vec 2) (C : hr a →L[ℝ] hr r) {f : Vec 2 → hr a}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) :
    smlRead h c ℓ j (lam • fluxOpApply K L C f x) =
      c * lam * ∑ d ∈ Finset.Icc 2 K, ∑ I : DerivativeWord2 (d - 1),
        fluxCoeff L d I x j * orderedDerivative I (fun y => ℓ0 (C (f y))) x := by
  rw [smlRead_apply h, sml_cast_apply h, hℓ0]
  simp only [fluxOpApply, WithLp.ofLp_smul, Pi.smul_apply, map_smul, smul_eq_mul, map_sum]
  rw [mul_assoc]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun I _ => ?_
  have hfd : ContDiff ℝ ((d - 1 : ℕ) : ℕ∞) f := hf.of_le (by exact_mod_cast le_top)
  have := orderedDerivative_clm_comp (ℓ0.comp C) I hfd
  have h2 : orderedDerivative I (fun y => ℓ0 (C (f y))) x = ℓ0 (C (orderedDerivative I f x)) :=
    congrFun this x
  rw [h2]

open scoped Classical in
/-- **Step 2 of the Left side**: a cell is the source term of its source. -/
theorem sml_termStep (hbk : RootSourceBookkeepingStatement)
    (h4 : TransferredIdentityEulerianOnStatement) (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hin : SplitInput P Mn G G' depth CcT) (W : SplitWitness P Mn G G')
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (hg : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v)) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2) (t : ℝ) (x : Vec 2) :
    SmlTermStep P Mn G G' W g v ℓ j t x := by
  intro v' u' γ'
  obtain ⟨-, hii, -⟩ := hbk P Mn G G' hin.stage hin.successor W
  by_cases h : compParent G.level v'.1 = v.1
  swap
  · have hc : ¬ (compParent G.level v'.1 = v.1 ∧ u'.1 ∈ G.comps ∧
        ¬ (W.e v' u' γ').1.IsDiag) := fun hh => h hh.1
    rw [ite_eq_right hc]
    unfold smlCell
    rw [dite_eq_right h]
  by_cases hu : u'.1 ∈ G.comps
  swap
  · have hc : ¬ (compParent G.level v'.1 = v.1 ∧ u'.1 ∈ G.comps ∧
        ¬ (W.e v' u' γ').1.IsDiag) := fun hh => hu hh.2.1
    rw [ite_eq_right hc]
    unfold smlCell
    rw [dite_eq_left h, dite_eq_right hu]
  obtain ⟨hw, hsrc, htg, hpar, hword, hlam, hdiag⟩ := hii v' u' γ' hu
  by_cases hD : (W.e v' u' γ').1.IsDiag
  · have hc : ¬ (compParent G.level v'.1 = v.1 ∧ u'.1 ∈ G.comps ∧
        ¬ (W.e v' u' γ').1.IsDiag) := fun hh => hh.2.2 hD
    rw [ite_eq_right hc]
    unfold smlCell
    rw [dite_eq_left h, dite_eq_left hu, ite_eq_left (hdiag.mp hD)]
  have hc : compParent G.level v'.1 = v.1 ∧ u'.1 ∈ G.comps ∧ ¬ (W.e v' u' γ').1.IsDiag :=
    ⟨h, hu, hD⟩
  have hprov : ¬ (G'.prov v' u' γ' = Prov.letter G.level WordLetter.diag []) :=
    fun hp => hD (hdiag.mpr hp)
  rw [ite_eq_left hc]
  have hvalid := (W.e v' u' γ').2.1
  have hroot := smlRoot_eq G'.comps G.level v' v.1 h
  obtain ⟨ℓ0, hℓ0, hR⟩ := sml_root_linear hroot ℓ
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y => g y ⟨u'.1, hu⟩) := hg ⟨u'.1, hu⟩
  have hf' : ContDiff ℝ (Dm - 1 : ℕ) (fun y => g y ⟨u'.1, hu⟩) :=
    hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have p4 := h4 P Mn G G' hin.stage hin.successor hin.transferInput W v' u' γ' hD t _ hf' x
  rw [(W.spec v' u' γ').2.1] at p4
  have hphys : smlPhys G G' g v' u' hu γ' t x =
      (W.e v' u' γ').1.lam G.level Mn.η0 •
        fluxOpApply Dm (sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor
          (W.e v' u' γ').1 (W.Cc (W.e v' u' γ').1) t)
          (rootPathMap hr u'.1.root (W.e v' u' γ').1.maps v'.1.root)
          (fun y => g y ⟨u'.1, hu⟩) x := p4
  have hL : D.eps (G.level - 1) ^ (Mn.η0 * ((compWord G.level v'.1).length : ℝ)) *
      ℓ ((cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) hroot)
        (smlPhys G G' g v' u' hu γ' t x)) j) =
      smlRead hroot (D.eps (G.level - 1) ^ (Mn.η0 * ((compWord G.level v'.1).length : ℝ))) ℓ j
        (smlPhys G G' g v' u' hu γ' t x) := (smlRead_apply hroot _ ℓ j _).symm
  unfold smlCell
  rw [dite_eq_left h, dite_eq_left hu, ite_eq_right hprov, hL, hphys,
    sml_read_fluxOpApply hroot _ _ ℓ ℓ0 hℓ0 j Dm _ _ hf x, hlam, one_mul]
  have hs : (W.e v' u' γ').1.oldSrc ∈ G.comps := by rw [hsrc]; exact hu
  unfold smlSrc
  rw [dite_eq_left hs]
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y => ℓ (rootPathMap hr (W.e v' u' γ').1.oldSrc.root
      (W.e v' u' γ').1.maps v.1.root (g y ⟨(W.e v' u' γ').1.oldSrc, hs⟩))) :=
    (ℓ.comp (rootPathMap hr (W.e v' u' γ').1.oldSrc.root (W.e v' u' γ').1.maps
      v.1.root)).contDiff.comp (hg ⟨(W.e v' u' γ').1.oldSrc, hs⟩)
  have hord : (((W.e v' u' γ').1.prov G.level).tags P).order ≤ Dm := by
    have h1 := (hin.successor.2.2.2.2.1 v' u' γ').2
    rw [(W.spec v' u' γ').1] at h1
    rw [← h1]
    exact (G'.fam.identity v' u' γ').le_D
  rw [sml_sourceEuler_expansion P Mn G G' hin.stage hin.successor hin.transferInput W
    (W.e v' u' γ').1 hvalid hD hord t x hφ j]
  have hfield : (fun y => ℓ (rootPathMap hr (W.e v' u' γ').1.oldSrc.root
      (W.e v' u' γ').1.maps v.1.root (g y ⟨(W.e v' u' γ').1.oldSrc, hs⟩))) =
      fun y => ℓ0 (rootPathMap hr u'.1.root (W.e v' u' γ').1.maps v'.1.root
        (g y ⟨u'.1, hu⟩)) := by
    funext y
    rw [sml_dep_eq (fun c => g y c) _ u'.1 hs hu hsrc (W.e v' u' γ').1.maps v.1.root]
    exact hR _ _ _
  rw [hfield]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Source mean: the matching step**: `sourceMeanMatch : SourceMeanMatchStatement`, the sum over
the sources is the sum over the paths.

`pathSet G depth c`: the paths of `1..depth` edges into the component `c`, as a finite set of
pairs (grade, path). `pathSide_eq_pathSet`: the sum over the paths in this form. The matching is
`sourceMean_match_algebra` with the dressed terms of the three kinds of sources with a path
(`sourceTerm_copyQuad`, `sourceTerm_letterMean`, `sourceTerm_letterCov`), the lift independence
(`dressedPathTerm_lift_indep`), the vanishing in high degree (`dressedPathTerm_high`, with
`2 ≤ Dord`), and the direct transports as the direct parts of the one-edge paths
(`sourceTerm_copyDir`, `sum_sigma_one_edge`, `nativeDirect_Icc_eq`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport Construction.Preservation.Ledger

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The paths of `1..depth` edges into the component `c`. -/
def pathSet (G : GenStage D hr Dm b j₀) (depth : ℕ) (c : Comp) : Finset (Σ h : ℕ, StagePath G h) :=
  ((Finset.Icc 1 depth).sigma (fun h => (Finset.univ : Finset (StagePath G h)))).filter
    (fun x => x.2.tgt = c)

open scoped Classical in
theorem sum_pathSet {V : Type*} [AddCommMonoid V] (G : GenStage D hr Dm b j₀) (depth : ℕ)
    (c : Comp) (f : ∀ h : ℕ, StagePath G h → V) :
    ∑ h ∈ Finset.Icc 1 depth, ∑ π : StagePath G h, (if π.tgt = c then f h π else 0) =
      ∑ x ∈ pathSet G depth c, f x.1 x.2 := by
  unfold pathSet
  rw [Finset.sum_filter, Finset.sum_sigma]

theorem mem_pathSet {G : GenStage D hr Dm b j₀} {depth : ℕ} {c : Comp}
    {x : Σ h : ℕ, StagePath G h} (hx : x ∈ pathSet G depth c) :
    1 ≤ x.1 ∧ x.1 ≤ depth ∧ x.2.tgt = c := by
  classical
  unfold pathSet at hx
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
  have h3 := Finset.mem_Icc.1 (Finset.mem_sigma.1 h1).1
  exact ⟨h3.1, h3.2, h2⟩

/-- The glue of the direct part of the order `n` of the edge of a one-edge path (zero for the other
grades), on the scalar field of the path: the term subtracted in the letter `𝖬_{n,1}`. -/
def dirTerm (G : GenStage D hr Dm b j₀) (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) (n : ℕ) (h : ℕ)
    (π : StagePath G h) : Vec 2 :=
  if hh : h = 1 then gluedFluxOp D G.level
    (fun k => nativeDirect G (π.step ⟨0, by omega⟩).2.2 {n} k t) t (pathField G g v ℓ π) x
  else 0

theorem gluedFluxOp_zero (D : OCData) (m : ℕ) (t : ℝ) (f : Vec 2 → ℝ) (x : Vec 2) :
    gluedFluxOp D m (fun _ _ _ => 0) t f x = 0 := by
  unfold gluedFluxOp
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pushFlux_zero, smul_zero]

open scoped Classical in
/-- **The direct transports are the direct parts of the one-edge paths.** -/
theorem sum_dirTerm_eq (G : GenStage D hr Dm b j₀) (depth : ℕ)
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) {Dord nMax : ℕ}
    (hvan : ∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) (v' u : CompIn G.comps)
      (γ : G.fam.Γ v' u) (d : ℕ) (I : DerivativeWord2 (d - 1)), Dord < d →
        G.fam.flux p c v' u γ d I = fun _ _ _ => 0)
    (hD : Dord ≤ nMax)
    (hdepth : (Σ v' u : CompIn G.comps, G.fam.Γ v' u) → 1 ≤ depth)
    (hsub : (Σ v' u : CompIn G.comps, G.fam.Γ v' u) → ∀ d ∈ Finset.Icc 3 nMax, d ≤ Dm) :
    ∑ n ∈ Finset.Icc 3 nMax, ∑ y ∈ pathSet G depth v.1, dirTerm G g v ℓ t x n y.1 y.2 =
      ∑ z : (Σ v' u : CompIn G.comps, G.fam.Γ v' u),
        if 3 ≤ (G.fam.identity z.1 z.2.1 z.2.2).maxOrder ∧ z.1.1 = v.1 then
          gluedFluxOp D G.level (fun k => nativeDirect G z.2.2 (Finset.Icc 3 Dm) k t) t
            (edgeField G g v ℓ z.2.2) x
        else 0 := by
  -- the sum over the paths, for one order
  have e1 : ∀ n, ∑ y ∈ pathSet G depth v.1, dirTerm G g v ℓ t x n y.1 y.2 =
      ∑ z : (Σ v' u : CompIn G.comps, G.fam.Γ v' u),
        if z.1.1 = v.1 then gluedFluxOp D G.level (fun k => nativeDirect G z.2.2 {n} k t) t
          (edgeField G g v ℓ z.2.2) x else 0 := by
    intro n
    unfold pathSet
    rw [Finset.sum_filter]
    have e : ∀ y : (Σ h : ℕ, StagePath G h),
        (if y.2.tgt = v.1 then dirTerm G g v ℓ t x n y.1 y.2 else 0) =
        if y.1 = 1 then (fun (h : ℕ) (π : StagePath G h) =>
          if π.tgt = v.1 then dirTerm G g v ℓ t x n h π else 0) y.1 y.2 else 0 := by
      intro y
      by_cases hy : y.1 = 1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hy)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hy)]
        have h0 : dirTerm G g v ℓ t x n y.1 y.2 = 0 := by
          unfold dirTerm
          exact dite_eq_right hy
        rw [h0, ite_self]
    rw [Finset.sum_congr rfl fun y _ => e y, sum_sigma_one_edge G depth
      (fun h π => if π.tgt = v.1 then dirTerm G g v ℓ t x n h π else 0)]
    by_cases hd : 1 ≤ depth
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
      refine Finset.sum_congr rfl fun z _ => ?_
      obtain ⟨v', u, γ⟩ := z
      rw [edgePath_tgt]
      by_cases hz : v'.1 = v.1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hz), ite_eq_left_of_eq_true _ _ (eq_true hz)]
        unfold dirTerm
        rw [dite_eq_left rfl, pathField_edgePath]
        rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hz), ite_eq_right_of_eq_false _ _ (eq_false hz)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
      exact (Finset.sum_eq_zero fun z _ => absurd (hdepth z) hd).symm
  rw [Finset.sum_congr rfl fun n _ => e1 n, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  obtain ⟨v', u, γ⟩ := z
  by_cases hz : v'.1 = v.1
  · simp only [hz, ↓reduceIte, and_true]
    have e2 : ∑ n ∈ Finset.Icc 3 nMax,
        gluedFluxOp D G.level (fun k => nativeDirect G γ {n} k t) t (edgeField G g v ℓ γ) x =
        gluedFluxOp D G.level (fun k => nativeDirect G γ (Finset.Icc 3 Dm) k t) t
          (edgeField G g v ℓ γ) x := by
      rw [← gluedFluxOp_sum D G.level (Finset.Icc 3 nMax)
        (fun n k => nativeDirect G γ {n} k t) t (edgeField G g v ℓ γ) x]
      congr 1
      funext k f y
      exact nativeDirect_Icc_eq G γ (fun p c d I hd => hvan p c v' u γ d I hd) hD
        (hsub ⟨v', u, γ⟩) k t f y
    rw [e2]
    by_cases h3 : 3 ≤ (G.fam.identity v' u γ).maxOrder
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h3)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h3)]
      have e3 : (fun k => nativeDirect G γ (Finset.Icc 3 Dm) k t) = fun _ _ _ => 0 := by
        funext k f y
        exact nativeDirect_eq_zero_of_maxOrder G γ (by omega) _
          (fun d hd => (Finset.mem_Icc.1 hd).1) k t f y
      rw [e3, gluedFluxOp_zero]
  · simp only [hz, ↓reduceIte, and_false, Finset.sum_const_zero]


open scoped Classical in
/-- The sum over the paths, over `pathSet`. -/
theorem pathSide_eq_pathSet {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') (depth : ℕ) (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) :
    pathSide W depth g v ℓ t x =
      ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
        ∑ y ∈ pathSet G depth v.1, ∑ n ∈ Finset.Icc 2 (Mn.N + Dm),
          ∑ a ∈ Finset.range (Mn.p + 1), ∑ a' ∈ Finset.range (Mn.p + 1),
            dressedPathTerm Mn G y.2 (W.Cc (SuccSource.copyQuad [] y.1 y.2)) n a a' k t
              (pathField G g v ℓ y.2) x := by
  unfold pathSide
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have e : ∀ h ∈ Finset.Icc 1 depth, ∀ n ∈ Finset.Icc 2 (Mn.N + Dm),
      (∑ᶠ π : StagePath G h, if hπ : π.tgt = v.1 ∧ π.src ∈ G.comps then
        ∑ a ∈ Finset.range (Mn.p + 1), ∑ a' ∈ Finset.range (Mn.p + 1),
          dressedPathTerm Mn G π (W.Cc (SuccSource.copyQuad [] h π)) n a a' k t
            (fun y => ℓ (rootPathMap hr π.src.root π.mapList v.1.root (g y ⟨π.src, hπ.2⟩))) x
      else 0) =
      ∑ π : StagePath G h, if π.tgt = v.1 then
        ∑ a ∈ Finset.range (Mn.p + 1), ∑ a' ∈ Finset.range (Mn.p + 1),
          dressedPathTerm Mn G π (W.Cc (SuccSource.copyQuad [] h π)) n a a' k t
            (pathField G g v ℓ π) x
      else 0 := by
    intro h hh n _
    have h1 : 1 ≤ h := (Finset.mem_Icc.1 hh).1
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun π _ => ?_
    have hsrc : π.src ∈ G.comps := Providers.CascadeInvariants.stagePath_src_mem π h1
    by_cases ht : π.tgt = v.1
    · rw [dite_eq_left ⟨ht, hsrc⟩, ite_eq_left_of_eq_true _ _ (eq_true ht),
        pathField_eq G g v ℓ π hsrc]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ht)]
      exact dite_eq_right fun hπ => ht hπ.1
  rw [Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun n hn => e h hh n hn,
    Finset.sum_comm]
  have e2 : ∀ n ∈ Finset.Icc 2 (Mn.N + Dm),
      ∑ h ∈ Finset.Icc 1 depth, ∑ π : StagePath G h, (if π.tgt = v.1 then
        ∑ a ∈ Finset.range (Mn.p + 1), ∑ a' ∈ Finset.range (Mn.p + 1),
          dressedPathTerm Mn G π (W.Cc (SuccSource.copyQuad [] h π)) n a a' k t
            (pathField G g v ℓ π) x
      else 0) =
      ∑ y ∈ pathSet G depth v.1, ∑ a ∈ Finset.range (Mn.p + 1),
        ∑ a' ∈ Finset.range (Mn.p + 1),
          dressedPathTerm Mn G y.2 (W.Cc (SuccSource.copyQuad [] y.1 y.2)) n a a' k t
            (pathField G g v ℓ y.2) x := fun n _ =>
    sum_pathSet G depth v.1 (fun h π => ∑ a ∈ Finset.range (Mn.p + 1),
      ∑ a' ∈ Finset.range (Mn.p + 1),
        dressedPathTerm Mn G π (W.Cc (SuccSource.copyQuad [] h π)) n a a' k t
          (pathField G g v ℓ π) x)
  rw [Finset.sum_congr rfl e2, Finset.sum_comm]

/-- **The matching step of the source mean**: the sum over the sources is the sum over the paths. -/
theorem sourceMeanMatch : SourceMeanMatchStatement := by
  intro hr _ _ _ _ _ _ D Dm b j₀ P Mn G G' depth CcT hin W g hg v t x ℓ
  classical
  obtain ⟨Dord, nMax, hMax, npad, hA, hnMax, hD2, hvan, hpaths, hsX, hsZ⟩ := hin.range
  have hΛ := hin.stage.base
  have hζ := hin.stage.profile
  have hκ := hin.stage.band
  have hlev := hin.stage.level
  have hm : 1 ≤ G.level := by omega
  have hj : j₀ ≤ G.level := by omega
  have hN1 := hin.stage.cutoff
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have hDX : Dm ≤ Mn.sX := by omega
  have hDZ : Dm ≤ Mn.sZ := by omega
  have hn3 : 3 ≤ nMax := by omega
  have hmax : max 2 Dord = Dord := max_eq_right hD2
  have hpd : ∀ (h : ℕ) (_ : StagePath G h), h ≤ depth := fun h π => (hpaths h π).2
  have hpm : ∀ (h : ℕ) (_ : StagePath G h), h ≤ hMax := fun h π => (hpaths h π).1
  -- a path of at least one edge gives `nMax ≤ Dm`
  have hnD : ∀ (h : ℕ) (_ : StagePath G h), 1 ≤ h → nMax ≤ Dm := by
    intro h π h1
    have hmem : WordLetter.mean nMax 1 ∈ Mn.A := by
      rw [hA, mean_mem_succAlphabet]
      exact ⟨Finset.mem_Icc.2 ⟨hn3, le_rfl⟩, Finset.mem_Icc.2 ⟨le_rfl, h1.trans (hpm h π)⟩⟩
    exact (hin.stage.letter_orders _ hmem).2
  rw [sourceSide_eq_finsum, finsum_succSource_split G (sourceTerm W g v ℓ t x) nMax depth Mn.p
    (sourceTerm_of_word_ne W g v ℓ t x) (sourceTerm_letterDiag W g v ℓ t x []) ?_ ?_ ?_]
  rotate_left
  · intro h π hh
    rw [sourceTerm_copyQuad]
    exact ite_eq_right_of_eq_false _ _
      (eq_false fun hc => hh (Finset.mem_Icc.2 ⟨hc.1, hpd h π⟩))
  · intro n h π hh
    rw [sourceTerm_letterMean]
    refine ite_eq_right_of_eq_false _ _ (eq_false fun hc => hh ?_)
    have hmem := hc.1.1
    rw [hA, mean_mem_succAlphabet] at hmem
    exact ⟨hmem.1, Finset.mem_Icc.2 ⟨hc.1.2, hpd h π⟩⟩
  · intro n h a a' π hh
    rw [sourceTerm_letterCov W hm]
    refine ite_eq_right_of_eq_false _ _ (eq_false fun hc => hh ?_)
    have hmem := hc.1.1
    rw [hA, covariance_mem_succAlphabet] at hmem
    exact ⟨hmem.1.1, Finset.mem_range.2 hmem.2.1.1, Finset.mem_range.2 hmem.2.1.2,
      Finset.mem_Icc.2 ⟨hc.1.2, hpd h π⟩⟩
  rw [pathSide_eq_pathSet]
  -- the quadratic conversions
  have E2 : ∑ h ∈ Finset.Icc 1 depth, ∑ π : StagePath G h,
      sourceTerm W g v ℓ t x (SuccSource.copyQuad [] h π) =
      ∑ y ∈ pathSet G depth v.1, ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t,
        ocCutoff D.α D.q D.Λ G.level k t •
          dressedPathTerm Mn G y.2 (W.Cc (SuccSource.copyQuad [] y.1 y.2)) 2 0 0 k t
            (pathField G g v ℓ y.2) x := by
    rw [← sum_pathSet G depth v.1 (fun h π => ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t,
      ocCutoff D.α D.q D.Λ G.level k t •
        dressedPathTerm Mn G π (W.Cc (SuccSource.copyQuad [] h π)) 2 0 0 k t
          (pathField G g v ℓ π) x)]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
    have h1 : 1 ≤ h := (Finset.mem_Icc.1 hh).1
    rw [sourceTerm_copyQuad]
    by_cases ht : π.tgt = v.1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ht⟩), ite_eq_left_of_eq_true _ _ (eq_true ht)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun hc => ht hc.2),
        ite_eq_right_of_eq_false _ _ (eq_false ht)]
  -- the letters `𝖬`
  have E3 : ∑ n ∈ Finset.Icc 3 nMax, ∑ h ∈ Finset.Icc 1 depth, ∑ π : StagePath G h,
      sourceTerm W g v ℓ t x (SuccSource.letterMean [] n h π) =
      ∑ n ∈ Finset.Icc 3 nMax, ∑ y ∈ pathSet G depth v.1,
        ((∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
          dressedPathTerm Mn G y.2 (W.Cc (SuccSource.letterMean [] n y.1 y.2)) n 0 0 k t
            (pathField G g v ℓ y.2) x) - dirTerm G g v ℓ t x n y.1 y.2) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← sum_pathSet G depth v.1 (fun h π =>
      (∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
        dressedPathTerm Mn G π (W.Cc (SuccSource.letterMean [] n h π)) n 0 0 k t
          (pathField G g v ℓ π) x) - dirTerm G g v ℓ t x n h π)]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
    have h1 : 1 ≤ h := (Finset.mem_Icc.1 hh).1
    have hmem : WordLetter.mean n h ∈ Mn.A := by
      rw [hA, mean_mem_succAlphabet]
      exact ⟨hn, Finset.mem_Icc.2 ⟨h1, hpm h π⟩⟩
    rw [sourceTerm_letterMean]
    by_cases ht : π.tgt = v.1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨⟨hmem, h1⟩, ht⟩),
        ite_eq_left_of_eq_true _ _ (eq_true ht)]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun hc => ht hc.2),
        ite_eq_right_of_eq_false _ _ (eq_false ht)]
  -- the letters `𝖵`
  have E4 : ∑ n ∈ Finset.Icc 2 nMax, ∑ a ∈ Finset.range (Mn.p + 1),
      ∑ a' ∈ Finset.range (Mn.p + 1), ∑ h ∈ Finset.Icc 1 depth, ∑ π : StagePath G h,
        sourceTerm W g v ℓ t x (SuccSource.letterCov [] n h a a' π) =
      ∑ n ∈ Finset.Icc 2 nMax, ∑ a ∈ Finset.range (Mn.p + 1),
        ∑ a' ∈ Finset.range (Mn.p + 1), ∑ y ∈ pathSet G depth v.1,
          if 1 ≤ a + a' then ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t,
            ocCutoff D.α D.q D.Λ G.level k t •
              dressedPathTerm Mn G y.2 (W.Cc (SuccSource.letterCov [] n y.1 a a' y.2)) n a a' k t
                (pathField G g v ℓ y.2) x
          else 0 := by
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun a ha =>
      Finset.sum_congr rfl fun a' ha' => ?_
    rw [← sum_pathSet G depth v.1 (fun h π => if 1 ≤ a + a' then
      ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
        dressedPathTerm Mn G π (W.Cc (SuccSource.letterCov [] n h a a' π)) n a a' k t
          (pathField G g v ℓ π) x else 0)]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun π _ => ?_
    have h1 : 1 ≤ h := (Finset.mem_Icc.1 hh).1
    have hmem : WordLetter.covariance n h a a' ∈ Mn.A ↔ 1 ≤ a + a' := by
      rw [hA, covariance_mem_succAlphabet]
      exact ⟨fun hc => hc.2.2, fun hc => ⟨⟨hn, Finset.mem_Icc.2 ⟨h1, hpm h π⟩⟩,
        ⟨Finset.mem_range.1 ha, Finset.mem_range.1 ha'⟩, hc⟩⟩
    rw [sourceTerm_letterCov W hm]
    by_cases ht : π.tgt = v.1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ht)]
      by_cases hs : 1 ≤ a + a'
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨⟨hmem.2 hs, h1⟩, ht⟩),
          ite_eq_left_of_eq_true _ _ (eq_true hs)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false fun hc => hs (hmem.1 hc.1.1)),
          ite_eq_right_of_eq_false _ _ (eq_false hs)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun hc => ht hc.2),
        ite_eq_right_of_eq_false _ _ (eq_false ht)]
  -- the direct transports
  have E1 : ∑ z : (Σ v' u : CompIn G.comps, G.fam.Γ v' u),
      sourceTerm W g v ℓ t x (SuccSource.copyDir [] z.1 z.2.1 z.2.2) =
      ∑ n ∈ Finset.Icc 3 nMax, ∑ y ∈ pathSet G depth v.1, dirTerm G g v ℓ t x n y.1 y.2 := by
    rw [sum_dirTerm_eq G depth g v ℓ t x hvan (by omega)
      (fun z => hpd 1 (edgePath G z))
      (fun z d hd => ((Finset.mem_Icc.1 hd).2).trans (hnD 1 (edgePath G z) le_rfl))]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [sourceTerm_copyDir]
  rw [E1, E2, E3, E4]
  rcases (pathSet G depth v.1).eq_empty_or_nonempty with hP | hP
  · simp only [hP, Finset.sum_empty, Finset.sum_const_zero, smul_zero, add_zero]
  · obtain ⟨y₀, hy₀⟩ := hP
    have hy₀' := mem_pathSet hy₀
    have hNtop : nMax ≤ Mn.N + Dm := (hnD y₀.1 y₀.2 hy₀'.1).trans (Nat.le_add_left _ _)
    have key := sourceMean_match_algebra (ocObsPulses D.α D.q D.Λ G.level t t)
      (fun k => ocCutoff D.α D.q D.Λ G.level k t) (pathSet G depth v.1) nMax (Mn.N + Dm) Mn.p
      (by omega) hNtop
      (fun y n a a' k => dressedPathTerm Mn G y.2 (W.Cc (SuccSource.copyQuad [] y.1 y.2)) n a a' k t
        (pathField G g v ℓ y.2) x)
      (fun y n k => dressedPathTerm Mn G y.2 (W.Cc (SuccSource.letterMean [] n y.1 y.2)) n 0 0 k t
        (pathField G g v ℓ y.2) x)
      (fun y n a a' k => dressedPathTerm Mn G y.2 (W.Cc (SuccSource.letterCov [] n y.1 a a' y.2))
        n a a' k t (pathField G g v ℓ y.2) x)
      (fun y n => dirTerm G g v ℓ t x n y.1 y.2)
      (fun y _ n k _ hc => dressedPathTerm_lift_indep hΛ hζ hκ Mn G hm hj y.2 _ _
        (W.lifts (SuccSource.letterMean [] n y.1 y.2)) (W.lifts (SuccSource.copyQuad [] y.1 y.2))
        n 0 0 k (Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hc) _ x)
      (fun y _ n a a' k _ hc => dressedPathTerm_lift_indep hΛ hζ hκ Mn G hm hj y.2 _ _
        (W.lifts (SuccSource.letterCov [] n y.1 a a' y.2))
        (W.lifts (SuccSource.copyQuad [] y.1 y.2))
        n a a' k (Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hc) _ x)
      (fun y _ n a a' hn k _ hc => dressedPathTerm_high hΛ hζ hκ Mn G hm hj y.2 _
        (W.lifts (SuccSource.copyQuad [] y.1 y.2)) (E := Dord)
        (fun j p c d I _ hd => hvan p c _ _ _ d I hd) hDX hDZ (by rw [hmax]; omega) a a' k
        (Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hc)
        (pathField_contDiff G hg v ℓ y.2) x)
    rw [← key]
    abel

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The source-mean step, the Left step**: `sourceMeanLeft : SourceMeanLeftStatement`.

The steps: the readout (`sml_readoutStep`), the term (`sml_termStep`: the root-bookkeeping and transfer steps and the finite
order of `sourceEulerOp`, `sml_sourceEuler_expansion`) and the reindexing (`sml_reindexStep`),
assembled by `sml_assembly`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- **The source-mean step, the Left step**: the tested difference of the plain and the diagonal readouts of a
smooth field frozen in time is the sum over the sources. -/
theorem sourceMeanLeft : SourceMeanLeftStatement := by
  intro hbk h4 hr _ _ _ _ _ _ D Dm b j₀ P seedK freshK φ₀ Mn G G' depth CcT hin W g hg v t x ℓ j
  exact sml_assembly P seedK freshK φ₀ Mn G G' W g v ℓ j t x
    (sml_readoutStep P seedK freshK φ₀ Mn G G' g v ℓ j t x)
    (sml_termStep hbk h4 P Mn G G' depth CcT hin W g hg v ℓ j t x)
    (sml_reindexStep hbk P Mn G G' hin.stage hin.successor W v)

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The source-mean step from its top-level steps**: the identity for a field of class `C^K` from the
identity for smooth fields, the jet locality of `Q_p 𝐄^flux P_p` and the realization of
jets by smooth functions.

`rootReadout_plain_congr`, `diagReadout_congr`: the plain flux out of the roots and its
first-source part read the field through its ordered derivatives of the orders `≤ Dm - 1` at the
point, at the time of evaluation. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The plain flux out of the roots sees the jets of the orders `≤ Dm - 1` of the field. -/
theorem rootFluxOn_plain_congr (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' : GenStage D hr Dm b j₀) {g₁ g₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root}
    {t : ℝ} {x : Vec 2}
    (h : ∀ (u : CompIn G.comps) (r : ℕ) (I : DerivativeWord2 r), r + 1 ≤ Dm →
      orderedDerivative I (fun y => g₁ t y u) x = orderedDerivative I (fun y => g₂ t y u) x)
    (v' : CompIn G'.comps) :
    rootFluxOn P seedK freshK φ₀ G G' .plain g₁ v' t x =
      rootFluxOn P seedK freshK φ₀ G G' .plain g₂ v' t x := by
  unfold rootFluxOn
  refine Finset.sum_congr rfl fun u' _ => ?_
  split_ifs with hu
  · refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun d _ => ?_
    have hd := Finset.mem_Icc.1 d.2
    have e : (fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => g₁ t y ⟨u'.1, hu⟩) x) =
        fun word => orderedDerivative word (fun y => g₂ t y ⟨u'.1, hu⟩) x := by
      funext word
      exact h ⟨u'.1, hu⟩ (d.1 - 1) word (by omega)
    show G'.physCoeff v' u' γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => g₁ t y ⟨u'.1, hu⟩) x) =
      G'.physCoeff v' u' γ d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        orderedDerivative word (fun y => g₂ t y ⟨u'.1, hu⟩) x)
    rw [e]
  · rfl

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The first-source part of the plain flux out of the roots, likewise. -/
theorem rootDiagFlux_congr (G G' : GenStage D hr Dm b j₀)
    {g₁ g₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root} {t : ℝ} {x : Vec 2}
    (h : ∀ (u : CompIn G.comps) (r : ℕ) (I : DerivativeWord2 r), r + 1 ≤ Dm →
      orderedDerivative I (fun y => g₁ t y u) x = orderedDerivative I (fun y => g₂ t y u) x)
    (v' : CompIn G'.comps) :
    rootDiagFlux G G' g₁ v' t x = rootDiagFlux G G' g₂ v' t x := by
  unfold rootDiagFlux
  refine Finset.sum_congr rfl fun u' _ => ?_
  split_ifs with hu
  · refine Finset.sum_congr rfl fun γ _ => ?_
    split_ifs with hp
    · refine Finset.sum_congr rfl fun d _ => ?_
      have hd := Finset.mem_Icc.1 d.2
      have e : (fun word : DerivativeWord2 (d.1 - 1) =>
          orderedDerivative word (fun y => g₁ t y ⟨u'.1, hu⟩) x) =
          fun word => orderedDerivative word (fun y => g₂ t y ⟨u'.1, hu⟩) x := by
        funext word
        exact h ⟨u'.1, hu⟩ (d.1 - 1) word (by omega)
      rw [e]
    · rfl
  · rfl

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The plain readout out of the roots sees the jets of the orders `≤ Dm - 1` of the field at the
point, at the time of evaluation. -/
theorem rootReadout_plain_congr (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' : GenStage D hr Dm b j₀) (m : ℕ) (E η : ℝ)
    {g₁ g₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root} {t : ℝ} {x : Vec 2}
    (h : ∀ (u : CompIn G.comps) (r : ℕ) (I : DerivativeWord2 r), r + 1 ≤ Dm →
      orderedDerivative I (fun y => g₁ t y u) x = orderedDerivative I (fun y => g₂ t y u) x)
    (v : CompIn G.comps) :
    rootReadout P seedK freshK φ₀ G G' .plain m E η g₁ v t x =
      rootReadout P seedK freshK φ₀ G G' .plain m E η g₂ v t x := by
  unfold rootReadout readoutFlux
  refine Finset.sum_congr rfl fun v' _ => ?_
  beta_reduce
  rw [rootFluxOn_plain_congr P seedK freshK φ₀ G G' h v']

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The first-source readout, likewise. -/
theorem diagReadout_congr (G G' : GenStage D hr Dm b j₀) (m : ℕ) (E η : ℝ)
    {g₁ g₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root} {t : ℝ} {x : Vec 2}
    (h : ∀ (u : CompIn G.comps) (r : ℕ) (I : DerivativeWord2 r), r + 1 ≤ Dm →
      orderedDerivative I (fun y => g₁ t y u) x = orderedDerivative I (fun y => g₂ t y u) x)
    (v : CompIn G.comps) :
    diagReadout G G' m E η g₁ v t x = diagReadout G G' m E η g₂ v t x := by
  unfold diagReadout readoutFlux
  refine Finset.sum_congr rfl fun v' _ => ?_
  beta_reduce
  rw [rootDiagFlux_congr G G' h v']

/-- **The source-mean step from its three top-level steps.** -/
theorem sourceMeanLetterSum_of_steps (hT : SmoothJetRealizationStatement)
    (hJ : CovMeanJetStatement) (hS : SourceMeanSmoothStatement) :
    SourceMeanLetterSumStatement := by
  intro h1 h4 h5 hr _ _ _ _ _ _ D Dm b j₀ P seedK freshK φ₀ Mn G G' depth CcT hin K hK ta tb g hg
    v t ht x
  have hex : ∀ u : CompIn G.comps, ∃ T : Vec 2 → hr u.1.root, ContDiff ℝ (⊤ : ℕ∞) T ∧
      ∀ (r : ℕ) (I : DerivativeWord2 r), r ≤ K →
        orderedDerivative I T x = orderedDerivative I (fun y => g t y u) x :=
    fun u => hT K _ (hg u t ht).1 x
  choose T hTs hTj using hex
  have hjet : ∀ (u : CompIn G.comps) (r : ℕ) (I : DerivativeWord2 r), r + 1 ≤ Dm →
      orderedDerivative I (fun y => g t y u) x = orderedDerivative I (fun y => T u y) x :=
    fun u r I hr => (hTj u r I (by omega)).symm
  have hsm := hS h1 h4 h5 P seedK freshK φ₀ Mn G G' depth CcT hin (fun y u => T u y)
    (fun u => hTs u) v t x
  have hR := hJ P Mn G G' depth CcT hin K hK t x g (fun _ y u => T u y)
    (fun u => (hg u t ht).1) (fun u => (hTs u).of_le (by exact_mod_cast le_top))
    (fun u r I hr => (hTj u r I hr).symm) v
  rw [rootReadout_plain_congr P seedK freshK φ₀ G G' G.level (D.eps (G.level - 1)) Mn.η0
      (g₂ := fun _ y u => T u y) hjet v,
    diagReadout_congr G G' G.level (D.eps (G.level - 1)) Mn.η0 (g₂ := fun _ y u => T u y) hjet v,
    hR]
  exact hsm

/-- **The source-mean step from the jet locality and the smooth case**: the jet locality and the
identity for smooth fields; the realization of jets is `smoothJetRealization`. -/
theorem sourceMeanLetterSum_of_jet_smooth (hJ : CovMeanJetStatement)
    (hS : SourceMeanSmoothStatement) : SourceMeanLetterSumStatement :=
  sourceMeanLetterSum_of_steps smoothJetRealization hJ hS

/-- **The source-mean step from the jet locality and the left, right and matching steps**: the
jet locality and the three steps of the identity for smooth fields (left, right, matching). -/
theorem sourceMeanLetterSum_of_open (hJ : CovMeanJetStatement) (hL : SourceMeanLeftStatement)
    (hR : SourceMeanRightStatement) (hM : SourceMeanMatchStatement) :
    SourceMeanLetterSumStatement :=
  sourceMeanLetterSum_of_jet_smooth hJ (sourceMeanSmooth_of_steps hL hR hM)

/-- **The source-mean step from the jet locality and the left and right steps**: the jet locality
and the left and right steps of the identity for smooth fields; the matching step is
`sourceMeanMatch`. -/
theorem sourceMeanLetterSum_of_left_right (hJ : CovMeanJetStatement)
    (hL : SourceMeanLeftStatement) (hR : SourceMeanRightStatement) :
    SourceMeanLetterSumStatement :=
  sourceMeanLetterSum_of_open hJ hL hR sourceMeanMatch

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
