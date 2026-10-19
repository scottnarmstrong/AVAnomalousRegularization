-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.Pieces
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.FullX
import AVRegularity.CycleComparison.Reconstruction.ChainLinear

section
section
/-! The kernel average commutes with the readout of the retained fields: the readout weights
as a continuous linear map on the product of the fibres, and the ordered derivatives of the kernel
average of the readout read through a continuous linear map (the coefficients of the successor)
as the weighted sum of the same expressions for the retained fields. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Providers
  AVRegularity.Providers.KernelSup AVRegularity.Analysis.Convolution
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]

/-- The cast of a fibre space along an equality of roots, as a continuous linear map. -/
def reindexCastCLM {r r' : ℕ} (e : r = r') : hr r →L[ℝ] hr r' :=
  e ▸ ContinuousLinearMap.id ℝ (hr r)

theorem reindexCastCLM_apply {r r' : ℕ} (e : r = r') (z : hr r) :
    reindexCastCLM (hr := hr) e z = cast (congrArg hr e) z := by
  subst e
  rfl

variable [∀ r, CompleteSpace (hr r)]

/-- The paired kernel average commutes with a continuous linear map. -/
theorem reindex_kernel_clm_comm {φ₀ : Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (S : KernelSpec) (t : ℝ)
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) {f : Vec 2 → E} (hf : Continuous f) (hp : IsZ2Periodic f) (y : Vec 2) :
    T (S.applyClassical φ₀ t f y) = S.applyClassical φ₀ t (fun x => T (f x)) y := by
  have hφc := hasCompactSupport_of_unitBall hφsupp
  have hkK : IsKer (tensorKer (momentKernel φ₀ S.order)) :=
    isKer_tensorKer (contDiff_momentKernel hφc hφs S.order)
      (hasCompactSupport_momentKernel hφc S.order)
  obtain ⟨B, hB⟩ := bdd_of_periodic hf hp
  have hTf : Continuous fun x => T (f x) := T.continuous.comp hf
  have hB' : ∀ y, ‖T (f y)‖ ≤ ‖T‖ * B := fun y =>
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _))
  rw [applyClassical_eq_op S _ rfl hkK t hf hB, applyClassical_eq_op S _ rfl hkK t hTf hB']
  unfold Op
  have hint := integrable_op (μ := (volume : Measure (Vec 2 × Vec 2))) hkK
    (kerMap S.width (S.H₁ t) (S.H₂ t)) hf hB y
  rw [← T.integral_comp_comm hint]
  congr 1
  funext z
  simp [map_smul]


open scoped Classical in
/-- The readout weights as a continuous linear map on the retained fields. -/
def reindexReadoutCLM (m : ℕ) (E η : ℝ) {S₁ : Finset Comp} (u : Comp) :
    (∀ c : CompIn S₁, hr c.1.root) →L[ℝ] hr u.root :=
  ∑ c : CompIn S₁, if h : compParent m c.1 = u then
    (E ^ (η * ((compWord m c.1).length : ℝ))) •
      (reindexCastCLM (hr := hr) ((compParent_root m c.1).symm.trans (congrArg Comp.root h))).comp
        (ContinuousLinearMap.proj c)
  else 0

omit [∀ r, CompleteSpace (hr r)] in
theorem reindexReadoutCLM_apply (m : ℕ) (E η : ℝ) {S₁ : Finset Comp} (u : Comp)
    (z : ∀ c : CompIn S₁, hr c.1.root) :
    reindexReadoutCLM (hr := hr) m E η u z =
      ∑ c : CompIn S₁, if h : compParent m c.1 = u then
        (E ^ (η * ((compWord m c.1).length : ℝ))) •
          cast (congrArg hr ((compParent_root m c.1).symm.trans (congrArg Comp.root h))) (z c)
      else 0 := by
  classical
  unfold reindexReadoutCLM
  rw [sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : compParent m c.1 = u
  · simp [h, reindexCastCLM_apply]
  · simp [h]


open scoped Classical in
/-- **The kernel average commutes with the readout.** For the readout `aZu` of fields `aY c` (at the
root `u`), the ordered derivatives of the kernel average of `aZu`, read through any continuous
linear map `B`, are the weighted sum over the columns of the same expression for each `aY c`. -/
theorem reindex_kernel_readout_term {φ₀ : Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hφsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (S : KernelSpec) (t : ℝ) (m : ℕ) (E η : ℝ) {S₁ : Finset Comp}
    (aY : Vec 2 → ∀ c : CompIn S₁, hr c.1.root) (hcont : ∀ c, Continuous fun x => aY x c)
    (hper : ∀ c, IsZ2Periodic fun x => aY x c) {j : ℕ}
    (hdiff : ∀ c, ContDiff ℝ (j : ℕ∞) (S.applyClassical φ₀ t fun x => aY x c))
    (u : Comp) (aZu : Vec 2 → hr u.root)
    (hZ : aZu = fun x => ∑ c : CompIn S₁, if h : compParent m c.1 = u then
      (E ^ (η * ((compWord m c.1).length : ℝ))) •
        cast (congrArg hr ((compParent_root m c.1).symm.trans (congrArg Comp.root h))) (aY x c)
      else 0) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : PiLp 2 (fun _ : DerivativeWord2 j => hr u.root) →L[ℝ] F) (x : Vec 2) :
    B (WithLp.toLp 2 fun word : DerivativeWord2 j =>
        orderedDerivative word (S.applyClassical φ₀ t aZu) x) =
      ∑ c : CompIn S₁, if h : compParent m c.1 = u then
        (E ^ (η * ((compWord m c.1).length : ℝ))) • B (WithLp.toLp 2 fun word : DerivativeWord2 j =>
          cast (congrArg hr ((compParent_root m c.1).symm.trans (congrArg Comp.root h)))
            (orderedDerivative word (S.applyClassical φ₀ t fun x' => aY x' c) x))
      else 0 := by
  let T := reindexReadoutCLM (hr := hr) m E η (S₁ := S₁) u
  let Yh : Vec 2 → ∀ c : CompIn S₁, hr c.1.root := aY
  have hYc : Continuous Yh := continuous_pi fun c => hcont c
  have hYp : IsZ2Periodic Yh := fun x i => funext fun c => hper c x i
  have hZT : aZu = fun x => T (Yh x) := by
    rw [hZ]
    funext x
    rw [reindexReadoutCLM_apply]
  have hS : ∀ y, S.applyClassical φ₀ t aZu y = T (S.applyClassical φ₀ t Yh y) := by
    intro y
    rw [hZT]
    exact (reindex_kernel_clm_comm hφs hφsupp S t T hYc hYp y).symm
  have hc : ∀ (c : CompIn S₁) y, S.applyClassical φ₀ t Yh y c =
      S.applyClassical φ₀ t (fun x' => aY x' c) y := by
    intro c y
    exact reindex_kernel_clm_comm hφs hφsupp S t (ContinuousLinearMap.proj c) hYc hYp y
  have hdY : ContDiff ℝ (j : ℕ∞) (S.applyClassical φ₀ t Yh) := by
    refine contDiff_pi.2 fun c => ?_
    have : (fun y => S.applyClassical φ₀ t Yh y c) = S.applyClassical φ₀ t fun x' => aY x' c :=
      funext (hc c)
    rw [this]
    exact hdiff c
  have e1 : S.applyClassical φ₀ t aZu = fun y => T (S.applyClassical φ₀ t Yh y) := funext hS
  have hword : ∀ word : DerivativeWord2 j, orderedDerivative word (S.applyClassical φ₀ t aZu) x =
      T (orderedDerivative word (S.applyClassical φ₀ t Yh) x) := by
    intro word
    rw [e1, orderedDerivative_clm_comp T word hdY]
  have hcomp : ∀ (word : DerivativeWord2 j) (c : CompIn S₁),
      orderedDerivative word (S.applyClassical φ₀ t Yh) x c =
        orderedDerivative word (S.applyClassical φ₀ t fun x' => aY x' c) x := by
    intro word c
    have h1 := orderedDerivative_clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun c : CompIn S₁ => hr c.1.root) c) word hdY
    have h2 : (fun y => (ContinuousLinearMap.proj (R := ℝ) (φ := fun c : CompIn S₁ => hr c.1.root) c)
        (S.applyClassical φ₀ t Yh y)) = S.applyClassical φ₀ t fun x' => aY x' c := funext (hc c)
    rw [h2] at h1
    exact (congrFun h1 x).symm
  have hsplit : (WithLp.toLp 2 fun word : DerivativeWord2 j =>
        orderedDerivative word (S.applyClassical φ₀ t aZu) x) =
      ∑ c : CompIn S₁, if h : compParent m c.1 = u then
        (E ^ (η * ((compWord m c.1).length : ℝ))) • (WithLp.toLp 2 fun word : DerivativeWord2 j =>
          cast (congrArg hr ((compParent_root m c.1).symm.trans (congrArg Comp.root h)))
            (orderedDerivative word (S.applyClassical φ₀ t fun x' => aY x' c) x))
      else 0 := by
    ext word
    rw [WithLp.ofLp_sum]
    simp only [hword, Finset.sum_apply]
    show (reindexReadoutCLM (hr := hr) m E η u (orderedDerivative word (S.applyClassical φ₀ t Yh) x)) = _
    rw [reindexReadoutCLM_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : compParent m c.1 = u
    · simp only [h, ↓reduceDIte, hcomp]
      rfl
    · simp [h]
  rw [hsplit, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : compParent m c.1 = u <;> simp [h]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The algebraic part of `CovarianceFluxRegularityStatement`: given that the temporal flux
`𝒟 g` and the mean flux `𝐄^flux P_p g` are `C^{2p}` in space, `Q_p` is additive on them
(third clause) and `Q_p G` is continuous (last clause). The smoothness of the two fluxes and the
continuity of the plain flux are proved separately. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The covariance operator is additive (subtractive) on `C^2` fields. -/
theorem covOperator_sub (Hc : Matrix (Fin 2) (Fin 2) ℝ) {f g : Vec 2 → E}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    covOperator Hc (fun y => f y - g y) = fun y => covOperator Hc f y - covOperator Hc g y := by
  funext x
  have hfd (y : Vec 2) : fderiv ℝ (fun y => f y - g y) y = fderiv ℝ f y - fderiv ℝ g y :=
    fderiv_sub (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  have hj (j : Fin 2) : (fun y => fderiv ℝ (fun y => f y - g y) y (basisVec j)) =
      fun y => fderiv ℝ f y (basisVec j) - fderiv ℝ g y (basisVec j) := by
    funext y
    rw [hfd]
    rfl
  have hdf (j : Fin 2) : DifferentiableAt ℝ (fun y => fderiv ℝ f y (basisVec j)) x :=
    (((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)) x
  have hdg (j : Fin 2) : DifferentiableAt ℝ (fun y => fderiv ℝ g y (basisVec j)) x :=
    (((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)) x
  have hx (i j : Fin 2) : fderiv ℝ (fun y => fderiv ℝ (fun y => f y - g y) y (basisVec j)) x
      (basisVec i) = fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x (basisVec i) -
        fderiv ℝ (fun y => fderiv ℝ g y (basisVec j)) x (basisVec i) := by
    rw [hj j, fderiv_fun_sub (hdf j) (hdg j)]
    rfl
  unfold covOperator
  simp only [hx, smul_sub, Finset.sum_sub_distrib]

/-- Iterates of the covariance operator are subtractive on fields of enough regularity. -/
theorem covOperator_iterate_sub (Hc : Matrix (Fin 2) (Fin 2) ℝ) (l : ℕ) :
    ∀ {f g : Vec 2 → E}, ContDiff ℝ (2 * l : ℕ) f → ContDiff ℝ (2 * l : ℕ) g →
      (covOperator Hc)^[l] (fun y => f y - g y) =
        fun y => (covOperator Hc)^[l] f y - (covOperator Hc)^[l] g y := by
  induction l with
  | zero => intro f g _ _; rfl
  | succ l ih =>
    intro f g hf hg
    have hf' : ContDiff ℝ (2 * l : ℕ) f :=
      hf.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * (l + 1)))
    have hg' : ContDiff ℝ (2 * l : ℕ) g :=
      hg.of_le (by exact_mod_cast (by omega : 2 * l ≤ 2 * (l + 1)))
    rw [Function.iterate_succ_apply', ih hf' hg']
    have h2 (u : Vec 2 → E) (hu : ContDiff ℝ (2 * (l + 1) : ℕ) u) :
        ContDiff ℝ 2 ((covOperator Hc)^[l] u) := by
      have hu' : ContDiff ℝ (((2 + 2 * l : ℕ) : ℕ∞)) u := by
        have : 2 + 2 * l = 2 * (l + 1) := by omega
        rw [this]
        exact_mod_cast hu
      have := AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc l 2 u
        hu'
      exact_mod_cast this
    have := covOperator_sub Hc (h2 f hf) (h2 g hg)
    funext x
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact congrFun this x

/-- `Q_p` is subtractive on `C^{2p}` fields. -/
theorem covPolyQ_sub (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {f g : Vec 2 → E}
    (hf : ContDiff ℝ (2 * p : ℕ) f) (hg : ContDiff ℝ (2 * p : ℕ) g) :
    covPolyQ Hc p (fun y => f y - g y) = fun y => covPolyQ Hc p f y - covPolyQ Hc p g y := by
  funext x
  unfold covPolyQ
  simp only [Finset.sum_apply, Pi.smul_apply, ← Finset.sum_sub_distrib, ← smul_sub]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hle : ((2 * l : ℕ) : WithTop ℕ∞) ≤ ((2 * p : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by omega : 2 * l ≤ 2 * p)
  rw [covOperator_iterate_sub Hc l (hf.of_le hle) (hg.of_le hle)]

/-- `Q_p` of a `C^{2p}` field is continuous. -/
theorem covPolyQ_continuous (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (2 * p : ℕ) f) : Continuous (covPolyQ Hc p f) := by
  unfold covPolyQ
  rw [show (∑ l ∈ Finset.range (p + 1), (((-1 : ℝ) ^ l / (l.factorial : ℝ))) •
      (covOperator Hc)^[l] f) = fun x => ∑ l ∈ Finset.range (p + 1),
        (((-1 : ℝ) ^ l / (l.factorial : ℝ))) • (covOperator Hc)^[l] f x by
    funext x; simp [Finset.sum_apply]]
  refine continuous_finsetSum _ fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  have hle : ((0 + 2 * l : ℕ) : WithTop ℕ∞) ≤ (2 * p : ℕ) := by
    exact_mod_cast (by omega : 0 + 2 * l ≤ 2 * p)
  have := AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc l 0 f
    (hf.of_le hle)
  exact (this.continuous).const_smul _

end Algebra

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **Clauses three and five of `CovarianceFluxRegularityStatement` from the first two.** -/
theorem menuCovFlux_split_of_contDiff (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m N p depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps) (t : ℝ)
    (hT : ContDiff ℝ (2 * p : ℕ) (fun y => menuTemporalFlux Mn G m N p CcT g t v y))
    (hM : ContDiff ℝ (2 * p : ℕ) (fun y => menuMeanFluxE Mn G m N depth CcT
      (menuCovPRep Mn D m p g) t y v)) :
    (∀ x : Vec 2, menuCovFlux Mn G m N p depth CcT g v t x =
      covTemporalAt Mn G m N p CcT g v t x - covMeanAt Mn G m N p depth CcT g v t x) ∧
    Continuous (menuCovFlux Mn G m N p depth CcT g v t) := by
  have hsub := covPolyQ_sub (menuCovPrimitive D Mn m t) p hT hM
  refine ⟨fun x => ?_, ?_⟩
  · have h := congrFun hsub x
    unfold menuCovFlux covTemporalAt covMeanAt
    change toFluxL (covPolyQ (menuCovPrimitive D Mn m t) p
      (fun y => menuTemporalFlux Mn G m N p CcT g t v y -
        menuMeanFluxE Mn G m N depth CcT (menuCovPRep Mn D m p g) t y v) x) = _
    rw [h]
    rfl
  · have hG : ContDiff ℝ (2 * p : ℕ) (fun y => menuGFlux Mn G m N p depth CcT g v t y) :=
      hT.sub hM
    exact (PiLp.continuous_toLp 2 _).comp (covPolyQ_continuous _ p hG)

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! The path-sum step (`HilbertLiftPathSumStatement`), split into three steps.

The Hilbert lift `CcT` and the lifts `Cπ` of the scalar path families are both unique
(`native_family_lift_coefficients_unique`), so the path sum is first an identity between
*coefficient arrays* on the ladder, and then a linear-algebra consequence for the slow flux
`liftFluxX`.

* `HLArrayIdentities`: the arrays of the Hilbert lift at grade `g + 1` (all rows and columns) and at
  grade `g` (rows that are the source of an identity `s`) are the path sums of the `(last ← 0)`
  entries of the lifts `Cπ` of the paths of `g + 1` edges, times the composed maps. Only lifts of
  paths of exactly `g + 1` edges are assumed; the grade-`g` array of the Hilbert lift into a source
  row of `s` is read off the lifts of the paths ending with `s` (every path of `g` edges into that
  source extends by `s`, so no path of fewer edges without extension enters).
* `HilbertLiftGradeZeroStatement`: the grade-zero conjunct.
* The arrays step (uniqueness on the ladder).
* The flux identity from the array identities (linearity of `liftApply` and `sourceFlux`,
  constant maps commuting with slow and fast derivatives on the open ladder, `ℓ` commuting with
  the cell mean).

`hilbertLiftPathSum` proves `HilbertLiftPathSumStatement` along these steps.

The hypothesis `ActualFluxJointSmooth G` (joint smoothness of the flux coefficients of the incoming
stage) is assumed in the path-sum step and in steps 2 and 3; the
proved step 1 (grade zero) does not need it. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

open scoped Classical in
/-- The two array identities of the Hilbert lift against the lifts `Cπ` of the paths of `g + 1`
edges, at the cell times of the window of the pulse `k` and the slow offsets of the ladder. -/
def HLArrayIdentities {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (G : GenStage D hr Dm b j₀) (ρ : ℝ) (k : ℤ)
    (CcT : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)) (g : ℕ)
    (Cπ : ∀ h' : ℕ, StagePath G h' → ℕ → ℕ → LiftCoeff (Fin (h' + 1)) (fun _ => ℝ)) : Prop :=
  (∀ (n m : ℕ) (α : DerivativeWord2 m) (τ : ℝ),
    τ ∈ Set.Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) →
    ∀ X ∈ ladderOmega D b j₀ G.level k (nativeChain G.level k) ρ, ∀ (z : Vec 2)
      (v u : CompIn G.comps),
      CcT (g + 1) n m α τ X z v u =
        ∑ᶠ π : StagePath G (g + 1), if π.tgt = v.1 ∧ π.src = u.1 then
          (Cπ (g + 1) π (g + 1) n m α τ X z (Fin.last (g + 1)) 0 1) •
            rootPathMap hr u.1.root π.mapList v.1.root
        else 0) ∧
  (∀ (s : Σ (v u : CompIn G.comps), G.fam.Γ v u) (n m : ℕ) (α : DerivativeWord2 m) (τ : ℝ),
    τ ∈ Set.Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) →
    ∀ X ∈ ladderOmega D b j₀ G.level k (nativeChain G.level k) ρ, ∀ (z : Vec 2)
      (u : CompIn G.comps),
      CcT g n m α τ X z s.2.1 u =
        ∑ᶠ π : StagePath G (g + 1), if π.step (Fin.last g) = s ∧ π.src = u.1 then
          (Cπ (g + 1) π g n m α τ X z (Fin.castSucc (Fin.last g)) 0 1) •
            rootPathMap hr u.1.root (π.mapList.take g) s.2.1.1.root
        else 0)

/-- **Step 1 of the path-sum step (grade zero).** The second conjunct of `HilbertLiftPathSumStatement`: the
grade-zero Hilbert lift is the scalar lift with no edge, on each component. Route: the global
relation gives the localized one (`IsLiftSequence.toOn`); the candidate `δ_{vu} C0 · id` is a
localized lift sequence of the Hilbert operator data at grade zero (the cell equation is componentwise and
`liftCellSource` at grade zero reads no edge); `native_family_lift_coefficients_unique` on the
open ladder (`isOpen_ladderOmega`) identifies it with `CcT` on the ladder; then
`liftFluxX` at grade zero reads the arrays only in neighbourhoods of `X`
(`LocEq`). -/
def HilbertLiftGradeZeroStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀),
    StageSuccessor.Input P Mn G → Mn.N + Dm + 2 ≤ Mn.sX → Mn.N + Dm + 2 ≤ Mn.sZ →
    ∀ (ρ : ℝ), ρ = Mn.lenFactor * liftLength D G.level →
    ∀ (depth : ℕ) (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (k : ℤ) (hk : Odd k) (_hadm : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k)),
    IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k) ρ
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N depth
      (CcT k) →
    ∀ τ ∈ Set.Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
    ∀ (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root), (∀ s, ContDiff ℝ (⊤ : ℕ∞) (a s)) →
    ∀ (n : ℕ) (X : Vec 2), X ∈ ladderOmega D b j₀ G.level k (nativeChain G.level k) ρ →
    ∀ (j : Fin 2) (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ),
    (∀ (C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)),
      IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k
          (nativeChain G.level k) ρ (fun _ _ _ => []))
        Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N 0 C0 →
      ℓ (fieldCellMean (fun z => liftFluxX (familyLiftData D G.level k (nativeChain G.level k) ρ
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩))) (CcT k) a 0 n τ X z j) v) =
        fieldCellMean (fun z => liftFluxX (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ)
            D G.level k (nativeChain G.level k) ρ (fun _ _ _ => [])) C0
          (fun s' X' => fun _ : Fin 1 => ℓ (a s' X' v)) 0 n τ X z j) 0)

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Source mean (the letters sum to the source mean): the top-level steps**.

`SourceMeanLetterSumStatement` concludes a pointwise identity for a field `g` of class `C^K`,
`K ≥ N + Dm + 4p`, while the ingredients from which the identity comes are statements about smooth
fields. The reduction (`sourceMeanLetterSum_of_steps`) is:

* `SourceMeanSmoothStatement`: the identity for a smooth field frozen in time (the letters
  algebra: degree `2` = `copyQuad`; degrees `n ≥ 3` = `letterMean` plus the direct part of a one-edge
  path = `copyDir`; the covariance letters `letterCov`; the two range conditions), from
  `RootSourceBookkeepingStatement`, `TransferredIdentityEulerianOnStatement` and
  `HilbertLiftPathSumStatement`;
* `CovMeanJetStatement`: `covMeanAt … g v t x` depends only on the jets of `g(t, ·)` at `x` of
  the orders `≤ K` (the field at other times is not seen: `liftFluxX` reads the coarse field at
  its time argument only; `liftApply` is an explicit differential operator; the `ε^{j-1}`
  coefficient of `sourceFlux` takes `j - 1` slow derivatives; so `𝐄^flux P_p g` uses the jets of the
  orders `≤ N + Dm - 1 + 2p` and `Q_p` adds `2p`). This is the `C^k` caveat of the module
  `FluxCancellation.Pieces`: a traversal of `liftFluxX` at finite regularity, of the kind of the
  covariance flux regularity;
* `SmoothJetRealizationStatement`: a `C^K` function has the jets of the orders `≤ K` at a point of
  a smooth function (its Taylor polynomial there).

The left side sees the jets of `g(t, ·)` at `x` of the orders `≤ Dm - 1` by definition
(`rootReadout_plain_congr`, `diagReadout_congr`), so the identity for `g` is the identity for the
Taylor polynomial of `g(t, ·)` at `x`, frozen in time.

For `g` smooth and constant in time the first statement alone suffices, and for `g = 0` every
side vanishes and the Taylor polynomial is `0`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

/-- A function of class `C^K` has, at every point, the jets of the orders `≤ K` of a smooth
function. -/
def SmoothJetRealizationStatement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : ℕ) (f : Vec 2 → E),
    ContDiff ℝ (K : ℕ) f → ∀ x : Vec 2, ∃ T : Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) T ∧
      ∀ (r : ℕ) (I : DerivativeWord2 r), r ≤ K →
        orderedDerivative I T x = orderedDerivative I f x

/-- **Jet locality of `Q_p 𝐄^flux P_p`.** Two fields which are of class `C^K` at the time `t`,
`K ≥ N + Dm + 4p`, and have the same jets of the orders `≤ K` at `x` at that time, have the same
`covMeanAt` at `(t, x)`. Nothing is asked of the fields at other times. -/
def CovMeanJetStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (K : ℕ), Mn.N + Dm + 4 * Mn.p ≤ K →
    ∀ (t : ℝ) (x : Vec 2) (g₁ g₂ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ (K : ℕ) (fun y => g₁ t y v)) →
      (∀ v, ContDiff ℝ (K : ℕ) (fun y => g₂ t y v)) →
      (∀ v (r : ℕ) (I : DerivativeWord2 r), r ≤ K →
        orderedDerivative I (fun y => g₁ t y v) x = orderedDerivative I (fun y => g₂ t y v) x) →
      ∀ v : CompIn G.comps,
        covMeanAt Mn G G.level Mn.N Mn.p depth CcT g₁ v t x =
          covMeanAt Mn G G.level Mn.N Mn.p depth CcT g₂ v t x

/-- **The letters sum to the source mean, for a smooth field frozen in time**, at every time
and point, from `RootSourceBookkeepingStatement`, `TransferredIdentityEulerianOnStatement` and
`HilbertLiftPathSumStatement`. -/
def SourceMeanSmoothStatement : Prop :=
  RootSourceBookkeepingStatement → TransferredIdentityEulerianOnStatement →
    HilbertLiftPathSumStatement →
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT →
    ∀ (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v)) →
    ∀ (v : CompIn G.comps) (t : ℝ) (x : Vec 2),
      rootReadout P seedK freshK φ₀ G G' .plain G.level (D.eps (G.level - 1)) Mn.η0
            (fun _ => g) v t x -
          diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 (fun _ => g) v t x =
        covMeanAt Mn G G.level Mn.N Mn.p depth CcT (fun _ => g) v t x

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end

section
section
/-! **Source mean: the identity for smooth fields, and its three steps**.

For a smooth field `g` frozen in time, a functional `ℓ` on the space of the component `v` and the
witnesses `W` of the successor, both sides of the identity are compared with two scalar sums:

* `sourceSide`: the sum over the valid sources `s` other than the first source, with the empty
  word and the old target `v`, of the Eulerian operator `sourceEulerOp` of `s` applied to the scalar
  field `ℓ ∘ C_s ∘ g_{src s}`, `C_s` the ordered product of the maps of `s`;
* `pathSide`: the sum over the active pulses `k`, the grades `1 ≤ h ≤ depth`, the degrees
  `2 ≤ n ≤ N + Dm`, the paths `π` of `h` edges into `v` and the pairs `a, a' ≤ p` of the dressed
  terms `((-1)^a/(a! a'!)) 𝒞^a Ψ_{k*}(𝐄_n^{(π)}) 𝒞^{a'}` (`dressedPathTerm`) applied to
  `ℓ ∘ C_π ∘ g_{src π}`, with the path means of the lifts `W.Cc (copyQuad [] h π)` on the native
  family of `k` (`nativePathMean`).

Steps:
* `SourceMeanLeftStatement` (the root-bookkeeping and transfer steps, and the finite order of `sourceEulerOp`): the left side
  of the source mean, read through `ℓ`, is `sourceSide`;
* `SourceMeanRightStatement` (the Hilbert-lift path sum and the expansion
  `Q_p 𝐄 P_p = ∑_{a,a' ≤ p} (-1)^a 𝒞^a 𝐄 𝒞^{a'}/(a! a'!)`, linear over the glue): `covMeanAt`, read
  through `ℓ`, is `pathSide`;
* `SourceMeanMatchStatement` (the letters): `sourceSide = pathSide`. Degree `2` is `copyQuad`; a
  degree `3 ≤ n ≤ nMax` with `a = a' = 0` is `letterMean` plus, for a one-edge path, the direct part
  of order `n`, and the direct parts of the orders `3..Dm` are `copyDir`; `a + a' ≥ 1` is
  `letterCov` (the centred family map of the native chain and the flow chart differ by a
  translation, which commutes with `𝒞`); the degrees `nMax < n ≤ N + Dm` vanish (range condition
  on the degrees: `N + Dord ≤ nMax`, `2 ≤ Dord`); no path is longer than `min hMax depth` (range
  condition on the grades).

For a component `v` without incoming identity there is no source and no path, so both sums are
empty. For `p = 0` only `a = a' = 0` occurs, no covariance letter exists and `Q_0 = P_0 = id`.
At a time `t` with no active pulse `sourceEulerOp` and `pathSide` are empty sums. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- The label path mean of degree `n` of the path `π` on the native family of the pulse `k`, from
the lifts `Cc` (zero unless the native chain is admissible and `k` is odd, as in
`SuccSource.fluxOp`). -/
def nativePathMean (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {h : ℕ} (π : StagePath G h)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (k : ℤ) (t : ℝ) :
    (Vec 2 → ℝ) → Vec 2 → Vec 2 :=
  if hA : IsAdmissibleChain D b j₀ G.level k (nativeChain G.level k) ∧ Odd k then
    pathMeanFlux D G.level (Mn.lenFactor * liftLength D G.level)
      (familyLiftData D G.level k (nativeChain G.level k) (Mn.lenFactor * liftLength D G.level)
        (pathEdges G π ⟨k, hA.2⟩ ⟨nativeChain G.level k, hA.1⟩))
      (Cc k (nativeChain G.level k)) n t
  else fun _ _ => 0

/-- The dressed Eulerian term of one pulse:
`((-1)^a/(a! a'!)) 𝒞^a Ψ_{k*}(𝐄_n^{(π)}) 𝒞^{a'} φ` at `x`, with `Ψ_k` the natural chart of the pulse
`k` at the time `t` and `𝒞` the covariance operator of the menu's anchor. -/
def dressedPathTerm (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) {h : ℕ} (π : StagePath G h)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n a a' : ℕ) (k : ℤ)
    (t : ℝ) (φ : Vec 2 → ℝ) (x : Vec 2) : Vec 2 :=
  ((a.factorial * a'.factorial : ℝ)⁻¹ * (-1) ^ a) •
    (SuccSource.covAtFlux D G.level Mn.anchor t)^[a]
      (pushFlux (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level k))
        (fun x' => D.flowOf (G.level - 1) (D.slotAnchor G.level k) x' t)
        (nativePathMean Mn G π Cc n k t) ((SuccSource.covAt D G.level Mn.anchor t)^[a'] φ)) x

open scoped Classical in
/-- The sum over the sources: the valid sources other than the first source, with the empty word
and the old target `v`, each through its Eulerian operator on `ℓ ∘ C_s ∘ g_{src s}`. -/
def sourceSide {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑ᶠ s : SuccSource G,
    if hs : (s.Valid Mn.A Mn.J ∧ s.word = [] ∧ ¬ s.IsDiag) ∧ s.oldTgt = v.1 ∧
        s.oldSrc ∈ G.comps then
      sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor s (W.Cc s) t
        (fun y => ℓ (rootPathMap hr s.oldSrc.root s.maps v.1.root (g y ⟨s.oldSrc, hs.2.2⟩))) x
    else 0

open scoped Classical in
/-- The sum over the paths: the active pulses, the grades `1..depth`, the degrees `2..N + Dm`, the
paths into `v` and the pairs `a, a' ≤ p`, each through its dressed term on `ℓ ∘ C_π ∘ g_{src π}`,
with the lifts `W.Cc (copyQuad [] h π)`. -/
def pathSide {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') (depth : ℕ) (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑ k ∈ ocObsPulses D.α D.q D.Λ G.level t t, ocCutoff D.α D.q D.Λ G.level k t •
    ∑ h ∈ Finset.Icc 1 depth, ∑ n ∈ Finset.Icc 2 (Mn.N + Dm),
      ∑ᶠ π : StagePath G h, if hπ : π.tgt = v.1 ∧ π.src ∈ G.comps then
        ∑ a ∈ Finset.range (Mn.p + 1), ∑ a' ∈ Finset.range (Mn.p + 1),
          dressedPathTerm Mn G π (W.Cc (SuccSource.copyQuad [] h π)) n a a' k t
            (fun y => ℓ (rootPathMap hr π.src.root π.mapList v.1.root (g y ⟨π.src, hπ.2⟩))) x
      else 0

/-- **Left step**: the non-diagonal part of the plain flux out of the roots, read through `ℓ`, is
the sum over the sources. -/
def SourceMeanLeftStatement : Prop :=
  RootSourceBookkeepingStatement → TransferredIdentityEulerianOnStatement →
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT → ∀ (W : SplitWitness P Mn G G')
      (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v)) →
    ∀ (v : CompIn G.comps) (t : ℝ) (x : Vec 2) (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2),
      ℓ ((rootReadout P seedK freshK φ₀ G G' .plain G.level (D.eps (G.level - 1)) Mn.η0
            (fun _ => g) v t x -
          diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 (fun _ => g) v t x) j) =
        sourceSide W g v ℓ t x j

/-- **Right step**: `Q_p 𝐄^flux P_p g`, read through `ℓ`, is the sum over the paths. -/
def SourceMeanRightStatement : Prop :=
  HilbertLiftPathSumStatement →
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT → ∀ (W : SplitWitness P Mn G G')
      (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v)) →
    ∀ (v : CompIn G.comps) (t : ℝ) (x : Vec 2) (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2),
      ℓ ((covMeanAt Mn G G.level Mn.N Mn.p depth CcT (fun _ => g) v t x) j) =
        pathSide W depth g v ℓ t x j

/-- **Matching step (the letters)**: the sum over the sources is the sum over the paths. -/
def SourceMeanMatchStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)),
    SplitInput P Mn G G' depth CcT → ∀ (W : SplitWitness P Mn G G')
      (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root),
      (∀ v, ContDiff ℝ (⊤ : ℕ∞) (fun y => g y v)) →
    ∀ (v : CompIn G.comps) (t : ℝ) (x : Vec 2) (ℓ : hr v.1.root →L[ℝ] ℝ),
      sourceSide W g v ℓ t x = pathSide W depth g v ℓ t x

/-- **The identity for smooth fields from its three steps.** -/
theorem sourceMeanSmooth_of_steps (hL : SourceMeanLeftStatement) (hR : SourceMeanRightStatement)
    (hM : SourceMeanMatchStatement) : SourceMeanSmoothStatement := by
  intro h1 h4 h5 hr _ _ _ _ _ _ D Dm b j₀ P seedK freshK φ₀ Mn G G' depth CcT hin g hg v t x
  obtain ⟨W⟩ := splitWitness_nonempty hin.successor
  rw [← sub_eq_zero]
  ext j
  refine ext_inner_left ℝ fun w => ?_
  have e1 := hL h1 h4 P seedK freshK φ₀ Mn G G' depth CcT hin W g hg v t x (innerSL ℝ w) j
  have e2 := hR h5 P Mn G G' depth CcT hin W g hg v t x (innerSL ℝ w) j
  have e3 := hM P Mn G G' depth CcT hin W g hg v t x (innerSL ℝ w)
  rw [e3] at e1
  have e4 := e1.trans e2.symm
  simp only [innerSL_apply_apply, PiLp.sub_apply, inner_sub_right] at e4
  simp only [PiLp.sub_apply, PiLp.zero_apply, inner_sub_right, inner_zero_right, sub_eq_zero]
  exact e4

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Source mean, the Left step: the steps of its proof**.

`SourceMeanLeftStatement` (the tested difference of the plain and the diagonal readouts is the sum
over the sources) is assembled from three steps, each a parametrized proposition:

* `SmlReadoutStep`: the difference of the readouts is the sum, over the triples `(v', u', γ')`, of
  the cells `smlCell` (rows of `v` in the readout, roots `u'`, identities whose provenance is not
  the first source), read through `ℓ` and the component `j`;
* `SmlTermStep`: a cell is, for the source `s = W.e v' u' γ'`, the source term `smlSrc s`
  (by the source identities of the stage and the finite order of the Eulerian operator of `s`),
  or zero;
* `SmlReindexStep`: the sum over the triples of the source terms is the `finsum` over the valid
  sources with the empty word, the old target `v` and the old source in the stage (the
  reindexing by `W.e`), and the set of these sources is finite.

If no pulse is active at `t` both sides vanish. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The flux of the identity `γ'` out of the root `u'` into the row `v'`, on the field `g` frozen
in time: `∑_d 𝖡_{γ',d} ∇^{d-1} g_{u'}`. -/
def smlPhys (G G' : GenStage D hr Dm b j₀) (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v' u' : CompIn G'.comps) (hu : u'.1 ∈ G.comps) (γ' : G'.fam.Γ v' u') (t : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => hr v'.1.root) :=
  ∑ d : Finset.Icc 2 Dm,
    G'.physCoeff v' u' γ' d.1 t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      orderedDerivative word (fun y => g y ⟨u'.1, hu⟩) x)

/-- The equality of the roots used by the cast of `readoutFlux`. -/
theorem smlRoot_eq (G : Finset Comp) (m : ℕ) (v' : CompIn G) (v : Comp)
    (h : compParent m v'.1 = v) : v'.1.root = v.root :=
  (compParent_root m v'.1).symm.trans (congrArg Comp.root h)

open scoped Classical in
/-- **A cell of the left side**: the row `v'` of the readout (`compParent = v`), the root `u'` in
the stage, an identity `γ'` whose provenance is not the first source; the flux of the identity
weighted by `E^{η₀|word|}`, cast to the space of `v`, read through `ℓ` at the component `j`. -/
def smlCell (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2) (t : ℝ) (x : Vec 2)
    (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u') : ℝ :=
  if h : compParent G.level v'.1 = v.1 then
    if hu : u'.1 ∈ G.comps then
      if G'.prov v' u' γ' = Prov.letter G.level WordLetter.diag [] then 0
      else
        D.eps (G.level - 1) ^ (Mn.η0 * ((compWord G.level v'.1).length : ℝ)) *
          ℓ ((cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r))
            (smlRoot_eq G'.comps G.level v' v.1 h)) (smlPhys G G' g v' u' hu γ' t x)) j)
    else 0
  else 0

open scoped Classical in
/-- **A term of the right side**: the Eulerian operator of the source `s` on the scalar field
`ℓ ∘ C_s ∘ g_{src s}`, at the component `j`. -/
def smlSrc {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2) (t : ℝ) (x : Vec 2)
    (s : SuccSource G) : ℝ :=
  if hs : s.oldSrc ∈ G.comps then
    sourceEulerOp (Mn.lenFactor * liftLength D G.level) Mn.anchor s (W.Cc s) t
      (fun y => ℓ (rootPathMap hr s.oldSrc.root s.maps v.1.root (g y ⟨s.oldSrc, hs⟩))) x j
  else 0

/-- The sources summed on the right side. -/
def SmlSrcSet {G : GenStage D hr Dm b j₀} {Mn : SuccMenu} (v : CompIn G.comps)
    (s : SuccSource G) : Prop :=
  (s.Valid Mn.A Mn.J ∧ s.word = [] ∧ ¬ s.IsDiag) ∧ s.oldTgt = v.1 ∧ s.oldSrc ∈ G.comps

/-- **Step 1**: the difference of the readouts, read through `ℓ` and `j`, is the sum of the
cells. -/
def SmlReadoutStep (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2) (t : ℝ) (x : Vec 2) : Prop :=
  ℓ ((rootReadout P seedK freshK φ₀ G G' .plain G.level (D.eps (G.level - 1)) Mn.η0
        (fun _ => g) v t x -
      diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 (fun _ => g) v t x) j) =
    ∑ v' : CompIn G'.comps, ∑ u' : CompIn G'.comps, ∑ γ' : G'.fam.Γ v' u',
      smlCell Mn G G' g v ℓ j t x v' u' γ'

open scoped Classical in
/-- **Step 2**: a cell is the source term of its source (by the source identities of the stage and the
finite order of the Eulerian operator), when the row is a parent of `v`, the root is in the stage and the source
is not the first source; and zero otherwise. -/
def SmlTermStep (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (W : SplitWitness P Mn G G') (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v : CompIn G.comps) (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2) (t : ℝ) (x : Vec 2) : Prop :=
  ∀ (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u'),
    smlCell Mn G G' g v ℓ j t x v' u' γ' =
      if compParent G.level v'.1 = v.1 ∧ u'.1 ∈ G.comps ∧ ¬ (W.e v' u' γ').1.IsDiag then
        smlSrc W g v ℓ j t x (W.e v' u' γ').1
      else 0

open scoped Classical in
/-- **Step 3**: the reindexing of the sum over the triples by the source. -/
def SmlReindexStep (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (W : SplitWitness P Mn G G') (v : CompIn G.comps) : Prop :=
  {s : SuccSource G | SmlSrcSet (Mn := Mn) v s}.Finite ∧
  ∀ F : SuccSource G → ℝ,
    ∑ v' : CompIn G'.comps, ∑ u' : CompIn G'.comps, ∑ γ' : G'.fam.Γ v' u',
      (if compParent G.level v'.1 = v.1 ∧ u'.1 ∈ G.comps ∧ ¬ (W.e v' u' γ').1.IsDiag then
        F (W.e v' u' γ').1 else 0) =
    ∑ᶠ s : SuccSource G, if SmlSrcSet (Mn := Mn) v s then F s else 0

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
open scoped Classical in
/-- **The assembly**: the three steps give the left side of the source mean. -/
theorem sml_assembly (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀) (W : SplitWitness P Mn G G')
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2) (t : ℝ) (x : Vec 2)
    (h1 : SmlReadoutStep P seedK freshK φ₀ Mn G G' g v ℓ j t x)
    (h2 : SmlTermStep P Mn G G' W g v ℓ j t x) (h3 : SmlReindexStep P Mn G G' W v) :
    ℓ ((rootReadout P seedK freshK φ₀ G G' .plain G.level (D.eps (G.level - 1)) Mn.η0
          (fun _ => g) v t x -
        diagReadout G G' G.level (D.eps (G.level - 1)) Mn.η0 (fun _ => g) v t x) j) =
      sourceSide W g v ℓ t x j := by
  rw [h1]
  unfold SmlTermStep at h2
  simp only [h2]
  rw [h3.2 (smlSrc W g v ℓ j t x)]
  unfold sourceSide
  rw [finsum_apply (h3.1.subset fun s hs => by
    by_contra hn
    have hn' : ¬ ((s.Valid Mn.A Mn.J ∧ s.word = [] ∧ ¬ s.IsDiag) ∧ s.oldTgt = v.1 ∧
        s.oldSrc ∈ G.comps) := hn
    exact hs (by simp only [hn', ↓reduceDIte]))]
  refine finsum_congr fun s => ?_
  by_cases hP : SmlSrcSet (Mn := Mn) v s
  · have hP' : ((s.Valid Mn.A Mn.J ∧ s.word = [] ∧ ¬ s.IsDiag) ∧ s.oldTgt = v.1 ∧
        s.oldSrc ∈ G.comps) := hP
    rw [ite_eq_left hP]
    unfold smlSrc
    rw [dite_eq_left hP.2.2, dite_eq_left hP']
  · have hP' : ¬ ((s.Valid Mn.A Mn.J ∧ s.word = [] ∧ ¬ s.IsDiag) ∧ s.oldTgt = v.1 ∧
        s.oldSrc ∈ G.comps) := hP
    simp only [hP, hP', ↓reduceIte, ↓reduceDIte]
    rfl

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **The jets of a `C^K` function at a point are those of a polynomial** (step (T) of
the source-mean step): `smoothJetRealization : SmoothJetRealizationStatement`.

The polynomial is the Taylor polynomial on words,
`T y = ∑_{r ≤ K} (1/r!) ∑_{I : words of length r} ∏_j (y - x)_{I j} • ∂^I f(x)`. At the centre the
ordered derivative `∂^J` of the monomial of the word `I` vanishes unless the lengths agree and then
counts the permutations `σ` with `J = I ∘ σ` (`orderedDerivative_mono_self`,
`orderedDerivative_mono_of_ne`); the ordered derivatives of `f` of order `s ≤ K` are symmetric in
the word (`orderedDerivative_comp_perm_of_contDiff`), so the `s!` permutations give `∂^J f(x)`.

For `K = 0` the polynomial `T` is the constant `f x`, and if `f` is a polynomial of degree
`≤ K` then `T = f`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open Providers.GenSem

/-- **Step (T) of the source-mean step.** -/
theorem smoothJetRealization : SmoothJetRealizationStatement := by
  intro E _ _ K f hf x
  classical
  let L : ∀ r : ℕ, DerivativeWord2 r → ℝ →L[ℝ] E := fun r I =>
    (r.factorial : ℝ)⁻¹ • ContinuousLinearMap.toSpanSingleton ℝ (orderedDerivative I f x)
  let β : ℕ → Vec 2 → E := fun r y => ∑ I : DerivativeWord2 r, L r I (mono x I y)
  have hmono : ∀ {r : ℕ} (I : DerivativeWord2 r) (n : ℕ∞), ContDiff ℝ n (mono x I) :=
    fun I n => (contDiff_mono x I).of_le (by exact_mod_cast le_top)
  have hβ : ∀ (r : ℕ) (n : ℕ∞), ContDiff ℝ n (β r) := fun r n =>
    ContDiff.sum fun I _ => (L r I).contDiff.comp (hmono I n)
  refine ⟨fun y => ∑ r ∈ Finset.range (K + 1), β r y, ContDiff.sum fun r _ => hβ r _, ?_⟩
  intro s J hs
  have h1 : orderedDerivative J (fun y => ∑ r ∈ Finset.range (K + 1), β r y) x =
      ∑ r ∈ Finset.range (K + 1), orderedDerivative J (β r) x := by
    have h := Providers.PathDecomp.orderedDerivative_clm_sum (Finset.range (K + 1))
      (fun _ => ContinuousLinearMap.id ℝ E) J (β := β) (fun r _ => hβ r _)
    simpa using congrFun h x
  have h2 : ∀ r : ℕ, orderedDerivative J (β r) x =
      ∑ I : DerivativeWord2 r, L r I (orderedDerivative J (mono x I) x) := by
    intro r
    have h := Providers.PathDecomp.orderedDerivative_clm_sum Finset.univ (L r) J
      (β := fun I => mono x I) (fun I _ => hmono I _)
    exact congrFun h x
  rw [h1, Finset.sum_eq_single s]
  · rw [h2]
    have hfs : ContDiff ℝ (s : ℕ∞) f := hf.of_le (by exact_mod_cast hs)
    have hterm : ∀ I : DerivativeWord2 s, L s I (orderedDerivative J (mono x I) x) =
        (s.factorial : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin s),
          (if (∀ j, J j = I (σ j)) then orderedDerivative I f x else 0) := by
      intro I
      rw [orderedDerivative_mono_self]
      simp only [L, FunLike.coe_smul, Pi.smul_apply,
        ContinuousLinearMap.toSpanSingleton_apply, Finset.sum_smul, ite_smul, one_smul, zero_smul]
    simp only [hterm]
    rw [← Finset.smul_sum, Finset.sum_comm]
    have hσ : ∀ σ : Equiv.Perm (Fin s), ∑ I : DerivativeWord2 s,
        (if (∀ j, J j = I (σ j)) then orderedDerivative I f x else 0) =
          orderedDerivative J f x := by
      intro σ
      rw [Finset.sum_eq_single (J ∘ σ.symm)]
      · have hc : ∀ j, J j = (J ∘ σ.symm) (σ j) := fun j => by simp
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
        exact CycleComparison.Reconstruction.orderedDerivative_comp_perm_of_contDiff J σ.symm
          hfs x
      · intro I _ hI
        refine ite_eq_right_of_eq_false _ _ (eq_false fun h => hI ?_)
        funext j
        have hj := h (σ.symm j)
        simp only [Equiv.apply_symm_apply] at hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ _) h
    simp only [hσ]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_pos s).ne'), one_smul]
  · intro r _ hr
    rw [h2]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [orderedDerivative_mono_of_ne x I J (fun h => hr h.symm), map_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Source mean, Left: the difference of the readouts is the sum of the cells**.

`sml_readoutStep`: `SmlReadoutStep`. The plain flux out of the roots minus the flux of the first
source is the flux of the identities whose provenance is not the first source
(`sml_flux_diff`); the cast of `readoutFlux`, the weight, `ℓ` and the component `j` are additive
(`smlRead`), hence commute with the finite sums. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The cast along an equality of roots is additive. -/
theorem sml_cast_add {r r' : ℕ} (h : r = r') (a b : PiLp 2 (fun _ : Fin 2 => hr r)) :
    cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) h) (a + b) =
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) h) a +
        cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) h) b := by
  subst h
  rfl

omit [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] in
/-- The cast along an equality of roots acts componentwise as the cast of the space. -/
theorem sml_cast_apply {r r' : ℕ} (h : r = r') (a : PiLp 2 (fun _ : Fin 2 => hr r)) (j : Fin 2) :
    (cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) h) a) j =
      cast (congrArg hr h) (a j) := by
  subst h
  rfl

/-- The reading `z ↦ c · ℓ ((cast z) j)` of a vector field of the space of the row `v'` in the
space of `v`, as an additive map. -/
def smlRead {r r' : ℕ} (h : r = r') (c : ℝ) (ℓ : hr r' →L[ℝ] ℝ) (j : Fin 2) :
    PiLp 2 (fun _ : Fin 2 => hr r) →+ ℝ :=
  AddMonoidHom.mk'
    (fun z => c * ℓ ((cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) h) z) j))
    (fun a b => by
      rw [sml_cast_add h, WithLp.ofLp_add, Pi.add_apply, map_add, mul_add])

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem smlRead_apply {r r' : ℕ} (h : r = r') (c : ℝ) (ℓ : hr r' →L[ℝ] ℝ) (j : Fin 2)
    (z : PiLp 2 (fun _ : Fin 2 => hr r)) :
    smlRead h c ℓ j z =
      c * ℓ ((cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) h) z) j) := rfl

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The reading of a weighted cast vector. -/
theorem sml_weight_read {r r' : ℕ} (h : r = r') (c : ℝ) (ℓ : hr r' →L[ℝ] ℝ) (j : Fin 2)
    (z : PiLp 2 (fun _ : Fin 2 => hr r)) :
    ℓ (((c • cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) h) z :
      PiLp 2 (fun _ : Fin 2 => hr r')) j)) = smlRead h c ℓ j z := by
  rw [smlRead_apply, WithLp.ofLp_smul, Pi.smul_apply, map_smul, smul_eq_mul]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
open scoped Classical in
/-- **The flux out of the roots minus the flux of the first source** is the flux of the other
identities. -/
theorem sml_flux_diff (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (G G' : GenStage D hr Dm b j₀) (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (v' : CompIn G'.comps) (t : ℝ) (x : Vec 2) :
    rootFluxOn P seedK freshK φ₀ G G' .plain (fun _ => g) v' t x -
        rootDiagFlux G G' (fun _ => g) v' t x =
      ∑ u' : CompIn G'.comps, if hu : u'.1 ∈ G.comps then
        ∑ γ' : G'.fam.Γ v' u',
          if G'.prov v' u' γ' = Prov.letter G.level WordLetter.diag [] then 0
          else smlPhys G G' g v' u' hu γ' t x
      else 0 := by
  unfold rootFluxOn rootDiagFlux
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u' _ => ?_
  by_cases hu : u'.1 ∈ G.comps
  · simp only [hu, dite_true, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun γ' _ => ?_
    by_cases hp : G'.prov v' u' γ' = Prov.letter G.level WordLetter.diag []
    · simp [hp]
    · simp only [hp, ite_false, sub_zero, smlPhys]
  · simp [hu]

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
open scoped Classical in
/-- **Step 1 of the Left side**: the difference of the readouts is the sum of the cells. -/
theorem sml_readoutStep (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ)
    (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀)
    (g : Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (v : CompIn G.comps)
    (ℓ : hr v.1.root →L[ℝ] ℝ) (j : Fin 2) (t : ℝ) (x : Vec 2) :
    SmlReadoutStep P seedK freshK φ₀ Mn G G' g v ℓ j t x := by
  unfold SmlReadoutStep rootReadout diagReadout readoutFlux
  rw [← Finset.sum_sub_distrib]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : compParent G.level v'.1 = v.1
  · have hc : compParent G.level v'.1 = v.1 ∧ True := ⟨h, trivial⟩
    rw [dite_eq_left hc, dite_eq_left hc]
    have hh := smlRoot_eq G'.comps G.level v' v.1 h
    rw [WithLp.ofLp_sub, Pi.sub_apply, map_sub, sml_weight_read hh, sml_weight_read hh,
      ← map_sub, sml_flux_diff, map_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    by_cases hu : u'.1 ∈ G.comps
    · rw [dite_eq_left hu, map_sum]
      refine Finset.sum_congr rfl fun γ' _ => ?_
      by_cases hp : G'.prov v' u' γ' = Prov.letter G.level WordLetter.diag []
      · simp [smlCell, h, hu, hp]
      · simp only [smlCell, h, hu, hp, dite_true, ite_false, smlRead_apply]
    · simp [smlCell, h, hu]
  · have hc : ¬ (compParent G.level v'.1 = v.1 ∧ True) := fun hh => h hh.1
    rw [dite_eq_right hc, dite_eq_right hc]
    simp [smlCell, h]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end

section
/-! **Source mean, Left: the reindexing of the identities by their sources**.

`sml_reindexStep`: `SmlReindexStep`. The map `(v', u', γ') ↦ (W.e v' u' γ').1` is injective (the
source determines its target and source components, and `W.e v' u'` is an equivalence); by the root-source bookkeeping
(ii) its values on the triples with `compParent = v`, root in the stage and not the first source are
sources of `SmlSrcSet`, and by the root-source bookkeeping (iii) every source of `SmlSrcSet` is a value of such a
triple. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The source of an identity is injective on the triples. -/
theorem sml_source_injective {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (W : SplitWitness P Mn G G') :
    Function.Injective (fun x : (Σ v' u' : CompIn G'.comps, G'.fam.Γ v' u') =>
      (W.e x.1 x.2.1 x.2.2).1) := by
  rintro ⟨v₁, u₁, γ₁⟩ ⟨v₂, u₂, γ₂⟩ h
  have h1 := (W.e v₁ u₁ γ₁).2.2.1
  have h2 := (W.e v₁ u₁ γ₁).2.2.2
  have h3 := (W.e v₂ u₂ γ₂).2.2.1
  have h4 := (W.e v₂ u₂ γ₂).2.2.2
  simp only at h
  rw [h] at h1 h2
  have hu : u₁ = u₂ := Subtype.ext (h1.symm.trans h3)
  have hv : v₁ = v₂ := Subtype.ext (h2.symm.trans h4)
  subst hu hv
  have : γ₁ = γ₂ := (W.e v₁ u₁).injective (Subtype.ext h)
  subst this
  rfl

open scoped Classical in
/-- **Step 3 of the Left side**: the reindexing of the sum over the identities by their
sources. -/
theorem sml_reindexStep (hbk : RootSourceBookkeepingStatement) (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) (hs : StageSuccessor.Input P Mn G)
    (hsucc : IsActualSuccessor D P Mn G G') (W : SplitWitness P Mn G G') (v : CompIn G.comps) :
    SmlReindexStep P Mn G G' W v := by
  obtain ⟨-, hii, hiii⟩ := hbk P Mn G G' hs hsucc W
  let Φ : (Σ v' u' : CompIn G'.comps, G'.fam.Γ v' u') → SuccSource G :=
    fun x => (W.e x.1 x.2.1 x.2.2).1
  let C : (Σ v' u' : CompIn G'.comps, G'.fam.Γ v' u') → Prop := fun x =>
    compParent G.level x.1.1 = v.1 ∧ x.2.1.1 ∈ G.comps ∧ ¬ (Φ x).IsDiag
  have hinj : Function.Injective Φ := sml_source_injective W
  have hCS : ∀ x, C x → SmlSrcSet (Mn := Mn) v (Φ x) := by
    rintro ⟨v', u', γ'⟩ ⟨h1, h2, h3⟩
    obtain ⟨hw, hsrc, htg, hpar, -, -, -⟩ := hii v' u' γ' h2
    exact ⟨⟨(W.e v' u' γ').2.1, hw, h3⟩, hpar.symm.trans h1 ▸ rfl, hsrc ▸ h2⟩
  have hSC : ∀ s, SmlSrcSet (Mn := Mn) v s → ∃ x, C x ∧ Φ x = s := by
    intro s hS
    obtain ⟨v', u', γ', he, hu⟩ := hiii s hS.1.1 hS.1.2.1
    refine ⟨⟨v', u', γ'⟩, ⟨?_, hu, ?_⟩, he⟩
    · obtain ⟨-, hsrc, -, hpar, -⟩ := hii v' u' γ' hu
      have : (W.e v' u' γ').1 = s := he
      rw [hpar, this]
      exact hS.2.1
    · show ¬ (W.e v' u' γ').1.IsDiag
      rw [he]
      exact hS.1.2.2
  have hnest : ∀ f : (Σ v' u' : CompIn G'.comps, G'.fam.Γ v' u') → ℝ,
      ∑ v', ∑ u', ∑ γ', f ⟨v', u', γ'⟩ = ∑ x, f x := by
    intro f
    simp only [Fintype.sum_sigma]
  have hfin : {s : SuccSource G | SmlSrcSet (Mn := Mn) v s}.Finite := by
    refine ((Finset.univ.image Φ).finite_toSet).subset fun s hS => ?_
    obtain ⟨x, -, hx⟩ := hSC s hS
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩)
  refine ⟨hfin, fun F => ?_⟩
  rw [hnest (fun x => if compParent G.level x.1.1 = v.1 ∧ x.2.1.1 ∈ G.comps ∧
      ¬ (W.e x.1 x.2.1 x.2.2).1.IsDiag then F (W.e x.1 x.2.1 x.2.2).1 else 0)]
  have hsub : (Function.support fun s => if SmlSrcSet (Mn := Mn) v s then F s else 0) ⊆
      ↑((Finset.univ.filter C).image Φ) := by
    intro s hs'
    have hS : SmlSrcSet (Mn := Mn) v s := by
      by_contra hn
      exact hs' (by simp [hn])
    obtain ⟨x, hx, hxs⟩ := hSC s hS
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, hxs⟩)
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_image (fun x _ y _ h => hinj h),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : C x
  · have hx1 := hCS x hx
    have hx2 : compParent G.level x.1.1 = v.1 ∧ x.2.1.1 ∈ G.comps ∧
      ¬ (W.e x.1 x.2.1 x.2.2).1.IsDiag := hx
    rw [ite_eq_left hx1, ite_eq_left hx2]
  · have hx2 : ¬ (compParent G.level x.1.1 = v.1 ∧ x.2.1.1 ∈ G.comps ∧
      ¬ (W.e x.1 x.2.1 x.2.2).1.IsDiag) := hx
    rw [ite_eq_right hx2, ite_eq_right hx2]

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end
end
end
