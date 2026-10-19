-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Statements.Roots.IsZ2Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral

@[expose] public section
noncomputable section

section
open MeasureTheory Filter Topology Metric
namespace AVRegularity.Providers.KernelSup

/-! Calculus of a linear kernel average `Op K M W x = ∫ K(ζ) • W(x - Mζ) dζ`.

For a smooth compactly supported kernel `K` on a finite-dimensional space `E` carrying an additive
Haar measure, a continuous linear map `M : E → F` with a right inverse `R`, and a bounded
measurable `W`:
* `‖Op K M W x‖ ≤ (∫‖K‖) B` when `‖W‖ ≤ B`;
* (kernel side) `∂_e Op K M W = Op (D_{Re}K) M W`, from the translation identity
  `Op K M W (x + Mc) = ∫ K(ζ + c) • W(x - Mζ)`;
* (field side) `∂_e Op K M W = Op K M (∂_e W)` for `W ∈ C¹` with bounded derivative. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The directional derivative `D_v K`. -/
def dirD {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (v : X) (K : X → Y) : X → Y := fun ζ => fderiv ℝ K ζ v

/-- A smooth compactly supported kernel. -/
structure IsKer (K : E → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) K
  cpt : HasCompactSupport K

theorem IsKer.dir {K : E → ℝ} (hK : IsKer K) (v : E) : IsKer (dirD v K) :=
  ⟨(hK.smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const,
    hK.cpt.fderiv_apply (𝕜 := ℝ) v⟩

theorem IsKer.iterate_dirD {K : E → ℝ} (hK : IsKer K) (v : E) :
    ∀ n, IsKer ((dirD v)^[n] K)
  | 0 => hK
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact (hK.iterate_dirD v n).dir v

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- The kernel average. -/
def Op (μ : Measure E) (K : E → ℝ) (M : E →L[ℝ] F) (W : F → H) (x : F) : H :=
  ∫ ζ, K ζ • W (x - M ζ) ∂μ


theorem IsKer.integrable [IsFiniteMeasureOnCompacts μ] {K : E → ℝ} (hK : IsKer K) :
    Integrable K μ :=
  hK.smooth.continuous.integrable_of_hasCompactSupport hK.cpt

/-- The integrand is integrable for bounded measurable `W`. -/
theorem integrable_op [SecondCountableTopology E] [IsFiniteMeasureOnCompacts μ] {K : E → ℝ} (hK : IsKer K) (M : E →L[ℝ] F) {W : F → H}
    (hW : Continuous W) {B : ℝ} (hB : ∀ y, ‖W y‖ ≤ B) (x : F) :
    Integrable (fun ζ => K ζ • W (x - M ζ)) μ := by
  refine Integrable.mono' ((hK.integrable (μ := μ)).norm.mul_const B) ?_ ?_
  · exact (hK.smooth.continuous.smul (hW.comp (continuous_const.sub M.continuous))).aestronglyMeasurable
  · exact Eventually.of_forall fun ζ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)

/-- **Bound.** `‖Op K M W x‖ ≤ (∫‖K‖) B`. -/
theorem norm_op_le [SecondCountableTopology E] [IsFiniteMeasureOnCompacts μ] {K : E → ℝ} (hK : IsKer K) (M : E →L[ℝ] F) {W : F → H}
    {B : ℝ} (hB : ∀ y, ‖W y‖ ≤ B) (x : F) :
    ‖Op μ K M W x‖ ≤ (∫ ζ, ‖K ζ‖ ∂μ) * B := by
  unfold Op
  calc ‖∫ ζ, K ζ • W (x - M ζ) ∂μ‖ ≤ ∫ ζ, ‖K ζ‖ * B ∂μ := by
        refine norm_integral_le_of_norm_le ((hK.integrable (μ := μ)).norm.mul_const B) ?_
        exact Eventually.of_forall fun ζ => by
          rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    _ = (∫ ζ, ‖K ζ‖ ∂μ) * B := integral_mul_const B _

/-- **Translation identity.** -/
theorem op_add_apply [μ.IsAddRightInvariant] (K : E → ℝ) (M : E →L[ℝ] F) (W : F → H) (x : F) (c : E) :
    Op μ K M W (x + M c) = ∫ ζ, K (ζ + c) • W (x - M ζ) ∂μ := by
  unfold Op
  rw [← integral_add_right_eq_self (μ := μ) (fun ζ => K ζ • W (x + M c - M ζ)) c]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  simp only [map_add]
  congr 2
  abel

/-- The kernel-side parametric integral is differentiable at `0`. -/
theorem hasFDerivAt_shift [SecondCountableTopology E] [CompleteSpace H] [IsFiniteMeasureOnCompacts μ] [ProperSpace E]
    {K : E → ℝ} (hK : IsKer K) (M : E →L[ℝ] F) {W : F → H}
    (hW : Continuous W) {B : ℝ} (hB : ∀ y, ‖W y‖ ≤ B) (x : F) :
    HasFDerivAt (fun c : E => ∫ ζ, K (ζ + c) • W (x - M ζ) ∂μ)
      (∫ ζ, (fderiv ℝ K ζ).smulRight (W (x - M ζ)) ∂μ) 0 := by
  have hK1 : ContDiff ℝ 1 K := hK.smooth.of_le (by exact_mod_cast le_top)
  have hdK : Continuous (fderiv ℝ K) := hK1.continuous_fderiv (by norm_num)
  have hcdK : HasCompactSupport (fderiv ℝ K) := hK.cpt.fderiv (𝕜 := ℝ)
  obtain ⟨Cd, hCd⟩ := hdK.bounded_above_of_compact_support hcdK
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, tsupport K ⊆ closedBall 0 R₀ :=
    hK.cpt.isCompact.isBounded.subset_closedBall 0
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set bound : E → ℝ := (closedBall (0 : E) (R₀ + 1)).indicator fun _ => Cd * B
  have hbound_int : Integrable bound μ := by
    have hfin : μ (closedBall (0 : E) (R₀ + 1)) < ⊤ := (isCompact_closedBall _ _).measure_lt_top
    exact (integrableOn_const (C := Cd * B) hfin.ne).integrable_indicator measurableSet_closedBall
  suffices hs : HasFDerivAt (fun c : E => ∫ ζ, K (ζ + c) • W (x - M ζ) ∂μ)
      (∫ ζ, (fderiv ℝ K (ζ + 0)).smulRight (W (x - M ζ)) ∂μ) 0 by simpa using hs
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ)
    (F := fun c ζ => K (ζ + c) • W (x - M ζ))
    (F' := fun c ζ => (fderiv ℝ K (ζ + c)).smulRight (W (x - M ζ)))
    (ball_mem_nhds (0 : E) one_pos)
    (Eventually.of_forall fun c => ?_) ?_ ?_ ?_ ?_ ?_ (bound := bound)
  · exact ((hK.smooth.continuous.comp (continuous_id.add continuous_const)).smul
      (hW.comp (continuous_const.sub M.continuous))).aestronglyMeasurable
  · simpa using integrable_op hK M hW hB x
  · exact ((ContinuousLinearMap.smulRightL ℝ E H).continuous₂.comp
      ((hdK.comp (continuous_id.add continuous_const)).prodMk
        (hW.comp (continuous_const.sub M.continuous)))).aestronglyMeasurable
  · refine Eventually.of_forall fun ζ c hc => ?_
    by_cases hz : ζ + c ∈ tsupport K
    · have hmem : ζ ∈ closedBall (0 : E) (R₀ + 1) := by
        have h1 := hR₀ hz
        rw [mem_closedBall, dist_zero_right] at h1 ⊢
        have h2 : ‖c‖ < 1 := by simpa using hc
        calc ‖ζ‖ = ‖(ζ + c) - c‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖ζ + c‖ + ‖c‖ := norm_sub_le _ _
          _ ≤ R₀ + 1 := by linarith
      simp only [bound, Set.indicator_of_mem hmem]
      calc ‖(fderiv ℝ K (ζ + c)).smulRight (W (x - M ζ))‖
          ≤ ‖fderiv ℝ K (ζ + c)‖ * ‖W (x - M ζ)‖ := (ContinuousLinearMap.norm_smulRight_apply _ _).le
        _ ≤ Cd * B := mul_le_mul (hCd _) (hB _) (norm_nonneg _)
            ((norm_nonneg _).trans (hCd 0))
    · have h0 : fderiv ℝ K (ζ + c) = 0 := by
        have : ζ + c ∉ tsupport (fderiv ℝ K) := fun h => hz (tsupport_fderiv_subset ℝ h)
        exact image_eq_zero_of_notMem_tsupport this
      rw [h0, ContinuousLinearMap.zero_smulRight, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hCd 0)) hB0) _
  · exact hbound_int
  · refine Eventually.of_forall fun ζ c _ => ?_
    have hd : HasFDerivAt (fun c' => K (ζ + c')) (fderiv ℝ K (ζ + c)) c := by
      have := (hK1.differentiable (by norm_num) (ζ + c)).hasFDerivAt
      have h2 : HasFDerivAt (fun c' => K (ζ + c'))
          ((fderiv ℝ K (ζ + c)).comp (ContinuousLinearMap.id ℝ E)) c :=
        this.comp c ((hasFDerivAt_id c).const_add ζ)
      rwa [ContinuousLinearMap.comp_id] at h2
    exact hd.smul_const (W (x - M ζ))

/-- **Kernel-side derivative.** If `M ∘ R = id`, then `∂_e Op K M W = Op (D_{Re}K) M W`. -/
theorem fderiv_op_kernel [SecondCountableTopology E] [CompleteSpace H] [IsFiniteMeasureOnCompacts μ] [ProperSpace E]
    [μ.IsAddRightInvariant] {K : E → ℝ} (hK : IsKer K) (M : E →L[ℝ] F) (R : F →L[ℝ] E)
    (hMR : ∀ y, M (R y) = y) {W : F → H} (hW : Continuous W) {B : ℝ}
    (hB : ∀ y, ‖W y‖ ≤ B) (x e : F) :
    fderiv ℝ (Op μ K M W) x e = Op μ (dirD (R e) K) M W x := by
  set Θ : E → H := fun c => ∫ ζ, K (ζ + c) • W (x - M ζ) ∂μ with hΘdef
  have hrep : Op μ K M W = fun y => Θ (R (y - x)) := by
    funext y
    show _ = ∫ ζ, K (ζ + R (y - x)) • W (x - M ζ) ∂μ
    rw [← op_add_apply, hMR, add_sub_cancel]
  have hR : HasFDerivAt (fun y => R (y - x)) R x := by
    have h := R.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)
    rwa [ContinuousLinearMap.comp_id] at h
  have h0 : R (x - x) = 0 := by simp
  have hΘ : HasFDerivAt Θ (∫ ζ, (fderiv ℝ K ζ).smulRight (W (x - M ζ)) ∂μ) (R (x - x)) := by
    rw [h0]; exact hasFDerivAt_shift (μ := μ) hK M hW hB x
  have hcomp : HasFDerivAt (fun y => Θ (R (y - x)))
      ((∫ ζ, (fderiv ℝ K ζ).smulRight (W (x - M ζ)) ∂μ).comp R) x :=
    HasFDerivAt.comp (g := Θ) x hΘ hR
  rw [hrep, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have hint : Integrable (fun ζ => (fderiv ℝ K ζ).smulRight (W (x - M ζ))) μ := by
    have hK1 : ContDiff ℝ 1 K := hK.smooth.of_le (by exact_mod_cast le_top)
    have hdK : Continuous (fderiv ℝ K) := hK1.continuous_fderiv (by norm_num)
    refine Integrable.mono' ((hdK.norm.integrable_of_hasCompactSupport (hK.cpt.fderiv (𝕜 := ℝ)).norm).mul_const B)
      ((ContinuousLinearMap.smulRightL ℝ E H).continuous₂.comp
        (hdK.prodMk (hW.comp (continuous_const.sub M.continuous)))).aestronglyMeasurable ?_
    exact Eventually.of_forall fun ζ => by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  rw [ContinuousLinearMap.integral_apply hint]
  simp [Op, dirD, ContinuousLinearMap.smulRight_apply]
end

/-! Iterated derivatives of a kernel average.

* `iterate_op_kernel`: `(∂_e)^n Op K M W = Op ((D_{Re})^n K) M W` (kernel side);
* `iterate_op_field`: `(∂_e)^n Op K M W = Op K M ((∂_e)^n W)` for regular `W` (field side);
* `iterate_dirD_rep`: iterated directional derivatives of a smooth kernel are its iterated Fréchet
  derivative on bounded vectors, whence `∫‖(D_{v₁})^b (D_{v₀})^a K‖ ≤ ρ^{a+b} ∫‖D^{a+b}K‖`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

section Rep

/-- One more directional derivative of an iterated derivative on fixed vectors. -/
theorem dirD_iteratedFDeriv {K : E → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K) (n : ℕ)
    (w : Fin n → E) (v : E) :
    dirD v (fun ζ => iteratedFDeriv ℝ n K ζ w) =
      fun ζ => iteratedFDeriv ℝ (n + 1) K ζ (Fin.cons v w) := by
  funext ζ
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n K) ζ :=
    (hK.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast WithTop.coe_lt_top _)) ζ
  unfold dirD
  rw [fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]
  simp [Fin.tail_cons]

/-- Iterating a bounded direction keeps the representation by bounded vectors. -/
theorem iterate_dirD_rep {K : E → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K) {ρ : ℝ} {v : E}
    (hv : ‖v‖ ≤ ρ) : ∀ (k n : ℕ) (w : Fin n → E), (∀ i, ‖w i‖ ≤ ρ) →
    ∃ w' : Fin (n + k) → E, (∀ i, ‖w' i‖ ≤ ρ) ∧
      (dirD v)^[k] (fun ζ => iteratedFDeriv ℝ n K ζ w) =
        fun ζ => iteratedFDeriv ℝ (n + k) K ζ w'
  | 0, n, w, hw => ⟨w, hw, rfl⟩
  | k + 1, n, w, hw => by
      obtain ⟨w', hw', heq⟩ := iterate_dirD_rep hK hv k n w hw
      refine ⟨Fin.cons v w', ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hv
        · simpa using hw' j
      · rw [Function.iterate_succ_apply', heq, dirD_iteratedFDeriv hK]
        rfl

/-- The kernel itself is its zeroth iterated derivative. -/
theorem kernel_eq_iteratedFDeriv_zero (K : E → ℝ) :
    K = fun ζ => iteratedFDeriv ℝ 0 K ζ (Fin.elim0 : Fin 0 → E) := by
  funext ζ; simp

/-- Two bounded directions iterated: representation by `iteratedFDeriv` of order `a + b`. -/
theorem iterate2_rep {K : E → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K) {ρ : ℝ} {v₀ v₁ : E}
    (h0 : ‖v₀‖ ≤ ρ) (h1 : ‖v₁‖ ≤ ρ) (a b : ℕ) :
    ∃ w : Fin (0 + a + b) → E, (∀ i, ‖w i‖ ≤ ρ) ∧
      (dirD v₁)^[b] ((dirD v₀)^[a] K) = fun ζ => iteratedFDeriv ℝ (0 + a + b) K ζ w := by
  obtain ⟨w₁, hw₁, he₁⟩ := iterate_dirD_rep hK h0 a 0 Fin.elim0 (fun i => Fin.elim0 i)
  obtain ⟨w₂, hw₂, he₂⟩ := iterate_dirD_rep hK h1 b (0 + a) w₁ hw₁
  refine ⟨w₂, hw₂, ?_⟩
  conv_lhs => rw [kernel_eq_iteratedFDeriv_zero K]
  rw [he₁, he₂]

/-- Pointwise bound of an iterated derivative on bounded vectors. -/
theorem norm_iteratedFDeriv_apply_le {K : E → ℝ} {n : ℕ} {ρ : ℝ} (w : Fin n → E)
    (hw : ∀ i, ‖w i‖ ≤ ρ) (ζ : E) :
    ‖iteratedFDeriv ℝ n K ζ w‖ ≤ ρ ^ n * ‖iteratedFDeriv ℝ n K ζ‖ := by
  calc ‖iteratedFDeriv ℝ n K ζ w‖ ≤ ‖iteratedFDeriv ℝ n K ζ‖ * ∏ i, ‖w i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ ‖iteratedFDeriv ℝ n K ζ‖ * ρ ^ n := by
        gcongr
        calc ∏ i, ‖w i‖ ≤ ∏ _i : Fin n, ρ :=
              Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hw i)
          _ = ρ ^ n := by simp
    _ = ρ ^ n * ‖iteratedFDeriv ℝ n K ζ‖ := mul_comm _ _

end Rep

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {μ : Measure E}

/-- **Kernel-side iteration.** -/
theorem iterate_op_kernel [CompleteSpace H] [IsFiniteMeasureOnCompacts μ] [ProperSpace E]
    [μ.IsAddRightInvariant] (M : E →L[ℝ] F) (R : F →L[ℝ] E) (hMR : ∀ y, M (R y) = y)
    {W : F → H} (hW : Continuous W) {B : ℝ} (hB : ∀ y, ‖W y‖ ≤ B) (e : F) :
    ∀ (n : ℕ) (K : E → ℝ), IsKer K →
      (dirD e)^[n] (Op μ K M W) = Op μ ((dirD (R e))^[n] K) M W
  | 0, _, _ => rfl
  | n + 1, K, hK => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have h1 : dirD e (Op μ K M W) = Op μ (dirD (R e) K) M W := by
        funext x
        exact fderiv_op_kernel hK M R hMR hW hB x e
      rw [h1]
      exact iterate_op_kernel M R hMR hW hB e n _ (hK.dir (R e))

/-- **Field-side derivative.** -/
theorem fderiv_op_field [CompleteSpace H] [IsFiniteMeasureOnCompacts μ] {K : E → ℝ}
    (hK : IsKer K) (M : E →L[ℝ] F) {W : F → H} (hW1 : ContDiff ℝ 1 W) {B' : ℝ}
    (hB' : ∀ y, ‖fderiv ℝ W y‖ ≤ B') {B : ℝ} (hB : ∀ y, ‖W y‖ ≤ B) (x e : F) :
    fderiv ℝ (Op μ K M W) x e = Op μ K M (dirD e W) x := by
  have hdW : Continuous (fderiv ℝ W) := hW1.continuous_fderiv (by norm_num)
  have hd : HasFDerivAt (Op μ K M W) (∫ ζ, K ζ • fderiv ℝ W (x - M ζ) ∂μ) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ)
      (F := fun y ζ => K ζ • W (y - M ζ)) (F' := fun y ζ => K ζ • fderiv ℝ W (y - M ζ))
      (bound := fun ζ => ‖K ζ‖ * B') (Filter.univ_mem)
      (Eventually.of_forall fun y => (integrable_op hK M hW1.continuous hB y).aestronglyMeasurable)
      (integrable_op hK M hW1.continuous hB x) ?_ ?_ ((hK.integrable (μ := μ)).norm.mul_const B') ?_
    · exact (hK.smooth.continuous.smul (hdW.comp (continuous_const.sub M.continuous))).aestronglyMeasurable
    · exact Eventually.of_forall fun ζ y _ => by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hB' _) (norm_nonneg _)
    · refine Eventually.of_forall fun ζ y _ => ?_
      have h := (hW1.differentiable (by norm_num) (y - M ζ)).hasFDerivAt
      have h2 : HasFDerivAt (fun y' => W (y' - M ζ))
          ((fderiv ℝ W (y - M ζ)).comp (ContinuousLinearMap.id ℝ F)) y :=
        h.comp y ((hasFDerivAt_id y).sub_const (M ζ))
      rw [ContinuousLinearMap.comp_id] at h2
      exact h2.const_smul (K ζ)
  have hint : Integrable (fun ζ => K ζ • fderiv ℝ W (x - M ζ)) μ := by
    refine Integrable.mono' ((hK.integrable (μ := μ)).norm.mul_const B')
      (hK.smooth.continuous.smul (hdW.comp (continuous_const.sub M.continuous))).aestronglyMeasurable
      (Eventually.of_forall fun ζ => ?_)
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hB' _) (norm_nonneg _)
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hint]
  rfl

/-- **Field-side iteration.** -/
theorem iterate_op_field [CompleteSpace H] [IsFiniteMeasureOnCompacts μ] {K : E → ℝ}
    (hK : IsKer K) (M : E →L[ℝ] F) (e : F) :
    ∀ (n : ℕ) (W : F → H),
      (∀ j ≤ n, Continuous ((dirD e)^[j] W) ∧ ∃ B, ∀ y, ‖(dirD e)^[j] W y‖ ≤ B) →
      (∀ j < n, ContDiff ℝ 1 ((dirD e)^[j] W) ∧
        ∃ B', ∀ y, ‖fderiv ℝ ((dirD e)^[j] W) y‖ ≤ B') →
      (dirD e)^[n] (Op μ K M W) = Op μ K M ((dirD e)^[n] W)
  | 0, _, _, _ => rfl
  | n + 1, W, h0, h1 => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      obtain ⟨hW1, B', hB'⟩ := h1 0 (Nat.succ_pos n)
      obtain ⟨-, B, hB⟩ := h0 0 (Nat.zero_le _)
      have hstep : dirD e (Op μ K M W) = Op μ K M (dirD e W) := by
        funext x
        exact fderiv_op_field hK M hW1 hB' hB x e
      rw [hstep]
      refine iterate_op_field hK M e n (dirD e W) (fun j hj => ?_) (fun j hj => ?_)
      · have := h0 (j + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this
      · have := h1 (j + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this
end

end AVRegularity.Providers.KernelSup
end

section
open Homogenization Filter Topology
namespace AVRegularity.Providers.KernelSup

/-! Periodic fields on `ℝ²`: continuous periodic fields are bounded, and directional derivatives
preserve periodicity and lower the smoothness by one. -/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedSpace ℝ H] in
/-- A continuous `ℤ²`-periodic field is bounded. -/
theorem bdd_of_periodic {W : Vec 2 → H} (hW : Continuous W) (hp : AVenhance.IsZ2Periodic W) :
    ∃ B, ∀ y, ‖W y‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : Vec 2)) (b := 1)).exists_bound_of_continuousOn
    hW.continuousOn
  refine ⟨B, fun x => ?_⟩
  let y : Vec 2 := fun i => Int.fract (x i)
  let n : Fin 2 → ℤ := fun i => ⌊x i⌋
  have hx : x = y + AVenhance.latticeShift n := by
    funext i
    simp only [Pi.add_apply, y, AVenhance.latticeShift, n]
    linarith [Int.fract_add_floor (x i)]
  have hy : y ∈ Set.Icc (0 : Vec 2) 1 :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  rw [hx, hp n y]
  exact hB y hy

/-- Directional derivatives of periodic fields are periodic. -/
theorem periodic_dirD {W : Vec 2 → H} (hp : AVenhance.IsZ2Periodic W) (e : Vec 2) :
    AVenhance.IsZ2Periodic (dirD e W) := by
  intro n x
  unfold dirD
  have h : (fun y => W (y + AVenhance.latticeShift n)) = W := funext fun y => hp n y
  rw [← fderiv_comp_add_right, h]

/-- The derivative of a periodic field is periodic. -/
theorem periodic_fderiv {W : Vec 2 → H} (hp : AVenhance.IsZ2Periodic W) :
    AVenhance.IsZ2Periodic (fderiv ℝ W) := by
  intro n x
  have h : (fun y => W (y + AVenhance.latticeShift n)) = W := funext fun y => hp n y
  rw [← fderiv_comp_add_right, h]

/-- A directional derivative lowers the smoothness by one. -/
theorem contDiff_dirD {W : Vec 2 → H} {n : ℕ} (hW : ContDiff ℝ (n + 1 : ℕ) W) (e : Vec 2) :
    ContDiff ℝ n (dirD e W) :=
  (hW.fderiv_right (m := n) (by push_cast; exact le_rfl)).clm_apply contDiff_const

/-- Regularity of iterated directional derivatives. -/
theorem iterate_reg {W : Vec 2 → H} {n : ℕ} (hW : ContDiff ℝ n W)
    (hp : AVenhance.IsZ2Periodic W) (e : Vec 2) :
    ∀ j ≤ n, ContDiff ℝ (n - j : ℕ) ((dirD e)^[j] W) ∧
      AVenhance.IsZ2Periodic ((dirD e)^[j] W)
  | 0, _ => ⟨by simpa using hW, hp⟩
  | j + 1, hj => by
      obtain ⟨h1, h2⟩ := iterate_reg hW hp e j (by omega)
      rw [Function.iterate_succ_apply']
      refine ⟨contDiff_dirD (by rwa [show n - j = n - (j + 1) + 1 by omega] at h1) e,
        periodic_dirD h2 e⟩

/-- The hypotheses of `iterate_op_field` for a periodic field of class `C^n`. -/
theorem iterate_field_hyps {W : Vec 2 → H} {n : ℕ} (hW : ContDiff ℝ n W)
    (hp : AVenhance.IsZ2Periodic W) (e : Vec 2) :
    (∀ j ≤ n, Continuous ((dirD e)^[j] W) ∧ ∃ B, ∀ y, ‖(dirD e)^[j] W y‖ ≤ B) ∧
    (∀ j < n, ContDiff ℝ 1 ((dirD e)^[j] W) ∧
      ∃ B', ∀ y, ‖fderiv ℝ ((dirD e)^[j] W) y‖ ≤ B') := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨h1, h2⟩ := iterate_reg hW hp e j hj
    exact ⟨h1.continuous, bdd_of_periodic h1.continuous h2⟩
  · obtain ⟨h1, h2⟩ := iterate_reg hW hp e j hj.le
    have h1' : ContDiff ℝ 1 ((dirD e)^[j] W) := h1.of_le (by exact_mod_cast (by omega : 1 ≤ n - j))
    exact ⟨h1', bdd_of_periodic (h1'.continuous_fderiv (by norm_num)) (periodic_fderiv h2)⟩

end AVRegularity.Providers.KernelSup
end
