-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.ScalarEnergyDecay
import AVRegularity.CycleEvolution.CellBochnerCarrier
public import AVRegularity.CoupledEnergy.Variational.CarrierFiberCLM
public import AVRegularity.CoupledEnergy.Galerkin.CarrierFamilyProjection
import AVenhance.Infra.Classical.GalerkinGenerator
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public noncomputable section

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Cross pairings of the H1 state and dual curves are genuinely integrable in time. -/

theorem cellH1Pair_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    {g z : ℝ → TorusHk 1 ℂ}
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hz : MemLp z 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => inner ℝ (g t) (z t)) volume a b := by
  have hm : Integrable (fun t => ‖g t‖ * ‖z t‖) (volume.restrict (Icc a b)) :=
    memLp_one_iff_integrable.mp (hg.norm.mul hz.norm : MemLp _ 1 _)
  have hp : Integrable (fun t => inner ℝ (g t) (z t)) (volume.restrict (Icc a b)) := by
    apply hm.mono'
    · exact hg.aestronglyMeasurable.inner hz.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs]
        exact abs_real_inner_le_norm (g t) (z t))
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hab]
  exact hp.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Bivariate fibre coefficient arrays as genuine Banach-valued formal multilinear series. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def fibreFormalSeries (c : ℕ × ℕ → E) : FormalMultilinearSeries ℂ (Fin 2 → ℂ) E :=
  fun n => ∑ α ∈ (Finset.HasAntidiagonal.antidiagonal n).attach,
    (fibreMonomialDegreeCoefficient n α.val (Finset.HasAntidiagonal.mem_antidiagonal.mp α.property)).smulRight (c α.val)

theorem fibreFormalSeries_coeff_norm_le (c : ℕ × ℕ → E) (n : ℕ) :
    ‖fibreFormalSeries c n‖ ≤ ∑ α ∈ Finset.HasAntidiagonal.antidiagonal n, ‖c α‖ := by
  unfold fibreFormalSeries
  calc
    _ ≤ ∑ α ∈ (Finset.HasAntidiagonal.antidiagonal n).attach,
        ‖(fibreMonomialDegreeCoefficient n α.val (Finset.HasAntidiagonal.mem_antidiagonal.mp α.property)).smulRight (c α.val)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ α ∈ (Finset.HasAntidiagonal.antidiagonal n).attach, ‖c α.val‖ := by
      apply Finset.sum_le_sum
      intro α _
      rw [ContinuousMultilinearMap.norm_smulRight]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (fibreMonomialDegreeCoefficient_norm_le n α.val (Finset.HasAntidiagonal.mem_antidiagonal.mp α.property)) (norm_nonneg _)
    _ = _ := Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal n) (fun α => ‖c α‖)

theorem fibreFormalSeries_diag (c : ℕ × ℕ → E) (n : ℕ) (ξ : Fin 2 → ℂ) :
    fibreFormalSeries c n (fun _ => ξ) = ∑ α ∈ Finset.HasAntidiagonal.antidiagonal n, fibreMonomial ξ α • c α := by
  simp only [fibreFormalSeries, sum_apply,
    ContinuousMultilinearMap.smulRight_apply, fibreMonomialDegreeCoefficient_diag]
  exact Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal n) (fun α => fibreMonomial ξ α • c α)
end

/-! Pointwise frequency and monomial estimates for the literal fibre Taylor series. -/

/-- Each complex coordinate is bounded by the literal fibre norm. -/
theorem fibreNorm_coordinate_le (ξ : Fin 2 → ℂ) (j : Fin 2) : ‖ξ j‖ ≤ fibreNorm ξ := by
  have hs : fibreNorm ξ ^ 2 = ∑ i, ‖ξ i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖ξ i‖))
  have hi : ‖ξ j‖ ^ 2 ≤ ∑ i, ‖ξ i‖ ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ‖ξ i‖) (Finset.mem_univ j)
  nlinarith [fibreNorm_nonneg ξ, norm_nonneg (ξ j)]

/-- Every literal monomial is bounded by the corresponding power of the fibre norm. -/
theorem fibreMonomial_norm_le (ξ : Fin 2 → ℂ) (α : ℕ × ℕ) :
    ‖fibreMonomial ξ α‖ ≤ fibreNorm ξ ^ (α.1 + α.2) := by
  rw [fibreMonomial, norm_mul, norm_pow, norm_pow, pow_add]
  have hn := fibreNorm_nonneg ξ
  gcongr <;> first | positivity | apply fibreNorm_coordinate_le

/-- Addition of multi-indices becomes multiplication of literal monomials. -/
theorem fibreMonomial_add (ξ : Fin 2 → ℂ) (α β : ℕ × ℕ) :
    fibreMonomial ξ (α + β) = fibreMonomial ξ α * fibreMonomial ξ β := by
  simp only [fibreMonomial, Prod.add_def, pow_add]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Convolution form of a forced scalar energy inequality. -/

/-- A scalar dissipative differential inequality gives the exact past-forcing convolution. -/
theorem StrongTimeRegularity.scalar_forced_decay {a b : ℝ} (hab : a ≤ b)
    {E P : ℝ → ℝ} (h : StrongTimeRegularity a b E P) (c : ℝ) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b)
    (hg : ∀ᵐ t ∂volume.restrict (Icc a b), P t + c * E t ≤ f t) :
    E b ≤ Real.exp (-c * (b - a)) * E a +
      ∫ t in a..b, Real.exp (-c * (b - t)) * f t := by
  have hw := h.scalar_weighted_bound hab c f 0 hf intervalIntegrable_const (by simpa using hg)
  simp only [Pi.zero_apply, mul_zero, intervalIntegral.integral_zero, add_zero] at hw
  have hc : (∫ t in a..b, Real.exp (-c * (b - t)) * f t) =
      Real.exp (-c * (b - a)) * ∫ t in a..b, Real.exp (c * (t - a)) * f t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hc]
  have hm := mul_le_mul_of_nonneg_left hw (Real.exp_pos (-c * (b - a))).le
  have he : Real.exp (-c * (b - a)) * Real.exp (c * (b - a)) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa only [mul_add, ← mul_assoc, he, one_mul] using hm

end AVRegularity.CycleEvolution
end

section
open Metric
open scoped ContDiff
namespace AVRegularity.CycleEvolution

/-! Cauchy estimates for linear readouts of genuine Banach-valued frequency jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem complexFrequencyWordJet_readout (f : (Fin 2 → ℂ) → E)
    (L : E →L[ℂ] F) (ξ : Fin 2 → ℂ) (hf : AnalyticAt ℂ f ξ)
    (n : ℕ) (w : Fin n → (Fin 2 → ℂ)) :
    L (complexFrequencyWordJet f n w ξ) = complexFrequencyWordJet (L ∘ f) n w ξ := by
  unfold complexFrequencyWordJet
  rw [L.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast (show n ≤ (ω : WithTop ℕ∞) from le_top))]
  rfl

 theorem complexFrequencyWordJet_readout_bound (f : (Fin 2 → ℂ) → E)
    (L : E →L[ℂ] F) (ξ : Fin 2 → ℂ) (R M : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball ξ R))
    (hb : ∀ ζ ∈ ball ξ R, ‖L (f ζ)‖ ≤ M)
    (n : ℕ) (w : Fin n → (Fin 2 → ℂ)) (hw : ∀ i, ‖w i‖ ≤ 1) :
    ‖L (complexFrequencyWordJet f n w ξ)‖ ≤ analyticBallDerivativeConstant n * M / R ^ n := by
  rw [complexFrequencyWordJet_readout f L ξ (hf ξ (mem_ball_self hR))]
  have ha : AnalyticOnNhd ℂ (L ∘ f) (ball ξ R) := fun ζ hζ =>
    (L.analyticAt (f ζ)).comp (hf ζ hζ)
  have hn := analytic_ball_iterated_derivative_le n hR ha hb
  have he := (iteratedFDeriv ℂ n (L ∘ f) ξ).le_opNorm_mul_prod_of_le
    (b := fun _ => (1 : ℝ)) hw
  have heval : ‖complexFrequencyWordJet (L ∘ f) n w ξ‖ ≤
      ‖iteratedFDeriv ℂ n (L ∘ f) ξ‖ := by
    simpa only [complexFrequencyWordJet, Finset.prod_const_one, mul_one] using he
  exact heval.trans hn

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Complex primitive time regularity assembled through its proved real component calculus. -/

theorem complexStrongTime_of_primitive {a b : ℝ} (hab : a ≤ b) (E P : ℝ → ℂ)
    (hP : IntervalIntegrable P volume a b)
    (he : ∀ t ∈ Icc a b, E t = E a + ∫ s in a..t, P s) :
    StrongTimeRegularity a b E P := by
  apply complexStrongTime_of_components
  · apply scalarStrongTime_of_primitive hab _ _ (intervalIntegrable_iff.mpr (Complex.reCLM.integrable_comp (intervalIntegrable_iff.mp hP)))
    intro t ht
    have hr := congrArg Complex.re (he t ht)
    have hi : IntervalIntegrable P volume a t := hP.mono_set (by rw [uIcc_of_le hab, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
    have hm := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ s in a..t, (P s).re) = (∫ s in a..t, P s).re at hm
    rw [Complex.add_re, ← hm] at hr
    exact hr
  · apply scalarStrongTime_of_primitive hab _ _ (intervalIntegrable_iff.mpr (Complex.imCLM.integrable_comp (intervalIntegrable_iff.mp hP)))
    intro t ht
    have hr := congrArg Complex.im (he t ht)
    have hi : IntervalIntegrable P volume a t := hP.mono_set (by rw [uIcc_of_le hab, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
    have hm := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ s in a..t, (P s).im) = (∫ s in a..t, P s).im at hm
    rw [Complex.add_im, ← hm] at hr
    exact hr

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! Each multilinear coefficient is controlled by the complete absolute coefficient budget. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fibreFormalSeries_coeff_eq_zero (c : ℕ × ℕ → E) (n : ℕ)
    (hc : ∀ α, α.1 + α.2 = n → c α = 0) : fibreFormalSeries c n = 0 := by
  unfold fibreFormalSeries
  apply Finset.sum_eq_zero
  intro α _
  rw [hc α.val (Finset.HasAntidiagonal.mem_antidiagonal.mp α.property)]
  ext v
  simp
end

/-! Absolute bivariate coefficient majorants give an actual analytic convergence radius. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fibreFormalSeries_radius_le (c : ℕ × ℕ → E) (R : ℝ≥0)
    (hs : Summable (fun α => ‖c α‖ * (R : ℝ) ^ (α.1 + α.2))) :
    (R : ENNReal) ≤ (fibreFormalSeries c).radius := by
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hσ : Summable (fun x : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) =>
      ‖c x.2.val‖ * (R : ℝ) ^ (x.2.val.1 + x.2.val.2)) := e.summable_iff.mpr hs
  have ha : Summable (fun n => ∑ α ∈ Finset.HasAntidiagonal.antidiagonal n,
      ‖c α‖ * (R : ℝ) ^ (α.1 + α.2)) := by
    have ht := hσ.sigma' (fun _ => (hasSum_fintype _).summable)
    convert ht using 1
    funext n
    rw [tsum_fintype]
    exact (Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal n)
      (fun α => ‖c α‖ * (R : ℝ) ^ (α.1 + α.2))).symm
  have ha' : Summable (fun n => (∑ α ∈ Finset.HasAntidiagonal.antidiagonal n, ‖c α‖) * (R : ℝ) ^ n) := by
    convert ha using 1
    funext n
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α hα
    rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hα]
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  exact ha'.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (pow_nonneg R.coe_nonneg _))
    (fun n => mul_le_mul_of_nonneg_right (fibreFormalSeries_coeff_norm_le c n) (pow_nonneg R.coe_nonneg _))
end

/-! Identification of the analytic formal series with the literal bivariate fibre sum. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem fibreMonomial_norm_le_pi (ξ : Fin 2 → ℂ) (α : ℕ × ℕ) :
    ‖fibreMonomial ξ α‖ ≤ ‖ξ‖ ^ (α.1 + α.2) := by
  rw [fibreMonomial, norm_mul, norm_pow, norm_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm ξ 0) _)
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm ξ 1) _)
    (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _)

theorem fibreBivariateSum_summable (c : ℕ × ℕ → E) (R : ℝ≥0)
    (hs : Summable (fun α => ‖c α‖ * (R : ℝ) ^ (α.1 + α.2)))
    (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ R) :
    Summable (fun α => fibreMonomial ξ α • c α) := by
  apply hs.of_norm_bounded
  intro α
  rw [norm_smul, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (fibreMonomial_norm_le_pi ξ α).trans
    (pow_le_pow_left₀ (norm_nonneg _) hξ _)

theorem fibreFormalSeries_sum_eq (c : ℕ × ℕ → E) (R : ℝ≥0)
    (hs : Summable (fun α => ‖c α‖ * (R : ℝ) ^ (α.1 + α.2)))
    (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ R) :
    (fibreFormalSeries c).sum ξ = ∑' α, fibreMonomial ξ α • c α := by
  have ht := fibreBivariateSum_summable c R hs ξ hξ
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hσ : Summable (fun x : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) =>
      fibreMonomial ξ x.2.val • c x.2.val) := e.summable_iff.mpr ht
  change (∑' n, fibreFormalSeries c n (fun _ => ξ)) = _
  simp_rw [fibreFormalSeries_diag]
  rw [← e.tsum_eq (fun α => fibreMonomial ξ α • c α)]
  change (∑' n, ∑ α ∈ Finset.HasAntidiagonal.antidiagonal n, fibreMonomial ξ α • c α) =
    ∑' x : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n), fibreMonomial ξ x.2.val • c x.2.val
  rw [hσ.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  congr 1
  funext n
  rw [tsum_fintype]
  exact (Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal n)
    (fun α => fibreMonomial ξ α • c α)).symm
end

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! The Banach frequency norm is bounded by the literal two-coordinate fibre norm. -/

theorem fibrePiNorm_le (ξ : Fin 2 → ℂ) : ‖ξ‖ ≤ fibreNorm ξ := by
  exact (pi_norm_le_iff_of_nonneg (fibreNorm_nonneg ξ)).mpr (fibreNorm_coordinate_le ξ)

/-! The actual Bloch shift is bounded by the literal complex frequency uniformly in contrast. -/

theorem fibreScaledFrequency_coordinate_le (η : ℝ) (hη : η ≤ 1)
    (ξ : Fin 2 → ℂ) (j : Fin 2) : ‖(Real.sqrt η : ℂ) * ξ j‖ ≤ fibreNorm ξ := by
  have hs : Real.sqrt η ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hη
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg η)]
  calc
    _ ≤ 1 * fibreNorm ξ := mul_le_mul hs (fibreNorm_coordinate_le ξ j)
      (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Short-interval forcing bounds for a nonnegative dissipative scalar energy. -/

/-- On any interval, a nonnegative forcing convolution is bounded by its unweighted integral. -/
theorem scalar_forcing_convolution_le {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b)
    (hn : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ f t) :
    (∫ t in a..b, Real.exp (-c * (b - t)) * f t) ≤ ∫ t in a..b, f t := by
  have hw : IntervalIntegrable (fun t => Real.exp (-c * (b - t)) * f t) volume a b :=
    hf.continuousOn_mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  apply intervalIntegral.integral_mono_ae_restrict hab hw hf
  filter_upwards [hn, ae_restrict_mem measurableSet_Icc] with t ht hti
  have he : Real.exp (-c * (b - t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sub_nonneg.mpr hti.2)
  exact (mul_le_mul_of_nonneg_right he ht).trans_eq (one_mul _)

/-- A dissipative scalar equation contracts its old value and adds at most the interval forcing. -/
theorem StrongTimeRegularity.scalar_forced_step {a b : ℝ} (hab : a ≤ b)
    {E P : ℝ → ℝ} (h : StrongTimeRegularity a b E P) (c : ℝ) (hc : 0 ≤ c)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b)
    (hn : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ f t)
    (hg : ∀ᵐ t ∂volume.restrict (Icc a b), P t + c * E t ≤ f t) :
    E b ≤ Real.exp (-c * (b - a)) * E a + ∫ t in a..b, f t :=
  (h.scalar_forced_decay hab c f hf hg).trans
    (add_le_add le_rfl (scalar_forcing_convolution_le hab hc f hf hn))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Periodic raw weak jets are invariant under cellwise almost-everywhere changes. -/

/-- A periodic raw jet representing a given H¹ graph element has the same weak derivatives. -/
theorem cellPeriodicJet_of_class (D : RawJet2 1 ℂ) (u : TorusHk 1 ℂ)
    (hper : ∀ a, AVenhance.IsZ2Periodic (D a))
    (he : ∀ a, (u.val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D a) :
    HasPeriodicOrderedWeakJet D := by
  have hmem : JetMemL2On AVenhance.unitCube D := fun a => (Lp.memLp (u.val a)).ae_eq (he a)
  have he' (a) : D a =ᵐ[volume.restrict AVenhance.unitCube] u.toFunction.jet a :=
    (he a).symm.trans (periodicJetRepresentative_ae u.val a).symm
  refine ⟨hper, hmem, ?_⟩
  intro j w i e φ hφ hc hs
  simp only [setIntegral_univ]
  let ψ := fun x => (fderiv ℝ φ x) (basisVec i)
  have hψ : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψc : HasCompactSupport ψ := hc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hp (a) (χ : Vec 2 → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ) :
      (∫ x, inner ℝ e (D a x) * χ x) =
        ∫ x, inner ℝ e (u.toFunction.jet a x) * χ x := by
    rw [periodicRawPairing_eq_cell D hper hmem a e hχ hcχ,
      periodicRawPairing_eq_cell u.toFunction.jet u.toFunction.hasPeriodicWeakJet.1
        u.toFunction.hasPeriodicWeakJet.2.1 a e hχ hcχ]
    apply integral_congr_ae
    filter_upwards [he' a] with x hx
    rw [hx]
  rw [hp (lowerIndex2 j w) ψ hψ hψc,
    hp (nextIndex2 j w i) φ hφ.continuous hc]
  simpa only [setIntegral_univ, ψ] using
    u.toFunction.hasPeriodicWeakJet.2.2 j w i e φ hφ hc hs

/-! Periodic raw weak jets transfer across equality of every cell L2 component. -/

/-- Cell-ae equality of periodic representatives preserves the actual global periodic weak-jet identities. -/
theorem cellPeriodicWeakJet_of_ae_components {K : ℕ} {D E : RawJet2 K ℂ}
    (hE : HasPeriodicOrderedWeakJet E)
    (hDper : ∀ a, AVenhance.IsZ2Periodic (D a))
    (he : ∀ a, D a =ᵐ[volume.restrict AVenhance.unitCube] E a) :
    HasPeriodicOrderedWeakJet D := by
  have hDm : JetMemL2On AVenhance.unitCube D :=
    fun a => (memLp_congr_ae (he a)).mpr (hE.2.1 a)
  have hpair (a : JetIndex2 K) (e : ℂ) (ψ : Vec 2 → ℝ)
      (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
      (∫ x, inner ℝ e (D a x) * ψ x) = ∫ x, inner ℝ e (E a x) * ψ x := by
    rw [periodicRawPairing_eq_cell D hDper hDm a e hψ hc,
      periodicRawPairing_eq_cell E hE.1 hE.2.1 a e hψ hc]
    apply integral_congr_ae
    filter_upwards [he a] with x hx
    rw [hx]
  refine ⟨hDper, hDm, ?_⟩
  intro j w i e φ hφ hc hs
  simp only [Measure.restrict_univ]
  rw [hpair (lowerIndex2 j w) e _
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply (𝕜 := ℝ) (basisVec i)),
    hpair (nextIndex2 j w i) e φ hφ.continuous hc]
  simpa only [Measure.restrict_univ] using hE.2.2 j w i e φ hφ hc hs

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Abstract complex quadratic metric bounds with no drift or contrast dependence. -/

theorem fibreQuad_norm_le_eight (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ j k, |G j k| ≤ 2) (ξ : Fin 2 → ℂ) :
    ‖fibreQuad G ξ‖ ≤ 8 * fibreNorm ξ ^ 2 := by
  have ht (j k : Fin 2) : ‖(G j k : ℂ) * ξ j * ξ k‖ ≤ 2 * fibreNorm ξ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ 2 * fibreNorm ξ * fibreNorm ξ := by
        gcongr
        · exact mul_nonneg (by norm_num) (fibreNorm_nonneg ξ)
        · exact hG j k
        · exact fibreNorm_coordinate_le ξ j
        · exact fibreNorm_coordinate_le ξ k
      _ = _ := by ring
  have he : fibreQuad G ξ = ∑ j : Fin 2, ∑ k : Fin 2, (G j k : ℂ) * ξ j * ξ k := by
    simp only [fibreQuad, Fin.sum_univ_two]
    ring
  rw [he]
  calc
    _ ≤ ∑ j : Fin 2, ‖∑ k : Fin 2, (G j k : ℂ) * ξ j * ξ k‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 2, ∑ k : Fin 2, ‖(G j k : ℂ) * ξ j * ξ k‖ :=
      Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j : Fin 2, ∑ k : Fin 2, 2 * fibreNorm ξ ^ 2 :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ht j k))
    _ = _ := by simp only [Fin.sum_univ_two]; ring

/-! Abstract complex quadratic metric bounds with no drift or contrast dependence. -/

theorem fibreQuad_norm_le_four_mul (G : Matrix (Fin 2) (Fin 2) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hG : ∀ j k, |G j k| ≤ B) (ξ : Fin 2 → ℂ) :
    ‖fibreQuad G ξ‖ ≤ 4 * B * fibreNorm ξ ^ 2 := by
  have ht (j k : Fin 2) : ‖(G j k : ℂ) * ξ j * ξ k‖ ≤ B * fibreNorm ξ ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ B * fibreNorm ξ * fibreNorm ξ := by
        gcongr
        · exact mul_nonneg hB (fibreNorm_nonneg ξ)
        · exact hG j k
        · exact fibreNorm_coordinate_le ξ j
        · exact fibreNorm_coordinate_le ξ k
      _ = _ := by ring
  have he : fibreQuad G ξ = ∑ j : Fin 2, ∑ k : Fin 2, (G j k : ℂ) * ξ j * ξ k := by
    simp only [fibreQuad, Fin.sum_univ_two]
    ring
  rw [he]
  calc
    _ ≤ ∑ j : Fin 2, ‖∑ k : Fin 2, (G j k : ℂ) * ξ j * ξ k‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 2, ∑ k : Fin 2, ‖(G j k : ℂ) * ξ j * ξ k‖ :=
      Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j : Fin 2, ∑ k : Fin 2, B * fibreNorm ξ ^ 2 :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ht j k))
    _ = _ := by simp only [Fin.sum_univ_two]; ring

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! All-frequency scalar homogeneous bounds from geometric coefficient estimates. -/

/-- Geometric scalar coefficient bounds give the literal homogeneous Taylor estimate at every frequency. -/
theorem fibreHomogeneous_scalar_le_of_geometric (a : ℕ × ℕ → ℝ → ℂ)
    (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (ha : ∀ p t, ‖a p t‖ ≤ K * A ^ (p.1 + p.2))
    (n : ℕ) (ξ : Fin 2 → ℂ) (t : ℝ) :
    ‖fibreHomogeneous a ξ n t‖ ≤ K * (2 * A) ^ n * fibreNorm ξ ^ n := by
  have he : fibreHomogeneous a ξ n t = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      fibreMonomial ξ p * a p t := by
    simp only [fibreHomogeneous, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  apply (norm_sum_le _ _).trans
  have hp p (hpn : p ∈ Finset.HasAntidiagonal.antidiagonal n) : ‖fibreMonomial ξ p * a p t‖ ≤
      K * A ^ n * fibreNorm ξ ^ n := by
    have ho : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hpn
    rw [norm_mul]
    calc
      _ ≤ fibreNorm ξ ^ n * (K * A ^ n) := by
        apply mul_le_mul (by simpa only [ho] using fibreMonomial_norm_le ξ p)
          (by simpa only [ho] using ha p t) (norm_nonneg _)
          (pow_nonneg (fibreNorm_nonneg ξ) n)
      _ = _ := by ring
  apply (Finset.sum_le_sum hp).trans
  rw [Finset.sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal]
  have hn : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.succ_le_of_lt ((show n < 2 ^ n from Nat.lt_two_pow_self))
  calc
    _ ≤ (2 : ℝ) ^ n * (K * A ^ n * fibreNorm ξ ^ n) :=
      mul_le_mul_of_nonneg_right hn
        (mul_nonneg (mul_nonneg hK (pow_nonneg hA n)) (pow_nonneg (fibreNorm_nonneg ξ) n))
    _ = _ := by rw [mul_pow]; ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! The actual exponential integral phase, with its derivative and cocycle law. -/

theorem complexPrimitivePhase_strongTime {a b : ℝ} (hab : a ≤ b) (lam : ℝ → ℂ)
    (hlam : IntervalIntegrable lam volume a b) :
    StrongTimeRegularity a b (fun t => Complex.exp (∫ r in a..t, lam r))
      (fun t => Complex.exp (∫ r in a..t, lam r) * lam t) := by
  have hp := complexStrongTime_of_primitive hab (fun t => ∫ r in a..t, lam r) lam hlam
    (fun t _ => by simp only [intervalIntegral.integral_same, zero_add])
  exact hp.complex_exp

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! Analyticity of the literal fibre sum, proved from its absolute coefficient majorant. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem fibreBivariateSum_hasFPowerSeriesOnBall (c : ℕ × ℕ → E) (R : ℝ≥0)
    (hR : 0 < R)
    (hs : Summable (fun α => ‖c α‖ * (R : ℝ) ^ (α.1 + α.2))) :
    HasFPowerSeriesOnBall (fun ξ => ∑' α, fibreMonomial ξ α • c α)
      (fibreFormalSeries c) 0 (R : ENNReal) := by
  have hr := fibreFormalSeries_radius_le c R hs
  have hpos : (0 : ENNReal) < R := by exact_mod_cast hR
  have hp := (fibreFormalSeries c).hasFPowerSeriesOnBall (hpos.trans_le hr)
  apply (hp.mono hpos hr).congr
  intro ξ hξ
  rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right] at hξ
  exact fibreFormalSeries_sum_eq c R hs ξ hξ.le

theorem fibreBivariateSum_analyticOnNhd (c : ℕ × ℕ → E) (R : ℝ≥0)
    (hR : 0 < R)
    (hs : Summable (fun α => ‖c α‖ * (R : ℝ) ^ (α.1 + α.2))) :
    AnalyticOnNhd ℂ (fun ξ => ∑' α, fibreMonomial ξ α • c α)
      (Metric.ball 0 (R : ℝ)) := by
  simpa only [Metric.eball_coe] using
    (fibreBivariateSum_hasFPowerSeriesOnBall c R hR hs).analyticOnNhd

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Every actual two-variable monomial has a degree-sensitive quantitative frequency increment. -/

theorem fibreMonomial_increment_bound (ξ ζ : Fin 2 → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hξ : fibreNorm ξ ≤ M) (hζ : fibreNorm ζ ≤ M) (p : ℕ × ℕ) :
    ‖fibreMonomial ξ p - fibreMonomial ζ p‖ ≤
      ((p.1 + p.2 : ℕ) : ℝ) * M ^ (p.1 + p.2 - 1) * fibreNorm (fun j => ξ j - ζ j) :=
  complex_mixed_power_increment_bound (ξ 0) (ξ 1) (ζ 0) (ζ 1) M
    (fibreNorm (fun j => ξ j - ζ j)) hM (fibreNorm_nonneg _)
    ((fibreNorm_coordinate_le ξ 0).trans hξ) ((fibreNorm_coordinate_le ξ 1).trans hξ)
    ((fibreNorm_coordinate_le ζ 0).trans hζ) ((fibreNorm_coordinate_le ζ 1).trans hζ)
    (fibreNorm_coordinate_le (fun j => ξ j - ζ j) 0)
    (fibreNorm_coordinate_le (fun j => ξ j - ζ j) 1) p.1 p.2

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Uniform scalar energy bounds from uniformly bounded unit-window forcing. -/

/-- Uniformly bounded forcing on intervals of length at most one bounds the entire energy trace. -/
theorem StrongTimeRegularity.scalar_ul_bound {a b : ℝ} (hab : a ≤ b)
    {E P : ℝ → ℝ} (h : StrongTimeRegularity a b E P) {c B : ℝ}
    (hc : 0 < c) (hB : 0 ≤ B) (ha : 0 ≤ E a)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b)
    (hn : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ f t)
    (hg : ∀ᵐ t ∂volume.restrict (Icc a b), P t + c * E t ≤ f t)
    (hshort : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → t - s ≤ 1 →
      (∫ r in s..t, f r) ≤ B) :
    ∀ t ∈ Icc a b, E t ≤ E a + B / (1 - Real.exp (-c)) + B := by
  have hstep (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
      (hsmall : t - s ≤ 1) : E t ≤ Real.exp (-c * (t - s)) * E s + B := by
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hu : uIcc s t ⊆ uIcc a b := by
      simpa only [uIcc_of_le hst, uIcc_of_le hab] using hsub
    have hm : volume.restrict (Icc s t) ≤ volume.restrict (Icc a b) :=
      Measure.restrict_mono hsub le_rfl
    exact ((h.mono hu).scalar_forced_step hst c hc.le f (hf.mono_set hu)
      (hn.filter_mono (ae_mono hm)) (hg.filter_mono (ae_mono hm))).trans
      (add_le_add le_rfl (hshort s hs t ht hst hsmall))
  intro t ht
  let N := ⌊t - a⌋₊
  have hN : (N : ℝ) ≤ t - a := Nat.floor_le (sub_nonneg.mpr ht.1)
  have hN1 : t - a < (N : ℝ) + 1 := Nat.lt_floor_add_one (t - a)
  have hp (n : ℕ) (hn : n ≤ N) : a + n ∈ Icc a b := by
    have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
    constructor
    · exact le_add_of_nonneg_right (Nat.cast_nonneg n)
    · have := ht.2; linarith
  have hd := scalar_discrete_forced_bound_on (fun n => E (a + n)) N
    (Real.exp_pos (-c)).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)) hB (by
      intro n hn
      have he := hstep (a + n) (a + (n + 1 : ℕ)) (hp n (Nat.le_of_lt hn))
        (hp (n + 1) hn) (by simp only [Nat.cast_add, Nat.cast_one]; linarith)
        (by simp only [Nat.cast_add, Nat.cast_one]; linarith)
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_add_left_eq_sub, add_sub_cancel_left,
        mul_one] using he)
  have hdisc := hd N le_rfl
  simp only [Nat.cast_zero, add_zero] at hdisc
  have hpow : Real.exp (-c) ^ N ≤ 1 :=
    pow_le_one₀ (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)).le
  have hbound : E (a + N) ≤ E a + B / (1 - Real.exp (-c)) :=
    hdisc.trans (add_le_add (by simpa using mul_le_mul_of_nonneg_right hpow ha) le_rfl)
  have hlast := hstep (a + N) t (hp N le_rfl) ht (by linarith) (by linarith)
  have hfactor : Real.exp (-c * (t - (a + N))) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (by linarith))
  have hupper : 0 ≤ E a + B / (1 - Real.exp (-c)) :=
    add_nonneg ha (div_nonneg hB (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc))).le)
  calc
    E t ≤ Real.exp (-c * (t - (a + N))) * E (a + N) + B := hlast
    _ ≤ Real.exp (-c * (t - (a + N))) * (E a + B / (1 - Real.exp (-c))) + B :=
      add_le_add (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le) le_rfl
    _ ≤ E a + B / (1 - Real.exp (-c)) + B :=
      add_le_add (by simpa using mul_le_mul_of_nonneg_right hfactor hupper) le_rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Constant fibre maps commute with real Hilbert adjoints on the periodic H1 graph. -/

theorem cellH1FiberMap_inner (L : ℂ →L[ℝ] ℂ) (u z : TorusHk 1 ℂ) :
    inner ℝ (mapTorusHkCLM 1 L u) z = inner ℝ u (mapTorusHkCLM 1 L.adjoint z) := by
  change inner ℝ (mapTorusHkCLM 1 L u).val z.val =
    inner ℝ u.val (mapTorusHkCLM 1 L.adjoint z).val
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mapTorusHk_jet_ae L u a, mapTorusHk_jet_ae L.adjoint z a] with x hu hz
  rw [mapTorusHkCLM_apply, mapTorusHkCLM_apply]
  rw [hu, hz]
  exact (ContinuousLinearMap.adjoint_inner_right L (u.val a x) (z.val a x)).symm

theorem cellH1FiberMap_adjoint (L : ℂ →L[ℝ] ℂ) :
    (mapTorusHkCLM 1 L).adjoint = mapTorusHkCLM 1 L.adjoint := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    _ = inner ℝ (mapTorusHkCLM 1 L u) z := real_inner_comm _ _
    _ = inner ℝ u (mapTorusHkCLM 1 L.adjoint z) := cellH1FiberMap_inner L u z
    _ = _ := real_inner_comm _ _

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! A bounded measurable scalar potential yields an actual bounded differentiable integral phase. -/

theorem complexBoundedPhase_regular {a b : ℝ} (hab : a ≤ b) (lam : ℝ → ℂ)
    (hlam : MemLp lam ⊤ (volume.restrict (Icc a b))) :
    StrongTimeRegularity a b (fun t => Complex.exp (∫ r in a..t, lam r))
      (fun t => Complex.exp (∫ r in a..t, lam r) * lam t) ∧
    MemLp (fun t => Complex.exp (∫ r in a..t, lam r) * lam t) ⊤
      (volume.restrict (Icc a b)) := by
  have hi : IntervalIntegrable lam volume a b := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hab]
    exact (hlam.integrable (by simp)).mono_measure
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hp := complexPrimitivePhase_strongTime hab lam hi
  have hm := hp.complex_memLp_top hab
  refine ⟨hp, ?_⟩
  have hprod : MemLp ((fun t => Complex.exp (∫ r in a..t, lam r)) * lam) ⊤
      (volume.restrict (Icc a b)) := hm.mul hlam
  simpa only [Pi.mul_def] using hprod

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Weighted high-order monomial increments gain two full frequency powers. -/

theorem fibreMonomial_high_increment_bound (ξ ζ : Fin 2 → ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M) (hMR : M ≤ R / 2)
    (hξ : fibreNorm ξ ≤ M) (hζ : fibreNorm ζ ≤ M)
    (p : ℕ × ℕ) (hp : 3 ≤ p.1 + p.2) :
    ‖fibreMonomial ξ p - fibreMonomial ζ p‖ ≤
      (3 * M ^ 2 / R ^ 3) * R ^ (p.1 + p.2) * fibreNorm (fun j => ξ j - ζ j) :=
  (fibreMonomial_increment_bound ξ ζ M hM hξ hζ p).trans
    (mul_le_mul_of_nonneg_right
      (scalar_high_power_increment_bound R M hR hM hMR _ hp) (fibreNorm_nonneg _))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.CycleEvolution

/-! Linear algebra of periodic raw weak jets, proved using genuine local integrability. -/

/-- Compactly supported smooth tests pair integrably with every periodic weak-jet coordinate. -/
theorem cellPeriodicJet_test_integrable {K : ℕ} {D : RawJet2 K ℂ}
    (hD : HasPeriodicOrderedWeakJet D) (a : JetIndex2 K) (e : ℂ)
    (φ : Vec 2 → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => inner ℝ e (D a x) * φ x) volume := by
  simpa only [smul_eq_mul] using
    (periodicJet_scalar_locallyIntegrable hD a e).integrable_smul_right_of_hasCompactSupport hφ hc

/-- Periodic raw weak jets are closed under addition. -/
theorem cellPeriodicWeakJet_add {K : ℕ} {D E : RawJet2 K ℂ}
    (hD : HasPeriodicOrderedWeakJet D) (hE : HasPeriodicOrderedWeakJet E) :
    HasPeriodicOrderedWeakJet (D + E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a n x
    change D a (x + AVenhance.latticeShift n) + E a (x + AVenhance.latticeShift n) = _
    rw [hD.1 a n x, hE.1 a n x]
    rfl
  · intro a
    exact (hD.2.1 a).add (hE.2.1 a)
  · intro j w i e φ hφ hc hsub
    have hdc : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdcompact := hc.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hD0 := cellPeriodicJet_test_integrable hD (lowerIndex2 j w) e _ hdc hdcompact
    have hE0 := cellPeriodicJet_test_integrable hE (lowerIndex2 j w) e _ hdc hdcompact
    have hD1 := cellPeriodicJet_test_integrable hD (nextIndex2 j w i) e φ hφ.continuous hc
    have hE1 := cellPeriodicJet_test_integrable hE (nextIndex2 j w i) e φ hφ.continuous hc
    have hd := hD.2.2 j w i e φ hφ hc hsub
    have he := hE.2.2 j w i e φ hφ hc hsub
    simp only [Pi.add_apply, inner_add_right, add_mul, Measure.restrict_univ] at hd he ⊢
    rw [integral_add hD0 hE0, integral_add hD1 hE1, hd, he]
    ring

/-- Periodic raw weak jets are closed under real scaling. -/
theorem cellPeriodicWeakJet_smul {K : ℕ} {D : RawJet2 K ℂ}
    (hD : HasPeriodicOrderedWeakJet D) (r : ℝ) :
    HasPeriodicOrderedWeakJet (r • D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a n x
    change r • D a (x + AVenhance.latticeShift n) = r • D a x
    rw [hD.1 a n x]
  · intro a
    exact (hD.2.1 a).const_smul r
  · intro j w i e φ hφ hc hsub
    have hd := hD.2.2 j w i e φ hφ hc hsub
    simp only [Pi.smul_apply, real_inner_smul_right, Measure.restrict_univ] at hd ⊢
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_const_mul, hd]
    ring

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Coordinate projections identify absolutely convergent raw gradient series. -/

/-- For a summable gradient family, the gradient of the literal raw series is its vector series. -/
theorem cellGradient_tsum_of_summable {J : Type*} [Countable J]
    (D : J → RawJet2 1 ℂ) (x : Vec 2)
    (hs : Summable (fun j => cellGradient (D j) x)) :
    cellGradient (fun a y => ∑' j, D j a y) x = ∑' j, cellGradient (D j) x := by
  apply WithLp.ofLp_injective
  funext k
  have he := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) k).map_tsum hs
  exact he.symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.Classical
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.CycleEvolution

/-! Smooth scalar periodic tests for the weak divergence-free cell drift condition.
Uses the upstream ordered-derivative calculus and the weak-jet lift. -/

/-- A smooth scalar function and its first derivatives as an ordered raw jet. -/
def cellSmoothScalarJet (q : Vec 2 → ℝ) : RawJet2 1 ℝ :=
  fun a => classicalWordDerivative (smoothLiftWord a.1.val a.2) q

/-- The smooth scalar jet is a genuine periodic weak H¹ jet. -/
theorem cellSmoothScalarJet_periodicWeak (q : Vec 2 → ℝ)
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) (hp : AVenhance.IsZ2Periodic q) :
    HasPeriodicOrderedWeakJet (cellSmoothScalarJet q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact GalerkinGenerator.classicalWordDerivative_periodic _ q hp
  · intro a
    exact weak_continuous_memL2On
      (GalerkinGenerator.classicalWordDerivative_smooth _ q hq).continuous
  · intro j w i e
    fin_cases j
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    have hq1 := ((contDiff_const : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : Vec 2 => e)).mul hq).of_le (show (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by simp)
    have hweak := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := i) hq1
    have hder (x : Vec 2) : fderiv ℝ (fun y => e * q y) x (basisVec i) =
        e * AVenhance.spaceGrad q x i := by
      rw [fderiv_const_mul (hq.differentiable (by simp) x)]
      rfl
    intro φ hφ hc hs
    change (∫ x in Set.univ, q x * e * fderiv ℝ φ x (basisVec i)) =
      -∫ x in Set.univ, AVenhance.spaceGrad q x i * e * φ x
    simpa only [hder, mul_comm] using hweak φ hφ hc hs

/-- The raw smooth test, bundled for the public weak divergence-free condition. -/
def cellSmoothScalarH1 (q : Vec 2 → ℝ) (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q)
    (hp : AVenhance.IsZ2Periodic q) : TorusHkFunction 1 ℝ :=
  ⟨cellSmoothScalarJet q, cellSmoothScalarJet_periodicWeak q hq hp⟩

/-- Weakly divergence-free bounded cell drifts annihilate smooth periodic scalar transport. -/
theorem cellDrift_smooth_transport_zero {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (t : ℝ) (q : Vec 2 → ℝ) (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q)
    (hp : AVenhance.IsZ2Periodic q) :
    (∫ x in AVenhance.unitCube, ∑ k : Fin 2, v t x k * AVenhance.spaceGrad q x k) = 0 := by
  simpa only [cellSmoothScalarH1, cellSmoothScalarJet, smoothLiftWord,
    classicalWordDerivative, Fin.snoc_last] using hv.2.2.2 t (cellSmoothScalarH1 q hq hp)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Energy neutrality of bounded weakly divergence-free drifts for smooth cell fields.
The transport-cancellation argument, with the public weak drift predicate. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A weakly divergence-free cell drift does no work on a smooth periodic Hilbert field. -/
theorem cellDrift_smooth_energy_zero {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (t : ℝ) (u : Vec 2 → E) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (hp : AVenhance.IsZ2Periodic u) :
    (∫ x in AVenhance.unitCube, ∑ k : Fin 2,
      v t x k * inner ℝ (fderiv ℝ u x (basisVec k)) (u x)) = 0 := by
  let q := fun x => inner ℝ (u x) (u x)
  have hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q := hu.inner ℝ hu
  have hqp : AVenhance.IsZ2Periodic q := fun n x => by dsimp [q]; rw [hp n x]
  have hder (x : Vec 2) (k : Fin 2) :
      AVenhance.spaceGrad q x k = 2 * inner ℝ (fderiv ℝ u x (basisVec k)) (u x) := by
    change fderiv ℝ q x (basisVec k) = _
    rw [fderiv_inner_apply ℝ (hu.differentiable (by simp) x) (hu.differentiable (by simp) x),
      real_inner_comm (u x)]
    ring
  have hz := cellDrift_smooth_transport_zero hv t q hq hqp
  have he : (fun x => ∑ k : Fin 2, v t x k * AVenhance.spaceGrad q x k) =
      fun x => 2 * ∑ k : Fin 2, v t x k * inner ℝ (fderiv ℝ u x (basisVec k)) (u x) := by
    funext x
    simp_rw [hder, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, integral_const_mul] at hz
  linarith

end AVRegularity.CycleEvolution
end
