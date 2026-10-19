-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.TorusOrderedGradientTensor
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleReference.CorrectorMeanGeometry
import AVRegularity.CycleReference.SingleModeFlux
import AVenhance.Infra.Section3.CorrectorGradient
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.TestDriftIntegrability
public import AVRegularity.Definitions.CycleWords.CoreScalarPackage
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The genuine higher torus norm consists of its value and all preceding ordered gradients. -/

theorem torusHigher_norm_sq_eq_value_gradient (q : ℕ) (U : TorusHk (q + 1) ℂ) :
    ‖U‖ ^ 2 = ‖torusHkValueCLM U‖ ^ 2 +
      ∑ r : Fin (q + 1), ∑ w : DerivativeWord2 r.val, ∑ i : Fin 2,
        ‖cellDerivativeCLM i (derivativeTorusHk (K := 1) w
          (truncateTorusHk (by omega : 1 + r.val ≤ q + 1) U))‖ ^ 2 := by
  change ‖U.val‖ ^ 2 = _
  rw [jet_norm_sq_eq_sum, Fin.sum_univ_succ]
  congr 1
  · change (∑ w : DerivativeWord2 0, ‖U.val ⟨⟨0, by omega⟩, w⟩‖ ^ 2) = _
    let : Unique (DerivativeWord2 0) := ⟨⟨Fin.elim0⟩, fun w => funext (fun i => Fin.elim0 i)⟩
    rw [Fintype.sum_unique]
    rfl
  · apply Finset.sum_congr rfl
    intro r _
    rw [← torusOrdered_gradient_tensor_sq]
    simp only [derivativeNormSq, truncateTorusHk_apply, truncateJetIndex]
    rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Native higher jet bounds control the classical cell Sobolev norm of any smooth representative. -/

theorem torusHigher_smooth_word_enorm_le {K : ℕ} (U : TorusHk K ℂ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (K : ℕ∞) f)
    (hv : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f)
    (a : JetIndex2 K) : cellL2Norm (orderedDerivative a.2 f) ≤ ‖U‖ₑ := by
  have he : cellL2Norm (orderedDerivative a.2 f) = ‖U.val a‖ₑ := by
    rw [Lp.enorm_def, cellL2Norm]
    exact (eLpNorm_congr_ae (torusHigher_smooth_local_readout U f hf hv a)).symm
  rw [he]
  exact PiLp.enorm_apply_le U.val a

theorem torusHigher_smooth_derivative_enorm_le {K : ℕ} (U : TorusHk K ℂ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (K : ℕ∞) f)
    (hv : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f)
    (b : ℕ) (hb : b ≤ K) :
    cellL2Norm (fun x => ‖iteratedFDeriv ℝ b f x‖) ≤
      (Fintype.card (DerivativeWord2 b) : ℝ≥0∞) * ‖U‖ₑ := by
  have hfb : ContDiff ℝ (b : ℕ∞) f := hf.of_le (by exact_mod_cast hb)
  have hm : AEStronglyMeasurable (fun x => ‖iteratedFDeriv ℝ b f x‖)
      (volume.restrict AVenhance.unitCube) := (ContDiff.continuous_iteratedFDeriv' hfb).norm.aestronglyMeasurable.restrict
  have hpoint : ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      ‖iteratedFDeriv ℝ b f x‖ ≤ ∑ w : DerivativeWord2 b, ‖orderedDerivative w f x‖ := Filter.Eventually.of_forall
    (fun x => ChartTransport.norm_iteratedFDeriv_le_sum_words hfb x)
  have hmono := eLpNorm_mono_ae_real (p := (2 : ℝ≥0∞))
    (g := fun x => ∑ w : DerivativeWord2 b, ‖orderedDerivative w f x‖) hm
    (by simpa only [norm_norm] using hpoint)
  have hsum := eLpNorm_sum_le (p := (2 : ℝ≥0∞))
    (μ := volume.restrict AVenhance.unitCube)
    (f := fun w : DerivativeWord2 b => fun x => ‖orderedDerivative w f x‖)
    (s := Finset.univ) (by norm_num)
  have he : (∑ w : DerivativeWord2 b, fun x => ‖orderedDerivative w f x‖) =
      (fun x => ∑ w : DerivativeWord2 b, ‖orderedDerivative w f x‖) := by
    funext x
    exact Finset.sum_apply x Finset.univ (fun w => fun y => ‖orderedDerivative w f y‖)
  rw [he] at hsum
  have hn (w : DerivativeWord2 b) :
      eLpNorm (fun x => ‖orderedDerivative w f x‖) 2 (volume.restrict AVenhance.unitCube) ≤ ‖U‖ₑ := by
    rw [eLpNorm_norm _ ((orderedDerivative_contDiff w 0 f
      (by simpa only [zero_add] using hfb)).continuous.aestronglyMeasurable.restrict)]
    exact torusHigher_smooth_word_enorm_le U f hf hv ⟨⟨b, by omega⟩, w⟩
  exact (hmono.trans hsum).trans ((Finset.sum_le_sum (fun w _ => hn w)).trans_eq
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]))

theorem torusHigher_smooth_cellSobolevNorm_le {K : ℕ} (U : TorusHk K ℂ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (K : ℕ∞) f)
    (hv : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f) :
    cellSobolevNorm K f ≤
      (∑ b ∈ Finset.range (K + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) * ‖U‖ₑ := by
  unfold cellSobolevNorm
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun b hb =>
    torusHigher_smooth_derivative_enorm_le U f hf hv b (Nat.le_of_lt_succ (Finset.mem_range.mp hb)))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Pointwise size of the literal transverse shear. -/

theorem ocShearVel_component_abs_le {α q : ℝ} {Λ m : ℕ} {k : ℤ}
    (hk : Odd k) (y : Vec 2) (j : Fin 2) :
    |ocShearVel α q Λ m k y j| ≤
      |2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) * (ocEpsilon q Λ m)⁻¹| := by
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · rw [CycleReference.ocShearVel_horizontal h1]
    fin_cases j
    · change |(0 : ℝ)| ≤ _
      simpa only [abs_zero] using (abs_nonneg (2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) * (ocEpsilon q Λ m)⁻¹))
    · dsimp
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · rw [CycleReference.ocShearVel_vertical h3]
    fin_cases j
    · dsimp
      rw [abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · change |(0 : ℝ)| ≤ _
      simpa only [abs_zero] using (abs_nonneg (2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) * (ocEpsilon q Λ m)⁻¹))

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The physical radius pays every derivative of a polynomial metric insertion. -/

theorem homogeneousPolynomial_scaled_jet_budget (r J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) ℝ,
      ∀ (ϖ ρ : ℝ), 0 ≤ ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 → ∀ j ≤ J, ∀ z : Vec 2,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => a (fun _ => ϖ • z)) z‖ ≤
          C * ‖a‖ * polynomialMomentRoot ϖ z ^ r := by
  obtain ⟨C, hC, hb⟩ := homogeneousPolynomial_jet_budget r J
  refine ⟨C * 2 ^ r, by positivity, ?_⟩
  intro a ϖ ρ hϖ hρ hscale j hj z
  let p := fun z : Vec 2 => a (fun _ => z)
  have hp : ContDiff ℝ (j : ℕ) p := by
    simpa only [one_smul] using
      Weighted.multilinear_diagonal_contDiff j (fun _ => a) contDiff_const 1
  have hd := congrFun (iteratedFDeriv_comp_const_smul ϖ hp) z
  have hroot : 1 + ‖ϖ • z‖ ≤ 2 * polynomialMomentRoot ϖ z := by
    rw [norm_smul, Real.norm_of_nonneg hϖ]
    linarith [polynomialMomentRoot_one_le ϖ z, scaledNorm_le_polynomialMomentRoot hϖ z]
  have hrad : (ρ * ϖ) ^ j ≤ 1 := pow_le_one₀ (mul_nonneg hρ hϖ) hscale
  change ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => p (ϖ • z)) z‖ ≤ _
  rw [hd, norm_smul, Real.norm_of_nonneg (pow_nonneg hϖ j)]
  calc
    _ = (ρ * ϖ) ^ j * ‖iteratedFDeriv ℝ j p (ϖ • z)‖ := by rw [mul_pow]; ring
    _ ≤ ‖iteratedFDeriv ℝ j p (ϖ • z)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hrad (norm_nonneg _)
    _ ≤ C * ‖a‖ * (1 + ‖ϖ • z‖) ^ r := hb a j hj (ϖ • z)
    _ ≤ C * ‖a‖ * (2 * polynomialMomentRoot ϖ z) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hroot r) (mul_nonneg hC (norm_nonneg _))
    _ = _ := by rw [mul_pow]; ring

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! First spatial derivatives of the literal shear. -/

theorem cosCoordinate_gradient_abs_le (A ω : ℝ) (r i : Fin 2) (y : Vec 2) :
    |fderiv ℝ (fun x : Vec 2 => A * Real.cos (ω * x r)) y (basisVec i)| ≤ |A * ω| := by
  have hh : fderiv ℝ (fun x : Vec 2 => A * Real.cos (ω * x r)) y (basisVec i) =
      if i = r then -A * ω * Real.sin (ω * y r) else 0 :=
    AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate A ω r i y
  rw [hh]
  split_ifs
  · rw [abs_mul, abs_mul, abs_neg, abs_mul]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg A) (abs_nonneg ω)) (Real.abs_sin_le_one _)
  · simpa only [abs_zero] using abs_nonneg (A * ω)

theorem ocShearVel_gradient_abs_le {α q : ℝ} {Λ m : ℕ} {k : ℤ}
    (hk : Odd k) (y : Vec 2) (j i : Fin 2) :
    |fderiv ℝ (fun x => ocShearVel α q Λ m k x j) y (basisVec i)| ≤
      |(2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) *
        (2 * Real.pi * (ocEpsilon q Λ m)⁻¹)| := by
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · have he := funext (fun x => congrFun
      (CycleReference.ocShearVel_horizontal (α := α) (q := q) (Λ := Λ) (m := m) h1 x) j)
    rw [he]
    fin_cases j
    · dsimp
      change |fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) y (basisVec i)| ≤ _
      rw [fderiv_const_apply, zero_apply, abs_zero]
      exact abs_nonneg _
    · exact cosCoordinate_gradient_abs_le _ _ _ _ _
  · have he := funext (fun x => congrFun
      (CycleReference.ocShearVel_vertical (α := α) (q := q) (Λ := Λ) (m := m) h3 x) j)
    rw [he]
    fin_cases j
    · dsimp
      have hh := cosCoordinate_gradient_abs_le
        (-(2 * Real.pi * (ocEpsilon q Λ m) ^ (1 + α) * (ocEpsilon q Λ m)⁻¹))
        (2 * Real.pi * (ocEpsilon q Λ m)⁻¹) 1 i y
      simpa only [neg_mul, abs_neg] using hh
    · dsimp
      change |fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) y (basisVec i)| ≤ _
      rw [fderiv_const_apply, zero_apply, abs_zero]
      exact abs_nonneg _

/-! A shear has no derivative along its own velocity. -/

theorem ocShearVel_self_transport_zero {α q : ℝ} {Λ m : ℕ} {k : ℤ}
    (hk : Odd k) (y : Vec 2) (j : Fin 2) :
    (∑ i : Fin 2, ocShearVel α q Λ m k y i *
      fderiv ℝ (fun z => ocShearVel α q Λ m k z j) y (basisVec i)) = 0 := by
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · have he := funext (fun z => congrFun (CycleReference.ocShearVel_horizontal
      (α := α) (q := q) (Λ := Λ) (m := m) h1 z) j)
    rw [he, Fin.sum_univ_two, CycleReference.ocShearVel_horizontal h1 y]
    fin_cases j <;> dsimp
    · simp
    · change 0 * _ + _ * spaceGrad (fun z : Vec 2 => _ * Real.cos (_ * z 0)) y 1 = 0
      rw [AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
      simp
  · have he := funext (fun z => congrFun (CycleReference.ocShearVel_vertical
      (α := α) (q := q) (Λ := Λ) (m := m) h3 z) j)
    rw [he, Fin.sum_univ_two, CycleReference.ocShearVel_vertical h3 y]
    fin_cases j <;> dsimp
    · change _ * spaceGrad (fun z : Vec 2 => _ * Real.cos (_ * z 1)) y 0 + 0 * _ = 0
      rw [AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
      simp
    · simp

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! A homogeneous metric degree retains its geometric ratio in every normalized jet. -/

theorem geometricHomogeneousPolynomial_jet_budget (r J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) ℝ,
      ∀ (ϖ ρ δ ζ M g : ℝ), 0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → 0 ≤ M → 0 ≤ g → δ = ζ * ϖ → ‖a‖ ≤ M * g * δ ^ r →
      ∀ j ≤ J, ∀ z : Vec 2,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => a (fun _ => z)) z‖ ≤
          C * M * g * ζ ^ r * polynomialMomentRoot ϖ z ^ r := by
  obtain ⟨C, hC, hb⟩ := homogeneousPolynomial_scaled_jet_budget r J
  refine ⟨C, hC, ?_⟩
  intro a ϖ ρ δ ζ M g hϖ hρ hscale hζ hM hg hδ ha j hj z
  let a' := (ϖ ^ r)⁻¹ • a
  have he : (fun z : Vec 2 => a' (fun _ => ϖ • z)) = (fun z => a (fun _ => z)) := by
    funext z
    change (ϖ ^ r)⁻¹ • a (fun _ => ϖ • z) = a (fun _ => z)
    rw [a.map_smul_univ (fun _ => ϖ) (fun _ => z)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero r hϖ.ne'), one_smul]
  have ha' : ‖a'‖ ≤ M * g * ζ ^ r := by
    dsimp only [a']
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hϖ.le r))]
    apply (mul_le_mul_of_nonneg_left ha (by positivity)).trans_eq
    rw [hδ, mul_pow]
    field_simp
  have hh := hb a' ϖ ρ hϖ.le hρ hscale j hj z
  rw [he] at hh
  apply hh.trans
  have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha' hC)
    (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) r)
  convert ht using 1; ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! The literal future pulse memory, including its early quiet tail. -/

def adjointPulseMemory (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν : ℝ) (k : ℤ) : ℝ → ℝ :=
  futureMemory (ocMu q Λ m ν) (ocPulse α q Λ ζ m k)

theorem adjointPulseMemory_hasDerivAt {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (t : ℝ) :
    HasDerivAt (adjointPulseMemory α q Λ ζ m ν k)
      (ocMu q Λ m ν * adjointPulseMemory α q Λ ζ m ν k t - ocPulse α q Λ ζ m k t) t :=
  futureMemory_hasDerivAt _ _ (CycleReference.ocPulse_continuous hζ k)
    (CycleReference.ocPulse_hasCompactSupport hΛ hζ k) t

theorem adjointPulseMemory_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (n : ℕ) :
    ContDiff ℝ n (adjointPulseMemory α q Λ ζ m ν k) :=
  futureMemory_contDiff_nat _ _ (CycleReference.ocPulse_contDiff hζ k)
    (CycleReference.ocPulse_hasCompactSupport hΛ hζ k) n

theorem adjointPulseMemory_range {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (k : ℤ) (t : ℝ) :
    0 ≤ adjointPulseMemory α q Λ ζ m ν k t ∧
      adjointPulseMemory α q Λ ζ m ν k t ≤ (ocMu q Λ m ν)⁻¹ := by
  have hμ : 0 < ocMu q Λ m ν := by
    unfold ocMu
    have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
    positivity
  exact ⟨futureMemory_nonneg _ _ (fun s => (CycleReference.ocPulse_range hζ k s).1) t,
    futureMemory_le_inv hμ _ (CycleReference.ocPulse_continuous hζ k)
      (CycleReference.ocPulse_hasCompactSupport hΛ hζ k)
      (fun s => (CycleReference.ocPulse_range hζ k s).2) t⟩

theorem adjointPulseMemory_early_tail {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (k : ℤ) (t : ℝ) (ht : t ≤ ((k : ℝ) - 3 / 4) * ocTau α q Λ m) :
    adjointPulseMemory α q Λ ζ m ν k t ≤
      Real.exp (-ocMu q Λ m ν * (ocTau α q Λ m / 12)) * (ocMu q Λ m ν)⁻¹ := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hμ : 0 < ocMu q Λ m ν := by
    unfold ocMu
    have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
    positivity
  apply futureMemory_delay_bound hμ _ (CycleReference.ocPulse_continuous hζ k)
    (CycleReference.ocPulse_hasCompactSupport hΛ hζ k)
    (fun s => (CycleReference.ocPulse_range hζ k s).2) t (ocTau α q Λ m / 12)
    (by positivity)
  intro s hs
  by_contra hne
  have hh := (CycleReference.pulse_nonzero_center_distance hΛ hζ hne).1
  nlinarith only [ht, hs.2, hh]

/-! The late cutoff contributes no adjoint residual; the early cutoff has the true quiet tail. -/

theorem adjointPulseMemory_zero_after {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (t : ℝ)
    (ht : ((k : ℝ) + 2 / 3) * ocTau α q Λ m ≤ t) :
    adjointPulseMemory α q Λ ζ m ν k t = 0 := by
  unfold adjointPulseMemory futureMemory
  have hz : (∫ s in Set.Ici t, ocPulse α q Λ ζ m k s * Real.exp (-ocMu q Λ m ν * s)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    have hp : ocPulse α q Λ ζ m k s = 0 := by
      by_contra hne
      have hh := (CycleReference.pulse_nonzero_center_distance hΛ hζ hne).2
      have hs' : t ≤ s := hs
      linarith
    rw [hp, zero_mul]
  rw [hz, mul_zero]

theorem adjointPulseMemory_cutoff_derivative_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ k t, |deriv (ocCutoff α q Λ m k) t| ≤ K / ocTau α q Λ m)
    (k : ℤ) (t : ℝ) :
    |deriv (ocCutoff α q Λ m k) t * adjointPulseMemory α q Λ ζ m ν k t| ≤
      (K / ocTau α q Λ m) *
        (Real.exp (-ocMu q Λ m ν * (ocTau α q Λ m / 12)) * (ocMu q Λ m ν)⁻¹) := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hμ : 0 < ocMu q Λ m ν := by
    unfold ocMu
    have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
    positivity
  by_cases hd : deriv (ocCutoff α q Λ m k) t = 0
  · rw [hd, zero_mul, abs_zero]
    positivity
  · have hs := CycleReference.cutoff_derivative_nonzero_distance hΛ k t hd
    rcases lt_abs.mp hs.1 with hr | hl
    · rw [adjointPulseMemory_zero_after hΛ hζ ν k t (by nlinarith only [hr, hτ]),
        mul_zero, abs_zero]
      positivity
    · rw [abs_mul, abs_of_nonneg (adjointPulseMemory_range hΛ hζ hν k t).1]
      apply mul_le_mul (hb k t)
        (adjointPulseMemory_early_tail hΛ hζ hν k t (by nlinarith only [hl]))
        (adjointPulseMemory_range hΛ hζ hν k t).1 (div_nonneg hK hτ.le)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual singleton chain separates into its scalar metric and literal sampled source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem geometryActualCoefficient_split (D : ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (edge : ConstituentEdges D h)
    (X0 : Vec 2) (δ : ℝ) (κ : Fin 1 → ι → ℕ)
    (i i' : Fin 1 × ι) (d : admissibleOrders (fun p => κ p.1 p.2) D i i')
    (t : ℝ) (z : Vec 2) :
    planeChainCoefficient (geometryActualData G edge X0 δ) κ i i' d t z =
      planeChainCoefficient (geometryScalarData D G) κ i i' d t z +
        slowEvalCoefficient (fun f z => f (X0 + δ • z))
          (edge i.2 i'.2 ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) t z := by
  classical
  have hj : i.1 = i'.1 := Subsingleton.elim _ _
  simp [planeChainCoefficient, geometryActualData, geometryScalarData, hj, slowEvalCoefficient]

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! Exact bounds and adjacent endpoints of the cell-time preparation pieces. -/

theorem ocPieceStart_global_lower (α q : ℝ) (Λ m : ℕ) (ν ta : ℝ) (l : ℤ)
    (hell : 0 < ocEll q Λ m ν ^ 2) :
    ta / ocEll q Λ m ν ^ 2 ≤ ocPieceStart α q Λ m ν ta l := by
  exact div_le_div_of_nonneg_right (le_max_left _ _) hell.le

theorem ocPieceEnd_global_upper (α q : ℝ) (Λ m : ℕ) (ν ta T : ℝ) (l : ℤ)
    (hell : 0 < ocEll q Λ m ν ^ 2) :
    ocPieceEnd α q Λ m ν ta T l ≤ (ta + T) / ocEll q Λ m ν ^ 2 := by
  exact div_le_div_of_nonneg_right (min_le_left _ _) hell.le

theorem ocPiece_interval_subset (α q : ℝ) (Λ m : ℕ) (ν ta T : ℝ) (l : ℤ)
    (hell : 0 < ocEll q Λ m ν ^ 2) :
    Set.Icc (ocPieceStart α q Λ m ν ta l) (ocPieceEnd α q Λ m ν ta T l) ⊆
      Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) := by
  intro t ht
  exact ⟨(ocPieceStart_global_lower α q Λ m ν ta l hell).trans ht.1,
    ht.2.trans (ocPieceEnd_global_upper α q Λ m ν ta T l hell)⟩

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.CycleWords

/-! The response coefficient separates the frozen metric, same-level Taylor source, and previous-level insertion. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem geometryResponseCoefficient_split (D J K : ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (edge : ConstituentEdges D h)
    (X0 : Vec 2) (δ : ℝ) (κ : ι → ℕ) (j j' : Fin (J + 1)) (v u : ι)
    (d : admissibleOrders κ D v u) (t : ℝ) (z : Vec 2) :
    planeChainCoefficient (geometryResponseData J K G 0 edge X0 δ) (fun _ v => κ v)
      (j, v) (j', u) d t z =
      (if j = j' then
        planeChainCoefficient (geometryScalarData D (fun t _ => G t 0)) (fun _ v => κ v)
          (0, v) (0, u) d t z +
        slowEvalCoefficient (fun f z => taylorSlow 0 K f X0 (δ • z))
          (edge v u ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) t z else 0) +
      (if j.val = j'.val + 1 then
        (if hv : v = u ∧ d.1 = 2 then
          metricFlux (metricTaylor 1 K G t 0 z) (d.1 - 1) hv.1 (by omega) else 0) else 0) := by
  classical
  simp [planeChainCoefficient, geometryResponseData, geometryScalarData, slowEvalCoefficient]

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Scalar geometry coefficients at an arbitrary reserved order are zero except at order two. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem geometryScalarCoefficient_offDiagonal (D : ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (i i' : Fin 1 × ι) (hi : i.2 ≠ i'.2)
    (d : admissibleOrders (fun p => κ p.1 p.2) D i i') (t : ℝ) (z : Vec 2) :
    planeChainCoefficient (geometryScalarData (h := h) D G) κ i i' d t z = 0 := by
  have hlevel : i.1 = i'.1 := Subsingleton.elim _ _
  simp [planeChainCoefficient, geometryScalarData, slowEvalCoefficient, hlevel, hi]

theorem geometryScalarCoefficient_otherOrder (D : ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (i i' : Fin 1 × ι) (d : admissibleOrders (fun p => κ p.1 p.2) D i i')
    (hd : d.val ≠ 2) (t : ℝ) (z : Vec 2) :
    planeChainCoefficient (geometryScalarData (h := h) D G) κ i i' d t z = 0 := by
  have hlevel : i.1 = i'.1 := Subsingleton.elim _ _
  simp [planeChainCoefficient, geometryScalarData, slowEvalCoefficient, hlevel, hd]

theorem geometryScalarCoefficient_diagonal (D : ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (i : Fin 1 × ι) (d : admissibleOrders (fun p => κ p.1 p.2) D i i)
    (hd : d.val = 2) (t : ℝ) (z : Vec 2) :
    planeChainCoefficient (geometryScalarData (h := h) D G) κ i i d t z =
      metricFlux (h := h) (G t z - 1) (d.val - 1) (a := i.2) rfl (by omega) := by
  simp [planeChainCoefficient, geometryScalarData, slowEvalCoefficient, hd]

end AVRegularity.CycleWords
end
