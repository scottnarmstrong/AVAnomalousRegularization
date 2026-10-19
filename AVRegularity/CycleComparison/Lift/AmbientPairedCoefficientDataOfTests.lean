-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.FibreCoefficientConvolutionSum
import AVRegularity.CycleComparison.Lift.DiagonalMeanLeftTermsActionOfCoefficients
public import AVRegularity.CycleComparison.Lift.ComplexDualProfileFourierData
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Lift.SettingAmbientCrossTestTransverse
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual first cross operator on a lift test raises its cell degree by one. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalizedCellB1_scaled_drift_lift_test_grading (n p q : ℕ) (η lam M W B : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hW : 0 ≤ W) (hB : 0 ≤ B)
    (A : Vec 2 →L[ℝ] ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (drift : ℝ → Vec 2 → Vec 2) (t : ℝ) (c : LiftCoeff ι h) (v u : ι) (ξ : h u)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v' u',
      IsBoxSmooth (p + 1) (q + 1) (fun X z => c m α t X z v' u'))
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun X (_ : Vec 2) => G t X i j))
    (hv : ∀ k, IsBoxSmooth p q (fun (_ : Vec 2) z => drift t z k)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbv : ∀ k, ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun (_ : Vec 2) => iteratedFDeriv ℝ b
        (fun y => Real.sqrt η * drift t y k) z) X‖ ≤ W * lam ^ a)
    (hbc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => c m α t Y y v u) z) X‖ ≤ B * lam ^ (n - m + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB1 η G drift t
        (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      (normalizedCellB1UniformConstant p q A M W * finiteLiftSymbolBudget n A * B * ‖ξ‖) *
        lam ^ ((n + 1) + r) := by
  let F := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t Y y
  have hf : IsBoxSmooth (p + 1) (q + 1) F := by
    apply isBoxSmooth_pi (p + 1) (q + 1) F
    intro w
    exact normalized_lift_test_box_reserve n (p + 1) (q + 1) c lam A t w u ξ
      (fun m hm α => hc m hm α w u)
  have hb : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun w => F Y w v) y) X‖ ≤
        (finiteLiftSymbolBudget n A * B * ‖ξ‖) * lam ^ (n + a) := by
    intro a ha b hb y
    have hh := normalized_lift_test_mixed_grading n a b c lam B hlam A t v u ξ
      (fun m hm α => (hc m hm α v u).mono ha hb) X y
      (fun m hm α => hbc m hm α a ha b hb y)
    simpa only [F, Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm] using! hh
  have he : (fun Y y => Real.exp ((lam • A) Y) • F Y y) =
      liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t := by
    funext Y y
    dsimp only [F]
    rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  rw [← he]
  have hh := normalizedCellB1_scaled_drift_component_uniform_grading p q n η lam M W
    (finiteLiftSymbolBudget n A * B * ‖ξ‖) hη hlam hM hW
    (mul_nonneg (mul_nonneg (finiteLiftSymbolBudget_nonneg n A) hB) (norm_nonneg ξ))
    A G drift t F v hf hG hv X hbG hbv hb r s hr hs z
  simpa only [mul_assoc] using hh

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! The exact Fourier derivative identity in the H¹ carrier and its weak test pairing. -/

theorem transverseFourierModeH1_derivative (par : Fin 2) (n : ℤ) (j : Fin 2) :
    cellDerivativeCLM j (transverseFourierModeH1 par n) =
      cellScalarCLM (if j = par.rev then profileFourierFrequency n else 0)
        (torusHkValueCLM (transverseFourierModeH1 par n)) := by
  apply Lp.ext
  filter_upwards [transverseFourierModeH1_derivative_ae par n j,
    transverseFourierModeH1_value_ae par n,
    cellScalarCLM_ae (if j = par.rev then profileFourierFrequency n else 0)
      (torusHkValueCLM (transverseFourierModeH1 par n))] with z hd hv hs
  rw [hd, hs, hv]
  split_ifs <;> simp

theorem transverseFourierModeH1_weak_derivative (par : Fin 2) (n : ℤ)
    (j : Fin 2) (z : TorusHk 1 ℂ) :
    cellComplexPair (torusHkValueCLM (transverseFourierModeH1 par n)) (cellDerivativeCLM j z) =
      -(if j = par.rev then profileFourierFrequency n else 0) *
        cellComplexPair (torusHkValueCLM (transverseFourierModeH1 par n)) (torusHkValueCLM z) := by
  have h := cellComplexDerivative_skew j (transverseFourierModeH1 par n) z
  rw [transverseFourierModeH1_derivative, cellComplexPair_scalar_left] at h
  simpa only [neg_neg, neg_mul] using (congrArg Neg.neg h).symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The genuine mean operator inherits clamped time measurability from the actual uncentered source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, SecondCountableTopology (h i)] {D : ℕ}

theorem liftMean_clamped_normalized_measurable_of_liftA
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n p q : ℕ)
    (a b : ℝ) (hab : a ≤ b) (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ)
    (hbox : ∀ t ∈ Set.Icc a b, ∀ v, IsBoxSmooth p q
      (fun X z => (Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f hh n t X z v))
    (hm : ∀ v X z, Measurable (fun t => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n (Set.projIcc a b hab t) X z v)) (v : ι) (X : Vec 2) :
    Measurable (fun t => (Real.exp ((lam • A) X))⁻¹ •
      liftMean Q Cc f hh n (Set.projIcc a b hab t) X v) := by
  let F := fun t z => liftA Q Cc f hh n (Set.projIcc a b hab t) X z
  have hF (z : Vec 2) : Measurable (fun t => F t z) := by
    apply Measurable.of_eval
    intro u
    have he : (fun t => F t z u) = fun t => Real.exp ((lam • A) X) •
        ((Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f hh n (Set.projIcc a b hab t) X z u) := by
      funext t
      rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
    rw [he]
    exact (hm u X z).const_smul _
  have hFc (t : ℝ) : Continuous (F t) :=
    liftA_fast_continuous_of_normalized_box Q Cc f hh n p q _ A lam
      (hbox _ (Set.projIcc a b hab t).2) X
  have hmean := fieldCellMean_parameter_measurable F hF hFc
  exact ((measurable_pi_apply v).comp hmean).const_smul _

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Source-height powers survive the conversion to literal energy jets. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem physical_power_schurEnergyJet_le
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (edge : ι → ι → ℝ)
    (Θ : ℝ) (hΘ : 0 ≤ Θ) (hedge : HasRealSchurBudget edge Θ)
    (hh : ℕ) (B : ℝ) (hB : 0 ≤ B)
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {c : LiftCoeff ι h}
    (data : AmbientLiftCoefficientData par a b hab lam n p q c
      (fun v u => B * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
    (hlam : 0 ≤ lam) {m r fast : ℕ} (hm : m ≤ n) (hr : r ≤ p)
    (hfast : fast + 1 ≤ q) :
    schurEnergyJet π (Set.Icc a b) fast r (c m) ≤
      ENNReal.ofReal (((2 ^ m : ℝ) * (fast + 1) * 2 ^ (r + 1) * B) *
        Θ ^ hh * lam ^ (n - m + r)) := by
  have hmatrix := physicalEdgeEnvelopeMatrix_power_schur_budget π hπ edge Θ hΘ hedge hh
  have hscaled : HasRealSchurBudget
      (massConjugatedMatrix π
        (fun v u => B * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u))
      (B * Θ ^ hh) := by
    convert hmatrix.const_mul B hB using 1
    funext v u
    simp only [massConjugatedMatrix]
    ring
  exact (data.schurEnergyJet_le hlam hm hr hfast π (B * Θ ^ hh) hscaled).trans_eq (by
    congr 1
    ring)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVenhance.Infra.Torus AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Scalar-dual decay transfers to the literal two-dimensional cell coefficients. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complex_dual_transverse_fourier_parameter_data (p q r L : ℕ)
    (hr : r ≤ p) (hL : L + 2 ≤ q)
    (par : Fin 2) (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (ht : IsTransverseOn par Set.univ (fun _ : ℝ => f))
    (l : E →L[ℝ] ℝ)
    (hper : ∀ X, Function.Periodic
      (fun z : ℝ => ((l (f X (z • basisVec par.rev)) : ℝ) : ℂ)) 1)
    (C : ℕ → ℝ) (hb : ∀ a ≤ p, ∀ b ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C a)
    (k : Fin 2 → ℤ) :
    ContDiff ℝ (p : ℕ∞)
      (fun X => smoothFourierCoeff (fun z => ((l (f X z) : ℝ) : ℂ)) k) ∧
    (k par ≠ 0 → ∀ X, iteratedFDeriv ℝ r
      (fun Y => smoothFourierCoeff (fun z => ((l (f Y z) : ℝ) : ℂ)) k) X = 0) ∧
    (k par = 0 → k par.rev ≠ 0 → ∀ X,
      (1 + |(k par.rev : ℝ)|) ^ L * ‖iteratedFDeriv ℝ r
        (fun Y => smoothFourierCoeff (fun z => ((l (f Y z) : ℝ) : ℂ)) k) X‖ ≤
      profileJetMajorant (2 ^ r * (‖l‖ * C r)) 0 (k par.rev)) := by
  let line : ℝ →L[ℝ] Vec 2 := (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec par.rev)
  have hn : ‖line‖ = 1 := by simp [line, norm_basisVec]
  have hdata := complex_dual_profile_fourier_parameter_data p q r L hr hL f hf line hn
    l hper C hb (k par.rev)
  have he : (fun X => smoothFourierCoeff (fun z => ((l (f X z) : ℝ) : ℂ)) k) =
      fun X => if k par = 0 then
        unitProfileFourierCoeff (fun z => ((l (f X (line z)) : ℝ) : ℂ)) (k par.rev) else 0 := by
    funext X
    have hfield : (fun z => ((l (f X z) : ℝ) : ℂ)) =
        fun z => ((l (f X (z par.rev • basisVec par.rev)) : ℝ) : ℂ) := by
      funext z
      rw [transverse_profile_representation par Set.univ (fun _ : ℝ => f) ht 0
        (Set.mem_univ _) X z]
    rw [hfield]
    apply smoothFourierCoeff_transverse_profile_all par _ _ (hper X) k
    exact ((Complex.ofRealCLM.comp l).contDiff.comp ((hf.1 X).comp line.contDiff)).of_le
      (by exact_mod_cast (show 1 ≤ q by omega))
  rw [he]
  by_cases hk : k par = 0
  · simp only [hk, ite_true]
    exact ⟨hdata.1, fun h => False.elim (h rfl), fun _ hm X => hdata.2 hm X⟩
  · simp only [ite_eq_right hk]
    refine ⟨contDiff_const, fun _ X => ?_, fun h => False.elim (hk h)⟩
    simp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Each selected component of an actual normalized lift test solves the same scalar cell inverse. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_normalized_exponential_component_inverse (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (X : Vec 2) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b (fun _ => 0)
      (fun t z => (Real.exp (A X))⁻¹ •
        liftCellSource Q Cc (fun _ Y => Real.exp (A Y) • Pi.single u ξ) hh n t X z v)
      (fun t z => (Real.exp (A X))⁻¹ •
        liftApply n (Cc hh n) (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z v) := by
  have hi := liftSequence_normalized_exponential_inverse Q sX sZ a b N H Cc hc hh n hhh hn hnN A u ξ X
  have hp := cellFieldInverse_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) _ _ sZ hsZ a b _ _ _ hi
  simpa only [ContinuousLinearMap.proj_apply, Pi.smul_apply, Pi.zero_apply] using hp

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! Polynomial H¹ norm bounds for the actual promoted Fourier modes. -/

theorem transverseFourierModeH1_value_norm_le (par : Fin 2) (n : ℤ) :
    ‖torusHkValueCLM (transverseFourierModeH1 par n)‖ ≤ ‖cellConstantCLM 1‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [transverseFourierModeH1_value_ae par n, cellConstantCLM_ae 1] with z hv hc
  rw [hv, hc]
  simp only [transverseFourierMode, fourier_apply, Circle.norm_coe, norm_one, le_refl]

theorem transverseFourierModeH1_norm_le (par : Fin 2) (n : ℤ) :
    ‖transverseFourierModeH1 par n‖ ≤ ‖cellConstantCLM 1‖ * (1 + ‖profileFourierFrequency n‖) := by
  have hv := transverseFourierModeH1_value_norm_le par n
  have hh := cellH1_norm_sq (transverseFourierModeH1 par n)
  simp_rw [transverseFourierModeH1_derivative, cellScalarCLM_smul, norm_smul] at hh
  have he : ‖transverseFourierModeH1 par n‖ ^ 2 =
      (1 + ‖profileFourierFrequency n‖ ^ 2) *
        ‖torusHkValueCLM (transverseFourierModeH1 par n)‖ ^ 2 := by
    fin_cases par <;> simpa [Fin.sum_univ_two, add_mul, mul_pow] using hh
  have hsq := mul_le_mul_of_nonneg_left
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hv)
    (by positivity : 0 ≤ 1 + ‖profileFourierFrequency n‖ ^ 2)
  have hr := norm_nonneg (profileFourierFrequency n)
  have hC := norm_nonneg (cellConstantCLM 1)
  have hm := norm_nonneg (transverseFourierModeH1 par n)
  apply (sq_le_sq₀ hm (mul_nonneg hC (by positivity))).mp
  rw [he]
  apply hsq.trans
  nlinarith [mul_nonneg (sq_nonneg ‖cellConstantCLM 1‖) hr]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The actual cell response has fully mixed bounds with constants independent of the slow scale. -/

theorem profileCellResponse_graded_mixed_bound (p q δ r j : ℕ) (hr : r ≤ p) (hj : j ≤ q)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M lam κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ s ≤ p, ∀ t X, ‖iteratedFDeriv ℝ s (g t) X‖ ≤ M * lam ^ s)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → ℝ → ℂ)
    (hfm : ∀ X, Measurable (Function.uncurry (fun t z => f t X z)))
    (hff : ∀ t X, ContDiff ℝ (q : ℕ∞) (f t X))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ j ≤ q, ∀ t z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f t X) z))
    (S : ℕ → ℕ → ℝ) (hS : ∀ s ≤ p, ∀ i ≤ q, 0 ≤ S s i)
    (hfb : ∀ s ≤ p, ∀ i ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ s (fun Y => iteratedDeriv i (f t Y) z) X‖ ≤ S s i * lam ^ (δ + s))
    (hcenter : ∀ t X, unitProfileFourierCoeff (f t X) 0 = 0)
    (l : Vec 2 →L[ℝ] ℝ) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
      (fun y => profileCellResponse (fun t => g t Y) (fun t => f t Y) a b (l y)) z) X‖ ≤
      (‖l‖ ^ j * (parameterizedModeJetConstant p r M 1 κ
        (fun s => (2 : ℝ) ^ s * S s j) * centeredProfileJetConstant)) * lam ^ (δ + r) := by
  let S' := fun s i => S s i * lam ^ δ
  have hS' : ∀ s ≤ p, ∀ i ≤ q, 0 ≤ S' s i :=
    fun s hs i hi => mul_nonneg (hS s hs i hi) (pow_nonneg hlam δ)
  have hfb' : ∀ s ≤ p, ∀ i ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ s (fun Y => iteratedDeriv i (f t Y) z) X‖ ≤ S' s i * lam ^ s := by
    intro s hs i hi t z X
    simpa only [S', pow_add, mul_assoc] using hfb s hs i hi t z X
  have hi : ∀ X, IntegrableOn (fun t => g t X) (Icc a b) := by
    intro X
    apply (integrable_const M).mono' (hm X).aestronglyMeasurable
    exact ae_of_all _ (fun t => by simpa using hb 0 (Nat.zero_le p) t X)
  have hfast : ∀ i ≤ q, ∀ t X z, ‖iteratedDeriv i (f t X) z‖ ≤ S' 0 i := by
    intro i hi t X z
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using!
      hfb' 0 (Nat.zero_le p) i hi t z X
  have he (y : ℝ) :
      (fun Y => iteratedDeriv j (profileCellResponse (fun t => g t Y) (fun t => f t Y) a b) y) =
        fun Y => profileWeightedResponse (fun t => g t Y) (fun t => f t Y) a b y j := by
    funext Y
    exact profileCellResponse_fast_jet_identity (fun t => g t Y) (fun t => f t Y) a b κ hab hκ
      (hi Y) (fun t _ => hgl t Y) j (S' 0)
      (fun i hi => hS' 0 (Nat.zero_le p) i (hi.trans hj))
      (fun t _ => (hff t Y).of_le (by exact_mod_cast hj)) (fun t _ => hper t Y)
      (fun i hi t _ y _ => hfast i (hi.trans hj) t Y y) y
  have hres := profileWeightedResponse_graded_slow_dependent_reserve p j δ g hm hs
    M lam κ a b hM hlam hκ hab hb hgl f hfm
    (fun t Y => (hff t Y).of_le (by exact_mod_cast hj)) hper (hfs j hj)
    (fun s => S s j) (fun s hs => hS s hs j hj) (fun s hs => hfb s hs j hj) hcenter
  have hslow : ∀ y, ContDiff ℝ (p : ℕ∞) (fun Y => iteratedDeriv j
      (profileCellResponse (fun t => g t Y) (fun t => f t Y) a b) y) := by
    intro y
    rw [he y]
    exact hres.1 y
  have hresponse : ∀ Y, ContDiff ℝ (q : ℕ∞)
      (profileCellResponse (fun t => g t Y) (fun t => f t Y) a b) := by
    intro Y
    exact profileCellResponse_contDiff (fun t => g t Y) (fun t => f t Y) a b κ hab hκ (hi Y)
      (fun t _ => hgl t Y) q (S' 0) (hS' 0 (Nat.zero_le p))
      (fun t _ => hff t Y) (fun t _ => hper t Y)
      (fun i hi t _ y _ => hfast i hi t Y y)
  have hh := scalar_fast_mixed_jet_norm_le p q r j hr hj
    (fun Y => profileCellResponse (fun t => g t Y) (fun t => f t Y) a b) hresponse l z X (hslow (l z))
  apply hh.trans
  rw [he (l z)]
  calc
    _ ≤ ‖l‖ ^ j * ((parameterizedModeJetConstant p r M 1 κ
        (fun s => (2 : ℝ) ^ s * S s j) * centeredProfileJetConstant) * lam ^ (δ + r)) :=
      mul_le_mul_of_nonneg_left (hres.2.2 r hr X (l z)) (pow_nonneg (norm_nonneg l) j)
    _ = _ := (mul_assoc _ _ _).symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Actual Fourier synthesis of the metric comparison retains every reserved slow jet and its smallness factor. -/

theorem parameterizedProfileResponse_metric_difference_reserve (p : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M Md eps lam κ a b : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hab : a ≤ b)
    (hb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hdb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (fun Y => g t Y - 1) X‖ ≤ Md * eps * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (U : ℤ → ℝ → Vec 2 → ℂ) (hUm : ∀ m X, Measurable (fun t => U m t X))
    (hUs : ∀ m t, ContDiff ℝ (p : ℕ∞) (U m t)) (S : ℕ → ℝ)
    (hS : ∀ j ≤ p, 0 ≤ S j) (hUb : ∀ j ≤ p, ∀ m t X, ‖iteratedFDeriv ℝ j (U m t) X‖ ≤ S j * lam ^ j)
    (hU0 : ∀ t X, U 0 t X = 0) :
    (∀ z, ContDiff ℝ (p : ℕ∞) (fun X =>
      parameterizedProfileResponse g U a b X z - parameterizedProfileResponse (fun _ _ => 1) U a b X z)) ∧
    (∀ q ≤ p, Continuous (fun x : Vec 2 × ℝ => iteratedFDeriv ℝ q (fun X =>
      parameterizedProfileResponse g U a b X x.2 - parameterizedProfileResponse (fun _ _ => 1) U a b X x.2) x.1)) ∧
    ∀ q ≤ p, ∀ X z, ‖iteratedFDeriv ℝ q (fun Y =>
      parameterizedProfileResponse g U a b Y z - parameterizedProfileResponse (fun _ _ => 1) U a b Y z) X‖ ≤
      (metricDifferenceModeJetConstant p q M Md κ S * eps * lam ^ q) * centeredProfileJetConstant := by
  let Fg := fun m X => transverseModeResponse (‖profileFourierFrequency m‖ ^ 2)
    (fun t => g t X) (fun t => U m t X) a b
  let Fi := fun m X => transverseModeResponse (‖profileFourierFrequency m‖ ^ 2)
    (fun _ => 1) (fun t => U m t X) a b
  let F := fun m X => Fg m X - Fi m X
  let V := fun q => profileJetMajorant (metricDifferenceModeJetConstant p q M Md κ S * eps * lam ^ q) 0
  have hbi : ∀ j ≤ p, ∀ (t : ℝ) (X : Vec 2),
      ‖iteratedFDeriv ℝ j (fun _ : Vec 2 => (1 : ℝ)) X‖ ≤ 1 * lam ^ j := by
    intro j _ t X
    simpa only [abs_one] using scalarConstant_scaled_jet_le 1 lam hlam j X
  have hFg (m : ℤ) : ContDiff ℝ (p : ℕ∞) (Fg m) :=
    transverseModeResponse_parameter_contDiff p g hm hs M lam _ κ a b hM hlam
      (sq_nonneg _) hκ hab hb hgl (U m) (hUm m) (hUs m) S hS (fun j hj => hUb j hj m)
  have hFi (m : ℤ) : ContDiff ℝ (p : ℕ∞) (Fi m) :=
    transverseModeResponse_parameter_contDiff p (fun _ _ => 1) (fun _ => measurable_const)
      (fun _ => contDiff_const) 1 lam _ κ a b zero_le_one hlam
      (sq_nonneg _) hκ hab hbi (fun _ _ => hκ1) (U m) (hUm m) (hUs m) S hS (fun j hj => hUb j hj m)
  have hF (m : ℤ) : ContDiff ℝ (p : ℕ∞) (F m) := (hFg m).sub (hFi m)
  have hV : ∀ q ≤ p, Summable (V q) := fun _ _ => profileJetMajorant_summable _ _
  have hbound : ∀ q ≤ p, ∀ m X, ‖iteratedFDeriv ℝ q (F m) X‖ ≤ V q m := by
    intro q hq m X
    exact parameterizedModeResponse_metric_difference_jet_bound p q hq g hm hs M Md eps lam κ a b
      hM hMd heps hlam hκ hκ1 hab hb hdb hgl U hUm hUs S hS hUb m X
  have hsg (X : Vec 2) : Summable (fun m => Fg m X) :=
    (profileJetMajorant_summable (parameterizedModeJetConstant p 0 M lam κ S) 0).of_norm_bounded
      (fun m => by simpa only [norm_iteratedFDeriv_zero] using
        (parameterizedModeResponse_jet_bound p 0 (by omega) g hm hs M lam κ a b
          hM hlam hκ hab hb hgl U hUm hUs S hS hUb hU0 m X))
  have hsi (X : Vec 2) : Summable (fun m => Fi m X) :=
    (profileJetMajorant_summable (parameterizedModeJetConstant p 0 1 lam κ S) 0).of_norm_bounded
      (fun m => by simpa only [norm_iteratedFDeriv_zero] using
        (parameterizedModeResponse_jet_bound p 0 (by omega) (fun _ _ => 1) (fun _ => measurable_const)
          (fun _ => contDiff_const) 1 lam κ a b zero_le_one hlam hκ hab hbi (fun _ _ => hκ1)
          U hUm hUs S hS hUb hU0 m X))
  have he (z : ℝ) : (fun X => parameterizedProfileResponse g U a b X z -
      parameterizedProfileResponse (fun _ _ => 1) U a b X z) =
      fun X => ∑' m : ℤ, fourier m (z : AddCircle (1 : ℝ)) * F m X := by
    funext X
    change (∑' m : ℤ, fourier m (z : AddCircle (1 : ℝ)) * Fg m X) -
      (∑' m : ℤ, fourier m (z : AddCircle (1 : ℝ)) * Fi m X) = _
    rw [← (profileFourierSeries_term_summable _ (hsg X) z).tsum_sub
      (profileFourierSeries_term_summable _ (hsi X) z)]
    apply tsum_congr
    intro m
    exact (mul_sub _ _ _).symm
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rw [he z]
    apply contDiff_tsum (fun m => unit_complex_mul_contDiff p _ (hF m) _)
      (fun q hq => hV q (by exact_mod_cast hq))
    intro q m X hq
    exact (norm_iteratedFDeriv_unit_complex_mul_le p q (by exact_mod_cast hq) _ (hF m) _
      (by simp only [fourier_apply, Circle.norm_coe]) X).trans (hbound q (by exact_mod_cast hq) m X)
  · intro q hq
    have hej : (fun x : Vec 2 × ℝ => iteratedFDeriv ℝ q (fun X =>
      parameterizedProfileResponse g U a b X x.2 - parameterizedProfileResponse (fun _ _ => 1) U a b X x.2) x.1) =
      fun x => iteratedFDeriv ℝ q (fun X => ∑' m : ℤ, fourier m (x.2 : AddCircle (1 : ℝ)) * F m X) x.1 := by
      funext x
      rw [he x.2]
    rw [hej]
    exact fourier_parameter_jet_continuous p q hq F hF V hV hbound
  · intro q hq X z
    rw [he z]
    exact (fourier_parameter_jet_norm_le p q hq F hF V hV hbound X z).trans_eq
      (profileJetMajorant_tsum_centered _)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! Constant cell metrics act on each transverse Fourier mode by its scalar diffusion rate in the genuine weak form. -/

theorem transverseFourierModeH1_weak_diffusion
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (t : ℝ) (par : Fin 2) (n : ℤ) (z : TorusHk 1 ℂ) :
    -(∑ j : Fin 2, ∑ k : Fin 2,
      cellComplexPair (cellMetricEntryCLM hG t j k
        (cellDerivativeCLM j (transverseFourierModeH1 par n))) (cellDerivativeCLM k z)) =
      -((‖profileFourierFrequency n‖ ^ 2 * G t par.rev par.rev : ℝ) : ℂ) *
        cellComplexPair (torusHkValueCLM (transverseFourierModeH1 par n)) (torusHkValueCLM z) := by
  simp_rw [cellConstantMetricEntryCLM, cellComplexPair_scalar_left,
    transverseFourierModeH1_derivative, cellComplexPair_scalar_left,
    transverseFourierModeH1_weak_derivative]
  have hs := profileFourierFrequency_sq n
  fin_cases par <;> simp <;>
    ring_nf <;> rw [hs] <;> push_cast <;> ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual normalized source flux inherits componentwise grading and the original entry budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceFluxComponent_mixed_bound
    (π : ι → ℝ) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (hπ : ∀ i, 0 < π i) (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (hp : p ≤ qs) (hq : q ≤ qf) (A : Vec 2 →L[ℝ] ℝ)
    (C : ι → ℝ) (hC : ∀ u, 0 ≤ C u)
    (f : Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ u, IsBoxSmooth (p + j) (q + (D - 1) - j) (fun Y y => f Y y u))
    (t : ℝ) (ht : t ∈ I)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth p q (γ.coeff α t))
    (X : Vec 2)
    (hbf : ∀ u, ∀ a ≤ p + j, ∀ s ≤ q + (D - 1) - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s (fun y => f Y y u) z) X‖ ≤
        C u * lam ^ (δ + a)) (k : Fin 2) (v : ι) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceFluxComponentCoefficient edge η t
        (fun Z y => Real.exp ((lam • A) Z) • f Z y) k j v Y y) z) X‖ ≤
      ∑ u, normalizedSourceOrderConstant D p q j A *
        sourceUniformMixedBudget edge I p q lam v u * C u * lam ^ (δ + j + p) := by
  let T := fun (u : ι) (d : Finset.Icc 2 D) (γ : Constituent d.val (h u) (h v))
    (α : DerivativeWord2 (d.val - 1)) (Y y : Vec 2) =>
      (Real.exp ((lam • A) Y))⁻¹ • (γ.coeff α t Y y k •
        γ.map (covariantListCoefficients η (List.ofFn α)
          (fun Z y => Real.exp ((lam • A) Z) • f Z y u) j Y y))
  have hterm (u : ι) (d : Finset.Icc 2 D) (γ : Constituent d.val (h u) (h v))
      (hm : γ ∈ edge v u d) (α : DerivativeWord2 (d.val - 1)) :
      IsBoxSmooth p q (T u d γ α) := by
    by_cases hj : j ≤ (List.ofFn α).length
    · have hfu : IsBoxSmooth (p + j) (q + (List.ofFn α).length - j)
          (fun Y y => f Y y u) := (hf u).mono le_rfl (by
        have hd := (Finset.mem_Icc.mp d.2).2
        simp only [List.length_ofFn]
        omega)
      have hexp := isBoxSmooth_slow_field (p + j) (q + (List.ofFn α).length - j)
        (fun Y => Real.exp ((lam • A) Y)) (Real.contDiff_exp.comp (lam • A).contDiff)
      have hΦ := isBoxSmooth_bilinear hexp hfu
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h u →L[ℝ] h u)
      have hw := covariantListCoefficient_box_reserve η (List.ofFn α) j p q _ hj hΦ
      have hg := (hΓ v u d γ hm α).clm_comp (ContinuousLinearMap.proj k)
      have hmixed := isBoxSmooth_bilinear hg (hw.clm_comp γ.map)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v)
      have hinv := isBoxSmooth_slow_field p q (fun Y => Real.exp (-((lam • A) Y)))
        (Real.contDiff_exp.comp ((lam • A).contDiff.neg))
      simpa only [T, Real.exp_neg, ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.proj_apply] using! isBoxSmooth_bilinear hinv hmixed
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v)
    · have hz := covariantListCoefficients_above_degree η (List.ofFn α)
        (fun Z y => Real.exp ((lam • A) Z) • f Z y u) j (by omega)
      simp only [T, hz, map_zero, smul_zero]
      exact IsBoxSmooth.zero
  have hb (u : ι) (d : Finset.Icc 2 D) (γ : Constituent d.val (h u) (h v))
      (hm : γ ∈ edge v u d) (α : DerivativeWord2 (d.val - 1)) :
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (T u d γ α Y) z) X‖ ≤
      normalizedSourceOrderConstant D p q j A *
        (‖γ.map‖ * constituentUniformMixedBudget I p q lam (γ.coeff α)) * C u *
          lam ^ (δ + j + p) := by
    by_cases hj : j ≤ (List.ofFn α).length
    · by_cases hm0 : γ.map = 0
      · simp [T, hm0]
      · have hd := Finset.mem_Icc.mp d.2
        have hlen : (List.ofFn α).length < D := by simp only [List.length_ofFn]; omega
        have hfu := (hf u).mono le_rfl
          (show q + (List.ofFn α).length - j ≤ q + (D - 1) - j by
            simp only [List.length_ofFn]; omega)
        have hh := envelope_normalized_constituent_mixed_bound π edge I lam hlam Cj qs qf b Θ he
          v u (hπ v) (hπ u) d γ hm hm0 α η hη δ p q j hp hq hj (C u) (hC u)
          A (fun Y y => f Y y u) t ht (hΓ v u d γ hm α) hfu X
          (fun a ha s hs y => hbf u a ha s (hs.trans (by simp only [List.length_ofFn]; omega)) y) k z
        apply hh.trans
        have hbudget := constituentUniformMixedBudget_nonneg I p q lam hlam.le (γ.coeff α)
        have hK := normalizedCovariantProductConstant_le_sourceOrderConstant D p q j
          (List.ofFn α) hlen A
        calc
          _ ≤ (normalizedSourceOrderConstant D p q j A *
              constituentUniformMixedBudget I p q lam (γ.coeff α) * ‖γ.map‖ * C u) *
                lam ^ (δ + j + p) := by
            gcongr
            exact hC u
          _ = _ := by ring
    · have hz := covariantListCoefficients_above_degree η (List.ofFn α)
        (fun Z y => Real.exp ((lam • A) Z) • f Z y u) j (by omega)
      simp only [T, hz, map_zero, smul_zero, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (normalizedSourceOrderConstant_nonneg D p q j A)
        (mul_nonneg (norm_nonneg _) (constituentUniformMixedBudget_nonneg I p q lam hlam.le _)))
        (hC u)) (pow_nonneg hlam.le _)
  have hsum := norm_mixed_source_constituent_sum_le edge I p q lam
    (normalizedSourceOrderConstant D p q j A) C (δ + j + p) v T hterm X z hb
  simpa only [T, sourceFluxComponentCoefficient, Finset.smul_sum, List.smul_sum,
    List.map_map, Function.comp_def, Pi.smul_apply] using hsum

end AVRegularity.CycleComparison.Lift
end

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! Summable coefficient and first Fourier jet bounds control the actual Hilbert curve states; the dual derivative only needs the coefficient bound. -/

theorem transverseFourierMode_scalar_state_norm_le (par : Fin 2) (n : ℤ) (c : ℂ) :
    ‖cellH1Scalar c (transverseFourierModeH1 par n)‖ ≤
      ‖cellConstantCLM 1‖ * (‖c‖ + ‖profileFourierFrequency n * c‖) := by
  rw [cellH1Scalar_norm, norm_mul]
  have h := mul_le_mul_of_nonneg_left (transverseFourierModeH1_norm_le par n) (norm_nonneg c)
  convert h using 1
  ring

theorem transverseFourierMode_scalar_value_norm_le (par : Fin 2) (n : ℤ) (c : ℂ) :
    ‖cellScalarCLM c (torusHkValueCLM (transverseFourierModeH1 par n))‖ ≤
      ‖cellConstantCLM 1‖ * ‖c‖ := by
  rw [cellScalarCLM_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (transverseFourierModeH1_value_norm_le par n) (norm_nonneg c)

theorem transverseFourierMode_scalar_dual_norm_le (par : Fin 2) (n : ℤ) (dc : ℂ) :
    ‖cellPivotDualCLM (cellScalarCLM dc (torusHkValueCLM (transverseFourierModeH1 par n)))‖ ≤
      (‖cellPivotDualCLM‖ * ‖cellConstantCLM 1‖) * ‖dc‖ := by
  apply (cellPivotDualCLM.le_opNorm _).trans
  have h := mul_le_mul_of_nonneg_left (transverseFourierMode_scalar_value_norm_le par n dc)
    (norm_nonneg cellPivotDualCLM)
  simpa only [mul_assoc] using h

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! Each actual Fourier response has a genuine weak Hilbert representative, with its actual ODE derivative. -/

theorem profileModeResponse_hilbert_curve (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b : ℝ) (hab : a ≤ b) (M : ℝ) (hM : 0 ≤ M)
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, |g t| ≤ M)
    (hfm : Measurable (Function.uncurry f)) (C : ℝ)
    (hfb : ∀ t ∈ uIcc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f t x‖ ≤ C)
    (par : Fin 2) (n : ℤ) :
    CellWeakHilbertCurve a b
      (fun t => cellScalarCLM (profileModeResponse g f a t n)
        (torusHkValueCLM (transverseFourierModeH1 par n)))
      (fun t => cellH1Scalar (profileModeResponse g f a t n) (transverseFourierModeH1 par n))
      (fun t => cellPivotDualCLM
        (cellScalarCLM ((-(‖profileFourierFrequency n‖ ^ 2) * g t) • profileModeResponse g f a t n +
          unitProfileFourierCoeff (f t) n) (torusHkValueCLM (transverseFourierModeH1 par n)))) := by
  exact transverseFourierMode_scalar_curve hab par n _ _
    (profileModeResponse_strongTime_actual g f a b hab M hM hgm hgb hfm C hfb n)
    (profileModeResponse_rhs_memLp_top g f a b hab M hM hgm hgb hfm C hfb n)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Symmetric operator coefficients for the averaged full source-flux convolution. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def sourceFluxMeanCoefficient (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : ℕ → LiftCoeff ι h) (k : Fin 2) : LiftCoeff ι h :=
  leftTermsMeanBlockCoefficient (sourceFluxConvolutionLeftTerms edge η t n c k)

theorem sourceFluxMeanCoefficient_perm (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : ℕ → LiftCoeff ι h) (k : Fin 2) (m : ℕ)
    (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    sourceFluxMeanCoefficient edge η t n c k m (α ∘ σ) =
      sourceFluxMeanCoefficient edge η t n c k m α :=
  leftTermsMeanBlockCoefficient_perm _ m α σ

theorem sourceFluxMeanCoefficient_apply (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : ℕ → LiftCoeff ι h) (k : Fin 2)
    (hc : ∀ j ≤ min (D - 1) n, ∀ m ≤ n - j, ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j) (fun X z => c (n - j) m α t X z u u'))
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IsBoxSmooth 0 0 (fun X z => γ.coeff α t X z k))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X z : Vec 2) (v : ι) :
    liftApply n (sourceFluxMeanCoefficient edge η t n c k) (fun _ => f) t X z v =
      fieldCellMean (fun z => ∑ j ∈ Finset.range (min (D - 1) n + 1),
        sourceFluxComponentCoefficient edge η t
          (liftApply (n - j) (c (n - j)) (fun _ => f) t) k j v X z) := by
  unfold sourceFluxMeanCoefficient
  rw [leftTermsMeanBlockCoefficient_apply _ n
    (sourceFluxConvolutionLeftTerms_order edge η t n c k)
    (fun v => sourceFluxConvolutionLeftTerms_box edge η t n c k 0 0 v
      (by simpa only [zero_add] using hc) (hΓ v)) f hf t X z v]
  congr 1
  funext z
  exact sourceFluxConvolutionLeftTerms_apply edge η t n c k v hc f hf X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Centering a genuinely graded field preserves every reserved mixed order. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem fieldCellMean_centered_graded_mixed_bound (p q δ : ℕ) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth p q f) (C lam : ℝ) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hb : ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (f Y) z) X‖ ≤
        C * lam ^ (δ + r)) :
    IsBoxSmooth p q (fun X z => f X z - fieldCellMean (f X)) ∧
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => f Y y - fieldCellMean (f Y)) z) X‖ ≤
            ((1 + (2 : ℝ) ^ p) * C) * lam ^ (δ + r) := by
  have hb0 r (hr : r ≤ p) X z :
      ‖iteratedFDeriv ℝ r (fun Y => f Y z) X‖ ≤ C * lam ^ (δ + r) := by
    simpa only [norm_mixed_fast_zero_eq] using hb r hr 0 (Nat.zero_le _) X z
  have hm r (hr : r ≤ p) :=
    fieldCellMean_graded_jet_bound p r q δ hr f hf (fun _ => C) lam hb0
  have hmean := isBoxSmooth_slow_field p q (fun X => fieldCellMean (f X)) (hm p le_rfl).1
  refine ⟨hf.sub hmean, ?_⟩
  intro r hr s hs X z
  have hslow := (norm_mixed_slow_field_le r s (fun Y => fieldCellMean (f Y)) X z).trans
    ((hm r hr).2 X)
  have hpow : (2 : ℝ) ^ r ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hr
  have hslow' := hslow.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow hC) (pow_nonneg hlam _))
  apply (norm_mixed_jet_sub_le (hf.mono hr hs) (hmean.mono hr hs) X z).trans
  exact (add_le_add (hb r hr s hs X z) hslow').trans_eq (by ring)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Uniform normalized flux budgets are finite sums of the original physical constituent budgets. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def normalizedSourceUniformMatrix (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q j : ℕ) (lam : ℝ) (A : Vec 2 →L[ℝ] ℝ) (v u : ι) : ℝ :=
  ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
    normalizedSourceOrderConstant D r s j A * sourceUniformMixedBudget edge I r s lam v u

omit [Fintype ι] in
theorem normalizedSourceUniformMatrix_nonneg (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q j : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    0 ≤ normalizedSourceUniformMatrix edge I p q j lam A v u := by
  exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ =>
    mul_nonneg (normalizedSourceOrderConstant_nonneg D r s j A)
      (sourceUniformMixedBudget_nonneg edge I r s lam hlam v u)

omit [Fintype ι] in
theorem normalizedSourceUniformMatrix_entry_le (edge : ConstituentEdges D h) (I : Set ℝ)
    (p q r s j : ℕ) (hr : r ≤ p) (hs : s ≤ q)
    (lam : ℝ) (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    normalizedSourceOrderConstant D r s j A * sourceUniformMixedBudget edge I r s lam v u ≤
      normalizedSourceUniformMatrix edge I p q j lam A v u := by
  have hn r s : 0 ≤ normalizedSourceOrderConstant D r s j A *
      sourceUniformMixedBudget edge I r s lam v u :=
    mul_nonneg (normalizedSourceOrderConstant_nonneg D r s j A)
      (sourceUniformMixedBudget_nonneg edge I r s lam hlam v u)
  apply (Finset.single_le_sum (fun s _ => hn r s)
    (show s ∈ Finset.range (q + 1) by simp only [Finset.mem_range]; omega)).trans
  exact Finset.single_le_sum (fun r _ => Finset.sum_nonneg fun s _ => hn r s)
    (show r ∈ Finset.range (p + 1) by simp only [Finset.mem_range]; omega)

end AVRegularity.CycleComparison.Lift
end

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! Absolute coefficient and first Fourier jet summability imply actual cell carrier summability. -/

theorem transverseFourierMode_value_summable (par : Fin 2) (c : ℤ → ℂ) (hc : Summable c) :
    Summable (fun n => cellScalarCLM (c n) (torusHkValueCLM (transverseFourierModeH1 par n))) := by
  apply (hc.norm.mul_left ‖cellConstantCLM 1‖).of_norm_bounded
  exact fun n => transverseFourierMode_scalar_value_norm_le par n (c n)

theorem transverseFourierMode_state_summable (par : Fin 2) (c : ℤ → ℂ) (hc : Summable c)
    (hjet : Summable (fun n => profileFourierFrequency n * c n)) :
    Summable (fun n => cellH1Scalar (c n) (transverseFourierModeH1 par n)) := by
  apply ((hc.norm.add hjet.norm).mul_left ‖cellConstantCLM 1‖).of_norm_bounded
  exact fun n => transverseFourierMode_scalar_state_norm_le par n (c n)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Literal weighted operator means inherit the actual ambient coefficient bounds. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b}
  {n p q : ℕ} {c : LiftCoeff ι h} {M : ι → ι → ℝ}

theorem AmbientLiftCoefficientData.weighted_mean_jet_le
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (r : ℕ) (hr : r ≤ p)
    (w : Vec 2 → ℝ) (hw : Continuous w) (W : ℝ) (hW : ∀ z, ‖w z‖ ≤ W) :
    ContDiff ℝ (p : ℕ∞) (fun X => fieldCellMean (fun z => w z • c m α t X z v u)) ∧
      ∀ X, ‖iteratedFDeriv ℝ r
        (fun Y => fieldCellMean (fun z => w z • c m α t Y z v u)) X‖ ≤
          ((2 : ℝ) ^ r * (W * M v u)) * lam ^ (n - m + r) := by
  apply weighted_cell_mean_graded_jet_bound p r q (n - m) hr
    (fun X z => c m α t X z v u) (data.box m hm α v u t ht) w hw W hW
    (fun _ => M v u) lam
  intro j hj X z
  simpa only [norm_mixed_jet_fast_zero] using!
    data.bound m hm α v u j hj 0 (Nat.zero_le q) t ht X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! One finite matrix budget controls every reserved suborder of the actual normalized source flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceFluxComponent_uniform_mixed_bound
    (π : ι → ℝ) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (hπ : ∀ i, 0 < π i) (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (hp : p ≤ qs) (hq : q ≤ qf) (A : Vec 2 →L[ℝ] ℝ)
    (C : ι → ℝ) (hC : ∀ u, 0 ≤ C u)
    (f : Vec 2 → Vec 2 → ∀ i, h i)
    (hf : ∀ u, IsBoxSmooth (p + j) (q + (D - 1) - j) (fun Y y => f Y y u))
    (t : ℝ) (ht : t ∈ I)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsBoxSmooth p q (γ.coeff α t))
    (X : Vec 2)
    (hbf : ∀ u, ∀ a ≤ p + j, ∀ s ≤ q + (D - 1) - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s (fun y => f Y y u) z) X‖ ≤
        C u * lam ^ (δ + a)) (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (k : Fin 2) (v : ι) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • sourceFluxComponentCoefficient edge η t
        (fun Z y => Real.exp ((lam • A) Z) • f Z y) k j v Y y) z) X‖ ≤
      ∑ u, normalizedSourceUniformMatrix edge I p q j lam A v u * C u * lam ^ (δ + j + r) := by
  have hh := normalizedSourceFluxComponent_mixed_bound π edge I lam hlam Cj qs qf b Θ he
    hπ η hη δ r s j (hr.trans hp) (hs.trans hq) A C hC f
    (fun u => (hf u).mono (by omega) (by omega)) t ht
    (fun v u d γ hm α => (hΓ v u d γ hm α).mono hr hs) X
    (fun u a ha b hb z => hbf u a (by omega) b (by omega) z) k v z
  apply hh.trans
  apply Finset.sum_le_sum
  intro u _
  have he := normalizedSourceUniformMatrix_entry_le edge I p q r s j hr hs lam hlam.le A v u
  have hb := mul_le_mul_of_nonneg_right he (hC u)
  exact mul_le_mul_of_nonneg_right hb (pow_nonneg hlam.le _)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Lift

/-! Absolute Hilbert Fourier sums have the literal classical transverse Fourier representative. -/

theorem transverseFourierMode_synthesis_ae (par : Fin 2) (c : ℤ → ℂ) (hc : Summable c) :
    ((∑' n : ℤ, cellScalarCLM (c n) (torusHkValueCLM (transverseFourierModeH1 par n)) : ComplexCellL2) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun z => profileFourierSeries c (z par.rev) := by
  let u := fun n => cellScalarCLM (c n) (torusHkValueCLM (transverseFourierModeH1 par n))
  have hn : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
      transverseFourierMode_scalar_value_norm_le par n (c n)) (hc.norm.mul_left ‖cellConstantCLM 1‖)
  have hall : ∀ᵐ z ∂volume.restrict AVenhance.unitCube, ∀ n, u n z = c n * transverseFourierMode par n z := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [cellScalarCLM_ae (c n) (torusHkValueCLM (transverseFourierModeH1 par n)),
      transverseFourierModeH1_value_ae par n] with z hs hv
    rw [hs, hv]
  filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hn), hall] with z hz hmode
  change ((∑' n, u n : ComplexCellL2) : Vec 2 → ℂ) z = _
  rw [hz]
  unfold profileFourierSeries
  apply tsum_congr
  intro n
  rw [hmode n]
  exact mul_comm _ _

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite source terms and their means only inspect coefficient degrees up to their own degree. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFluxConvolutionLeftTerms_congr_coefficients (edge : ConstituentEdges D h)
    (η t : ℝ) (n : ℕ) (c d : ℕ → LiftCoeff ι h)
    (hcd : ∀ q ≤ n, c q = d q) (k : Fin 2) (v : ι) :
    sourceFluxConvolutionLeftTerms edge η t n c k v =
      sourceFluxConvolutionLeftTerms edge η t n d k v := by
  unfold sourceFluxConvolutionLeftTerms
  apply List.flatMap_congr
  intro j _
  rw [hcd (n - j) (Nat.sub_le n j)]

theorem sourceConvolutionLeftTerms_congr_coefficients (edge : ConstituentEdges D h)
    (η t : ℝ) (n : ℕ) (c d : ℕ → LiftCoeff ι h)
    (hcd : ∀ q ≤ n, c q = d q) (v : ι) :
    sourceConvolutionLeftTerms edge η t n c v =
      sourceConvolutionLeftTerms edge η t n d v := by
  unfold sourceConvolutionLeftTerms
  apply List.flatMap_congr
  intro k _
  simp only [covariantLeftTermStep]
  rw [sourceFluxConvolutionLeftTerms_congr_coefficients edge η t n c d hcd k v,
    sourceFluxConvolutionLeftTerms_congr_coefficients edge η t (n - 1) c d
      (fun q hq => hcd q (by omega)) k v]

variable [DecidableEq ι]

theorem sourceFluxMeanCoefficient_congr_coefficients (edge : ConstituentEdges D h)
    (η t : ℝ) (n : ℕ) (c d : ℕ → LiftCoeff ι h)
    (hcd : ∀ q ≤ n, c q = d q) (k : Fin 2) :
    sourceFluxMeanCoefficient edge η t n c k = sourceFluxMeanCoefficient edge η t n d k := by
  unfold sourceFluxMeanCoefficient
  congr 1
  funext v
  exact sourceFluxConvolutionLeftTerms_congr_coefficients edge η t n c d hcd k v

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Centering a paired source difference preserves its degree and its single perturbation factor. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem fieldCellMean_centered_paired_graded_mixed_bound (p q δ : ℕ)
    (f fi : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f) (hfi : IsBoxSmooth p q fi)
    (C eps lam : ℝ) (hC : 0 ≤ C) (heps : 0 ≤ eps) (hlam : 0 ≤ lam)
    (hb : ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y => f Y y - fi Y y) z) X‖ ≤
        (C * eps) * lam ^ (δ + r)) :
    IsBoxSmooth p q (fun X z => (f X z - fieldCellMean (f X)) -
      (fi X z - fieldCellMean (fi X))) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (f Y y - fieldCellMean (f Y)) - (fi Y y - fieldCellMean (fi Y))) z) X‖ ≤
        ((1 + (2 : ℝ) ^ p) * C) * eps * lam ^ (δ + r) := by
  have he (X z : Vec 2) : (f X z - fieldCellMean (f X)) - (fi X z - fieldCellMean (fi X)) =
      (f X z - fi X z) - fieldCellMean (fun y => f X y - fi X y) := by
    rw [fieldCellMean_sub (hf.1 X).continuous (hfi.1 X).continuous]
    abel
  simp_rw [he]
  have hh := fieldCellMean_centered_graded_mixed_bound p q δ (fun X z => f X z - fi X z)
    (hf.sub hfi) (C * eps) lam (mul_nonneg hC heps) hlam hb
  refine ⟨hh.1, ?_⟩
  intro r hr s hs X z
  exact (hh.2 r hr s hs X z).trans_eq (by ring)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVenhance.Infra.Torus AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Uniform scalar-dual estimates for the full literal Wiener frequency lattice. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complex_dual_transverse_fourier_bound (p q r L : ℕ)
    (hr : r ≤ p) (hL : L + 2 ≤ q)
    (par : Fin 2) (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (ht : IsTransverseOn par Set.univ (fun _ : ℝ => f))
    (l : E →L[ℝ] ℝ)
    (hper : ∀ X, Function.Periodic
      (fun z : ℝ => ((l (f X (z • basisVec par.rev)) : ℝ) : ℂ)) 1)
    (C : ℕ → ℝ) (hb : ∀ a ≤ p, ∀ b ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C a)
    (k : Fin 2 → ℤ) (X : Vec 2) :
    (1 + max |(k 0 : ℝ)| |(k 1 : ℝ)|) ^ L * ‖iteratedFDeriv ℝ r
      (fun Y => smoothFourierCoeff (fun z => ((l (f Y z) : ℝ) : ℂ)) k) X‖ ≤
      ‖l‖ * (if k par = 0 then
        profileJetMajorant (2 ^ r * C r) (2 ^ r * C r) (k par.rev) else 0) := by
  let line : ℝ →L[ℝ] Vec 2 := (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec par.rev)
  have hn : ‖line‖ = 1 := by simp [line, norm_basisVec]
  have hprof (Y : Vec 2) : ContDiff ℝ 1
      (fun z : ℝ => ((l (f Y (z • basisVec par.rev)) : ℝ) : ℂ)) :=
    ((Complex.ofRealCLM.comp l).contDiff.comp ((hf.1 Y).comp line.contDiff)).of_le
      (by exact_mod_cast (show 1 ≤ q by omega))
  rw [transverse_parameterized_dual_fourier_identity par f ht l hprof hper k]
  by_cases hk : k par = 0
  · simp only [ite_eq_left hk]
    rw [frequency_max_eq_parallel_transverse par k, hk, Int.cast_zero, abs_zero,
      max_eq_right (abs_nonneg _)]
    have h := complex_dual_profile_fourier_bound p q r L hr hL f hf line hn l hper C hb (k par.rev) X
    have hc : 2 ^ r * (‖l‖ * C r) = ‖l‖ * (2 ^ r * C r) := by ring
    rw [hc, profileJetMajorant_const_mul] at h
    exact h
  · simp only [ite_eq_right hk]
    simp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Exponential normalization commutes with centering the literal recurrence source. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem exponential_centered_source_mixed_grading (p q δ : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (f : Vec 2 → Vec 2 → E) (C lam : ℝ)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hf : IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ • f X z))
    (hb : ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • f Y y) z) X‖ ≤ C * lam ^ (δ + r)) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      (f X z - fieldCellMean (f X))) ∧
      ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
          (fun y => (Real.exp ((lam • A) Y))⁻¹ •
            (f Y y - fieldCellMean (f Y))) z) X‖ ≤
              ((1 + (2 : ℝ) ^ p) * C) * lam ^ (δ + r) := by
  have he (X z : Vec 2) : (Real.exp ((lam • A) X))⁻¹ • (f X z - fieldCellMean (f X)) =
      (Real.exp ((lam • A) X))⁻¹ • f X z -
        fieldCellMean (fun y => (Real.exp ((lam • A) X))⁻¹ • f X y) := by
    rw [AVRegularity.fieldCellMean_smul, smul_sub]
  simp_rw [he]
  exact fieldCellMean_centered_graded_mixed_bound p q δ
    (fun X z => (Real.exp ((lam • A) X))⁻¹ • f X z) hf C lam hC hlam hb

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Native coefficient geometry and paired test bounds give the actual difference induction state. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {N n p q : ℕ}
  {c ci : LiftCoeff ι h} {M Mi : ι → ι → ℝ}

theorem ambient_paired_coefficient_data_of_tests
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (datai : AmbientLiftCoefficientData par a b hab lam n p q ci Mi)
    (hn : n ≤ N) (hlam : 0 < lam)
    (hc : ∀ m ≤ n, ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (hci : ∀ m ≤ n, ∀ β (σ : Equiv.Perm (Fin m)), ci m (β ∘ σ) = ci m β)
    (B : ι → ι → ℝ) (hB : ∀ v u, 0 ≤ B v u) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (hb : ∀ A u v ξ, ∀ r ≤ p, ∀ s ≤ q, ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (fun y => normalizedLiftTestField c n (lam • A) u v ξ t Y y -
          normalizedLiftTestField ci n (lam • A) u v ξ t Y y) z) X‖ ≤
        (K A * B v u * ‖ξ‖) * lam ^ (n + r)) :
    AmbientLiftCoefficientData par a b hab lam n p q
      (fun m α t X z v u => c m α t X z v u - ci m α t X z v u)
      (fun v u => finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N K * B v u) := by
  refine ⟨fun v u => mul_nonneg (mul_nonneg (finiteLiftCalibrationBudget_nonneg N)
    (finiteLiftTestDirectionBudget_nonneg N K)) (hB v u), ?_, ?_, ?_, ?_⟩
  · intro m hm α v u t ht
    exact (data.box m hm α v u t ht).sub (datai.box m hm α v u t ht)
  · intro m hm α v u r hr s hs t ht X z
    exact paired_coefficient_grading_of_direction_budget c ci N n m r s hn hm
      (hc m hm) (hci m hm) α t v u X z lam (B v u) hlam (hB v u) K
      (fun A ξ => ((data.normalized_test_box A v u ξ t ht).sub
        (datai.normalized_test_box A v u ξ t ht)).mono hr hs)
      (fun A ξ => hb A u v ξ r hr s hs t ht X z)
  · intro m hm α v u t ht X z s
    exact congrArg₂ (fun x y => x - y)
      (data.transverse m hm α v u t ht X z s)
      (datai.transverse m hm α v u t ht X z s)
  · intro m hm α v u l X z
    simp_rw [map_sub]
    exact (data.measurable m hm α v u l X z).sub
      (datai.measurable m hm α v u l X z)

end AVRegularity.CycleComparison.Lift
end
