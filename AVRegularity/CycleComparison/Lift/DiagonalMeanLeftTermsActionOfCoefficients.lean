-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.ComplexDualProfileFourierData
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.SettingAmbientCrossTestTransverse

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The height-zero flux coefficients act as the drift mean and the degree-two molecular term. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_diagonal_mean_flux_coefficient_vector_apply
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (n : ℕ) (hn : 2 ≤ n) (f : Vec 2 → ∀ i, h i)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftApply (n - 1) (diagonalMeanFluxCoefficient Q Cc n k₀) (fun _ => f) t X z =
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k₀) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t X y) +
      if n = 2 then -Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fderiv ℝ f X (basisVec j) else 0 := by
  let c := weightedLiftCoefficientMean (Cc 0 (n - 1))
    (fun t z => Real.sqrt Q.η * Q.v t z k₀)
  have hw : Continuous (fun y => Real.sqrt Q.η * Q.v t y k₀) :=
    (setting_normalized_drift_contDiff_one P t ht k₀).continuous
  have hc : ∀ m ≤ n - 1, ∀ α : DerivativeWord2 m, ∀ v u,
      Continuous (fun y => Cc 0 (n - 1) m α t X y v u) := fun m hm α v u =>
    (hseq.2.2.2.2.2.1 0 (Nat.zero_le H) (n - 1) m α v u t ht).1.1 X |>.continuous
  have hfast : Continuous (liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t X) :=
    continuous_pi (fun v => liftApply_component_fast_continuous (n - 1) _ _ t X v
      (fun m hm α u => hc m hm α v u))
  have hca : liftApply (n - 1) c (fun _ => f) t X z =
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k₀) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t X y) := by
    ext v
    rw [weightedLiftCoefficientMean_apply (n - 1) _ _ _ t X z v hw (fun m hm α u => hc m hm α v u)]
    exact fieldCellMean_pi_apply _ (hw.smul hfast) v
  change liftApply (n - 1) (fun m α t X z v u => c m α t X z v u +
    if n = 2 then metricFluxCoefficient Q.η Q.G k₀ m α t X z v u else 0) (fun _ => f) t X z = _
  by_cases hn2 : n = 2
  · subst n
    simp only [ite_true]
    rw [liftApply_coefficient_add]
    dsimp only
    rw [metricFluxCoefficient_apply, hca]
  · simp only [ite_eq_right hn2, add_zero, hca]
end

/-! The height-zero flux coefficients act as the drift mean and the degree-two molecular term. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_diagonal_mean_flux_coefficient_vector_apply_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (n : ℕ) (hn : 2 ≤ n) (f : Vec 2 → ∀ i, h i)
    (k₀ : Fin 2) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2)
    (hc : ∀ m ≤ n - 1, ∀ α : DerivativeWord2 m, ∀ v u,
      Continuous (fun y => Cc 0 (n - 1) m α t X y v u)) :
    liftApply (n - 1) (diagonalMeanFluxCoefficient Q Cc n k₀) (fun _ => f) t X z =
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k₀) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t X y) +
      if n = 2 then -Q.η • ∑ j : Fin 2, Q.G t X k₀ j • fderiv ℝ f X (basisVec j) else 0 := by
  let c := weightedLiftCoefficientMean (Cc 0 (n - 1))
    (fun t z => Real.sqrt Q.η * Q.v t z k₀)
  have hw : Continuous (fun y => Real.sqrt Q.η * Q.v t y k₀) :=
    (setting_normalized_drift_contDiff_one P t ht k₀).continuous
  have hfast : Continuous (liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t X) :=
    continuous_pi (fun v => liftApply_component_fast_continuous (n - 1) _ _ t X v
      (fun m hm α u => hc m hm α v u))
  have hca : liftApply (n - 1) c (fun _ => f) t X z =
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k₀) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t X y) := by
    ext v
    rw [weightedLiftCoefficientMean_apply (n - 1) _ _ _ t X z v hw (fun m hm α u => hc m hm α v u)]
    exact fieldCellMean_pi_apply _ (hw.smul hfast) v
  change liftApply (n - 1) (fun m α t X z v u => c m α t X z v u +
    if n = 2 then metricFluxCoefficient Q.η Q.G k₀ m α t X z v u else 0) (fun _ => f) t X z = _
  by_cases hn2 : n = 2
  · subst n
    simp only [ite_true]
    rw [liftApply_coefficient_add]
    dsimp only
    rw [metricFluxCoefficient_apply, hca]
  · simp only [ite_eq_right hn2, add_zero, hca]
end

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Metric-difference inverse constants are linear in source size and retain base slow grades. -/

theorem metricDifferenceSourceBudget_source_mul (p q : ℕ) (M c : ℝ) (S : ℕ → ℝ) :
    metricDifferenceSourceBudget p M (fun j => S j * c) q =
      metricDifferenceSourceBudget p M S q * c := by
  unfold metricDifferenceSourceBudget
  have he : (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * (S (q - j) * c)) =
      (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * S (q - j)) * c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

theorem metricDifferenceKernelSourceConstant_source_mul (p q : ℕ) (M Md κ c : ℝ) (S : ℕ → ℝ) :
    metricDifferenceKernelSourceConstant p q M Md κ (fun j => S j * c) =
      metricDifferenceKernelSourceConstant p q M Md κ S * c := by
  unfold metricDifferenceKernelSourceConstant
  simp_rw [metricDifferenceSourceBudget_source_mul]
  have he : (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial *
      (metricDifferenceSourceBudget p Md S (q - j) * c)) =
      (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial *
        metricDifferenceSourceBudget p Md S (q - j)) * c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

theorem metricDifferenceModeJetConstant_source_mul (p q : ℕ) (M Md κ c : ℝ) (S : ℕ → ℝ) :
    metricDifferenceModeJetConstant p q M Md κ (fun j => S j * c) =
      metricDifferenceModeJetConstant p q M Md κ S * c := by
  unfold metricDifferenceModeJetConstant
  rw [metricDifferenceKernelSourceConstant_source_mul]
  ring

theorem metricDifferenceModeJetConstant_base_grade (p q δ : ℕ) (M Md κ lam eps : ℝ) (S : ℕ → ℝ) :
    metricDifferenceModeJetConstant p q M Md κ (fun j => S j * lam ^ δ) * eps * lam ^ q =
      metricDifferenceModeJetConstant p q M Md κ S * eps * lam ^ (δ + q) := by
  rw [metricDifferenceModeJetConstant_source_mul, pow_add]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Paired second-cross bounds pass to the selected component without a dimension factor. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalizedCellB2_paired_component_mixed_grading
    (p q δ r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (η lam M Md g Cf Cd : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hMd : 0 ≤ Md)
    (hg : 0 ≤ g) (hCf : 0 ≤ Cf) (hCd : 0 ≤ Cd)
    (A : Vec 2 →L[ℝ] ℝ) (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (f fi : Vec 2 → Vec 2 → ∀ i, h i) (i₀ : ι)
    (hf : IsBoxSmooth (p + 2) q f) (hfi : IsBoxSmooth (p + 2) q fi)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (hJ : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => J t Y i j))
    (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbD : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j - J t Y i j) z) X‖ ≤ (Md * g) * lam ^ a)
    (hbfi : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun y => fi Y y i₀) z) X‖ ≤ Cf * lam ^ (δ + a))
    (hbdf : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun y => f Y y i₀ - fi Y y i₀) z) X‖ ≤
        (Cd * g) * lam ^ (δ + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
      (Real.exp ((lam • A) Y))⁻¹ • cellB2 η G t (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y i₀ -
      (Real.exp ((lam • A) Y))⁻¹ • cellB2 η J t (fun Z w => Real.exp ((lam • A) Z) • fi Z w) Y y i₀) z) X‖ ≤
      (normalizedCellB2UniformConstant p q A M * Cd +
        normalizedCellB2UniformConstant p q A Md * Cf) * g * lam ^ ((δ + 2) + r) := by
  let Φ := fun Y y => Real.exp ((lam • A) Y) • f Y y
  let Φi := fun Y y => Real.exp ((lam • A) Y) • fi Y y
  have hΦ : IsBoxSmooth (p + 2) q Φ := isBoxSmooth_bilinear
    (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hf
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (∀ i, h i) →L[ℝ] (∀ i, h i))
  have hΦi : IsBoxSmooth (p + 2) q Φi := isBoxSmooth_bilinear
    (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hfi
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (∀ i, h i) →L[ℝ] (∀ i, h i))
  have heG (Y y : Vec 2) := cellB2_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀) η G t Φ
    (hΦ.mono (by omega) (by omega))
    (fun i j => (hG i j).mono (by omega) (Nat.zero_le _)) Y y
  have heJ (Y y : Vec 2) := cellB2_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀) η J t Φi
    (hΦi.mono (by omega) (by omega))
    (fun i j => (hJ i j).mono (by omega) (Nat.zero_le _)) Y y
  change ∀ Y y, cellB2 η G t (fun Z w => Φ Z w i₀) Y y = cellB2 η G t Φ Y y i₀ at heG
  change ∀ Y y, cellB2 η J t (fun Z w => Φi Z w i₀) Y y = cellB2 η J t Φi Y y i₀ at heJ
  change ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
    (Real.exp ((lam • A) Y))⁻¹ • cellB2 η G t Φ Y y i₀ -
      (Real.exp ((lam • A) Y))⁻¹ • cellB2 η J t Φi Y y i₀) z) X‖ ≤ _
  simp_rw [← heG, ← heJ]
  exact normalizedCellB2_paired_mixed_grading p q δ r s hr hs η lam M Md g Cf Cd
    hη0 hη hlam hM hMd hg hCf hCd A G J t (fun Y y => f Y y i₀) (fun Y y => fi Y y i₀)
    (hf.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀))
    (hfi.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀))
    hG hJ X hbG hbD hbfi hbdf z
end

/-! A summable scalar-dual majorant also controls the zero Fourier mode. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complex_dual_profile_fourier_bound (p q r L : ℕ)
    (hr : r ≤ p) (hL : L + 2 ≤ q)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (line : ℝ →L[ℝ] Vec 2) (hline : ‖line‖ = 1)
    (l : E →L[ℝ] ℝ) (hper : ∀ X,
      Function.Periodic (fun z => ((l (f X (line z)) : ℝ) : ℂ)) 1)
    (C : ℕ → ℝ) (hb : ∀ a ≤ p, ∀ b ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C a)
    (m : ℤ) (X : Vec 2) :
    (1 + |(m : ℝ)|) ^ L * ‖iteratedFDeriv ℝ r
      (fun Y => unitProfileFourierCoeff (fun z => ((l (f Y (line z)) : ℝ) : ℂ)) m) X‖ ≤
      profileJetMajorant (2 ^ r * (‖l‖ * C r)) (2 ^ r * (‖l‖ * C r)) m := by
  by_cases hm : m = 0
  · subst m
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, one_mul, profileJetMajorant,
      ite_true]
    have hbox := hf.clm_comp (Complex.ofRealCLM.comp l)
    apply unitProfileFourierCoeff_parameter_jet_norm_le p r hr
      (fun Y z => ((l (f Y (line z)) : ℝ) : ℂ))
      (fun Y => by simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
        Complex.ofRealCLM_apply] using
        ((Complex.ofRealCLM.comp l).continuous.comp ((hf.1 Y).continuous.comp line.continuous)).measurable)
      (fun z => by simpa only [iteratedDeriv_zero, ContinuousLinearMap.comp_apply,
        Complex.ofRealCLM_apply] using
        linear_profile_iteratedDeriv_parameter_contDiff p q 0 (Nat.zero_le q) _ hbox line z)
      (fun a => ‖l‖ * C a)
    intro a ha z Y
    have h := norm_mixed_complexified_linear_profile_le p q a 0 ha (Nat.zero_le q) f hf line l Y z
    simp only [iteratedDeriv_zero, pow_zero, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hb a ha 0 (Nat.zero_le q) Y (line z)) (norm_nonneg l))
  · have hdata := complex_dual_profile_fourier_parameter_data p q r L hr hL f hf line hline l hper C hb m
    simpa only [profileJetMajorant, ite_eq_right hm] using hdata.2 hm X
end

/-! Parameter-dependent synthesis is the literal weighted Fourier inverse. -/

theorem parameterizedProfileResponse_weighted_eq (g : ℝ → Vec 2 → ℝ)
    (f : ℝ → Vec 2 → ℝ → ℂ) (j : ℕ) (a b : ℝ) (X : Vec 2) (z : ℝ) :
    parameterizedProfileResponse g (weightedParameterSource f j) a b X z =
      profileWeightedResponse (fun t => g t X) (fun t => f t X) a b z j := by
  unfold parameterizedProfileResponse profileWeightedResponse profileFourierSeries
  apply tsum_congr
  intro m
  congr 1
  exact transverseModeResponse_complex_mul (‖profileFourierFrequency m‖ ^ 2)
    (fun t => g t X) (fun t => unitProfileFourierCoeff (f t X) m)
    (profileFourierFrequency m ^ j) a b

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Reuse the actual zero scalar solution to supply the zero field on every finite cell window. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_zero_field
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (a b : ℝ) (hab : a ≤ b) :
    IsCellFieldInverse G v sZ a b (0 : Vec 2 → E) 0 0 := by
  refine ⟨fun _ _ => contDiff_const, ?_⟩
  intro l
  have hj : cellJetOfField l (0 : ℝ → Vec 2 → E) = 0 := by
    funext t α z
    simp [cellJetOfField]
  rw [hj]
  have hs : IsCellSolution (Icc a b) ⟨fun t _ => G t, v, 0, 0⟩ 0 0 0 :=
    cellSolution_zero_field (Icc a b) ordConnected_Icc ⟨fun t _ => G t, v, 0, 0⟩
  simp only [Pi.zero_apply, map_zero, Complex.ofReal_zero]
  refine ⟨hs, ?_, ?_, cellSolution_compact_energy_finite a b hab _ _ _ _ hs⟩
  · intro t _
    simp [cellValue, cellMean]
  · exact Filter.Eventually.of_forall (fun _ => rfl)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Paired first-cross jets have one metric perturbation factor and the original single-degree gain. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalizedCellB1_paired_mixed_grading
    (p q δ r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (η lam M Md W g Cf Cd : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (hW : 0 ≤ W)
    (hg : 0 ≤ g) (hCf : 0 ≤ Cf) (hCd : 0 ≤ Cd)
    (A : Vec 2 →L[ℝ] ℝ) (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (f fi : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth (p + 1) (q + 1) f) (hfi : IsBoxSmooth (p + 1) (q + 1) fi)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (hJ : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => J t Y i j))
    (hv : ∀ k, IsBoxSmooth p q (fun (_ : Vec 2) z => v t z k)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbD : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j - J t Y i j) z) X‖ ≤ (Md * g) * lam ^ a)
    (hbv : ∀ k, ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun (_ : Vec 2) => iteratedFDeriv ℝ b
        (fun y => Real.sqrt η * v t y k) z) X‖ ≤ W * lam ^ a)
    (hbfi : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fi Y) z) X‖ ≤ Cf * lam ^ (δ + a))
    (hbdf : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun y => f Y y - fi Y y) z) X‖ ≤
        (Cd * g) * lam ^ (δ + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
      (Real.exp ((lam • A) Y))⁻¹ • cellB1 η G v t (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y -
      (Real.exp ((lam • A) Y))⁻¹ • cellB1 η J v t (fun Z w => Real.exp ((lam • A) Z) • fi Z w) Y y) z) X‖ ≤
      (normalizedCellB1UniformConstant p q A M W * Cd +
        normalizedCellB1UniformConstant p q A Md 0 * Cf) * g * lam ^ ((δ + 1) + r) := by
  let df := fun Y y => f Y y - fi Y y
  let D := fun u Y i j => G u Y i j - J u Y i j
  let U := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    cellB1 η G v t (fun Z w => Real.exp ((lam • A) Z) • df Z w) Y y
  let T := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    cellB1 η D (fun _ _ => 0) t (fun Z w => Real.exp ((lam • A) Z) • fi Z w) Y y
  have hdf : IsBoxSmooth (p + 1) (q + 1) df := hf.sub hfi
  have hD (i j : Fin 2) : IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => D t Y i j) :=
    (hG i j).sub (hJ i j)
  have hΦdf : IsBoxSmooth (p + 1) (q + 1)
      (fun Y y => Real.exp ((lam • A) Y) • df Y y) :=
    isBoxSmooth_bilinear (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hdf
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hΦfi : IsBoxSmooth (p + 1) (q + 1)
      (fun Y y => Real.exp ((lam • A) Y) • fi Y y) :=
    isBoxSmooth_bilinear (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hfi
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hU : IsBoxSmooth p q U := exponential_normalization_box_reserve p q (lam • A) _
    (cellB1_box_reserve p q η G v t _ hΦdf hG hv)
  have hT : IsBoxSmooth p q T := exponential_normalization_box_reserve p q (lam • A) _
    (cellB1_box_reserve p q η D (fun _ _ => 0) t _ hΦfi hD
      (fun _ => isBoxSmooth_slow_field p q (fun _ => (0 : ℝ)) contDiff_const))
  have he (Y y : Vec 2) :
      (Real.exp ((lam • A) Y))⁻¹ • cellB1 η G v t (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y -
      (Real.exp ((lam • A) Y))⁻¹ • cellB1 η J v t (fun Z w => Real.exp ((lam • A) Z) • fi Z w) Y y =
      U Y y + T Y y :=
    normalizedCellB1_paired_difference η (lam • A) G J v t f fi
      (hf.mono (by omega) (by omega)) (hfi.mono (by omega) (by omega))
      (fun i j => (hG i j).mono (by omega) (Nat.zero_le _))
      (fun i j => (hJ i j).mono (by omega) (Nat.zero_le _)) Y y
  simp_rw [he]
  apply (norm_mixed_jet_add_le (hU.mono hr hs) (hT.mono hr hs) X z).trans
  have hu := normalizedCellB1_scaled_drift_uniform_mixed_grading_at_slow_point p q δ η lam M W
    (Cd * g) hη hlam hM hW (mul_nonneg hCd hg) A G v t df hdf hG hv X hbG hbv hbdf r s hr hs z
  have ht := normalizedCellB1_scaled_drift_uniform_mixed_grading_at_slow_point p q δ η lam (Md * g) 0
    Cf hη hlam (mul_nonneg hMd hg) le_rfl hCf A D (fun _ _ => 0) t fi hfi hD
    (fun _ => isBoxSmooth_slow_field p q (fun _ => (0 : ℝ)) contDiff_const) X hbD
    (fun _ _ _ _ _ _ => by
      simp only [Pi.zero_apply, mul_zero, iteratedFDeriv_fun_zero, norm_zero, zero_mul]
      exact le_rfl) hbfi r s hr hs z
  apply (add_le_add hu ht).trans_eq
  rw [normalizedCellB1UniformConstant_metric_mul]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The literal inverse with slow-dependent forcing retains rectangular quantitative jets. -/

theorem profileWeightedResponse_slow_dependent_reserve (p j : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M lam κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (g t) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → ℝ → ℂ)
    (hfm : ∀ X, Measurable (Function.uncurry (fun t z => f t X z)))
    (hff : ∀ t X, ContDiff ℝ (j : ℕ∞) (f t X))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ t z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f t X) z))
    (S : ℕ → ℝ) (hS : ∀ r ≤ p, 0 ≤ S r)
    (hfb : ∀ r ≤ p, ∀ t z X,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (f t Y) z) X‖ ≤ S r * lam ^ r)
    (hcenter : ∀ t X, unitProfileFourierCoeff (f t X) 0 = 0) :
    (∀ z, ContDiff ℝ (p : ℕ∞)
      (fun X => profileWeightedResponse (fun t => g t X) (fun t => f t X) a b z j)) ∧
    (∀ q ≤ p, Continuous (fun x : Vec 2 × ℝ => iteratedFDeriv ℝ q
      (fun X => profileWeightedResponse (fun t => g t X) (fun t => f t X) a b x.2 j) x.1)) ∧
    ∀ q ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ q
        (fun Y => profileWeightedResponse (fun t => g t Y) (fun t => f t Y) a b z j) X‖ ≤
      parameterizedModeJetConstant p q M lam κ (fun r => (2 : ℝ) ^ r * S r) * centeredProfileJetConstant := by
  obtain ⟨hUm, hUs, hUb, hU0⟩ := weightedParameterSource_data p j f hfm hff hper hfs S lam hfb hcenter
  have hS' : ∀ r ≤ p, 0 ≤ (2 : ℝ) ^ r * S r := fun r hr =>
    mul_nonneg (pow_nonneg (by norm_num) r) (hS r hr)
  have hh := parameterizedProfileResponse_reserve p g hm hs M lam κ a b
    hM hlam hκ hab hb hgl (weightedParameterSource f j) hUm hUs
    (fun r => (2 : ℝ) ^ r * S r) hS' hUb hU0
  simpa only [parameterizedProfileResponse_weighted_eq] using hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual finite exponential tests supply every field of the common-reserve coefficient state. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem liftCoefficient_ambient_data_of_tests
    (a b : ℝ) (hab : a ≤ b) (N n p q : ℕ) (c : LiftCoeff ι h)
    (hsym : ∀ m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), c m (α ∘ σ) = c m α) (hn : n ≤ N)
    (par : Fin 2) (lam : ℝ) (hlam : 0 < lam) (B : ι → ι → ℝ)
    (hB : ∀ v u, 0 ≤ B v u) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (hbox : ∀ A u v ξ, ∀ t ∈ Set.Icc a b,
      IsBoxSmooth p q (normalizedLiftTestField c n (lam • A) u v ξ t))
    (hbound : ∀ A u v ξ, ∀ r ≤ p, ∀ s ≤ q, ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (normalizedLiftTestField c n (lam • A) u v ξ t Y) z) X‖ ≤
          (K A * B v u * ‖ξ‖) * lam ^ (n + r))
    (htransverse : ∀ A u v ξ, IsTransverseOn par (Set.Icc a b)
      (normalizedLiftTestField c n (lam • A) u v ξ))
    (hmeasurable : ∀ A u v ξ, ∀ l : h v →L[ℝ] ℝ, ∀ X z, Measurable (fun t =>
      l (normalizedLiftTestField c n (lam • A) u v ξ (Set.projIcc a b hab t) X z))) :
    AmbientLiftCoefficientData par a b hab lam n p q c
      (fun v u => finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N K * B v u) := by
  have hdir (j s : ℝ) : lam • (s • coordinateSymbolDirection j) =
      s • (lam • coordinateSymbolDirection j) := smul_comm _ _ _
  refine ⟨fun v u => mul_nonneg (mul_nonneg (finiteLiftCalibrationBudget_nonneg N)
    (finiteLiftTestDirectionBudget_nonneg N K)) (hB v u), ?_, ?_, ?_, ?_⟩
  · intro m hm α v u t ht
    apply liftCoefficient_box_reserve_of_finite_tests p q n m hm c lam
      (ne_of_gt hlam) (hsym m) α t v u
    intro ξ j s
    have hb := hbox ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) u v ξ t ht
    rw [hdir] at hb
    exact hb
  · intro m hm α v u r hr s hs t ht X z
    exact liftCoefficient_grading_of_direction_budget N n m r s c hsym hn hm α t v u X z lam (B v u) hlam (hB v u) K
      (fun A ξ => (hbox A u v ξ t ht).mono hr hs)
      (fun A ξ => hbound A u v ξ r hr s hs t ht X z)
  · intro m hm α v u
    apply liftCoefficient_transverse_of_finite_tests par (Set.Icc a b) n m hm c
      lam (ne_of_gt hlam) (hsym m) α v u
    intro ξ j s
    have ht := htransverse ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) u v ξ
    rw [hdir] at ht
    exact ht
  · intro m hm α v u l X z
    apply liftCoefficient_dual_measurable_of_finite_tests n m hm c lam
      (ne_of_gt hlam) (hsym m) α a b hab X z v u l
    intro ξ l' j s
    have ht := hmeasurable ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) u v ξ l' X z
    rw [hdir] at ht
    exact ht
end

/-! Actual finite exponential tests supply every field of the common-reserve coefficient state. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_ambient_data_of_tests (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (hab : a ≤ b) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n p q : ℕ) (hhh : hh ≤ H) (hn : n ≤ N)
    (par : Fin 2) (lam : ℝ) (hlam : 0 < lam) (B : ι → ι → ℝ)
    (hB : ∀ v u, 0 ≤ B v u) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (hbox : ∀ A u v ξ, ∀ t ∈ Set.Icc a b,
      IsBoxSmooth p q (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t))
    (hbound : ∀ A u v ξ, ∀ r ≤ p, ∀ s ≤ q, ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t Y) z) X‖ ≤
          (K A * B v u * ‖ξ‖) * lam ^ (n + r))
    (htransverse : ∀ A u v ξ, IsTransverseOn par (Set.Icc a b)
      (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ))
    (hmeasurable : ∀ A u v ξ, ∀ l : h v →L[ℝ] ℝ, ∀ X z, Measurable (fun t =>
      l (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ (Set.projIcc a b hab t) X z))) :
    AmbientLiftCoefficientData par a b hab lam n p q (Cc hh n)
      (fun v u => finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N K * B v u) := by
  have hdir (j s : ℝ) : lam • (s • coordinateSymbolDirection j) =
      s • (lam • coordinateSymbolDirection j) := smul_comm _ _ _
  refine ⟨fun v u => mul_nonneg (mul_nonneg (finiteLiftCalibrationBudget_nonneg N)
    (finiteLiftTestDirectionBudget_nonneg N K)) (hB v u), ?_, ?_, ?_, ?_⟩
  · intro m hm α v u t ht
    apply liftCoefficient_box_reserve_of_finite_tests p q n m hm (Cc hh n) lam
      (ne_of_gt hlam) (hseq.2.2.2.2.1 hh hhh n m) α t v u
    intro ξ j s
    have hb := hbox ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) u v ξ t ht
    rw [hdir] at hb
    exact hb
  · intro m hm α v u r hr s hs t ht X z
    exact liftSequence_coefficient_grading_of_direction_budget Q sX sZ a b N H Cc hseq
      hh n m r s hhh hn hm α t v u X z lam (B v u) hlam (hB v u) K
      (fun A ξ => (hbox A u v ξ t ht).mono hr hs)
      (fun A ξ => hbound A u v ξ r hr s hs t ht X z)
  · intro m hm α v u
    apply liftCoefficient_transverse_of_finite_tests par (Set.Icc a b) n m hm (Cc hh n)
      lam (ne_of_gt hlam) (hseq.2.2.2.2.1 hh hhh n m) α v u
    intro ξ j s
    have ht := htransverse ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) u v ξ
    rw [hdir] at ht
    exact ht
  · intro m hm α v u l X z
    apply liftCoefficient_dual_measurable_of_finite_tests n m hm (Cc hh n) lam
      (ne_of_gt hlam) (hseq.2.2.2.2.1 hh hhh n m) α a b hab X z v u l
    intro ξ l' j s
    have ht := hmeasurable ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) u v ξ l' X z
    rw [hdir] at ht
    exact ht
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Paired first-cross bounds pass to the selected component without a dimension factor. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalizedCellB1_paired_component_mixed_grading
    (p q δ r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (η lam M Md W g Cf Cd : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (hW : 0 ≤ W)
    (hg : 0 ≤ g) (hCf : 0 ≤ Cf) (hCd : 0 ≤ Cd)
    (A : Vec 2 →L[ℝ] ℝ) (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (f fi : Vec 2 → Vec 2 → ∀ i, h i) (i₀ : ι)
    (hf : IsBoxSmooth (p + 1) (q + 1) f) (hfi : IsBoxSmooth (p + 1) (q + 1) fi)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (hJ : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => J t Y i j))
    (hv : ∀ k, IsBoxSmooth p q (fun (_ : Vec 2) z => v t z k)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbD : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j - J t Y i j) z) X‖ ≤ (Md * g) * lam ^ a)
    (hbv : ∀ k, ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun (_ : Vec 2) => iteratedFDeriv ℝ b
        (fun y => Real.sqrt η * v t y k) z) X‖ ≤ W * lam ^ a)
    (hbfi : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun y => fi Y y i₀) z) X‖ ≤ Cf * lam ^ (δ + a))
    (hbdf : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun y => f Y y i₀ - fi Y y i₀) z) X‖ ≤
        (Cd * g) * lam ^ (δ + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
      (Real.exp ((lam • A) Y))⁻¹ • cellB1 η G v t (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y i₀ -
      (Real.exp ((lam • A) Y))⁻¹ • cellB1 η J v t (fun Z w => Real.exp ((lam • A) Z) • fi Z w) Y y i₀) z) X‖ ≤
      (normalizedCellB1UniformConstant p q A M W * Cd +
        normalizedCellB1UniformConstant p q A Md 0 * Cf) * g * lam ^ ((δ + 1) + r) := by
  let Φ := fun Y y => Real.exp ((lam • A) Y) • f Y y
  let Φi := fun Y y => Real.exp ((lam • A) Y) • fi Y y
  have hΦ : IsBoxSmooth (p + 1) (q + 1) Φ := isBoxSmooth_bilinear
    (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hf
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (∀ i, h i) →L[ℝ] (∀ i, h i))
  have hΦi : IsBoxSmooth (p + 1) (q + 1) Φi := isBoxSmooth_bilinear
    (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hfi
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (∀ i, h i) →L[ℝ] (∀ i, h i))
  have heG (Y y : Vec 2) := cellB1_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀) η G v t Φ
    (hΦ.mono (by omega) (by omega))
    (fun i j => (hG i j).mono (by omega) (Nat.zero_le _)) Y y
  have heJ (Y y : Vec 2) := cellB1_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀) η J v t Φi
    (hΦi.mono (by omega) (by omega))
    (fun i j => (hJ i j).mono (by omega) (Nat.zero_le _)) Y y
  change ∀ Y y, cellB1 η G v t (fun Z w => Φ Z w i₀) Y y = cellB1 η G v t Φ Y y i₀ at heG
  change ∀ Y y, cellB1 η J v t (fun Z w => Φi Z w i₀) Y y = cellB1 η J v t Φi Y y i₀ at heJ
  change ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
    (Real.exp ((lam • A) Y))⁻¹ • cellB1 η G v t Φ Y y i₀ -
      (Real.exp ((lam • A) Y))⁻¹ • cellB1 η J v t Φi Y y i₀) z) X‖ ≤ _
  simp_rw [← heG, ← heJ]
  exact normalizedCellB1_paired_mixed_grading p q δ r s hr hs η lam M Md W g Cf Cd
    hη hlam hM hMd hW hg hCf hCd A G J v t (fun Y y => f Y y i₀) (fun Y y => fi Y y i₀)
    (hf.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀))
    (hfi.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀))
    hG hJ hv X hbG hbD hbv hbfi hbdf z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Mixed profile responses retain the source base grade at every supported slow order. -/

theorem profileWeightedResponse_graded_slow_dependent_reserve (p j δ : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M lam κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (g t) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → ℝ → ℂ)
    (hfm : ∀ X, Measurable (Function.uncurry (fun t z => f t X z)))
    (hff : ∀ t X, ContDiff ℝ (j : ℕ∞) (f t X))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ t z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f t X) z))
    (S : ℕ → ℝ) (hS : ∀ r ≤ p, 0 ≤ S r)
    (hfb : ∀ r ≤ p, ∀ t z X,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (f t Y) z) X‖ ≤ S r * lam ^ (δ + r))
    (hcenter : ∀ t X, unitProfileFourierCoeff (f t X) 0 = 0) :
    (∀ z, ContDiff ℝ (p : ℕ∞)
      (fun X => profileWeightedResponse (fun t => g t X) (fun t => f t X) a b z j)) ∧
    (∀ q ≤ p, Continuous (fun x : Vec 2 × ℝ => iteratedFDeriv ℝ q
      (fun X => profileWeightedResponse (fun t => g t X) (fun t => f t X) a b x.2 j) x.1)) ∧
    ∀ q ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ q
        (fun Y => profileWeightedResponse (fun t => g t Y) (fun t => f t Y) a b z j) X‖ ≤
      (parameterizedModeJetConstant p q M 1 κ (fun r => (2 : ℝ) ^ r * S r) *
        centeredProfileJetConstant) * lam ^ (δ + q) := by
  let S' := fun r => S r * lam ^ δ
  have hS' : ∀ r ≤ p, 0 ≤ S' r := fun r hr => mul_nonneg (hS r hr) (pow_nonneg hlam δ)
  have hfb' : ∀ r ≤ p, ∀ t z X,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (f t Y) z) X‖ ≤ S' r * lam ^ r := by
    intro r hr t z X
    simpa only [S', pow_add, mul_assoc] using hfb r hr t z X
  obtain ⟨hreg, hcont, hbound⟩ := profileWeightedResponse_slow_dependent_reserve p j
    g hm hs M lam κ a b hM hlam hκ hab hb hgl f hfm hff hper hfs S' hS' hfb' hcenter
  refine ⟨hreg, hcont, ?_⟩
  intro q hq X z
  apply (hbound q hq X z).trans_eq
  have he : (fun r => (2 : ℝ) ^ r * S' r) =
      fun r => ((2 : ℝ) ^ r * S r) * lam ^ δ := by
    funext r
    exact (mul_assoc _ _ _).symm
  rw [he, parameterizedModeJetConstant_base_grade]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit finite differential terms for the uncentered lift recurrence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def liftALeftTerms (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hh n : ℕ) (t : ℝ) (v : ι) : List (LeftTerm (∀ i, h i) (h v)) :=
  cellB1LeftTerms Q.η (Q.G t) (Q.v t) (liftComponentLeftTerms (n - 1) (Cc hh (n - 1)) t v) ++
    (if 2 ≤ n then cellB2LeftTerms Q.η (Q.G t)
      (liftComponentLeftTerms (n - 2) (Cc hh (n - 2)) t v) else []) ++
    (if hh = 0 then [] else
      (sourceConvolutionLeftTerms Q.edge Q.η t n (Cc (hh - 1)) v).map (fun c => c.smul (-1)))

theorem liftALeftTerms_order (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ) (v : ι)
    (c : LeftTerm (∀ i, h i) (h v)) (hc : c ∈ liftALeftTerms Q Cc hh n t v) : c.order ≤ n := by
  rcases List.mem_append.mp hc with hab | hs
  · rcases List.mem_append.mp hab with hfirst | hsecond
    · have := cellB1LeftTerms_order Q.η (Q.G t) (Q.v t) _ (n - 1)
        (liftComponentLeftTerms_order (n - 1) (Cc hh (n - 1)) t v) c hfirst
      omega
    · split_ifs at hsecond with hn2
      · have := cellB2LeftTerms_order Q.η (Q.G t) _ (n - 2)
          (liftComponentLeftTerms_order (n - 2) (Cc hh (n - 2)) t v) c hsecond
        omega
      · simp only [List.not_mem_nil] at hsecond
  · split_ifs at hs with hh0
    · simp only [List.not_mem_nil] at hs
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hs
      exact sourceConvolutionLeftTerms_order Q.edge Q.η t n (Cc (hh - 1)) v d hd

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Cell averaging with a bounded scalar weight preserves the slow scale grading. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem weighted_cell_mean_graded_jet_bound (p r q δ : ℕ) (hr : r ≤ p)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (w : Vec 2 → ℝ) (hw : Continuous w) (W : ℝ) (hW : ∀ z, ‖w z‖ ≤ W)
    (C : ℕ → ℝ) (lam : ℝ)
    (hb : ∀ j ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ j (fun Y => f Y z) X‖ ≤ C j * lam ^ (δ + j)) :
    ContDiff ℝ (p : ℕ∞) (fun X => fieldCellMean (fun z => w z • f X z)) ∧
      ∀ X, ‖iteratedFDeriv ℝ r (fun Y => fieldCellMean (fun z => w z • f Y z)) X‖ ≤
        ((2 : ℝ) ^ r * (W * C r)) * lam ^ (δ + r) := by
  have hwbox := isBoxSmooth_fast_field p 0 w (contDiff_zero.mpr hw)
  have hbox : IsBoxSmooth p 0 (fun X z => w z • f X z) :=
    isBoxSmooth_bilinear hwbox (hf.mono le_rfl (Nat.zero_le q))
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  apply fieldCellMean_graded_jet_bound p r 0 δ hr _ hbox (fun j => W * C j) lam
  intro j hj X z
  have hs : ContDiffAt ℝ (j : ℕ∞) (fun Y => f Y z) X :=
    (boxSmooth_slow_contDiff hf z).contDiffAt.of_le (by exact_mod_cast hj)
  rw [iteratedFDeriv_const_smul_apply' hs, norm_smul]
  calc
    _ ≤ W * ‖iteratedFDeriv ℝ j (fun Y => f Y z) X‖ :=
      mul_le_mul_of_nonneg_right (hW z) (norm_nonneg _)
    _ ≤ W * (C j * lam ^ (δ + j)) :=
      mul_le_mul_of_nonneg_left (hb j hj X z) ((norm_nonneg (w z)).trans (hW z))
    _ = _ := by ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Ambient matrix envelopes give energy bounds without a constituent-count factor. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem AmbientLiftCoefficientData.schurEnergyJet_le
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {c : LiftCoeff ι h} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (hlam : 0 ≤ lam) {m r fast : ℕ} (hm : m ≤ n) (hr : r ≤ p)
    (hfast : fast + 1 ≤ q) (π : ι → ℝ) (C : ℝ)
    (hM : HasRealSchurBudget (massConjugatedMatrix π M) C) :
    schurEnergyJet π (Set.Icc a b) fast r (c m) ≤
      ENNReal.ofReal ((2 ^ m : ℝ) * (fast + 1) * 2 ^ (r + 1) *
        lam ^ (n - m + r) * C) := by
  let B : ℝ := (2 ^ m : ℝ) * (fast + 1) * 2 ^ (r + 1) * lam ^ (n - m + r)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbudget : HasRealSchurBudget
      (massConjugatedMatrix π (fun v u => B * M v u)) (B * C) := by
    convert hM.const_mul B hB using 1
    funext v u
    simp only [massConjugatedMatrix]
    ring
  apply schurSums_le_of_real_matrix_budget π _ (B * C) hbudget
  intro v u
  exact (data.energyArray_le hlam hm hr hfast v u).trans_eq (by
    congr 1
    dsimp [B]
    ring)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual second cross operator on a lift test raises its cell degree by two. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalizedCellB2_lift_test_uniform_grading (n p q : ℕ) (η lam M B : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (A : Vec 2 →L[ℝ] ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (c : LiftCoeff ι h) (v u : ι) (ξ : h u)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v' u',
      IsBoxSmooth (p + 2) q (fun X z => c m α t X z v' u'))
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun X (_ : Vec 2) => G t X i j))
    (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => c m α t Y y v u) z) X‖ ≤ B * lam ^ (n - m + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB2 η G t
        (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      (normalizedCellB2UniformConstant p q A M * finiteLiftSymbolBudget n A * B * ‖ξ‖) *
        lam ^ ((n + 2) + r) := by
  let F := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t Y y
  have hf : IsBoxSmooth (p + 2) q F := by
    apply isBoxSmooth_pi (p + 2) q F
    intro w
    exact normalized_lift_test_box_reserve n (p + 2) q c lam A t w u ξ
      (fun m hm α => hc m hm α w u)
  have hb : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ y,
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
  have hh := normalizedCellB2_component_uniform_mixed_grading p q n η lam M
    (finiteLiftSymbolBudget n A * B * ‖ξ‖) hη0 hη1 hlam hM
    (mul_nonneg (mul_nonneg (finiteLiftSymbolBudget_nonneg n A) hB) (norm_nonneg ξ))
    A G t F v hf hG X hbG hb r s hr hs z
  simpa only [mul_assoc] using hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The literal inverse preserves the rectangular reserve for slow-dependent forcing. -/

theorem profileCellResponse_slow_dependent_isBoxSmooth (p q : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M lam κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (g t) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → ℝ → ℂ)
    (hfm : ∀ X, Measurable (Function.uncurry (fun t z => f t X z)))
    (hff : ∀ t X, ContDiff ℝ (q : ℕ∞) (f t X))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ j ≤ q, ∀ t z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f t X) z))
    (S : ℕ → ℕ → ℝ) (hS : ∀ r ≤ p, ∀ j ≤ q, 0 ≤ S r j)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (f t Y) z) X‖ ≤ S r j * lam ^ r)
    (hcenter : ∀ t X, unitProfileFourierCoeff (f t X) 0 = 0)
    (l : Vec 2 →L[ℝ] ℝ) :
    IsBoxSmooth p q (fun X z => profileCellResponse (fun t => g t X) (fun t => f t X) a b (l z)) := by
  have hi : ∀ X, IntegrableOn (fun t => g t X) (Icc a b) := by
    intro X
    apply (integrable_const M).mono' (hm X).aestronglyMeasurable
    exact ae_of_all _ (fun t => by simpa using hb 0 (Nat.zero_le p) t X)
  have hfast : ∀ j ≤ q, ∀ t X z, ‖iteratedDeriv j (f t X) z‖ ≤ S 0 j := by
    intro j hj t X z
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using!
      hfb 0 (Nat.zero_le p) j hj t z X
  have he (j : ℕ) (hj : j ≤ q) (z : ℝ) :
      (fun X => iteratedDeriv j (profileCellResponse (fun t => g t X) (fun t => f t X) a b) z) =
        fun X => profileWeightedResponse (fun t => g t X) (fun t => f t X) a b z j := by
    funext X
    exact profileCellResponse_fast_jet_identity (fun t => g t X) (fun t => f t X) a b κ hab hκ
      (hi X) (fun t _ => hgl t X) j (S 0)
      (fun r hr => hS 0 (Nat.zero_le p) r (hr.trans hj))
      (fun t _ => (hff t X).of_le (by exact_mod_cast hj)) (fun t _ => hper t X)
      (fun r hr t _ z _ => hfast r (hr.trans hj) t X z) z
  apply scalar_fast_box_transport p q _ _ _ _ l
  · intro X
    exact profileCellResponse_contDiff (fun t => g t X) (fun t => f t X) a b κ hab hκ (hi X)
      (fun t _ => hgl t X) q (S 0) (hS 0 (Nat.zero_le p))
      (fun t _ => hff t X) (fun t _ => hper t X)
      (fun j hj t _ z _ => hfast j hj t X z)
  · intro j hj z
    rw [he j hj z]
    exact (profileWeightedResponse_slow_dependent_reserve p j g hm hs M lam κ a b
      hM hlam hκ hab hb hgl f hfm (fun t X => (hff t X).of_le (by exact_mod_cast hj))
      hper (hfs j hj) (fun r => S r j) (fun r hr => hS r hr j hj)
      (fun r hr => hfb r hr j hj) hcenter).1 z
  · intro r j hr hj
    simp_rw [he j hj]
    exact (profileWeightedResponse_slow_dependent_reserve p j g hm hs M lam κ a b
      hM hlam hκ hab hb hgl f hfm (fun t X => (hff t X).of_le (by exact_mod_cast hj))
      hper (hfs j hj) (fun r => S r j) (fun r hr => hS r hr j hj)
      (fun r hr => hfb r hr j hj) hcenter).2.1 r hr

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual paired coefficient envelopes give dimension-independent energy bounds. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem AmbientLiftCoefficientData.paired_diagonal_energy_le
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {c : LiftCoeff ι h} {B g : ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q c
      (fun v u => (B * (if v = u then 1 else 0)) * g))
    (hB : 0 ≤ B) (hg : 0 ≤ g) (hlam : 0 ≤ lam)
    {m r fast : ℕ} (hm : m ≤ n) (hr : r ≤ p) (hfast : fast + 1 ≤ q)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) :
    schurEnergyJet π (Set.Icc a b) fast r (c m) ≤
      ENNReal.ofReal ((2 ^ m * (fast + 1) * 2 ^ (r + 1) * B) * g * lam ^ (n - m + r)) := by
  have hb : HasRealSchurBudget
      (massConjugatedMatrix π (fun v u => (B * (if v = u then 1 else 0)) * g)) (B * g) := by
    convert (mass_identity_matrix_schur_budget π hπ).const_mul (B * g) (mul_nonneg hB hg) using 1
    · funext v u
      simp only [massConjugatedMatrix]
      ring
    · ring
  exact (data.schurEnergyJet_le hlam hm hr hfast π (B * g) hb).trans_eq (by congr 1; ring)
end

/-! The actual lift mean inherits normalized grading from its actual uncentered source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, SecondCountableTopology (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, SecondCountableTopology (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem liftA_fast_continuous_of_normalized_box (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n p q : ℕ) (t : ℝ) (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ)
    (hf : ∀ u, IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n t X z u)) (X : Vec 2) :
    Continuous (fun z => liftA Q Cc f hh n t X z) := by
  apply continuous_pi
  intro u
  have he (z : Vec 2) : liftA Q Cc f hh n t X z u =
      Real.exp ((lam • A) X) • ((Real.exp ((lam • A) X))⁻¹ •
        liftA Q Cc f hh n t X z u) := by
    rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hEq : (fun z => liftA Q Cc f hh n t X z u) =
      (fun z => Real.exp ((lam • A) X) • ((Real.exp ((lam • A) X))⁻¹ •
        liftA Q Cc f hh n t X z u)) := funext he
  rw [hEq]
  exact ((hf u).1 X).continuous.const_smul _

theorem liftMean_normalized_component_grading_of_liftA (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n p q r : ℕ) (hr : r ≤ p) (t : ℝ) (v : ι)
    (A : Vec 2 →L[ℝ] ℝ) (lam C : ℝ) (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (hf : ∀ u, IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n t X z u))
    (hb : ∀ j ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ j (fun Y => (Real.exp ((lam • A) Y))⁻¹ •
        liftA Q Cc f hh n t Y z v) X‖ ≤ C * lam ^ (n + j)) :
    ContDiff ℝ (p : ℕ∞) (fun X => (Real.exp ((lam • A) X))⁻¹ •
      liftMean Q Cc f hh n t X v) ∧
      ∀ X, ‖iteratedFDeriv ℝ r (fun Y => (Real.exp ((lam • A) Y))⁻¹ •
        liftMean Q Cc f hh n t Y v) X‖ ≤ ((2 : ℝ) ^ p * C) * lam ^ (n + r) := by
  have hc (X : Vec 2) :=
    liftA_fast_continuous_of_normalized_box Q Cc f hh n p q t A lam hf X
  have he (X : Vec 2) : fieldCellMean (fun z => liftA Q Cc f hh n t X z v) =
      liftMean Q Cc f hh n t X v := by
    exact AVRegularity.fieldCellMean_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) (hc X)
  have hm := normalized_fieldCellMean_graded_jet_bound p r q n hr A lam C hlam hC
    (fun X z => liftA Q Cc f hh n t X z v) (hf v) hb
  simpa only [he] using hm
end

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! One metric perturbation constant covers every slow order of an ambient reserve. -/

theorem metricDifferenceModeJetConstant_nonneg (p r : ℕ) (M Md κ : ℝ) (S : ℕ → ℝ)
    (hM : 0 ≤ M) (hMd : 0 ≤ Md) (hκ : 0 < κ) (hS : ∀ s ≤ r, 0 ≤ S s) :
    0 ≤ metricDifferenceModeJetConstant p r M Md κ S := by
  unfold metricDifferenceModeJetConstant
  exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity)
    (metricDifferenceKernelSourceConstant_nonneg p r M Md κ S hM hMd hκ hS)))
    (div_nonneg (by positivity) hκ.le)

def metricInverseUniformConstant (p : ℕ) (M Md κ : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (p + 1),
    metricDifferenceModeJetConstant p r M Md κ (fun s => (2 : ℝ) ^ s) * centeredProfileJetConstant

theorem metricInverseUniformConstant_entry_le (p r : ℕ) (hr : r ≤ p) (M Md κ : ℝ)
    (hM : 0 ≤ M) (hMd : 0 ≤ Md) (hκ : 0 < κ) :
    metricDifferenceModeJetConstant p r M Md κ (fun s => (2 : ℝ) ^ s) * centeredProfileJetConstant ≤
      metricInverseUniformConstant p M Md κ := by
  exact Finset.single_le_sum (fun r _ => mul_nonneg
    (metricDifferenceModeJetConstant_nonneg p r M Md κ _ hM hMd hκ
      (fun _ _ => by positivity)) centeredProfileJetConstant_nonneg)
    (Finset.mem_range.mpr (by omega))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Bounded drift-weighted means retain the grading of a genuine paired coefficient difference. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem weighted_cell_mean_paired_graded_jet_bound (p r q δ : ℕ) (hr : r ≤ p)
    (f fi : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f) (hfi : IsBoxSmooth p q fi)
    (w : Vec 2 → ℝ) (hw : Continuous w) (W : ℝ) (hW : ∀ z, ‖w z‖ ≤ W)
    (C eps lam : ℝ)
    (hb : ∀ j ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ j (fun Y => f Y z - fi Y z) X‖ ≤ (C * eps) * lam ^ (δ + j)) :
    ContDiff ℝ (p : ℕ∞) (fun X => fieldCellMean (fun z => w z • f X z) -
      fieldCellMean (fun z => w z • fi X z)) ∧
    ∀ X, ‖iteratedFDeriv ℝ r (fun Y => fieldCellMean (fun z => w z • f Y z) -
      fieldCellMean (fun z => w z • fi Y z)) X‖ ≤
      ((2 : ℝ) ^ r * (W * C)) * eps * lam ^ (δ + r) := by
  have he (X : Vec 2) : fieldCellMean (fun z => w z • f X z) -
      fieldCellMean (fun z => w z • fi X z) = fieldCellMean (fun z => w z • (f X z - fi X z)) := by
    simpa only [smul_sub] using
      (fieldCellMean_sub (f := fun z => w z • f X z) (g := fun z => w z • fi X z)
        (hw.smul (hf.1 X).continuous) (hw.smul (hfi.1 X).continuous)).symm
  simp_rw [he]
  have hh := weighted_cell_mean_graded_jet_bound p r q δ hr (fun X z => f X z - fi X z)
    (hf.sub hfi) w hw W hW (fun _ => C * eps) lam hb
  refine ⟨hh.1, ?_⟩
  intro X
  exact (hh.2 X).trans_eq (by ring)

end AVRegularity.CycleComparison.Lift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The actual second cross lift term has a fixed-data budget under its ambient predecessor state. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_second_cross_lift_bound
    (n p q p' q' : ℕ) (hp : p + 1 ≤ qs)
    (hp' : p + 2 ≤ p') (hq' : q ≤ q')
    (c : LiftCoeff ι h) (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' c M)
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB2 Q.η Q.G t
        (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      (normalizedCellB2UniformConstant p q A (metricParameterBudget (p + 1) CG) *
        finiteLiftSymbolBudget n A * M v u * ‖ξ‖) * lam ^ ((n + 2) + r) := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hη : 0 ≤ Q.η := by rw [P.η_eq]; exact (div_pos P.ν_pos P.B_pos).le
  exact normalizedCellB2_lift_test_uniform_grading n p q Q.η lam
    (metricParameterBudget (p + 1) CG) (M v u) hη P.η_le hlam
    (metricParameterBudget_nonneg (p + 1) CG) (data.nonneg v u) A Q.G t c v u ξ
    (fun m hm α v' u' => (data.box m hm α v' u' t ht).mono hp' hq')
    (fun i j => setting_metric_entry_box P (p + 1) q hp t ht i j) X
    (fun i j a ha b _ y => setting_metric_mixed_uniform_bound P (p + 1) a b hp ha t ht X y i j)
    (fun m hm α a ha b hb y => data.bound m hm α v u a (ha.trans hp') b (hb.trans hq') t ht X y)
    r s hr hs z

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Diagonal mean terms act correctly from predecessor fields, without a completed sequence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_diagonal_mean_left_terms_apply_of_coefficients
    (Cc : ℕ → ℕ → LiftCoeff ι h) (n : ℕ) (hn : 2 ≤ n)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2)
    (hc : ∀ k m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      ContDiff ℝ 1 (fun Y => diagonalMeanFluxCoefficient Q Cc n k m α t Y 0 v u))
    (hfast : ∀ Y m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      Continuous (fun y => Cc 0 (n - 1) m α t Y y v u))
    (hid : liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y)
    (hΦ : GoodField 2 (liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t))
    (hΨ : 3 ≤ n → CoefField True 2 (liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t)) :
    leftTermsApply (meanFluxLeftTerms n (diagonalMeanFluxCoefficient Q Cc n) t) f X z =
      liftMean Q Cc (fun _ => f) 0 n t X := by
  rw [meanFluxLeftTerms_apply n _ t hc f hf X z]
  have he (k : Fin 2) :
      (fun Y => liftApply (n - 1) (diagonalMeanFluxCoefficient Q Cc n k)
        (fun _ => f) t Y 0) = fun Y =>
      fieldCellMean (fun y => (Real.sqrt Q.η * Q.v t y k) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t Y y) +
      if n = 2 then -Q.η • ∑ j : Fin 2, Q.G t Y k j • fderiv ℝ f Y (basisVec j) else 0 := by
    funext Y
    exact setting_diagonal_mean_flux_coefficient_vector_apply_of_coefficients P
      Cc n hn f k t ht Y 0 (hfast Y)
  simp_rw [he]
  by_cases hn2 : n = 2
  · subst n
    simp only [ite_true, neg_smul, ← sub_eq_add_neg]
    exact (liftMean_diagonal_second_of_predecessor_fields P Cc f hf t ht X hid hΦ).symm
  · simp only [ite_eq_right hn2, add_zero]
    exact (liftMean_diagonal_ge_three_of_predecessor_fields P Cc f hf n (by omega)
      t ht X hΦ (hΨ (by omega))).symm

end AVRegularity.CycleComparison.Lift
end
end
