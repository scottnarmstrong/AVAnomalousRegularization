-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleDamping.ReferenceTimeEquation
import AVenhance.Infra.Section4.IteratesStreamFlux
import AVRegularity.CycleJoint.NativeRawOriginalFamilyTaylorSplitEdges
public import AVRegularity.CycleEvolution.FibreScalarSeriesHighIncrementBound
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.OcMeanFlux
public import AVRegularity.Weighted.BoundedWeightRoot
import AVRegularity.CycleReference.SingleModeFlux
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance Filter Topology
namespace AVRegularity.CycleWords.Interior

/-! The stream function in translated cell coordinates, including its uniform amplitude. -/

def cellStream (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν : ℝ) (y₀ : Vec 2)
    (t : ℝ) (z : Vec 2) : ℝ :=
  (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m ^ 2) *
    ocPulseStream α q Λ ζ m (ocEll q Λ m ν ^ 2 * t) (y₀ + ocEpsilon q Λ m • z)

theorem pulseStream_joint_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ocPulseStream α q Λ ζ m p.1 p.2) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro p
  obtain ⟨S, hS⟩ := CycleReference.cutoff_locally_finite
    (α := α) (q := q) (m := m) hΛ p.1
  let f := fun r : ℝ × Vec 2 =>
    ∑ k ∈ S, ocPulse α q Λ ζ m k.1 r.1 * ocShear α q Λ m k.1 r.2
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    apply ContDiff.sum
    intro k _
    exact ((CycleReference.ocPulse_contDiff hζ k.1).comp contDiff_fst).mul
      ((CycleReference.ocShear_contDiff α q Λ m k.1).comp contDiff_snd)
  have he : (fun r : ℝ × Vec 2 => ocPulseStream α q Λ ζ m r.1 r.2) =ᶠ[𝓝 p] f := by
    filter_upwards [continuous_fst.continuousAt.eventually hS] with r hr
    apply tsum_eq_sum
    intro k hk
    have hz : ocPulse α q Λ ζ m k.1 r.1 = 0 := by
      by_contra hn
      have h1 := CycleReference.ocCutoff_eq_one_of_pulse_ne_zero hΛ hζ hn
      rw [hr k hk] at h1
      exact zero_ne_one h1
    rw [hz, zero_mul]
  exact hf.contDiffAt.congr_of_eventuallyEq he

theorem cellStream_smooth {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => cellStream α q Λ ζ m ν y₀ p.1 p.2) := by
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      (ocEll q Λ m ν ^ 2 * p.1, y₀ + ocEpsilon q Λ m • p.2)) := by fun_prop
  have hh := (pulseStream_joint_contDiff (α := α) (q := q) (m := m) hΛ hζ).comp ha
  simpa only [cellStream, Function.comp_def] using
    (contDiff_const (c := ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m ^ 2)).mul hh

theorem cellStream_velocity {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y₀ z : Vec 2) :
    ocCellDrift α q Λ ζ m ν y₀ t z = streamVel (cellStream α q Λ ζ m ν y₀) t z := by
  have he := (Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne'
  have hf : Differentiable ℝ (ocPulseStream α q Λ ζ m (ocEll q Λ m ν ^ 2 * t)) := by
    exact ((pulseStream_joint_contDiff hΛ hζ).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have ha : Differentiable ℝ (fun z : Vec 2 => y₀ + ocEpsilon q Λ m • z) := by fun_prop
  have hc : Differentiable ℝ (fun z : Vec 2 =>
      ocPulseStream α q Λ ζ m (ocEll q Λ m ν ^ 2 * t) (y₀ + ocEpsilon q Λ m • z)) := hf.comp ha
  have hg : spaceGrad (cellStream α q Λ ζ m ν y₀ t) z =
      (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) •
        spaceGrad (ocPulseStream α q Λ ζ m (ocEll q Λ m ν ^ 2 * t))
          (y₀ + ocEpsilon q Λ m • z) := by
    ext i
    unfold spaceGrad cellStream
    rw [fderiv_const_mul (hc z)]
    simp only [smul_apply, smul_eq_mul, Pi.smul_apply]
    rw [CycleDamping.affine_coord_derivative _ hf]
    field_simp
  simp only [ocCellDrift, streamVel, hg, Matrix.mulVec_smul]

theorem cellStream_periodic {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t : ℝ) (y₀ : Vec 2) :
    IsZ2Periodic (cellStream α q Λ ζ m ν y₀ t) := by
  have he := (Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne'
  have hp (k : ℤ) : IsZ2Periodic (fun z => ocShear α q Λ m k (y₀ + ocEpsilon q Λ m • z)) := by
    intro n z
    have ha (i : Fin 2) :
        2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (y₀ + ocEpsilon q Λ m • (z + latticeShift n)) i =
        2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (y₀ + ocEpsilon q Λ m • z) i + (n i : ℝ) * (2 * Real.pi) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, latticeShift]
      field_simp
      ring
    simp only [CycleReference.ocShear_sine_formula]
    split_ifs <;> simp only [ha, Real.sin_add_int_mul_two_pi]
  intro n z
  unfold cellStream ocPulseStream
  congr 1
  apply tsum_congr
  intro k
  exact congrArg (fun r : ℝ => ocPulse α q Λ ζ m k.1 (ocEll q Λ m ν ^ 2 * t) * r)
    (hp k.1 n z)

theorem pulseStream_abs_le {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (t : ℝ) (y : Vec 2) :
    |ocPulseStream α q Λ ζ m t y| ≤ ocEpsilon q Λ m ^ (1 + α) := by
  have he := Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k t ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    rw [CycleReference.ocPulseStream_eq_active hΛ hζ hk hp, abs_mul]
    have hs : |ocShear α q Λ m k y| ≤ ocEpsilon q Λ m ^ (1 + α) := by
      rw [CycleReference.ocShear_sine_formula]
      split_ifs
      · rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos he _)]
        exact mul_le_of_le_one_right (Real.rpow_pos_of_pos he _).le (Real.abs_sin_le_one _)
      · rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos he _)]
        exact mul_le_of_le_one_right (Real.rpow_pos_of_pos he _).le (Real.abs_sin_le_one _)
      · simpa using (Real.rpow_pos_of_pos he (1 + α)).le
    rw [abs_of_nonneg (CycleReference.ocPulse_range hζ k t).1]
    exact (mul_le_mul_of_nonneg_left hs (CycleReference.ocPulse_range hζ k t).1).trans
      (mul_le_of_le_one_left (Real.rpow_pos_of_pos he _).le (CycleReference.ocPulse_range hζ k t).2)
  · have hz : ∀ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t = 0 := by
      intro k
      by_contra hn
      exact hp ⟨k.1, k.2, hn⟩
    simp only [ocPulseStream, hz, zero_mul, tsum_zero, abs_zero]
    exact (Real.rpow_pos_of_pos he _).le

theorem cellStream_amplitude {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (y₀ z : Vec 2) (t : ℝ) :
    Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * |cellStream α q Λ ζ m ν y₀ t z| ≤
      Real.sqrt (2 / ((1 - Real.exp (-2)) / 96)) := by
  have he := Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have ha : ocEpsilon q Λ m ^ (1 + α) / ocEpsilon q Λ m ^ 2 = ocA α q Λ m := by
    rw [← Real.rpow_two, ← Real.rpow_sub he]
    congr 1
  unfold cellStream
  rw [abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  calc
    _ ≤ Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
        ((ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m ^ 2) * ocEpsilon q Λ m ^ (1 + α)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pulseStream_abs_le hΛ hζ _ _)
        (div_nonneg (sq_nonneg _) (sq_nonneg _))) (Real.sqrt_nonneg _)
    _ = Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ocA α q Λ m * ocEll q Λ m ν ^ 2 := by
      rw [← ha]
      ring
    _ ≤ _ := CycleDamping.corrector_amplitude_bound hΛ hζ hν hr

end AVRegularity.CycleWords.Interior
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords.Interior

/-! The decaying weight `ω = (1 + ϖ²|z|²)^{-p}` of ingredient 05 and its energies.

`weightedJetNorm (fun _ => 1) (-p) k ϖ 1` of a plane carrier is `Σ_{a≤k} (1/a!)√I_a`, with
`I_a = ∫ ω Σ_w |D_w^a u|²`, and the factorial energy `Σ_a ρ^{2a}/(a!)² I_a` (`ρ ≤ 1`) is
comparable to its square up to `√(k+1)ρ^{-k}`. -/

/-- The decaying weight `(1 + ϖ²|z|²)^{-p}`. -/
def negWeight (ϖ : ℝ) (p : ℕ) (z : Vec 2) : ℝ := ((1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ p)⁻¹

theorem negWeight_base_pos (ϖ : ℝ) (z : Vec 2) : 0 < 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by
  positivity

theorem negWeight_pos (ϖ : ℝ) (p : ℕ) (z : Vec 2) : 0 < negWeight ϖ p z := by
  unfold negWeight
  have := negWeight_base_pos ϖ z
  positivity

theorem negWeight_le_one (ϖ : ℝ) (p : ℕ) (z : Vec 2) : negWeight ϖ p z ≤ 1 := by
  unfold negWeight
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_add_of_nonneg_right (by positivity)))

theorem continuous_negWeight (ϖ : ℝ) (p : ℕ) : Continuous (negWeight ϖ p) := by
  unfold negWeight
  exact (by fun_prop : Continuous fun z : Vec 2 => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ p).inv₀
    fun z => (pow_pos (negWeight_base_pos ϖ z) p).ne'

/-- The weight of `weightedJetNorm` at exponent `-p` squares to the decaying weight. -/
theorem negRoot_sq (ϖ : ℝ) (p : ℕ) (z : Vec 2) :
    ((1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p : ℝ) / 2)) ^ 2 = negWeight ϖ p z := by
  have hb := negWeight_base_pos ϖ z
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hb.le,
    show -(p : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(p : ℝ) by push_cast; ring, Real.rpow_neg hb.le,
    Real.rpow_natCast]
  rfl

/-- The weighted integral of the order-`a` jets. -/
def negJetIntegral (ϖ : ℝ) (p : ℕ) {k : ℕ} (D : RawJet2 k ℝ) (a : Fin (k + 1)) : ℝ :=
  ∫ z, negWeight ϖ p z * ∑ w : DerivativeWord2 a.val, ‖D ⟨a, w⟩ z‖ ^ 2

theorem jet_sq_integrable {k : ℕ} (U : PlaneHk Set.univ k ℝ) (a : Fin (k + 1))
    (w : DerivativeWord2 a.val) :
    Integrable (fun z => ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2) volume := by
  have h := U.toFunction.memL2 ⟨a, w⟩
  rw [Measure.restrict_univ] at h
  exact h.integrable_norm_pow (by norm_num)

theorem weighted_jet_sq_integrable {k : ℕ} (U : PlaneHk Set.univ k ℝ) (a : Fin (k + 1))
    (q : Vec 2 → ℝ) (hq : Continuous q) (C : ℝ) (hqC : ∀ z, |q z| ≤ C) :
    Integrable (fun z => q z * ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2)
      volume := by
  have hs : Integrable (fun z => ∑ w : DerivativeWord2 a.val,
      ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2) volume :=
    integrable_finsetSum _ fun w _ => jet_sq_integrable U a w
  exact hs.bdd_mul hq.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hqC z)

theorem negJetIntegral_nonneg (ϖ : ℝ) (p : ℕ) {k : ℕ} (D : RawJet2 k ℝ) (a : Fin (k + 1)) :
    0 ≤ negJetIntegral ϖ p D a :=
  integral_nonneg fun z => mul_nonneg (negWeight_pos ϖ p z).le
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The factorial energy at a weight `q`, written through the order integrals. -/
theorem rawWeightedFactorialEnergy_eq_sum {k : ℕ} (U : PlaneHk Set.univ k ℝ) (ρ : ℝ)
    (q : Vec 2 → ℝ) (hq : Continuous q) (C : ℝ) (hqC : ∀ z, |q z| ≤ C) :
    rawWeightedFactorialEnergy ρ q U.toFunction.jet =
      ∑ a : Fin (k + 1), factorialWeight ρ a.val *
        ∫ z, q z * ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2 := by
  unfold rawWeightedFactorialEnergy
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← integral_finsetSum]
  · simp only [Finset.mul_sum]
  · intro w _
    have h := jet_sq_integrable U a w
    exact h.bdd_mul hq.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hqC z)

/-- The negative-weight jet norm through the order integrals. -/
theorem weightedJetNorm_neg_eq {k : ℕ} (ϖ : ℝ) (p : ℕ) (U : PlaneHk Set.univ k ℝ) :
    weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
        (fun _ a w' => planeJetOrder U a w') =
      ENNReal.ofReal (∑ a : Fin (k + 1), (1 / (a.val.factorial : ℝ)) *
        Real.sqrt (negJetIntegral ϖ p U.toFunction.jet a)) := by
  unfold weightedJetNorm
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity), ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hjet : ∀ (w : DerivativeWord2 a.val) (z : Vec 2),
      planeJetOrder U a.val w z = U.toFunction.jet ⟨a, w⟩ z := fun w z => by
    rw [planeJetOrder_eq_stored (Nat.lt_succ_iff.mp a.isLt) U w]
  set g : Vec 2 → ℝ := fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p : ℝ) / 2) *
    Real.sqrt (∑ w : DerivativeWord2 a.val, ‖planeJetOrder U a.val w z‖ ^ 2) with hg
  have hg2 : ∀ z, g z ^ 2 = negWeight ϖ p z *
      ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2 := fun z => by
    rw [hg]
    dsimp only
    rw [mul_pow, negRoot_sq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [hjet]
  have hmeas : AEStronglyMeasurable g volume := by
    have h1 : Continuous fun z : Vec 2 =>
        (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-(p : ℝ) / 2) :=
      (by fun_prop : Continuous fun z : Vec 2 => 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)).rpow_const
        fun z => Or.inl (negWeight_base_pos ϖ z).ne'
    have h2 : AEStronglyMeasurable (fun z => ∑ w : DerivativeWord2 a.val,
        ‖planeJetOrder U a.val w z‖ ^ 2) volume := by
      simp only [hjet]
      exact Finset.aestronglyMeasurable_fun_sum _ fun w _ =>
        ((jet_sq_integrable U a w).aestronglyMeasurable)
    exact h1.aestronglyMeasurable.mul (Real.continuous_sqrt.comp_aestronglyMeasurable h2)
  have hint : Integrable (fun z => g z ^ 2) volume := by
    simp only [hg2]
    exact weighted_jet_sq_integrable U a (negWeight ϖ p) (continuous_negWeight ϖ p) 1
      fun z => by rw [abs_of_pos (negWeight_pos ϖ p z)]; exact negWeight_le_one ϖ p z
  have hmem : MemLp g 2 volume := (memLp_two_iff_integrable_sq hmeas).mpr hint
  have hE : eLpNorm g 2 volume = ENNReal.ofReal (Real.sqrt (negJetIntegral ϖ p
      U.toFunction.jet a)) := by
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    congr 1
    rw [Real.sqrt_eq_rpow]
    congr 1
    · unfold negJetIntegral
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      have h2 : ‖g z‖ ^ ((2 : ℝ≥0∞).toReal) = g z ^ 2 := by
        rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
      exact h2.trans (hg2 z)
    · norm_num
  simp only [Finset.univ_unique, Finset.sum_singleton, inv_one, ENNReal.ofReal_one, one_mul,
    one_pow]
  rw [hE, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem negNorm_le_energy (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (I : Fin (k + 1) → ℝ)
    (hI : ∀ a, 0 ≤ I a) :
    ∑ a : Fin (k + 1), (1 / (a.val.factorial : ℝ)) * Real.sqrt (I a) ≤
      Real.sqrt (k + 1) * ρ⁻¹ ^ k *
        Real.sqrt (∑ a : Fin (k + 1), factorialWeight ρ a.val * I a) := by
  set c : Fin (k + 1) → ℝ := fun a => ρ ^ a.val / (a.val.factorial : ℝ) * Real.sqrt (I a)
  have hc0 : ∀ a, 0 ≤ c a := fun a => by positivity
  have hinv : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ |>.mpr hρ1
  have hterm : ∀ a : Fin (k + 1), (1 / (a.val.factorial : ℝ)) * Real.sqrt (I a) ≤
      ρ⁻¹ ^ k * c a := fun a => by
    have ha : a.val ≤ k := Nat.lt_succ_iff.mp a.isLt
    have hpow : ρ⁻¹ ^ a.val ≤ ρ⁻¹ ^ k := pow_le_pow_right₀ hinv ha
    calc (1 / (a.val.factorial : ℝ)) * Real.sqrt (I a) = ρ⁻¹ ^ a.val * c a := by
          simp only [c]
          rw [inv_pow]
          field_simp
      _ ≤ ρ⁻¹ ^ k * c a := mul_le_mul_of_nonneg_right hpow (hc0 a)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin (k + 1) => (1 : ℝ)) c
  have hcsq : ∀ a : Fin (k + 1), c a ^ 2 = factorialWeight ρ a.val * I a := fun a => by
    simp only [c, factorialWeight]
    rw [mul_pow, div_pow, Real.sq_sqrt (hI a), ← pow_mul, mul_comm a.val 2]
  simp only [one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_mul, hcsq] at hcs
  calc ∑ a : Fin (k + 1), (1 / (a.val.factorial : ℝ)) * Real.sqrt (I a)
      ≤ ∑ a : Fin (k + 1), ρ⁻¹ ^ k * c a := Finset.sum_le_sum fun a _ => hterm a
    _ = ρ⁻¹ ^ k * ∑ a : Fin (k + 1), c a := (Finset.mul_sum _ _ _).symm
    _ ≤ ρ⁻¹ ^ k * (Real.sqrt (k + 1) *
          Real.sqrt (∑ a : Fin (k + 1), factorialWeight ρ a.val * I a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hcs
    _ = _ := by ring

theorem energy_le_negNorm_sq (k : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (I : Fin (k + 1) → ℝ) (hI : ∀ a, 0 ≤ I a) :
    ∑ a : Fin (k + 1), factorialWeight ρ a.val * I a ≤
      (∑ a : Fin (k + 1), (1 / (a.val.factorial : ℝ)) * Real.sqrt (I a)) ^ 2 := by
  have hterm : ∀ a : Fin (k + 1), factorialWeight ρ a.val * I a ≤
      ((1 / (a.val.factorial : ℝ)) * Real.sqrt (I a)) ^ 2 := fun a => by
    rw [mul_pow, Real.sq_sqrt (hI a), factorialWeight, div_pow, one_pow]
    apply mul_le_mul_of_nonneg_right _ (hI a)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_one₀ hρ0 hρ1
  exact (Finset.sum_le_sum fun a _ => hterm a).trans
    (Finset.sum_sq_le_sq_sum_of_nonneg fun a _ => by positivity)

theorem clipWeight_two_le {s : ℝ} (hs : 0 ≤ s) : clipWeight 2 s ≤ s := by
  unfold clipWeight
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem half_le_clipWeight_two {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 2) : s / 2 ≤ clipWeight 2 s := by
  unfold clipWeight
  rw [le_div_iff₀ (by linarith)]
  nlinarith

theorem continuous_clipWeight_two_shift (ϖ : ℝ) (p : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    Continuous fun z => clipWeight 2 (negWeight ϖ p z + ε) := by
  unfold clipWeight
  exact ((continuous_const.mul ((continuous_negWeight ϖ p).add continuous_const)).div
    (continuous_const.add ((continuous_negWeight ϖ p).add continuous_const))) fun z =>
      ne_of_gt (by
        have := negWeight_pos ϖ p z
        simp only [Pi.add_apply]
        linarith)

/-- The clipped shifted weight is between half the decaying weight and the decaying weight plus
`ε`, at the level of the factorial energies. -/
theorem clip_shift_energy_bounds {k : ℕ} (U : PlaneHk Set.univ k ℝ) (ϖ : ℝ) (p : ℕ)
    {ρ ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ a : Fin (k + 1), factorialWeight ρ a.val * negJetIntegral ϖ p U.toFunction.jet a) ≤
        2 * rawWeightedFactorialEnergy ρ (fun z => clipWeight 2 (negWeight ϖ p z + ε))
          U.toFunction.jet ∧
      rawWeightedFactorialEnergy ρ (fun z => clipWeight 2 (negWeight ϖ p z + ε))
          U.toFunction.jet ≤
        ∑ a : Fin (k + 1), factorialWeight ρ a.val * (negJetIntegral ϖ p U.toFunction.jet a +
          ε * ∫ z, ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2) := by
  have hqc := continuous_clipWeight_two_shift ϖ p ε hε.le
  have hs0 : ∀ z, 0 ≤ negWeight ϖ p z + ε := fun z => by
    have := negWeight_pos ϖ p z
    linarith
  have hs2 : ∀ z, negWeight ϖ p z + ε ≤ 2 := fun z => by
    have := negWeight_le_one ϖ p z
    linarith
  have hqb : ∀ z, |clipWeight 2 (negWeight ϖ p z + ε)| ≤ 2 := fun z => by
    have h1 := clipWeight_two_le (hs0 z)
    have h2 := half_le_clipWeight_two (hs0 z) (hs2 z)
    rw [abs_le]
    constructor <;> linarith [hs0 z, hs2 z]
  rw [rawWeightedFactorialEnergy_eq_sum U ρ _ hqc 2 hqb]
  have hfw : ∀ a : ℕ, 0 ≤ factorialWeight ρ a := fun a => by
    unfold factorialWeight
    exact div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg ρ) a) (by positivity)
  have hsum0 : ∀ (a : Fin (k + 1)) z,
      0 ≤ ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2 :=
    fun a z => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hintq : ∀ a : Fin (k + 1), Integrable (fun z => clipWeight 2 (negWeight ϖ p z + ε) *
      ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2) volume := fun a =>
    weighted_jet_sq_integrable U a _ hqc 2 hqb
  have hintω : ∀ a : Fin (k + 1), Integrable (fun z => negWeight ϖ p z *
      ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2) volume := fun a =>
    weighted_jet_sq_integrable U a _ (continuous_negWeight ϖ p) 1 fun z => by
      rw [abs_of_pos (negWeight_pos ϖ p z)]; exact negWeight_le_one ϖ p z
  have hint1 : ∀ a : Fin (k + 1), Integrable (fun z =>
      ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2) volume := fun a =>
    integrable_finsetSum _ fun w _ => jet_sq_integrable U a w
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← mul_assoc, mul_comm 2 (factorialWeight ρ a.val), mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hfw a.val)
    rw [← integral_const_mul]
    apply integral_mono (hintω a) ((hintq a).const_mul 2)
    intro z
    have h2 := half_le_clipWeight_two (hs0 z) (hs2 z)
    have hω : negWeight ϖ p z ≤ 2 * clipWeight 2 (negWeight ϖ p z + ε) := by linarith
    calc negWeight ϖ p z * ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2
        ≤ (2 * clipWeight 2 (negWeight ϖ p z + ε)) *
            ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hω (hsum0 a z)
      _ = _ := by ring
  · refine Finset.sum_le_sum fun a _ => ?_
    apply mul_le_mul_of_nonneg_left _ (hfw a.val)
    unfold negJetIntegral
    rw [← integral_const_mul, ← integral_add (hintω a) ((hint1 a).const_mul ε)]
    apply integral_mono (hintq a) ((hintω a).add ((hint1 a).const_mul ε))
    intro z
    have h1 := clipWeight_two_le (hs0 z)
    calc clipWeight 2 (negWeight ϖ p z + ε) *
          ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2
        ≤ (negWeight ϖ p z + ε) * ∑ w : DerivativeWord2 a.val, ‖U.toFunction.jet ⟨a, w⟩ z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (hsum0 a z)
      _ = _ := by simp only [Pi.add_apply]; ring

end AVRegularity.CycleWords.Interior
end

section
open Homogenization
namespace AVRegularity.CycleWords.Interior

/-! First and second derivatives of the decaying weight `ω_q = (1 + ϖ²|z|²)^{-q}`:
`∂_j ω_q = -2qϖ² z_j ω_{q+1}`, `∂_i∂_j ω_q = -2qϖ²(δ_ij ω_{q+1} - 2(q+1)ϖ² z_i z_j ω_{q+2})`, hence
`|∇ω_q|² ≤ 4q²ϖ² ω_q²` and `|∂_i∂_j ω_q| ≤ 6(q+1)²ϖ² ω_q`. -/

theorem contDiff_negWeight (ϖ : ℝ) (q : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (negWeight ϖ q) := by
  unfold negWeight
  exact ContDiff.inv (by fun_prop) fun z => (pow_pos (negWeight_base_pos ϖ z) q).ne'

theorem negWeight_succ (ϖ : ℝ) (q : ℕ) (z : Vec 2) :
    negWeight ϖ (q + 1) z * (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) = negWeight ϖ q z := by
  have hb := negWeight_base_pos ϖ z
  unfold negWeight
  rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hb.ne', mul_one]

theorem negWeight_succ_le (ϖ : ℝ) (q : ℕ) (z : Vec 2) : negWeight ϖ (q + 1) z ≤ negWeight ϖ q z := by
  rw [← negWeight_succ ϖ q z]
  have h1 := negWeight_pos ϖ (q + 1) z
  have h2 : 0 ≤ ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by positivity
  nlinarith

theorem hasFDerivAt_negWeight (ϖ : ℝ) (q : ℕ) (z : Vec 2) :
    HasFDerivAt (negWeight ϖ q)
      ((-(2 * (q : ℝ) * ϖ ^ 2) * negWeight ϖ (q + 1) z) •
        (z 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
          z 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)) z := by
  have hb := negWeight_base_pos ϖ z
  have hP : HasFDerivAt (fun y : Vec 2 => 1 + ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2))
      ((2 * ϖ ^ 2) • (z 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
          z 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)) z := by
    have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).pow 2
    have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z).pow 2
    have h := ((h0.add h1).const_mul (ϖ ^ 2)).const_add 1
    convert h using 1
    ext h'
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    push_cast
    ring
  have h : HasFDerivAt (negWeight ϖ q) _ z :=
    (hasDerivAt_inv (pow_pos hb q).ne').comp_hasFDerivAt z (hP.pow q)
  convert h using 1
  ext h'
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul, negWeight]
  rcases q with _ | n
  · simp
  · rw [pow_succ _ (n + 1)]
    field_simp
    push_cast
    ring

theorem fderiv_negWeight (ϖ : ℝ) (q : ℕ) (z h : Vec 2) :
    fderiv ℝ (negWeight ϖ q) z h =
      -(2 * (q : ℝ) * ϖ ^ 2) * negWeight ϖ (q + 1) z * (z 0 * h 0 + z 1 * h 1) := by
  rw [(hasFDerivAt_negWeight ϖ q z).fderiv]
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem basis_coord (z : Vec 2) (j : Fin 2) :
    z 0 * basisVec j 0 + z 1 * basisVec j 1 = z j := by
  fin_cases j <;> simp [basisVec]

theorem fderiv_negWeight_basis (ϖ : ℝ) (q : ℕ) (z : Vec 2) (j : Fin 2) :
    fderiv ℝ (negWeight ϖ q) z (basisVec j) =
      -(2 * (q : ℝ) * ϖ ^ 2) * negWeight ϖ (q + 1) z * z j := by
  rw [fderiv_negWeight, basis_coord]

theorem negWeight_hessian (ϖ : ℝ) (q : ℕ) (z : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun z' => fderiv ℝ (negWeight ϖ q) z' (basisVec j)) z (basisVec i) =
      -(2 * (q : ℝ) * ϖ ^ 2) * (negWeight ϖ (q + 1) z * (if i = j then 1 else 0) -
        2 * ((q : ℝ) + 1) * ϖ ^ 2 * negWeight ϖ (q + 2) z * z i * z j) := by
  have he : (fun z' => fderiv ℝ (negWeight ϖ q) z' (basisVec j)) =
      fun z' => -(2 * (q : ℝ) * ϖ ^ 2) * (negWeight ϖ (q + 1) z' * z' j) := by
    funext z'
    rw [fderiv_negWeight_basis]
    ring
  rw [he]
  have hd := ((hasFDerivAt_negWeight ϖ (q + 1) z).mul
    (hasFDerivAt_apply (𝕜 := ℝ) j z)).const_mul (-(2 * (q : ℝ) * ϖ ^ 2))
  rw [show (fun z' => -(2 * (q : ℝ) * ϖ ^ 2) * (negWeight ϖ (q + 1) z' * z' j)) =
    (fun y => -(2 * (q : ℝ) * ϖ ^ 2) * (negWeight ϖ (q + 1) * fun f : Vec 2 => f j) y) from rfl,
    hd.fderiv]
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, basis_coord]
  have hij : basisVec (d := 2) i j = if i = j then 1 else 0 := by
    simp [basisVec, Pi.single_apply, eq_comm]
  rw [hij]
  push_cast
  ring

theorem differentiable_negWeight_grad (ϖ : ℝ) (q : ℕ) (j : Fin 2) :
    Differentiable ℝ (fun z' => fderiv ℝ (negWeight ϖ q) z' (basisVec j)) := by
  have he : (fun z' => fderiv ℝ (negWeight ϖ q) z' (basisVec j)) =
      fun z' => -(2 * (q : ℝ) * ϖ ^ 2) * negWeight ϖ (q + 1) z' * z' j := by
    funext z'
    rw [fderiv_negWeight_basis]
  rw [he]
  exact ((differentiable_const _).mul
    ((contDiff_negWeight ϖ (q + 1)).differentiable (by simp))).mul (differentiable_apply j)

theorem negWeight_grad_sq_le (ϖ : ℝ) (q : ℕ) (z : Vec 2) :
    ∑ k : Fin 2, fderiv ℝ (negWeight ϖ q) z (basisVec k) ^ 2 ≤
      4 * (q : ℝ) ^ 2 * ϖ ^ 2 * negWeight ϖ q z ^ 2 := by
  simp only [fderiv_negWeight_basis, Fin.sum_univ_two]
  have hs := negWeight_succ ϖ q z
  have h1 := negWeight_pos ϖ (q + 1) z
  have hle := negWeight_succ_le ϖ q z
  set a := negWeight ϖ (q + 1) z
  set b := negWeight ϖ q z
  set r := ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)
  have hr : 0 ≤ r := by positivity
  -- `ϖ² r_z a² ≤ ϖ² (1 + r) a² ≤ ...`: write the left side as `4q²ϖ² (r a) a`
  have hra : r * a ≤ b := by rw [← hs]; nlinarith
  have hkey : (-(2 * (q : ℝ) * ϖ ^ 2) * a * z 0) ^ 2 + (-(2 * (q : ℝ) * ϖ ^ 2) * a * z 1) ^ 2 =
      4 * (q : ℝ) ^ 2 * ϖ ^ 2 * ((r * a) * a) := by
    simp only [r]
    ring
  rw [hkey]
  have hq : 0 ≤ 4 * (q : ℝ) ^ 2 * ϖ ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_left _ hq
  rw [sq]
  exact mul_le_mul hra hle h1.le (negWeight_pos ϖ q z).le

theorem negWeight_hessian_abs_le (ϖ : ℝ) (q : ℕ) (z : Vec 2) (i j : Fin 2) :
    |fderiv ℝ (fun z' => fderiv ℝ (negWeight ϖ q) z' (basisVec j)) z (basisVec i)| ≤
      6 * ((q : ℝ) + 1) ^ 2 * ϖ ^ 2 * negWeight ϖ q z := by
  rw [negWeight_hessian]
  have hs1 := negWeight_succ ϖ (q + 1) z
  have hle1 := negWeight_succ_le ϖ q z
  have hle2 := negWeight_succ_le ϖ (q + 1) z
  have h2 := negWeight_pos ϖ (q + 2) z
  set a := negWeight ϖ (q + 1) z
  set c := negWeight ϖ (q + 2) z
  set b := negWeight ϖ q z
  have hzz : |z i * z j| ≤ z 0 ^ 2 + z 1 ^ 2 := by
    rw [abs_mul]
    have h0 := sq_abs (z 0)
    have h1 := sq_abs (z 1)
    fin_cases i <;> fin_cases j <;> simp <;> nlinarith [abs_nonneg (z 0), abs_nonneg (z 1)]
  have hϖ : 0 ≤ ϖ ^ 2 := sq_nonneg ϖ
  -- `ϖ² |z_i z_j| c ≤ ϖ²|z|² c ≤ (1 + ϖ²|z|²) c = a ≤ b`
  have hc : ϖ ^ 2 * |z i * z j| * c ≤ b := by
    have : ϖ ^ 2 * |z i * z j| * c ≤ ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) * c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzz hϖ) h2.le
    have h3 : ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) * c ≤ a := by
      rw [← hs1]
      nlinarith
    linarith
  have hδ : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  have ha0 : 0 ≤ a := (negWeight_pos ϖ (q + 1) z).le
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  calc |-(2 * (q : ℝ) * ϖ ^ 2) * (a * (if i = j then 1 else 0) -
        2 * ((q : ℝ) + 1) * ϖ ^ 2 * c * z i * z j)|
      ≤ 2 * (q : ℝ) * ϖ ^ 2 * (a * 1 + 2 * ((q : ℝ) + 1) * (ϖ ^ 2 * |z i * z j| * c)) := by
        rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * (q : ℝ) * ϖ ^ 2)]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg ha0]
          exact mul_le_mul_of_nonneg_left hδ ha0
        · rw [show 2 * ((q : ℝ) + 1) * ϖ ^ 2 * c * z i * z j =
            2 * ((q : ℝ) + 1) * (ϖ ^ 2 * (z i * z j) * c) by ring, abs_mul,
            abs_of_nonneg (by positivity : 0 ≤ 2 * ((q : ℝ) + 1)), abs_mul, abs_mul,
            abs_of_nonneg hϖ, abs_of_nonneg h2.le]
    _ ≤ 2 * (q : ℝ) * ϖ ^ 2 * (b + 2 * ((q : ℝ) + 1) * b) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [mul_one]
        exact add_le_add hle1 (mul_le_mul_of_nonneg_left hc (by positivity))
    _ ≤ 6 * ((q : ℝ) + 1) ^ 2 * ϖ ^ 2 * b := by
        have hb0 : 0 ≤ b := (negWeight_pos ϖ q z).le
        have : 2 * (q : ℝ) * (1 + 2 * ((q : ℝ) + 1)) ≤ 6 * ((q : ℝ) + 1) ^ 2 := by nlinarith
        calc 2 * (q : ℝ) * ϖ ^ 2 * (b + 2 * ((q : ℝ) + 1) * b) =
            (2 * (q : ℝ) * (1 + 2 * ((q : ℝ) + 1))) * (ϖ ^ 2 * b) := by ring
          _ ≤ 6 * ((q : ℝ) + 1) ^ 2 * (ϖ ^ 2 * b) :=
            mul_le_mul_of_nonneg_right this (mul_nonneg hϖ hb0)
          _ = _ := by ring

end AVRegularity.CycleWords.Interior
end

section
open Homogenization AVenhance AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Interior

/-! The shifted decaying weight `W = (1 + ϖ²|z|²)^{-p} + ε` is a chart weight of order `0` for
a time-only cell metric and a stream drift `v = σ∇ψ` with `√η|ψ| ≤ Cψ`, at scale `ϖ = √(η/S)`:
the transport is the divergence of the stream flux `-ψσ∇W`, the diffusion is bounded by the
Hessian of the weight, and the rate is `64(p+1)²(1+Cψ²)/S`, independent of `ε` (only the
comparability constant depends on `ε`). -/

/-- The stream flux `-ψσ∇W`, whose divergence is the transport `σ∇ψ · ∇W`. -/
def negStreamFlux (ψ : ℝ → Vec 2 → ℝ) (W : Vec 2 → ℝ) (t : ℝ) (z : Vec 2) : Vec 2 :=
  (-ψ t z • sigmaMat).mulVec (spaceGrad W z)

theorem negStreamFlux_smooth (ψ : ℝ → Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (W : Vec 2 → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 => negStreamFlux ψ W p.1 p.2) := by
  have hg (j : Fin 2) : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => spaceGrad W p.2 j) :=
    ((hW.fderiv_right (m := 1) (by simp)).comp contDiff_snd).clm_apply contDiff_const
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ 1 (fun p : ℝ × Vec 2 =>
    ∑ j : Fin 2, (-ψ p.1 p.2 * sigmaMat i j) * spaceGrad W p.2 j)
  apply ContDiff.sum
  intro j _
  exact (((hψ.of_le (by simp)).neg).mul contDiff_const).mul (hg j)

theorem negStreamFlux_divergence (ψ : ℝ → Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (W : Vec 2 → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) (t : ℝ) (z : Vec 2) :
    (∑ k : Fin 2, fderiv ℝ (fun x => negStreamFlux ψ W t x k) z (basisVec k)) =
      ∑ k : Fin 2, streamVel ψ t z k * fderiv ℝ W z (basisVec k) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ t x) :=
    hψ.comp (contDiff_const.prodMk contDiff_id)
  have hh := Infra.Section4.iterate_stream_flux_divergence hs.neg hW z
  change (∑ k : Fin 2, fderiv ℝ (fun x => negStreamFlux ψ W t x k) z (basisVec k)) = _ at hh
  rw [hh]
  have he : spaceGrad (fun x => -ψ t x) z = -spaceGrad (ψ t) z := by
    ext k
    simp only [spaceGrad, fderiv_fun_neg, neg_apply, Pi.neg_apply]
  rw [he, Matrix.mulVec_neg]
  simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg, streamVel,
    spaceGrad]

theorem negStreamFlux_sq (ψ : ℝ → Vec 2 → ℝ) (W : Vec 2 → ℝ) (t : ℝ) (z : Vec 2) :
    (∑ k : Fin 2, negStreamFlux ψ W t z k ^ 2) =
      ψ t z ^ 2 * ∑ k : Fin 2, (fderiv ℝ W z (basisVec k)) ^ 2 := by
  simp [negStreamFlux, Matrix.mulVec, dotProduct, sigmaMat, spaceGrad, Fin.sum_univ_two]
  ring

/-- The rate constant of the decaying weight: `λ = negWeightRate p Cψ / S`. -/
def negWeightRate (p : ℕ) (Cψ : ℝ) : ℝ := 64 * ((p : ℝ) + 1) ^ 2 * (1 + Cψ ^ 2)

theorem negWeightRate_nonneg (p : ℕ) (Cψ : ℝ) : 0 ≤ negWeightRate p Cψ := by
  unfold negWeightRate
  positivity

theorem fderiv_negWeight_shift (ϖ ε : ℝ) (p : ℕ) (z : Vec 2) :
    fderiv ℝ (fun y => negWeight ϖ p y + ε) z = fderiv ℝ (negWeight ϖ p) z :=
  fderiv_add_const ε

/-- The diffusion of the shifted weight by a constant matrix with entries at most `2`. -/
theorem metric_diffusion_negWeight_le (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : ∀ i j, |G i j| ≤ 2)
    (ϖ ε : ℝ) (p : ℕ) (z : Vec 2) :
    ∑ k : Fin 2, fderiv ℝ (fun z' => ∑ j : Fin 2, G k j *
        fderiv ℝ (fun y => negWeight ϖ p y + ε) z' (basisVec j)) z (basisVec k) ≤
      48 * ((p : ℝ) + 1) ^ 2 * ϖ ^ 2 * negWeight ϖ p z := by
  have hH (j : Fin 2) : HasFDerivAt (fun z' => fderiv ℝ (negWeight ϖ p) z' (basisVec j))
      (fderiv ℝ (fun z' => fderiv ℝ (negWeight ϖ p) z' (basisVec j)) z) z :=
    (differentiable_negWeight_grad ϖ p j z).hasFDerivAt
  have hterm (k : Fin 2) : fderiv ℝ (fun z' => ∑ j : Fin 2, G k j *
        fderiv ℝ (fun y => negWeight ϖ p y + ε) z' (basisVec j)) z (basisVec k) =
      ∑ j : Fin 2, G k j *
        fderiv ℝ (fun z' => fderiv ℝ (negWeight ϖ p) z' (basisVec j)) z (basisVec k) := by
    simp only [fderiv_negWeight_shift, Fin.sum_univ_two]
    rw [(((hH 0).const_mul (G k 0)).fun_add ((hH 1).const_mul (G k 1))).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [hterm]
  set B := 6 * ((p : ℝ) + 1) ^ 2 * ϖ ^ 2 * negWeight ϖ p z
  have hB : 0 ≤ B := by
    have := negWeight_pos ϖ p z
    positivity
  have hkj (k j : Fin 2) : G k j *
      fderiv ℝ (fun z' => fderiv ℝ (negWeight ϖ p) z' (basisVec j)) z (basisVec k) ≤ 2 * B := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul (hG k j) (negWeight_hessian_abs_le ϖ p z k j) (abs_nonneg _)
      (by norm_num)
  calc ∑ k : Fin 2, ∑ j : Fin 2, G k j *
        fderiv ℝ (fun z' => fderiv ℝ (negWeight ϖ p) z' (basisVec j)) z (basisVec k)
      ≤ ∑ _k : Fin 2, ∑ _j : Fin 2, 2 * B :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => hkj k j
    _ = 48 * ((p : ℝ) + 1) ^ 2 * ϖ ^ 2 * negWeight ϖ p z := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, B]
        ring

/-- **The decaying chart weight.** -/
theorem negChartWeights_exists (η S Cψ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hS : 0 < S)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (ψ : ℝ → Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (hv : ∀ t z, v t z = streamVel ψ t z) (hψb : ∀ t z, Real.sqrt η * |ψ t z| ≤ Cψ)
    (p : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (t₀ : ℝ) :
    ∃ C : ChartWeights (fun t _ => G t) v t₀ S (Real.sqrt (η / S)) 0 0
        (fun _ => 2 + ε⁻¹ + negWeightRate p Cψ),
      (∀ t z, C.W 0 t z = negWeight (Real.sqrt (η / S)) p z + ε) ∧
        C.lam 0 = negWeightRate p Cψ / S := by
  set ϖ := Real.sqrt (η / S) with hϖdef
  have hϖ2 : ϖ ^ 2 = η / S := Real.sq_sqrt (div_pos hη hS).le
  have hϖS : ϖ ^ 2 ≤ 1 / S := by
    rw [hϖ2]
    exact div_le_div_of_nonneg_right hη1 hS.le
  have hCψ : 0 ≤ Cψ := (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)).trans (hψb 0 0)
  have hψ2 : ∀ t z, ϖ ^ 2 * ψ t z ^ 2 ≤ Cψ ^ 2 / S := fun t z => by
    have h1 := hψb t z
    have h2 : (Real.sqrt η * |ψ t z|) ^ 2 ≤ Cψ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) h1 2
    rw [mul_pow, Real.sq_sqrt hη.le, sq_abs] at h2
    rw [hϖ2, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right h2 hS.le
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun y => negWeight ϖ p y + ε) :=
    (contDiff_negWeight ϖ p).add contDiff_const
  have hWpos : ∀ z, 0 < negWeight ϖ p z + ε := fun z => by
    have := negWeight_pos ϖ p z
    linarith
  have hωW : ∀ z, negWeight ϖ p z ≤ negWeight ϖ p z + ε := fun z => by linarith
  have hR := negWeightRate_nonneg p Cψ
  have hGe : ∀ t i j, |G t i j| ≤ 2 := fun t i j => cellMetric_entry_bound hG t 0 i j
  refine ⟨{
    W := fun _ _ z => negWeight ϖ p z + ε
    Phi := fun _ => negStreamFlux ψ (fun y => negWeight ϖ p y + ε)
    lam := fun _ => negWeightRate p Cψ / S
    smooth := fun _ _ => ⟨(hW.of_le (by simp)).comp contDiff_snd,
      negStreamFlux_smooth ψ hψ _ hW⟩
    pos := fun _ _ _ z => hWpos z
    comparable := ?_
    defect := ?_
    bound := ?_
    lam_bound := fun _ _ => ⟨div_nonneg hR hS.le, div_le_div_of_nonneg_right
      (by have := inv_pos.mpr hε; linarith) hS.le⟩ }, fun _ _ => rfl, rfl⟩
  · intro m hm t _ z
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    simp only [pow_zero, mul_one]
    have hω0 := negWeight_pos ϖ p z
    have hω1 := negWeight_le_one ϖ p z
    have hεi : ε⁻¹ ≤ 2 + ε⁻¹ + negWeightRate p Cψ := by linarith
    constructor
    · rw [inv_le_comm₀ hε (by positivity)] at hεi
      linarith
    · have := inv_pos.mpr hε
      linarith
  · intro m _ t _ z
    simp only [deriv_const, zero_add]
    rw [negStreamFlux_divergence ψ hψ _ hW, show (fun k => v t z k * fderiv ℝ
      (fun y => negWeight ϖ p y + ε) z (basisVec k)) = fun k => streamVel ψ t z k *
        fderiv ℝ (fun y => negWeight ϖ p y + ε) z (basisVec k) by rw [hv t z]]
    have hd := metric_diffusion_negWeight_le (G t) (hGe t) ϖ ε p z
    have hrate : 48 * ((p : ℝ) + 1) ^ 2 * ϖ ^ 2 * negWeight ϖ p z ≤
        negWeightRate p Cψ / S * (negWeight ϖ p z + ε) := by
      have hω0 := (negWeight_pos ϖ p z).le
      have h1 : 48 * ((p : ℝ) + 1) ^ 2 * ϖ ^ 2 ≤ negWeightRate p Cψ / S := by
        unfold negWeightRate
        have hp : 0 ≤ 48 * ((p : ℝ) + 1) ^ 2 := by positivity
        calc 48 * ((p : ℝ) + 1) ^ 2 * ϖ ^ 2 ≤ 48 * ((p : ℝ) + 1) ^ 2 * (1 / S) :=
              mul_le_mul_of_nonneg_left hϖS hp
          _ ≤ 64 * ((p : ℝ) + 1) ^ 2 * (1 + Cψ ^ 2) / S := by
              rw [mul_one_div]
              apply div_le_div_of_nonneg_right _ hS.le
              nlinarith [sq_nonneg Cψ, sq_nonneg ((p : ℝ) + 1)]
      exact mul_le_mul h1 (hωW z) hω0 (div_nonneg hR hS.le)
    linarith
  · intro m _ t _ z
    rw [negStreamFlux_sq, fderiv_negWeight_shift]
    have hg := negWeight_grad_sq_le ϖ p z
    have hW2 : 0 < (negWeight ϖ p z + ε) ^ 2 := pow_pos (hWpos z) 2
    have hωW2 : negWeight ϖ p z ^ 2 ≤ (negWeight ϖ p z + ε) ^ 2 :=
      pow_le_pow_left₀ (negWeight_pos ϖ p z).le (hωW z) 2
    set g := ∑ k : Fin 2, fderiv ℝ (negWeight ϖ p) z (basisVec k) ^ 2
    have hg0 : 0 ≤ g := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hgW : g ≤ 4 * (p : ℝ) ^ 2 * ϖ ^ 2 * (negWeight ϖ p z + ε) ^ 2 :=
      hg.trans (mul_le_mul_of_nonneg_left hωW2 (by positivity))
    rw [← add_div, div_le_iff₀ hW2]
    -- `g + ψ²g ≤ 4p²ϖ²(1 + ψ²) W² ≤ 4p²(1/S + Cψ²/S) W²`
    have hψ0 : 0 ≤ ψ t z ^ 2 := sq_nonneg _
    have h1 : g + ψ t z ^ 2 * g ≤
        4 * (p : ℝ) ^ 2 * (ϖ ^ 2 + ϖ ^ 2 * ψ t z ^ 2) * (negWeight ϖ p z + ε) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hgW hψ0
      nlinarith
    have h2 : ϖ ^ 2 + ϖ ^ 2 * ψ t z ^ 2 ≤ (1 + Cψ ^ 2) / S := by
      have := hψ2 t z
      rw [add_div]
      linarith
    have h3 : 4 * (p : ℝ) ^ 2 * ((1 + Cψ ^ 2) / S) ≤ negWeightRate p Cψ / S := by
      unfold negWeightRate
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hS]
      have : 4 * (p : ℝ) ^ 2 ≤ 64 * ((p : ℝ) + 1) ^ 2 := by
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    calc g + ψ t z ^ 2 * g
        ≤ 4 * (p : ℝ) ^ 2 * (ϖ ^ 2 + ϖ ^ 2 * ψ t z ^ 2) * (negWeight ϖ p z + ε) ^ 2 := h1
      _ ≤ 4 * (p : ℝ) ^ 2 * ((1 + Cψ ^ 2) / S) * (negWeight ϖ p z + ε) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) hW2.le
      _ ≤ negWeightRate p Cψ / S * (negWeight ϖ p z + ε) ^ 2 :=
          mul_le_mul_of_nonneg_right h3 hW2.le

end AVRegularity.CycleWords.Interior
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Interior

/-! Galerkin approximations of a real fibre evolution (real Bloch shift, no scalar potential) are
`L²` contractions: the drift coupling is skew and the metric part dissipates.
-/

theorem cellGalerkin_real_contraction (N : ℕ)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB ⟨G, v, θ, 0⟩ hG V hv.1 hb t) (y t))) :
    ∀ t ∈ Icc a b, ‖cellGalerkinValue N (y t)‖ ^ 2 ≤ ‖cellGalerkinValue N (y a)‖ ^ 2 := by
  have he := (hy.map (cellGalerkinValue N)).norm_sq_le_gronwall hab 0 le_rfl 0
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun _ => by simp only [Pi.zero_apply, le_refl])) (by
      apply Filter.Eventually.of_forall
      intro t
      simp only [Pi.zero_apply, add_zero, zero_mul]
      rw [real_inner_comm]
      have hp := cellGalerkinOperator_pairing N
        (cellGeneratorB ⟨G, v, θ, 0⟩ hG V hv.1 hb t) (y t) (y t)
      have hp' : inner ℝ (cellGalerkinValue N (cellGalerkinOperator N
          (cellGeneratorB ⟨G, v, θ, 0⟩ hG V hv.1 hb t) (y t))) (cellGalerkinValue N (y t)) =
          cellGeneratorForm ⟨G, v, θ, 0⟩ hG V hv.1 hb t (y t).val (y t).val := hp
      rw [hp', ← cellComplexGenerator_re]
      have hn := cellComplexGenerator_real_nonpos hG hv V hb θ hθ t (y t).val
      linarith)
  intro t ht
  simpa only [Pi.zero_apply, intervalIntegral.integral_zero, add_zero, zero_mul, Real.exp_zero,
    mul_one] using he t ht

end AVRegularity.CycleWords.Interior
end

section
open Homogenization AVenhance AVRegularity.Weighted AVRegularity.CycleJointProofs
namespace AVRegularity.CycleWords.Interior

/-! Mixed second derivatives of the static polynomial chart weights. -/

theorem polynomial_mixed_derivative (U : Vec 2 → ℝ) (hU : ContDiff ℝ 2 U)
    (n : ℕ) (z : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => U y ^ n) x (basisVec j)) z (basisVec i) =
      (n : ℝ) * U z ^ (n - 1) *
        fderiv ℝ (fun x => fderiv ℝ U x (basisVec j)) z (basisVec i) +
      (n : ℝ) * (n - 1 : ℕ) * U z ^ (n - 2) *
        fderiv ℝ U z (basisVec i) * fderiv ℝ U z (basisVec j) := by
  have hu := hU.differentiable (by norm_num)
  rw [funext (fun x => polynomial_weight_gradient U hu n x j)]
  have hd := weight_gradient_differentiable U hU j
  have hp := (((hu z).hasFDerivAt.pow (n - 1)).const_mul (n : ℝ)).mul (hd z).hasFDerivAt
  change fderiv ℝ ((fun x => (n : ℝ) * U x ^ (n - 1)) *
    (fun x => fderiv ℝ U x (basisVec j))) z (basisVec i) = _
  rw [hp.fderiv]
  simp only [add_apply, smul_apply,
    smul_eq_mul, Nat.sub_sub]
  ring

theorem momentBase_mixed_derivative (e : ℝ) (z : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun x : Vec 2 => fderiv ℝ
      (fun y : Vec 2 => 1 + e ^ 2 * ((y 0) ^ 2 + (y 1) ^ 2)) x (basisVec j))
      z (basisVec i) = 2 * e ^ 2 * (if i = j then 1 else 0) := by
  have he : (fun x : Vec 2 => fderiv ℝ
      (fun y : Vec 2 => 1 + e ^ 2 * ((y 0) ^ 2 + (y 1) ^ 2)) x (basisVec j)) =
      (fun x : Vec 2 => 2 * e ^ 2 * x j) := by
    funext x
    simpa only [Pi.zero_apply, sub_zero] using planeMomentBase_gradient e 0 x j
  rw [he, fderiv_const_mul (differentiableAt_apply j z),
    (hasFDerivAt_apply (𝕜 := ℝ) j z).fderiv]
  fin_cases i <;> fin_cases j <;> simp [basisVec]

theorem moment_mixed_derivative (m : ℕ) (e : ℝ) (z : Vec 2) (i j : Fin 2) :
    fderiv ℝ (fun x => fderiv ℝ (planeMomentPolynomial m e 0) x (basisVec j)) z (basisVec i) =
      (m : ℝ) * (1 + e ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2)) ^ (m - 1) *
        (2 * e ^ 2 * (if i = j then 1 else 0)) +
      (m : ℝ) * (m - 1 : ℕ) * (1 + e ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2)) ^ (m - 2) *
        (2 * e ^ 2 * z i) * (2 * e ^ 2 * z j) := by
  change fderiv ℝ (fun x => fderiv ℝ
    (fun y : Vec 2 => (1 + e ^ 2 * ((y 0 - (0 : Vec 2) 0) ^ 2 + (y 1 - (0 : Vec 2) 1) ^ 2)) ^ m)
      x (basisVec j)) z (basisVec i) = _
  simp only [Pi.zero_apply, sub_zero]
  rw [polynomial_mixed_derivative _ (by fun_prop), momentBase_mixed_derivative]
  have hg (k : Fin 2) := planeMomentBase_gradient e 0 z k
  simp only [Pi.zero_apply, sub_zero] at hg
  rw [hg i, hg j]

end AVRegularity.CycleWords.Interior
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords.Interior

/-! A smooth stream flux cancels the weight's transport without differentiating the metric. -/

def chartStreamFlux (ψ : ℝ → Vec 2 → ℝ) (W : Vec 2 → ℝ) (t : ℝ) (z : Vec 2) : Vec 2 :=
  (-ψ t z • sigmaMat).mulVec (spaceGrad W z)

theorem chartStreamFlux_smooth (ψ : ℝ → Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (W : Vec 2 → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 => chartStreamFlux ψ W p.1 p.2) := by
  have hg (j : Fin 2) : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => spaceGrad W p.2 j) := by
    exact ((hW.fderiv_right (m := 1) (by simp)).comp contDiff_snd).clm_apply contDiff_const
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ 1 (fun p : ℝ × Vec 2 => ∑ j : Fin 2, (-ψ p.1 p.2 * sigmaMat i j) * spaceGrad W p.2 j)
  apply ContDiff.sum
  intro j _
  exact (((hψ.of_le (by simp)).neg).mul contDiff_const).mul (hg j)

theorem chartStreamFlux_divergence (ψ : ℝ → Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (W : Vec 2 → ℝ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) (t : ℝ) (z : Vec 2) :
    (∑ k : Fin 2, fderiv ℝ (fun x => chartStreamFlux ψ W t x k) z (basisVec k)) =
      ∑ k : Fin 2, streamVel ψ t z k * fderiv ℝ W z (basisVec k) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ t x) :=
    hψ.comp (contDiff_const.prodMk contDiff_id)
  have hh := Infra.Section4.iterate_stream_flux_divergence hs.neg hW z
  change (∑ k : Fin 2, fderiv ℝ (fun x => chartStreamFlux ψ W t x k) z (basisVec k)) = _ at hh
  rw [hh]
  have he : spaceGrad (fun x => -ψ t x) z = -spaceGrad (ψ t) z := by
    ext k
    simp only [spaceGrad, fderiv_fun_neg, neg_apply, Pi.neg_apply]
  rw [he, Matrix.mulVec_neg]
  simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg, streamVel, spaceGrad]

theorem chartStreamFlux_sq (ψ : ℝ → Vec 2 → ℝ) (W : Vec 2 → ℝ) (t : ℝ) (z : Vec 2) :
    (∑ k : Fin 2, chartStreamFlux ψ W t z k ^ 2) =
      ψ t z ^ 2 * ∑ k : Fin 2, (fderiv ℝ W z (basisVec k)) ^ 2 := by
  simp [chartStreamFlux, Matrix.mulVec, dotProduct, sigmaMat, spaceGrad, Fin.sum_univ_two]
  ring

end AVRegularity.CycleWords.Interior
end

section
open Homogenization AVenhance AVRegularity.Weighted AVRegularity.CycleJointProofs
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Interior

/-! Uniform relative Hessian and gradient budgets for a static polynomial weight. -/

private theorem mixed_weight_algebra (n : ℕ) (e U a b d : ℝ) (hU : 1 ≤ U)
    (ha : |e * a| ≤ U) (hb : |e * b| ≤ U) (hd : |d| ≤ 1) :
    |(n : ℝ) * U ^ (n - 1) * (2 * e ^ 2 * d) +
      (n : ℝ) * (n - 1 : ℕ) * U ^ (n - 2) * (2 * e ^ 2 * a) * (2 * e ^ 2 * b)| ≤
      (8 * ((n : ℝ) + 1) ^ 2) * e ^ 2 * U ^ n := by
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hgrad (x : ℝ) (hx : |e * x| ≤ U) : |2 * e ^ 2 * x| ≤ 2 * |e| * U := by
    calc
      _ = 2 * |e| * |e * x| := by simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
  have hprod : |2 * e ^ 2 * a| * |2 * e ^ 2 * b| ≤ 4 * e ^ 2 * U ^ 2 := by
    have hh := mul_le_mul (hgrad a ha) (hgrad b hb) (abs_nonneg _) (by positivity : 0 ≤ 2 * |e| * U)
    apply hh.trans_eq
    calc
      _ = 4 * |e| ^ 2 * U ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  have hdiag : |2 * e ^ 2 * d| ≤ 2 * e ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * e ^ 2)]
    exact mul_le_of_le_one_right (by positivity) hd
  cases n with
  | zero => simpa using sq_nonneg e
  | succ n =>
    cases n with
    | zero =>
      norm_num only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, Nat.reduceSubDiff,
        zero_add, one_mul, pow_zero, pow_one, mul_zero, zero_mul, add_zero]
      have hh := mul_le_mul_of_nonneg_left hU (sq_nonneg e)
      nlinarith only [hdiag, hh, sq_nonneg e]
    | succ n =>
      rw [show n.succ.succ - 1 = n + 1 by omega,
        show n.succ.succ - 2 = n by omega]
      change |((n + 2 : ℕ) : ℝ) * U ^ (n + 1) * (2 * e ^ 2 * d) +
        ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * U ^ n * (2 * e ^ 2 * a) * (2 * e ^ 2 * b)| ≤
        (8 * (((n + 2 : ℕ) : ℝ) + 1) ^ 2) * e ^ 2 * U ^ (n + 2)
      have hm : 0 ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hn : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hp : U ^ (n + 1) ≤ U ^ (n + 2) := by
        exact pow_le_pow_right₀ hU (by omega)
      have h1 := mul_le_mul_of_nonneg_left hdiag
        (mul_nonneg hm (pow_nonneg hU0 (n + 1)))
      have h2 := mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (mul_nonneg hm hn) (pow_nonneg hU0 n))
      have hpow : U ^ n * U ^ 2 = U ^ (n + 2) := (pow_add _ _ _).symm
      have hfirst := mul_le_mul_of_nonneg_left hp
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm) (sq_nonneg e))
      calc
        _ ≤ |((n + 2 : ℕ) : ℝ) * U ^ (n + 1) * (2 * e ^ 2 * d)| +
            |((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * U ^ n *
              (2 * e ^ 2 * a) * (2 * e ^ 2 * b)| := abs_add_le _ _
        _ ≤ (2 * ((n + 2 : ℕ) : ℝ) + 4 * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) *
            e ^ 2 * U ^ (n + 2) := by
          simp only [abs_mul, abs_of_nonneg hm, abs_of_nonneg hn, abs_of_nonneg (pow_nonneg hU0 _)]
          have h2' := h2.trans_eq (calc
            _ = (4 * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * e ^ 2) * (U ^ n * U ^ 2) := by ring
            _ = _ := by rw [hpow])
          have h1' := h1.trans_eq (show ((n + 2 : ℕ) : ℝ) * U ^ (n + 1) * (2 * e ^ 2) =
            2 * ((n + 2 : ℕ) : ℝ) * e ^ 2 * U ^ (n + 1) by ring)
          calc
            _ = ((n + 2 : ℕ) : ℝ) * U ^ (n + 1) * |2 * e ^ 2 * d| +
                ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * U ^ n *
                  (|2 * e ^ 2 * a| * |2 * e ^ 2 * b|) := by simp only [abs_mul]; ring
            _ ≤ _ := add_le_add (h1'.trans hfirst) h2'
            _ = _ := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hU0 _)
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg e)
          norm_num only [Nat.cast_add, Nat.cast_ofNat]
          nlinarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), sq_nonneg (n : ℝ)]

theorem moment_hessian_abs_le (m : ℕ) (e : ℝ) (z : Vec 2) (i j : Fin 2) :
    |fderiv ℝ (fun x => fderiv ℝ (planeMomentPolynomial m e 0) x (basisVec j)) z (basisVec i)| ≤
      (8 * ((m : ℝ) + 1) ^ 2) * e ^ 2 * planeMomentPolynomial m e 0 z := by
  rw [moment_mixed_derivative]
  have h := mixed_weight_algebra m e (1 + e ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) (z i) (z j)
    (if i = j then 1 else 0)
  have hh := h (le_add_of_nonneg_right (by positivity))
  simp only [planeMomentPolynomial, Pi.zero_apply, sub_zero]
  apply hh
  · simpa only [Pi.zero_apply, sub_zero] using momentCoordinate_abs_le_base e 0 z i
  · simpa only [Pi.zero_apply, sub_zero] using momentCoordinate_abs_le_base e 0 z j
  · split_ifs <;> norm_num

theorem moment_metric_diffusion_le
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (m : ℕ) (e t : ℝ) (z : Vec 2) :
    (∑ i : Fin 2, fderiv ℝ (fun x => ∑ j : Fin 2, G t i j *
      fderiv ℝ (planeMomentPolynomial m e 0) x (basisVec j)) z (basisVec i)) ≤
      (64 * ((m : ℝ) + 1) ^ 2) * e ^ 2 * planeMomentPolynomial m e 0 z := by
  have hW : ContDiff ℝ 2 (planeMomentPolynomial m e 0) := by
    unfold planeMomentPolynomial
    fun_prop
  have hd := weight_gradient_differentiable _ hW
  have he (i j : Fin 2) : G t i j * fderiv ℝ
      (fun x => fderiv ℝ (planeMomentPolynomial m e 0) x (basisVec j)) z (basisVec i) ≤
      2 * ((8 * ((m : ℝ) + 1) ^ 2) * e ^ 2 * planeMomentPolynomial m e 0 z) := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact mul_le_mul (cellMetric_entry_bound hG t 0 i j) (moment_hessian_abs_le m e z i j)
      (abs_nonneg _) (by norm_num)
  simp_rw [fderiv_fun_sum (fun j _ => (hd j z).const_mul (G t _ j)),
    sum_apply, fderiv_const_mul (hd _ z), smul_apply, smul_eq_mul]
  simp only [Fin.sum_univ_two]
  linarith only [he 0 0, he 0 1, he 1 0, he 1 1]

end AVRegularity.CycleWords.Interior
end

section
namespace AVRegularity.CycleWords.Interior

/-! Abstract real arithmetic for the uniform chart rate, away from the PDE expressions. -/

def chartWeightConstant (C : ℝ) (m : ℕ) : ℝ := 64 * (1 + C ^ 2) * ((m : ℝ) + 1) ^ 2

theorem chartWeightConstant_ge_one (C : ℝ) (m : ℕ) : 1 ≤ chartWeightConstant C m := by
  have hm : 1 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ)), sq_nonneg (m : ℝ)]
  have hC : 1 ≤ 1 + C ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  have hh := mul_le_mul hC hm (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 1 + C ^ 2)
  unfold chartWeightConstant
  nlinarith only [hh]

theorem chart_diffusion_rate {η S e C W : ℝ} (hη : η ≤ 1) (hS : 0 < S)
    (he : e ^ 2 = η / S) (hW : 0 ≤ W) (m : ℕ) :
    (64 * ((m : ℝ) + 1) ^ 2) * e ^ 2 * W ≤ chartWeightConstant C m / S * W := by
  apply mul_le_mul_of_nonneg_right _ hW
  rw [he, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hS.le
  have hh : η ≤ 1 + C ^ 2 := hη.trans (le_add_of_nonneg_right (sq_nonneg _))
  have hb := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 64 * ((m : ℝ) + 1) ^ 2)
  simpa only [chartWeightConstant, mul_assoc, mul_comm, mul_left_comm] using hb

theorem chart_gradient_flux_rate {η S e C P W : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hS : 0 < S) (he : e ^ 2 = η / S) (hW : 0 < W)
    (hP : Real.sqrt η * |P| ≤ C) (m : ℕ) (d : Fin 2 → ℝ)
    (hd : ∀ k, |d k| ≤ (2 * (m : ℝ) * |e|) * W) :
    (∑ k, d k ^ 2) / W ^ 2 + (P ^ 2 * ∑ k, d k ^ 2) / W ^ 2 ≤
      chartWeightConstant C m / S := by
  have hC : 0 ≤ C := (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)).trans hP
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt η * |P|) hC).mpr hP
  rw [mul_pow, Real.sq_sqrt hη.le, sq_abs] at hsq
  have hh (k : Fin 2) : d k ^ 2 ≤ ((2 * (m : ℝ) * |e|) * W) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hd k)
  have hsum : (∑ k, d k ^ 2) ≤ 8 * (m : ℝ) ^ 2 * e ^ 2 * W ^ 2 := by
    have hs := add_le_add (hh 0) (hh 1)
    simp only [Fin.sum_univ_two]
    apply hs.trans_eq
    calc
      _ = 8 * (m : ℝ) ^ 2 * |e| ^ 2 * W ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  have hr : (∑ k, d k ^ 2) / W ^ 2 ≤ 8 * (m : ℝ) ^ 2 * e ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hW)).mpr hsum
  have hp := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 1 + P ^ 2)
  have hnum : η * (1 + P ^ 2) ≤ 1 + C ^ 2 := by nlinarith only [hη1, hsq]
  have hc := mul_le_mul_of_nonneg_left hnum (by positivity : 0 ≤ 8 * (m : ℝ) ^ 2)
  have hm : 8 * (m : ℝ) ^ 2 ≤ 64 * ((m : ℝ) + 1) ^ 2 := by
    nlinarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ)), sq_nonneg (m : ℝ)]
  have hlast := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 1 + C ^ 2)
  calc
    _ = (1 + P ^ 2) * ((∑ k, d k ^ 2) / W ^ 2) := by ring
    _ ≤ (1 + P ^ 2) * (8 * (m : ℝ) ^ 2 * e ^ 2) := hp
    _ = (8 * (m : ℝ) ^ 2 * (η * (1 + P ^ 2))) / S := by rw [he]; ring
    _ ≤ (8 * (m : ℝ) ^ 2 * (1 + C ^ 2)) / S := div_le_div_of_nonneg_right hc hS.le
    _ ≤ chartWeightConstant C m / S := by
      apply div_le_div_of_nonneg_right _ hS.le
      simpa only [chartWeightConstant, mul_comm, mul_left_comm, mul_assoc] using hlast

end AVRegularity.CycleWords.Interior
end
