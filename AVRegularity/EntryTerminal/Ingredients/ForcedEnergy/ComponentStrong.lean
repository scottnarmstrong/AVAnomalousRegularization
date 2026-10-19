-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Scales.Times
public import AVRegularity.Statements.Intermediate.CycleReference.OcBand
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.KernelEnergy.TorusKernelStrongTraceExistence
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
public import AVRegularity.Statements.Construction.IsAdmissibleQ
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CoupledEnergy.CouplingBounds
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.EntryTerminal.ForcedEnergy

/-! Real arithmetic for the forced component energy: the absorption of the
unknown time supremum, and the weighted `ℓ²` Minkowski inequality for time integrals. -/

/-- A nonnegative bounded function whose pointwise bound `E ≤ Q + 2 m G` holds for every upper
bound `m` of `√E` has `√E ≤ m` with `m² ≤ 2Q + 4G²` for a suitable `m`. -/
theorem exists_sqrt_bound {I : Set ℝ} (hI : I.Nonempty) (E : ℝ → ℝ) (Q G m₀ : ℝ)
    (hE : ∀ t ∈ I, 0 ≤ E t) (hbd : ∀ t ∈ I, Real.sqrt (E t) ≤ m₀)
    (hstep : ∀ m, 0 ≤ m → (∀ t ∈ I, Real.sqrt (E t) ≤ m) → ∀ t ∈ I, E t ≤ Q + 2 * m * G) :
    ∃ m, 0 ≤ m ∧ (∀ t ∈ I, Real.sqrt (E t) ≤ m) ∧ m ^ 2 ≤ 2 * Q + 4 * G ^ 2 := by
  have hbdd : BddAbove (E '' I) := by
    refine ⟨m₀ ^ 2, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have h1 := hbd t ht
    calc E t = Real.sqrt (E t) ^ 2 := (Real.sq_sqrt (hE t ht)).symm
      _ ≤ m₀ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  set S := sSup (E '' I) with hS
  obtain ⟨t₀, ht₀⟩ := hI
  have hle (t : ℝ) (ht : t ∈ I) : E t ≤ S := le_csSup hbdd ⟨t, ht, rfl⟩
  have hS0 : 0 ≤ S := (hE t₀ ht₀).trans (hle t₀ ht₀)
  refine ⟨Real.sqrt S, Real.sqrt_nonneg _, fun t ht => Real.sqrt_le_sqrt (hle t ht), ?_⟩
  rw [Real.sq_sqrt hS0]
  have hSq : S ≤ Q + 2 * Real.sqrt S * G := by
    apply csSup_le (Set.Nonempty.image E ⟨t₀, ht₀⟩)
    rintro _ ⟨t, ht, rfl⟩
    exact hstep _ (Real.sqrt_nonneg _) (fun t ht => Real.sqrt_le_sqrt (hle t ht)) t ht
  have hsq := Real.sq_sqrt hS0
  nlinarith [sq_nonneg (Real.sqrt S - 2 * G), Real.sqrt_nonneg S]

variable {ι : Type*} [Fintype ι]

/-- Weighted `ℓ²` Minkowski inequality for time integrals of nonnegative functions. -/
theorem weighted_integral_sq_le {T : Type*} [MeasurableSpace T] (μ : Measure T) (ω : ι → ℝ)
    (hω : ∀ i, 0 ≤ ω i) (x : ι → T → ℝ)
    (hint : ∀ i, Integrable (x i) μ)
    (hJ : Integrable (fun t => Real.sqrt (∑ i, ω i * x i t ^ 2)) μ) :
    ∑ i, ω i * (∫ t, x i t ∂μ) ^ 2 ≤ (∫ t, Real.sqrt (∑ i, ω i * x i t ^ 2) ∂μ) ^ 2 := by
  set G : ι → ℝ := fun i => ∫ t, x i t ∂μ with hGdef
  set S := ∑ i, ω i * G i ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => mul_nonneg (hω i) (sq_nonneg _))
  set J := ∫ t, Real.sqrt (∑ i, ω i * x i t ^ 2) ∂μ with hJdef
  have hJ0 : 0 ≤ J := integral_nonneg (fun t => Real.sqrt_nonneg _)
  have hpt (t : T) : ∑ i, ω i * G i * x i t ≤ Real.sqrt S * Real.sqrt (∑ i, ω i * x i t ^ 2) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => Real.sqrt (ω i) * G i)
      (fun i => Real.sqrt (ω i) * x i t)
    have e1 : ∀ i, Real.sqrt (ω i) * G i * (Real.sqrt (ω i) * x i t) = ω i * G i * x i t := by
      intro i
      have := Real.mul_self_sqrt (hω i)
      calc _ = (Real.sqrt (ω i) * Real.sqrt (ω i)) * G i * x i t := by ring
        _ = _ := by rw [this]
    have e2 : ∀ i, (Real.sqrt (ω i) * G i) ^ 2 = ω i * G i ^ 2 := by
      intro i; rw [mul_pow, Real.sq_sqrt (hω i)]
    have e3 : ∀ i, (Real.sqrt (ω i) * x i t) ^ 2 = ω i * x i t ^ 2 := by
      intro i; rw [mul_pow, Real.sq_sqrt (hω i)]
    simpa only [e1, e2, e3] using hcs
  have hxint (i : ι) : Integrable (fun t => ω i * G i * x i t) μ := (hint i).const_mul _
  have hsum : S = ∫ t, ∑ i, ω i * G i * x i t ∂μ := by
    rw [integral_finsetSum _ (fun i _ => hxint i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    simp only [hGdef]
    ring
  have hle : S ≤ Real.sqrt S * J := by
    calc S = ∫ t, ∑ i, ω i * G i * x i t ∂μ := hsum
      _ ≤ ∫ t, Real.sqrt S * Real.sqrt (∑ i, ω i * x i t ^ 2) ∂μ :=
        integral_mono (integrable_finsetSum _ (fun i _ => hxint i)) (hJ.const_mul _) hpt
      _ = Real.sqrt S * J := by rw [integral_const_mul]
  have hrs := Real.sq_sqrt hS0
  have hsq0 := Real.sqrt_nonneg S
  rcases hsq0.eq_or_lt with h0 | hpos
  · rw [← h0] at hrs
    nlinarith [sq_nonneg J]
  · have : Real.sqrt S ≤ J := by
      by_contra hcon
      have hcon := not_le.mp hcon
      nlinarith
    nlinarith

end AVRegularity.EntryTerminal.ForcedEnergy
end
end

section
@[expose] public section
open Filter Topology
namespace AVRegularity.EntryTerminal.ForcedEnergy

/-! The level floor of the forced energy: for every large level the scales
`ε_M` meet the finitely many smallness conditions used by the weak operator. -/

theorem term_level_floor {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {Λ : ℕ} (hΛ : 128 ≤ Λ)
    (cK Cχ χw Cd : ℝ) (hcK : 0 < cK) (hχ : 0 < χw) (hCd : 0 ≤ Cd) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      Cχ * ocEpsilon q Λ M ^ χw ≤ 1 / 8 ∧
      cK * ocEpsilon q Λ M ≤ ocEpsilon q Λ (M - 1) ∧
      ocEpsilon q Λ M ^ ocGamma α q ≤ 1 / 2 ∧
      ocEpsilon q Λ M ^ ocGamma α q ≤ 256 / (Cd + 1) := by
  have hγ := (AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).1
  have hq1 := hq.1
  obtain ⟨M1, h1⟩ := AVRegularity.EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 hΛ hχ
    (c := 1 / (8 * (|Cχ| + 1))) (by positivity)
  obtain ⟨M2, h2⟩ := AVRegularity.EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 hΛ hγ
    (c := 1 / 2) (by norm_num)
  obtain ⟨M3, h3⟩ := AVRegularity.EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 hΛ hγ
    (c := 256 / (Cd + 1)) (by positivity)
  obtain ⟨M4, h4⟩ := AVRegularity.EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 hΛ
    (sub_pos.2 hq1) (c := 1 / (2 * cK)) (by positivity)
  refine ⟨max (max M1 M2) (max M3 (M4 + 1)) + 2, by omega, fun M hM => ?_⟩
  have hM1 : M1 ≤ M := by omega
  have hM2 : M2 ≤ M := by omega
  have hM3 : M3 ≤ M := by omega
  have hM4 : M4 ≤ M - 1 := by omega
  refine ⟨?_, ?_, h2 M hM2, h3 M hM3⟩
  · have hb := h1 M hM1
    have hε := (AVRegularity.Scales.epsilon_basic (m := M) hq1 hΛ).1
    have hp : 0 ≤ ocEpsilon q Λ M ^ χw := Real.rpow_nonneg hε.le _
    have hCa : Cχ ≤ |Cχ| := le_abs_self _
    calc Cχ * ocEpsilon q Λ M ^ χw ≤ |Cχ| * ocEpsilon q Λ M ^ χw := mul_le_mul_of_nonneg_right hCa hp
      _ ≤ |Cχ| * (1 / (8 * (|Cχ| + 1))) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ 1 / 8 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg Cχ]
  · have hstep := AVRegularity.Scales.epsilon_q_step (m := M) hq1 hq.2.1 hΛ (by omega)
    have hE := (AVRegularity.Scales.epsilon_basic (m := M - 1) hq1 hΛ).1
    have hb := h4 (M - 1) hM4
    have hsplit : ocEpsilon q Λ (M - 1) ^ q =
        ocEpsilon q Λ (M - 1) ^ (q - 1) * ocEpsilon q Λ (M - 1) := by
      rw [← Real.rpow_add_one hE.ne']
      congr 1; ring
    have hpow : 0 ≤ ocEpsilon q Λ (M - 1) ^ (q - 1) := Real.rpow_nonneg hE.le _
    have h5 : 2 * cK * ocEpsilon q Λ (M - 1) ^ (q - 1) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * cK)
      calc _ ≤ 2 * cK * (1 / (2 * cK)) := this
        _ = 1 := by field_simp
    calc cK * ocEpsilon q Λ M ≤ cK * (2 * ocEpsilon q Λ (M - 1) ^ q) :=
          mul_le_mul_of_nonneg_left hstep hcK.le
      _ = (2 * cK * ocEpsilon q Λ (M - 1) ^ (q - 1)) * ocEpsilon q Λ (M - 1) := by
          rw [hsplit]; ring
      _ ≤ 1 * ocEpsilon q Λ (M - 1) := mul_le_mul_of_nonneg_right h5 hE.le
      _ = _ := one_mul _

/-- The scale facts at the terminal level inside the band: positivity, `ε² a_M ≤ κ`, and the drift
strain at the radius `c' ε`. -/
theorem term_scale_facts {α q : ℝ} {Λ : ℕ} (M : ℕ) (hq : 1 < q) (hΛ : 128 ≤ Λ) {κ : ℝ}
    (hκ : κ ∈ ocBand α q Λ M) (cd c' : ℝ) (hcd : 0 ≤ cd) (hc'0 : 0 ≤ c') (hc' : c' ≤ 1 / 2048)
    (h2 : ocEpsilon q Λ M ^ ocGamma α q ≤ 1 / 2)
    (hCd : ocEpsilon q Λ M ^ ocGamma α q ≤ 256 / (cd + 1)) :
    0 < ocEpsilon q Λ M ∧ 0 < κ ∧ ocEpsilon q Λ M ^ 2 * ocA α q Λ M ≤ κ ∧
      cd * ocA α q Λ M * 1024 * (c' * ocEpsilon q Λ M) ^ 2 ≤ κ / 8 := by
  have hε := (AVRegularity.Scales.epsilon_basic (m := M) hq hΛ).1
  set ε := ocEpsilon q Λ M with hεd
  set γ := ocGamma α q with hγ
  set X := ε ^ ((1 + α) - γ) with hX
  set Y := ε ^ γ with hY
  have hXpos : 0 < X := Real.rpow_pos_of_pos hε _
  have hY0 : 0 ≤ Y := (Real.rpow_pos_of_pos hε _).le
  have hκlo : X / 2 ≤ κ := hκ.1
  have hκpos : 0 < κ := lt_of_lt_of_le (by positivity) hκlo
  have hsplit : ε ^ ((1 + α) - 2) * ε ^ 2 = X * Y := by
    rw [hX, hY, ← Real.rpow_natCast ε 2, ← Real.rpow_add hε, ← Real.rpow_add hε]
    congr 1
    push_cast
    ring
  refine ⟨hε, hκpos, ?_, ?_⟩
  · have : ε ^ 2 * ocA α q Λ M = X * Y := by
      rw [← hsplit, ocA]; ring
    rw [this]
    nlinarith
  · have hCY : cd * Y ≤ 256 := by
      have h1 : cd * Y ≤ cd * (256 / (cd + 1)) := mul_le_mul_of_nonneg_left hCd hcd
      have h2' : cd * (256 / (cd + 1)) ≤ 256 := by
        rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
        linarith
      linarith
    have hcK2 : c' ^ 2 ≤ (1 / 2048) ^ 2 := pow_le_pow_left₀ hc'0 hc' 2
    have hmain : 1024 * c' ^ 2 * (cd * Y) ≤ 1024 * (1 / 2048) ^ 2 * 256 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcK2 (by norm_num)) hCY (mul_nonneg hcd hY0)
        (by norm_num)
    calc cd * ocA α q Λ M * 1024 * (c' * ε) ^ 2
        = 1024 * c' ^ 2 * cd * (ε ^ ((1 + α) - 2) * ε ^ 2) := by rw [ocA]; ring
      _ = 1024 * c' ^ 2 * (cd * Y) * X := by rw [hsplit]; ring
      _ ≤ 1024 * (1 / 2048) ^ 2 * 256 * X := mul_le_mul_of_nonneg_right hmain hXpos.le
      _ = X / 16 := by ring
      _ ≤ κ / 8 := by linarith

end AVRegularity.EntryTerminal.ForcedEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! Forced component energy inequality for the Galerkin ODE with the forcing of the component
kept per component: the pairing of `g_i` with the solution costs `m_i ‖g_i‖`, the flux forcing costs
`ε⁻¹ ‖F_i‖²`, and neither is bounded by the mass sum of the forcing. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem kernelRhs_component_forced_le (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) (v t)) (hvp : AVenhance.IsZ2Periodic (v t))
    (c : CoupledPlainCoefficients (h := h) N)
    (F : ∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk k (h i)) (αv B lam : ℝ)
    (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (i : ι) (m ε : ℝ) (hε : 0 < ε)
    (hm : Real.sqrt (factorialNormSq ρ (coupledPlainSynthesis N i k c).val) ≤ m) :
    inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
      (coupledPlainSynthesis N i k
        (plainMatrixCLM (P.projectedMatrix N v t) c + plainSourceCoefficients N (fun _ => k) F g)).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainSynthesis N i k c).val) +
      (3 * ν / 4 - ε / 2) * gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) c).val ≤
    |P.carrierPair (fun j (_r : ℝ) => coupledPlainSynthesis N j (k + 1) c) i t| +
      m * Real.sqrt (factorialNormSq ρ (g i).val) +
      (1 / (2 * ε)) * factorialNormSq ρ (F i).val := by
  let U := fun j => (coupledPlainSynthesis N j k c).val
  let R := gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) c).val
  have hR : 0 ≤ R := by
    change 0 ≤ gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) c).val
    rw [← coupledPlainGradientHk_factorialNormSq]
    exact factorialNormSq_nonneg ρ _
  have hG := factorialPairing_abs_le ρ (g i).val (U i)
  rw [← factorialWeightedJet_inner] at hG
  have hGb : |inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (g i).val)
      (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i))| ≤
      m * Real.sqrt (factorialNormSq ρ (g i).val) := by
    have h2 := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg (factorialNormSq ρ (g i).val))
    change _ ≤ Real.sqrt (factorialNormSq ρ (g i).val) * Real.sqrt (factorialNormSq ρ (U i)) at hG
    nlinarith only [hG, h2]
  have hV := coupledPlainDriftHk_energy_abs_le (le_refl k) N c i ρ αv B lam ν
    P.radius_pos hα hB hlam P.diffusivity_pos hsmall hstrain (v t) hv hvp hd hjets
  rw [← factorialWeightedJet_inner] at hV
  have hF := factorialPairing_abs_le ρ (F i).val (coupledPlainGradientHk N c i k).val
  rw [← factorialWeightedJet_inner, coupledPlainGradientHk_factorialNormSq] at hF
  have hy := coupledFluxYoung (show 0 < 4 * ε by positivity)
    (Real.sqrt (factorialNormSq ρ (F i).val)) (Real.sqrt R)
  rw [Real.sq_sqrt (factorialNormSq_nonneg ρ _), Real.sq_sqrt hR] at hy
  have hcoef : 2 / (4 * ε) = 1 / (2 * ε) := by field_simp; ring
  rw [hcoef] at hy
  have hcp : P.carrierPair (fun j (_r : ℝ) => coupledPlainSynthesis N j (k + 1) c) i t =
      inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ
        (P.flux t ht (coefficientSynthesis (h := h) (k := k) N c) i).val)
        (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i k).val) := by
    simp only [carrierPair, carrierFlux_of_mem P _ i t ht, torusFactorialReadout_apply,
      torusFactorialGradientReadout_apply, coefficientSynthesis,
      coupledPlainGradientHk_eq_gradientTensor]
    rfl
  rw [P.kernelRhs_factorial_energy_identity N v t ht hv hvp c F g i, hcp]
  change _ + (3 * ν / 4 - ε / 2) * R ≤ _
  have hGpos := le_abs_self (inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (g i).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)))
  have hVneg := neg_le_abs (inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainDriftHk N c i k (v t) hv hvp).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (U i)))
  have hCneg := neg_le_abs (P.carrierPair (fun j (_r : ℝ) => coupledPlainSynthesis N j (k + 1) c) i t)
  rw [hcp] at hCneg
  have hFneg := neg_le_abs (inner ℝ
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (F i).val)
    (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (coupledPlainGradientHk N c i k).val))
  dsimp only [U, R] at *
  linarith

end TorusKernelOperator
end

/-! The Galerkin ODE satisfies the forced component energy inequality on every subinterval, with
the forcing of component `i` entering only through `‖F_i‖` and `‖g_i‖`. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelODE_component_forced_deriv_le
    (i : ι) (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y)
    (m ε : ℝ) (hε : 0 < ε)
    (hm : ∀ t ∈ Set.Icc a b,
      Real.sqrt (factorialNormSq ρ (coupledPlainSynthesis N i k (y t)).val) ≤ m)
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) y) volume a b) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      deriv (fun s => factorialNormSq ρ (coupledPlainSynthesis N i k (y s)).val) t +
        (3 * ν / 2 - ε) * gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) (y t)).val ≤
      2 * |P.carrierPair (fun j r => coupledPlainSynthesis N j (k + 1) (y r)) i t| +
        2 * m * Real.sqrt (factorialNormSq ρ (g i t).val) +
        (1 / ε) * factorialNormSq ρ (F i t).val := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hy.ae_hasDerivAt P.htime hint] with t ht
  intro hmem
  rw [(plainSynthesis_factorial_hasDerivAt N i k ρ (ht hmem)).deriv]
  have hpoint := P.kernelRhs_component_forced_le N v t hmem (hv t hmem) (hvp t hmem)
    (y t) (fun j => F j t) (fun j => g j t) αv B lam hα hB hlam
    hsmall hstrain (hd t hmem) (hjets t hmem) i m ε hε (hm t hmem)
  have hp : P.carrierPair (fun j (_r : ℝ) => coupledPlainSynthesis N j (k + 1) (y t)) i t =
      P.carrierPair (fun j r => coupledPlainSynthesis N j (k + 1) (y r)) i t :=
    P.carrierPair_congr_time _ _ i t (fun _ => rfl)
  rw [hp] at hpoint
  dsimp only [AVenhance.Infra.ODE.linearRhs]
  convert mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2) using 1
  · ring
  · field_simp

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelODE_component_forced_interval_le
    (i : ι) (y : ℝ → CoupledPlainCoefficients (h := h) N) (initial : CoupledPlainCoefficients (h := h) N)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) initial a b y)
    (hycont : Continuous y) (m ε : ℝ) (hm0 : 0 ≤ m) (hε : 0 < ε)
    (hm : ∀ t ∈ Set.Icc a b,
      Real.sqrt (factorialNormSq ρ (coupledPlainSynthesis N i k (y t)).val) ≤ m)
    (hF : MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM (P.projectedMatrix N v t))
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) y) volume a b) :
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      factorialNormSq ρ (coupledPlainSynthesis N i k (y t)).val +
        (3 * ν / 2 - ε) * (∫ r in Set.Ioc s t,
          gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) (y r)).val) ≤
      factorialNormSq ρ (coupledPlainSynthesis N i k (y s)).val +
        2 * (∫ r in Set.Icc a b,
          |P.carrierPair (fun j τ => coupledPlainSynthesis N j (k + 1) (y τ)) i r|) +
        2 * m * (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)) +
        (1 / ε) * (∫ r in Set.Icc a b, factorialNormSq ρ (F i r).val) := by
  have hac := plainSynthesis_factorial_absolutelyContinuous N i k ρ
    (hy.absolutelyContinuousOnInterval P.htime hint)
  have hc := ((torusFactorialGradientReadout (E := h i) ρ k).continuous.comp
    (coupledPlainSynthesis_continuous N i (k + 1) hycont)).norm.pow 2
  change Continuous (fun r => ‖torusFactorialGradientReadout (E := h i) ρ k
    (coupledPlainSynthesis N i (k + 1) (y r))‖ ^ 2) at hc
  simp only [torusFactorialGradientReadout_normSq] at hc
  have hr := hc.intervalIntegrable (μ := volume) a b
  let W := fun j r => coupledPlainSynthesis N j (k + 1) (y r)
  have hW (j : ι) : MemLp (W j) 2 (volume.restrict (Set.Icc a b)) :=
    coupledPlainSynthesis_memLp N j (k + 1) a b hycont
  have hCp := (P.carrierPair_integrable W hW i).abs
  have hf : Integrable (fun r => factorialNormSq ρ (F i r).val) (volume.restrict (Set.Icc a b)) :=
    factorialNormSq_integrable ρ k (torusJet_memLp k hF)
  have hg' : Integrable (fun r => Real.sqrt (factorialNormSq ρ (g i r).val))
      (volume.restrict (Set.Icc a b)) := by
    have := ((torusFactorialReadout (E := h i) ρ k).integrable_comp hg).norm
    simpa only [torusFactorialReadout_norm] using this
  let H := fun r => 2 * |P.carrierPair W i r| + 2 * m * Real.sqrt (factorialNormSq ρ (g i r).val) +
    (1 / ε) * factorialNormSq ρ (F i r).val
  have hH : Integrable H (volume.restrict (Set.Icc a b)) :=
    ((hCp.const_mul 2).add (hg'.const_mul (2 * m))).add (hf.const_mul (1 / ε))
  have hd := P.kernelODE_component_forced_deriv_le N v hv hvp F g αv B lam hα hB hlam
    hsmall hstrain hd hjets i y initial hy m ε hε hm hint
  intro s hs t ht hst
  have hpos : ∀ r, 0 ≤ H r := fun r =>
      add_nonneg (add_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
        (mul_nonneg (mul_nonneg (by norm_num) hm0) (Real.sqrt_nonneg _)))
        (mul_nonneg (by positivity) (factorialNormSq_nonneg ρ _))
  have he := perturbedTimeEnergyGlobal P.htime hs ht hst hac hr hH hpos hd
  have heq : (∫ r in Set.Icc a b, H r) =
      2 * (∫ r in Set.Icc a b, |P.carrierPair W i r|) +
      2 * m * (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)) +
      (1 / ε) * (∫ r in Set.Icc a b, factorialNormSq ρ (F i r).val) := by
    have hfirst := integral_add ((hCp.const_mul 2).add (hg'.const_mul (2 * m)))
      (hf.const_mul (1 / ε))
    have hsecond := integral_add (hCp.const_mul 2) (hg'.const_mul (2 * m))
    simp only [Pi.add_apply] at hfirst hsecond
    dsimp only [H]
    rw [hfirst, hsecond]
    simp only [integral_const_mul]
  rw [heq] at he
  simpa only [add_assoc] using he

end TorusKernelOperator
end

/-! The projected component energy inequality of a weak solution, with the forcing of component
`i` entering only through the norms of its own residual forcing. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_residualComponentForced
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (i : ι) (m ε : ℝ) (hm0 : 0 ≤ m) (hε : 0 < ε)
    (hm : ∀ t ∈ Set.Icc a b, Real.sqrt (factorialNormSq ρ (u i t).val) ≤ m)
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      F g u w) :
    let z := fun i t => w i t - galerkinProj N (w i t)
    let RF := fun i t => F i t + P.diffusionResidual z i t
    let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
    ∃ y : ℝ → CoupledPlainCoefficients (h := h) N,
      Continuous y ∧ (∀ t ∈ Set.Icc a b, y t = plainInitialCoefficients N (fun _ => k) (fun i => u i t)) ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
        factorialNormSq ρ (galerkinProj N (u i t)).val +
          (3 * ν / 2 - ε) * (∫ r in Set.Ioc s t, gradFactorialNormSq ρ (galerkinProj N (w i r)).val) ≤
        factorialNormSq ρ (galerkinProj N (u i s)).val +
          2 * (∫ r in Set.Icc a b, |P.carrierPair (fun j τ => coupledPlainSynthesis N j (k + 1) (y τ)) i r|) +
          2 * m * (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (Rg i r).val)) +
          (1 / ε) * (∫ r in Set.Icc a b, factorialNormSq ρ (RF i r - P.finiteFlux N y i r).val) := by
  dsimp only
  let z := fun i t => w i t - galerkinProj N (w i t)
  let RF := fun i t => F i t + P.diffusionResidual z i t
  let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
  obtain ⟨y, hycont, hy, hRFnew, hRg, hkODE, hkint⟩ :=
    P.kernelForcedWeakSolution_residualODE N v hv hvp F g hv_meas V hV hvb T hT w u f hF hg hsol
  have hlower (t : ℝ) (ht : t ∈ Set.Icc a b) (j : ι) :
      coupledPlainSynthesis N j (k) (y t) = galerkinProj N (u j t) := by
    rw [hy t ht]
    exact plainInitialCoefficients_synthesis N (fun _ => k) (fun j => u j t) j
  have hmy (t : ℝ) (ht : t ∈ Set.Icc a b) :
      Real.sqrt (factorialNormSq ρ (coupledPlainSynthesis N i k (y t)).val) ≤ m := by
    rw [hlower t ht i]
    exact (Real.sqrt_le_sqrt (galerkinProj_factorialNormSq_le N ρ (u i t))).trans (hm t ht)
  have he := P.kernelODE_component_forced_interval_le N v hv hvp
    (fun i t => RF i t - P.finiteFlux N y i t) Rg αv B lam hα hB hlam hsmall
    hstrain hd hjets i y (plainInitialCoefficients N (fun _ => k) f) hkODE hycont m ε hm0 hε hmy
    (hRFnew i) (hRg i) hkint
  have hhigher : ∀ᵐ s ∂volume.restrict (Set.Icc a b),
      coupledPlainSynthesis N i (k + 1) (y s) = galerkinProj N (w i s) := by
    filter_upwards [ae_all_iff.mpr hsol.2.2.1, ae_restrict_mem measurableSet_Icc] with s hs hsI
    rw [hy s hsI]
    have he : (fun j => u j s) = (fun j => truncateTorusHk (Nat.le_succ (k)) (w j s)) :=
      funext (fun j => (hs j).symm)
    rw [he]
    exact plainInitialCoefficients_higher_synthesis N (fun _ => k) (fun j => w j s) i
  refine ⟨y, hycont, hy, ?_⟩
  intro s hs t ht hst
  have hsub : Set.Ioc s t ⊆ Set.Icc a b := fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
  have hintG : (∫ r in Set.Ioc s t, gradFactorialNormSq ρ (coupledPlainSynthesis N i (k + 1) (y r)).val) =
      ∫ r in Set.Ioc s t, gradFactorialNormSq ρ (galerkinProj N (w i r)).val := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hhigher] with r hr
    simp only [hr]
  have h := he s hs t ht hst
  simp only [hlower t ht i, hlower s hs i, hintG] at h
  exact h

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_projectedComponentForced
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (i : ι) (m ε : ℝ) (hm0 : 0 ≤ m) (hε : 0 < ε)
    (hm : ∀ t ∈ Set.Icc a b, Real.sqrt (factorialNormSq ρ (u i t).val) ≤ m)
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w) :
    let z := fun i t => w i t - galerkinProj N (w i t)
    let RF := fun i t => F i t + P.carrierFlux z i t + P.diffusionResidual z i t
    let Rg := fun i t => g i t - plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT z i t
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      factorialNormSq ρ (galerkinProj N (u i t)).val +
        (3 * ν / 2 - ε) * (∫ r in Set.Ioc s t, gradFactorialNormSq ρ (galerkinProj N (w i r)).val) ≤
      factorialNormSq ρ (galerkinProj N (u i s)).val +
        2 * (∫ r in Set.Icc a b, |P.carrierPair (fun j τ => galerkinProj N (w j τ)) i r|) +
        2 * m * (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (Rg i r).val)) +
        (1 / ε) * (∫ r in Set.Icc a b, factorialNormSq ρ (RF i r).val) := by
  dsimp only
  let z := fun i t => w i t - galerkinProj N (w i t)
  let Ftotal := fun i t => F i t + P.carrierFlux w i t
  have hFt (j : ι) : MemLp (Ftotal j) 2 (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_add _ 2 (F j) (P.carrierFlux w j) (hF j)
      (P.carrierFlux_memLp_of_family w hsol.2.1 j)
  obtain ⟨y, _, hy, he⟩ := P.kernelForcedWeakSolution_residualComponentForced N v hv hvp Ftotal g
    αv B lam hα hB hlam hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hFt hg i m ε hm0 hε hm hsol
  have hflux (j : ι) := P.finiteFlux_eq_projectedCarrierFlux_ae N y u w hy hsol.2.2.1 j
  have hintEq :
      (∫ s in Set.Icc a b, factorialNormSq ρ
        (((F i s + P.carrierFlux w i s) +
          P.diffusionResidual z i s - P.finiteFlux N y i s)).val) =
      (∫ s in Set.Icc a b, factorialNormSq ρ
        ((F i s + P.carrierFlux z i s + P.diffusionResidual z i s)).val) := by
    apply integral_congr_ae
    filter_upwards [hflux i] with s hs
    apply congrArg (factorialNormSq ρ)
    rw [hs, P.carrierFlux_sub w (fun j t => galerkinProj N (w j t)) i s]
    congr 1
    abel
  have hp : (∫ s in Set.Icc a b, |P.carrierPair (fun j τ => coupledPlainSynthesis N j (k + 1) (y τ)) i s|) =
      ∫ s in Set.Icc a b, |P.carrierPair (fun j τ => galerkinProj N (w j τ)) i s| := by
    apply integral_congr_ae
    filter_upwards [P.carrierPair_synthesis_projected_ae N y u w hy hsol.2.2.1 i] with s hs
    rw [hs]
  intro s hs t ht hst
  have h := he s hs t ht hst
  rw [hintEq, hp] at h
  exact h

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! The forced component energy inequality of a weak solution of the kernel system: for every
component `i`, every subinterval `[s, t]` and every bound `m` of `√(|u_i|²)` on the window,
`|u_i(t)|² + (3ν/2 - ε) ∫_s^t |∇u_i|² ≤ |u_i(s)|² + 2 ∫ |⟨flux, ∇u_i⟩| + 2 m ‖g_i‖_{L¹} + ε⁻¹ ‖F_i‖²_{L²}`,
the forcing entering only through its own component. -/

section Single
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] {T : Type*} [MeasurableSpace T] {k : ℕ}

/-- Single-component time `L¹` perturbation of the factorial norm. -/
theorem factorialNorm_sub_integral_tendsto (μ : Measure T) (ρ : ℝ)
    (f : T → TorusHk k E) (hf : Integrable f μ)
    (r : ℕ → T → TorusHk k E) (hr : ∀ n, Integrable (r n) μ)
    (hlim : Tendsto (fun n => ∫ t, ‖r n t‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, Real.sqrt (factorialNormSq ρ (f t - r n t).val) ∂μ)
      atTop (𝓝 (∫ t, Real.sqrt (factorialNormSq ρ (f t).val) ∂μ)) := by
  have hh := torusMassNorm_sub_integral_tendsto (ι := Unit) (E := fun _ => E) μ (fun _ => k) ρ
    (fun _ => 1) (fun _ => one_pos) (fun _ => f) (fun _ => hf) (fun n _ => r n) (fun n _ => hr n)
    (fun _ => hlim)
  simpa only [massNormSq, Finset.univ_unique, Finset.sum_singleton, inv_one, one_mul] using hh

/-- Single-component time `L²` perturbation of the squared factorial norm. -/
theorem factorialNormSq_perturbed_integral_tendsto (μ : Measure T) (ρ : ℝ)
    (f : T → TorusHk k E) (hf : MemLp f 2 μ)
    (r : ℕ → T → TorusHk k E) (hr : ∀ n, MemLp (r n) 2 μ)
    (hlim : Tendsto (fun n => ∫ t, ‖r n t‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, factorialNormSq ρ (f t + r n t).val ∂μ)
      atTop (𝓝 (∫ t, factorialNormSq ρ (f t).val ∂μ)) := by
  have hh := torusMassNormSq_perturbed_integral_tendsto (ι := Unit) (E := fun _ => E) μ
    (fun _ => k) ρ (fun _ => 1) (fun _ => f) (fun _ => hf) (fun n _ => r n) (fun n _ => hr n)
    (fun _ => hlim)
  simpa only [massNormSq, Finset.univ_unique, Finset.sum_singleton, inv_one, one_mul] using hh

end Single

variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_component_forced_interval
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (i : ι) (m ε : ℝ) (hm0 : 0 ≤ m) (hε : 0 < ε)
    (hm : ∀ t ∈ Set.Icc a b, Real.sqrt (factorialNormSq ρ (u i t).val) ≤ m)
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w) :
    ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      factorialNormSq ρ (u i t).val +
        (3 * ν / 2 - ε) * (∫ r in Set.Ioc s t, gradFactorialNormSq ρ (w i r).val) ≤
      factorialNormSq ρ (u i s).val +
        2 * (∫ r in Set.Icc a b, |P.carrierPair w i r|) +
        2 * m * (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)) +
        (1 / ε) * (∫ r in Set.Icc a b, factorialNormSq ρ (F i r).val) := by
  have hw := hsol.2.1
  let z := fun N i t => w i t - galerkinProj N (w i t)
  have hz (N : ℕ) (j : ι) : MemLp (z N j) 2 (volume.restrict (Set.Icc a b)) :=
    timeMemLp_pointwise_sub _ 2 _ _ (hw j) ((galerkinProj N).comp_memLp' (hw j))
  -- flux forcing tail
  have hQ (N : ℕ) (j : ι) : MemLp (P.carrierFlux (z N) j) 2 (volume.restrict (Set.Icc a b)) :=
    P.carrierFlux_memLp_of_family _ (hz N) j
  have hR (N : ℕ) (j : ι) : MemLp (P.diffusionResidual (z N) j) 2 (volume.restrict (Set.Icc a b)) :=
    torusSpatialFluxPath_memLp (fun _ => k) 0 a b ν ρ P.radius_pos noLocalCoefficient
      noLocalSeminorm noLocalSmoothOnInterval noLocalPeriodicOnInterval P.htime
      noLocalMeasurable (z N) (hz N) j
  have hlR : Tendsto (fun N => ∫ t in Set.Icc a b, ‖P.diffusionResidual (z N) i t‖ ^ 2)
      atTop (𝓝 0) :=
    torusSpatialFluxPath_tail_square_tendsto (fun _ => k) 0 a b ν ρ P.radius_pos
      noLocalCoefficient noLocalSeminorm noLocalSmoothOnInterval noLocalPeriodicOnInterval
      P.htime noLocalMeasurable w hw i
  have hFlim := factorialNormSq_perturbed_integral_tendsto (volume.restrict (Set.Icc a b)) ρ
    (F i) (hF i) (fun N t => P.carrierFlux (z N) i t + P.diffusionResidual (z N) i t)
    (fun N => timeMemLp_pointwise_add _ 2 _ _ (hQ N i) (hR N i))
    (timeL2_residual_add_square_tendsto _ (fun N => P.carrierFlux (z N) i)
      (fun N => P.diffusionResidual (z N) i) (fun N => hQ N i) (fun N => hR N i)
      (P.carrierFlux_tail_square_tendsto w hw i) hlR)
  simp only [← add_assoc] at hFlim
  -- value forcing tail
  have hTint (N : ℕ) : Integrable (plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT (z N) i)
      (volume.restrict (Set.Icc a b)) :=
    (plainTransportCarrierPath_memLp (fun _ => k) a b v hv hvp T hT P.htime ρ P.radius_pos hv_meas
      V hV hvb (z N) (hz N) i).integrable (by norm_num)
  have hglim := factorialNorm_sub_integral_tendsto (volume.restrict (Set.Icc a b)) ρ (g i) (hg i)
    (fun N => plainTransportCarrierPath (fun _ => k) a b v hv hvp T hT (z N) i) hTint
    (plainTransportCarrierPath_tail_norm_tendsto (fun _ => k) a b v hv hvp T hT
      P.htime ρ P.radius_pos hv_meas V hV hvb w hw i)
  intro s hs t ht hst
  have hsub : Set.Icc s t ⊆ Set.Icc a b := Set.Icc_subset_Icc hs.1 ht.2
  have hwst (j : ι) : MemLp (w j) 2 (volume.restrict (Set.Icc s t)) :=
    (hw j).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgrad := galerkinProj_gradFactorial_integral_tendsto k s t ρ (w i) (hwst i)
  simp only [integral_Icc_eq_integral_Ioc] at hgrad
  have htime := galerkinProj_factorialNormSq_tendsto k ρ (u i t)
  have hstart := galerkinProj_factorialNormSq_tendsto k ρ (u i s)
  have hpair := P.carrierPair_projected_abs_integral_tendsto w hw i
  have hleft := htime.add (hgrad.const_mul (3 * ν / 2 - ε))
  have hright := ((hstart.add (hpair.const_mul 2)).add (hglim.const_mul (2 * m))).add
    (hFlim.const_mul (1 / ε))
  refine le_of_tendsto_of_tendsto' hleft hright (fun N => ?_)
  exact P.kernelForcedWeakSolution_projectedComponentForced N v hv hvp F g αv B lam hα hB hlam
    hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hF hg i m ε hm0 hε hm hsol s hs t ht hst

end TorusKernelOperator

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! The per-component budgets of the forced weak solution: the time supremum and the dissipation of
component `i` are at most `2 Q_i + 4 G_i²` with `Q_i = |f_i|² + 2 ∫|pair_i| + (2/ν) ∫|F_i|²`
and `G_i = ∫|g_i|`. The a priori bound `m₀` of the component is only used to know
that the supremum is finite. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_component_budget
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (i : ι) (m₀ : ℝ) (hm₀ : ∀ t ∈ Set.Icc a b, Real.sqrt (factorialNormSq ρ (u i t).val) ≤ m₀)
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w) :
    let Q := factorialNormSq ρ (f i).val + 2 * (∫ r in Set.Icc a b, |P.carrierPair w i r|) +
      (2 / ν) * (∫ r in Set.Icc a b, factorialNormSq ρ (F i r).val)
    let Gi := ∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)
    (∀ t ∈ Set.Icc a b, factorialNormSq ρ (u i t).val ≤ 2 * Q + 4 * Gi ^ 2) ∧
      ν * (∫ r in Set.Icc a b, gradFactorialNormSq ρ (w i r).val) ≤ 2 * Q + 4 * Gi ^ 2 := by
  dsimp only
  have hν := P.diffusivity_pos
  have hGi : 0 ≤ ∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val) :=
    integral_nonneg (fun r => Real.sqrt_nonneg _)
  have hstep := fun (m : ℝ) (hm0 : 0 ≤ m) (hm : ∀ t ∈ Set.Icc a b,
      Real.sqrt (factorialNormSq ρ (u i t).val) ≤ m) =>
    P.kernelForcedWeakSolution_component_forced_interval v hv hvp F g αv B lam hα hB hlam hsmall
      hstrain hd hjets hv_meas V hV hvb T hT w u f hF hg i m (ν / 2) hm0 (by positivity) hm hsol
  have hcoef : 3 * ν / 2 - ν / 2 = ν := by ring
  have hinv : 1 / (ν / 2) = 2 / ν := by field_simp
  have hRnn : 0 ≤ ∫ r in Set.Icc a b, gradFactorialNormSq ρ (w i r).val :=
    integral_nonneg (fun r => torusCarrierGradFactorial_nonneg ρ k (w i r))
  have hini : u i a = f i := hsol.2.2.2.1 i
  have hbase (m : ℝ) (hm0 : 0 ≤ m) (hm : ∀ t ∈ Set.Icc a b,
      Real.sqrt (factorialNormSq ρ (u i t).val) ≤ m) (t : ℝ) (ht : t ∈ Set.Icc a b) :
      factorialNormSq ρ (u i t).val +
        ν * (∫ r in Set.Ioc a t, gradFactorialNormSq ρ (w i r).val) ≤
      factorialNormSq ρ (f i).val + 2 * (∫ r in Set.Icc a b, |P.carrierPair w i r|) +
        2 * m * (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)) +
        (2 / ν) * (∫ r in Set.Icc a b, factorialNormSq ρ (F i r).val) := by
    have he := hstep m hm0 hm a ⟨le_rfl, P.htime⟩ t ht ht.1
    rw [hini, hcoef, hinv] at he
    exact he
  obtain ⟨m, hm0, hm, hm2⟩ := AVRegularity.EntryTerminal.ForcedEnergy.exists_sqrt_bound (I := Set.Icc a b) ⟨a, le_rfl, P.htime⟩
    (fun t => factorialNormSq ρ (u i t).val)
    (factorialNormSq ρ (f i).val + 2 * (∫ r in Set.Icc a b, |P.carrierPair w i r|) +
      (2 / ν) * (∫ r in Set.Icc a b, factorialNormSq ρ (F i r).val)) (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)) m₀
    (fun t _ => factorialNormSq_nonneg ρ _) hm₀
    (fun m hm0 hm t ht => by
      have := hbase m hm0 hm t ht
      have hn : 0 ≤ ν * ∫ r in Set.Ioc a t, gradFactorialNormSq ρ (w i r).val :=
        mul_nonneg hν.le (integral_nonneg (fun r => torusCarrierGradFactorial_nonneg ρ k (w i r)))
      linarith)
  have hQ' (t : ℝ) (ht : t ∈ Set.Icc a b) :
      factorialNormSq ρ (u i t).val + ν * (∫ r in Set.Ioc a t, gradFactorialNormSq ρ (w i r).val) ≤
        2 * (factorialNormSq ρ (f i).val + 2 * (∫ r in Set.Icc a b, |P.carrierPair w i r|) +
          (2 / ν) * (∫ r in Set.Icc a b, factorialNormSq ρ (F i r).val)) +
        4 * (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)) ^ 2 := by
    have := hbase m hm0 hm t ht
    nlinarith [sq_nonneg (m - 2 * (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)))]
  refine ⟨fun t ht => ?_, ?_⟩
  · have := hQ' t ht
    have hn : 0 ≤ ν * ∫ r in Set.Ioc a t, gradFactorialNormSq ρ (w i r).val :=
      mul_nonneg hν.le (integral_nonneg (fun r => torusCarrierGradFactorial_nonneg ρ k (w i r)))
    linarith
  · have := hQ' b ⟨P.htime, le_rfl⟩
    rw [← integral_Icc_eq_integral_Ioc] at this
    have := factorialNormSq_nonneg ρ (u i b).val
    linarith

end TorusKernelOperator
end

/-! **Forced strong energy of the kernel system**. A weak solution of the kernel
system with forcing `(F, g)` has strong energy
`≤ (8 ‖f‖² + (24/ν) ∫‖F‖² + 28 (∫‖g‖)²)^{1/2}`, norms in `L²_π`, with the time supremum taken
component by component before the mass sum. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

variable (v : ℝ → Vec 2 → Vec 2)
  (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
  (hvp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (v t))
  (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
  (g : ∀ i, ℝ → TorusHk k (h i))
  (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
  (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
  (hd : ∀ t ∈ Set.Icc a b, ∀ x, ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
  (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ k → ∀ x,
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_forced_budget_sum
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w) :
    ∃ S : ι → ℝ, (∀ i, 0 ≤ S i) ∧ (∀ i, ∀ t ∈ Set.Icc a b, factorialNormSq ρ (u i t).val ≤ S i) ∧
      (∑ i, (P.π i)⁻¹ * (S i + ν * ∫ r in Set.Icc a b, gradFactorialNormSq ρ (w i r).val)) ≤
        8 * massNormSq ρ P.π (fun i => (f i).val) +
        (24 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
        28 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2 := by
  have hν := P.diffusivity_pos
  have hπ := P.hπ
  set E0 := massNormSq ρ P.π (fun i => (f i).val) with hE0
  set FF := ∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val) with hFF
  set GG := ∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val)) with hGG
  have hE0n : 0 ≤ E0 := massNormSq_nonneg ρ P.π hπ _
  have hFn : 0 ≤ FF := integral_nonneg (fun s => massNormSq_nonneg ρ P.π hπ _)
  have hGn : 0 ≤ GG := integral_nonneg (fun s => Real.sqrt_nonneg _)
  have hen := P.kernelForcedWeakSolution_energy v hv hvp F g αv B lam hα hB hlam hsmall hstrain
    hd hjets hv_meas V hV hvb T hT w u f hF hg hsol
  set Rall := ∫ s in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i s).val) with hRall
  have hRn : 0 ≤ Rall := integral_nonneg (fun s => massGradNormSq_nonneg ρ P.π hπ _)
  set Gb := 2 * E0 + (8 / ν) * FF + 10 * GG ^ 2 with hGb
  have hRb : (ν / 2) * Rall ≤ Gb := by
    have := hen a ⟨le_rfl, P.htime⟩
    have hn := massNormSq_nonneg ρ P.π hπ (fun i => (u i a).val)
    linarith
  have hUb (t : ℝ) (ht : t ∈ Set.Icc a b) : massNormSq ρ P.π (fun i => (u i t).val) ≤ Gb := by
    have := hen t ht
    have hn : 0 ≤ (ν / 2) * Rall := mul_nonneg (by positivity) hRn
    linarith
  have hbud (i : ι) := P.kernelForcedWeakSolution_component_budget v hv hvp F g αv B lam hα hB hlam
    hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hF hg i (Real.sqrt (P.π i * Gb))
    (fun t ht => Real.sqrt_le_sqrt ((componentFactorial_le_mass ρ P.π hπ (fun j => (u j t).val) i).trans
      (mul_le_mul_of_nonneg_left (hUb t ht) (hπ i).le))) hsol
  dsimp only at hbud
  let ω := fun i => (P.π i)⁻¹
  let C := fun i => ∫ r in Set.Icc a b, |P.carrierPair w i r|
  let A := fun i => ∫ r in Set.Icc a b, factorialNormSq ρ (F i r).val
  let Gi := fun i => ∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)
  let R := fun i => ∫ r in Set.Icc a b, gradFactorialNormSq ρ (w i r).val
  let e0 := fun i => factorialNormSq ρ (f i).val
  let S := fun i => 2 * (e0 i + 2 * C i + (2 / ν) * A i) + 4 * Gi i ^ 2
  have hω (i : ι) : 0 ≤ ω i := inv_nonneg.mpr (hπ i).le
  have he0 (i : ι) : 0 ≤ e0 i := factorialNormSq_nonneg ρ _
  have hC (i : ι) : 0 ≤ C i := integral_nonneg (fun _ => abs_nonneg _)
  have hA (i : ι) : 0 ≤ A i := integral_nonneg (fun _ => factorialNormSq_nonneg ρ _)
  have hG (i : ι) : 0 ≤ Gi i := integral_nonneg (fun _ => Real.sqrt_nonneg _)
  have hR (i : ι) : 0 ≤ R i := integral_nonneg (fun s => torusCarrierGradFactorial_nonneg ρ k (w i s))
  have hS (i : ι) : 0 ≤ S i := by
    have := he0 i; have := hC i; have := hA i
    have : 0 ≤ (2 / ν) * A i := mul_nonneg (by positivity) (hA i)
    have := sq_nonneg (Gi i)
    dsimp only [S]; linarith
  -- sums
  have hsumE : (∑ i, ω i * e0 i) = E0 := rfl
  have hsumC : (∑ i, ω i * C i) ≤ (ν * P.θ) * Rall := P.carrierPair_sum_integral_bound w hsol.2.1
  have hsumA : (∑ i, ω i * A i) = FF := by
    rw [hFF]
    exact (AVRegularity.CoupledEnergy.Variational.torusMassNormSq_integral_split
      (volume.restrict (Set.Icc a b)) (fun _ => k) ρ P.π F hF).symm
  have hxint (i : ι) : Integrable (fun t => Real.sqrt (factorialNormSq ρ (g i t).val))
      (volume.restrict (Set.Icc a b)) := by
    have := ((torusFactorialReadout (E := h i) ρ k).integrable_comp (hg i)).norm
    simpa only [torusFactorialReadout_norm] using this
  have hx2 (t : ℝ) : (∑ i, ω i * Real.sqrt (factorialNormSq ρ (g i t).val) ^ 2) =
      massNormSq ρ P.π (fun i => (g i t).val) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sq_sqrt (factorialNormSq_nonneg ρ _)]
  have hJ : Integrable (fun t => Real.sqrt (∑ i, ω i * Real.sqrt (factorialNormSq ρ (g i t).val) ^ 2))
      (volume.restrict (Set.Icc a b)) := by
    simp only [hx2]
    exact massNorm_integrable ρ P.π hπ
      (fun i => torusJet_memLp k (memLp_one_iff_integrable.mpr (hg i)))
  have hsumG : (∑ i, ω i * Gi i ^ 2) ≤ GG ^ 2 := by
    have := AVRegularity.EntryTerminal.ForcedEnergy.weighted_integral_sq_le
      (volume.restrict (Set.Icc a b)) ω hω (fun i t => Real.sqrt (factorialNormSq ρ (g i t).val)) hxint hJ
    simpa only [hx2] using this
  -- the bound on the pairing sum
  have hth : (ν * P.θ) * Rall ≤ Gb / 4 := by
    have hh := mul_le_mul_of_nonneg_right P.hθ (mul_nonneg hν.le hRn)
    linarith
  have hK : (24 / ν) * FF = 3 * ((8 / ν) * FF) := by ring
  -- the sum
  have hmain : (∑ i, ω i * (S i + ν * R i)) ≤ 8 * E0 + (24 / ν) * FF + 28 * GG ^ 2 := by
    have hpt (i : ι) : ω i * (S i + ν * R i) ≤
        ω i * (4 * e0 i + 8 * C i + (8 / ν) * A i + 8 * Gi i ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (hω i)
      have := (hbud i).2
      have e : 2 * (factorialNormSq ρ (f i).val + 2 * (∫ r in Set.Icc a b, |P.carrierPair w i r|) +
          (2 / ν) * (∫ r in Set.Icc a b, factorialNormSq ρ (F i r).val)) +
          4 * (∫ r in Set.Icc a b, Real.sqrt (factorialNormSq ρ (g i r).val)) ^ 2 = S i := rfl
      rw [e] at this
      have e2 : (8 / ν) * A i = 4 * ((2 / ν) * A i) := by ring
      dsimp only [S]
      dsimp only [S, R, e0, C, A, Gi] at this ⊢
      linarith
    refine (Finset.sum_le_sum (fun i _ => hpt i)).trans ?_
    have e (i : ι) : ω i * (4 * e0 i + 8 * C i + (8 / ν) * A i + 8 * Gi i ^ 2) =
        4 * (ω i * e0 i) + 8 * (ω i * C i) + (8 / ν) * (ω i * A i) + 8 * (ω i * Gi i ^ 2) := by ring
    simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsumE, hsumA]
    linarith [hsumC, hth, hsumG, hGb, hK]
  exact ⟨S, hS, fun i t ht => (hbud i).1 t ht, hmain⟩

include hv hvp hα hB hlam hsmall hstrain hd hjets in
theorem kernelForcedWeakSolution_forced_strongEnergy
    (hv_meas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (T : ∀ _ : ι, Fin (k + 1) → ℝ)
    (hT : ∀ t ∈ Set.Icc a b, ∀ i l x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l.val x‖ ≤ T i l)
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (f : ∀ i, TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (hsol : IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + P.carrierFlux w i t) g u w) :
    AVRegularity.strongEnergy ρ ν P.π a b u w ≤
      ENNReal.ofReal (Real.sqrt (8 * massNormSq ρ P.π (fun i => (f i).val) +
        (24 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
        28 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2)) := by
  have hν := P.diffusivity_pos
  obtain ⟨S, hS, hSu, hsum⟩ := P.kernelForcedWeakSolution_forced_budget_sum v hv hvp F g αv B lam hα hB
    hlam hsmall hstrain hd hjets hv_meas V hV hvb T hT w u f hF hg hsol
  have hR (i : ι) : 0 ≤ ∫ r in Set.Icc a b, gradFactorialNormSq ρ (w i r).val :=
    integral_nonneg (fun s => torusCarrierGradFactorial_nonneg ρ k (w i s))
  have hbudget := componentSupDissipation_le_budget (Set.Icc a b) (fun i => (P.π i)⁻¹) S
    (fun i => ν * ∫ r in Set.Icc a b, gradFactorialNormSq ρ (w i r).val)
    (fun i => inv_nonneg.mpr (P.hπ i).le) hS (fun i => mul_nonneg hν.le (hR i))
    (fun i t => factorialNormSq ρ (u i t).val) hSu
  rw [AVRegularity.Construction.Preservation.FullLift.strongEnergy_component_integral hν.le P.π u w hsol.2.1]
  have hY : 0 ≤ 8 * massNormSq ρ P.π (fun i => (f i).val) +
        (24 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
        28 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2 := by
    have h1 := massNormSq_nonneg ρ P.π P.hπ (fun i => (f i).val)
    have h2 : 0 ≤ ∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val) :=
      integral_nonneg (fun s => massNormSq_nonneg ρ P.π P.hπ _)
    exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) h1) (mul_nonneg (by positivity) h2))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  calc _ ≤ (ENNReal.ofReal (8 * massNormSq ρ P.π (fun i => (f i).val) +
        (24 / ν) * (∫ s in Set.Icc a b, massNormSq ρ P.π (fun i => (F i s).val)) +
        28 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ P.π (fun i => (g i s).val))) ^ 2)) ^ (1 / 2 : ℝ) := by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        exact hbudget.trans (ENNReal.ofReal_le_ofReal hsum)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hY (by norm_num)]

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end
end
