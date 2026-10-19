-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.TorusEnergy.LocalInt
import AVRegularity.CoupledEnergy.Variational.PullbackForm
import AVRegularity.Applications.TorusEnergy.StreamFacts
import AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy
import AVRegularity.Applications.Global.CompactRangeMain
public import Mathlib.MeasureTheory.Function.L2Space
import AVenhance.Infra.Classical.GalerkinGenerator
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section
noncomputable section

section
namespace AVRegularity.Applications

/-! # The balance of mollification error and time increment

Abstract real lemma: if `D ≤ A rˢ + h R r⁻ⁿ` for all `0 < r ≤ 1/4` and `D ≤ E`, then
`D ≤ (A + R + E 4ˢ) h^{s/(s+n)}`. -/

theorem modulus_balance {s : ℝ} (hs : 0 < s) (n : ℕ) (hn : 0 < n) {D E A R h : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hE : 0 ≤ E) (hh : 0 < h) (hDE : D ≤ E)
    (hbal : ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → D ≤ A * r ^ s + h * R * (r⁻¹) ^ n) :
    D ≤ (A + R + E * 4 ^ s) * h ^ (s / (s + n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < s + n := by linarith
  have hpow : 0 < h ^ (s / (s + n)) := Real.rpow_pos_of_pos hh _
  have h4 : 0 < (4 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  by_cases hcase : h ≤ (1 / 4 : ℝ) ^ (s + n)
  · set e : ℝ := 1 / (s + n) with he
    have he0 : 0 < e := by positivity
    set r : ℝ := h ^ e with hr
    have hr0 : 0 < r := Real.rpow_pos_of_pos hh _
    have hr4 : r ≤ 1 / 4 := by
      calc r = h ^ e := rfl
        _ ≤ ((1 / 4 : ℝ) ^ (s + n)) ^ e := Real.rpow_le_rpow hh.le hcase he0.le
        _ = 1 / 4 := by
          rw [← Real.rpow_mul (by norm_num)]
          have : (s + n) * e = 1 := by rw [he]; field_simp
          rw [this, Real.rpow_one]
    have hrs : r ^ s = h ^ (s / (s + n)) := by
      rw [hr, ← Real.rpow_mul hh.le, he]; congr 1; field_simp
    have hhr : h = r ^ (s + n) := by
      rw [hr, ← Real.rpow_mul hh.le, he]
      have : e * (s + n) = 1 := by rw [he]; field_simp
      rw [this, Real.rpow_one]
    have hrn : h * (r⁻¹) ^ n = r ^ s := by
      have : r ^ (s + n) = r ^ s * r ^ n := by
        rw [Real.rpow_add hr0, Real.rpow_natCast]
      rw [hhr, this, inv_pow]
      field_simp
    have := hbal r hr0 hr4
    have e2 : h * R * (r⁻¹) ^ n = R * r ^ s := by
      rw [mul_assoc, mul_comm R, ← mul_assoc, hrn]; ring
    rw [e2, hrs] at this
    have hnn : 0 ≤ E * 4 ^ s * h ^ (s / (s + n)) := by positivity
    generalize h ^ (s / (s + n)) = X at *
    generalize (4 : ℝ) ^ s = Y at *
    linarith
  · push Not at hcase
    have h1 : (1 / 4 : ℝ) ^ s ≤ h ^ (s / (s + n)) := by
      calc (1 / 4 : ℝ) ^ s = ((1 / 4 : ℝ) ^ (s + n)) ^ (s / (s + n)) := by
            rw [← Real.rpow_mul (by norm_num)]; congr 1; field_simp
        _ ≤ h ^ (s / (s + n)) :=
            Real.rpow_le_rpow (by positivity) hcase.le (by positivity)
    have h2 : 1 ≤ 4 ^ s * h ^ (s / (s + n)) := by
      have : (4 : ℝ) ^ s * (1 / 4 : ℝ) ^ s = 1 := by
        rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
      calc (1 : ℝ) = 4 ^ s * (1 / 4 : ℝ) ^ s := this.symm
        _ ≤ 4 ^ s * h ^ (s / (s + n)) := mul_le_mul_of_nonneg_left h1 h4.le
    have hAR : 0 ≤ (A + R) * h ^ (s / (s + n)) := by positivity
    have h3 : E ≤ E * (4 ^ s * h ^ (s / (s + n))) := by
      calc E = E * 1 := (mul_one _).symm
        _ ≤ E * (4 ^ s * h ^ (s / (s + n))) := mul_le_mul_of_nonneg_left h2 hE
    generalize h ^ (s / (s + n)) = X at *
    generalize (4 : ℝ) ^ s = Y at *
    nlinarith

end AVRegularity.Applications
end

section
open Filter Topology
namespace AVRegularity.Applications

/-! # The stream-tail ratio tends to zero (abstract real lemma)

`ϑ_i = C E1ᵢ^β / κ_i → 0` when `E1 ≤ 2^q E0^q`, `E0^e/2 ≤ κ`, `qβ = e + p` with `e, p > 0` and
`κ → 0`. -/

theorem vartheta_tendsto {C β e p q : ℝ} {κ E0 E1 : ℕ → ℝ} (hC : 0 ≤ C) (he : 0 < e) (hp : 0 < p)
    (hβ : 0 < β) (hE0 : ∀ i, 0 < E0 i) (hE1 : ∀ i, 0 < E1 i) (hκpos : ∀ i, 0 < κ i)
    (hκ : Tendsto κ atTop (𝓝 0)) (hlow : ∀ i, E0 i ^ e / 2 ≤ κ i)
    (hrec : ∀ i, E1 i ≤ 2 ^ q * E0 i ^ q) (hpq : q * β = e + p) :
    Tendsto (fun i => C * E1 i ^ β / κ i) atTop (𝓝 0) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hbound : ∀ i, C * E1 i ^ β / κ i ≤ (2 * C * 2 ^ (q * β)) * (2 * κ i) ^ (p / e) := by
    intro i
    have h0 := hE0 i
    have hk := hκpos i
    have hE1β : E1 i ^ β ≤ 2 ^ (q * β) * E0 i ^ (e + p) := by
      calc E1 i ^ β ≤ (2 ^ q * E0 i ^ q) ^ β :=
            Real.rpow_le_rpow (hE1 i).le (hrec i) hβ.le
        _ = 2 ^ (q * β) * E0 i ^ (q * β) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul h2.le,
              ← Real.rpow_mul h0.le]
        _ = 2 ^ (q * β) * E0 i ^ (e + p) := by rw [hpq]
    have hsplit : E0 i ^ (e + p) = E0 i ^ e * E0 i ^ p := Real.rpow_add h0 e p
    have hEe : E0 i ^ e ≤ 2 * κ i := by linarith [hlow i]
    have hEp : E0 i ^ p ≤ (2 * κ i) ^ (p / e) := by
      calc E0 i ^ p = (E0 i ^ e) ^ (p / e) := by
            rw [← Real.rpow_mul h0.le]; congr 1; field_simp
        _ ≤ (2 * κ i) ^ (p / e) :=
            Real.rpow_le_rpow (by positivity) hEe (by positivity)
    have hEp0 : 0 ≤ E0 i ^ p := by positivity
    rw [div_le_iff₀ hk]
    calc C * E1 i ^ β ≤ C * (2 ^ (q * β) * (E0 i ^ e * E0 i ^ p)) := by
          rw [← hsplit]; exact mul_le_mul_of_nonneg_left hE1β hC
      _ = C * 2 ^ (q * β) * E0 i ^ p * E0 i ^ e := by ring
      _ ≤ C * 2 ^ (q * β) * E0 i ^ p * (2 * κ i) := by
          gcongr
      _ ≤ C * 2 ^ (q * β) * (2 * κ i) ^ (p / e) * (2 * κ i) := by
          gcongr
      _ = (2 * C * 2 ^ (q * β)) * (2 * κ i) ^ (p / e) * κ i := by ring
  have hlim : Tendsto (fun i => (2 * C * 2 ^ (q * β)) * (2 * κ i) ^ (p / e)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun i => 2 * κ i) atTop (𝓝 0) := by simpa using hκ.const_mul 2
    have h3 : Tendsto (fun x : ℝ => x ^ (p / e)) (𝓝 0) (𝓝 (0 ^ (p / e))) :=
      (Real.continuousAt_rpow_const 0 (p / e) (Or.inr (by positivity))).tendsto
    rw [Real.zero_rpow (by positivity)] at h3
    simpa using (h3.comp h1).const_mul (2 * C * 2 ^ (q * β))
  refine squeeze_zero (fun i => ?_) hbound hlim
  have := hE1 i
  have := hκpos i
  positivity

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology
namespace AVRegularity.Applications

/-! # A weakly differentiable continuous function is the primitive of its derivative

If `A` is continuous on `[t₁, t₂]`, `K` is integrable on `(t₁, t₂)` and the identity
`∫ (A η' + η K) = -c η(t₁)` holds for the cutoffs `η = etaCut τ δ`, then
`A τ = c + ∫_{t₁}^{τ} K`. -/

theorem integrable_etaCut_mul {μ : Measure ℝ} {K : ℝ → ℝ} (hK : Integrable K μ) (τ δ : ℝ) :
    Integrable (fun t => etaCut τ δ t * K t) μ :=
  hK.bdd_mul (c := 1) etaCut_contDiff.continuous.aestronglyMeasurable
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (etaCut_nonneg t)]; exact etaCut_le_one t)

theorem tendsto_integral_kerCut {A : ℝ → ℝ} {t₁ t₂ τ : ℝ} (hτ1 : t₁ ≤ τ) (hτ2 : τ < t₂)
    (hA : ContinuousOn A (Set.Icc t₁ t₂)) :
    Tendsto (fun δ : ℝ => ∫ t in Set.Ioo t₁ t₂, A t * kerCut τ δ t) (𝓝[>] 0) (𝓝 (A τ)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨r, hr, hra⟩ := Metric.continuousWithinAt_iff.1 (hA τ ⟨hτ1, hτ2.le⟩) (ε / 2)
    (half_pos hε)
  refine ⟨min r (t₂ - τ), lt_min hr (by linarith), fun δ hδpos hδ => ?_⟩
  have hδ0 : 0 < δ := hδpos
  have hδ' : δ < min r (t₂ - τ) := by simpa [Real.dist_eq, abs_of_pos hδ0] using hδ
  have hδr : δ < r := lt_of_lt_of_le hδ' (min_le_left _ _)
  have hδt : δ < t₂ - τ := lt_of_lt_of_le hδ' (min_le_right _ _)
  have hker1 : ∫ t in Set.Ioo t₁ t₂, kerCut τ δ t = 1 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := τ)
      (kerCut_continuous.intervalIntegrable _ _) (kerCut_continuous.intervalIntegrable _ _)]
    have h0 : ∫ t in t₁..τ, kerCut τ δ t = 0 := by
      rw [intervalIntegral.integral_of_le hτ1, integral_Ioc_eq_integral_Ioo]
      exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => kerCut_eq_zero_of_lt hδ0 ht.2
    rw [h0, zero_add]
    exact integral_kerCut hδ0 (by linarith)
  have hkerInt : IntegrableOn (kerCut τ δ) (Set.Ioo t₁ t₂) :=
    (kerCut_continuous.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have haInt : IntegrableOn (fun t => A t * kerCut τ δ t) (Set.Ioo t₁ t₂) :=
    ((hA.mul kerCut_continuous.continuousOn).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hdiff : (∫ t in Set.Ioo t₁ t₂, A t * kerCut τ δ t) - A τ =
      ∫ t in Set.Ioo t₁ t₂, (A t - A τ) * kerCut τ δ t := by
    have : ∫ t in Set.Ioo t₁ t₂, (A t - A τ) * kerCut τ δ t =
        (∫ t in Set.Ioo t₁ t₂, A t * kerCut τ δ t) -
          ∫ t in Set.Ioo t₁ t₂, A τ * kerCut τ δ t := by
      rw [← integral_sub haInt (hkerInt.const_mul (A τ))]
      exact integral_congr_ae (Eventually.of_forall fun t => by ring)
    rw [this, integral_const_mul, hker1, mul_one]
  rw [Real.dist_eq, hdiff]
  have hle : ‖∫ t in Set.Ioo t₁ t₂, (A t - A τ) * kerCut τ δ t‖ ≤
      ∫ t in Set.Ioo t₁ t₂, (ε / 2) * kerCut τ δ t := by
    refine norm_integral_le_of_norm_le (hkerInt.const_mul (ε / 2)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (kerCut_nonneg hδ0 t)]
    rcases le_or_gt t (τ + δ) with h1 | h1
    · rcases lt_or_ge t τ with h2 | h2
      · simp [kerCut_eq_zero_of_lt hδ0 h2]
      · have := hra (x := t) ⟨ht.1.le, ht.2.le⟩ (by
          rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
        rw [Real.dist_eq] at this
        exact mul_le_mul_of_nonneg_right this.le (kerCut_nonneg hδ0 t)
    · simp [kerCut_eq_zero_of_gt hδ0 h1]
  rw [integral_const_mul, hker1, mul_one] at hle
  rw [Real.norm_eq_abs] at hle
  linarith

theorem tendsto_integral_etaCut {K : ℝ → ℝ} {t₁ t₂ τ : ℝ} (hτ1 : t₁ ≤ τ) (hτ2 : τ < t₂)
    (hK : IntegrableOn K (Set.Ioo t₁ t₂)) :
    Tendsto (fun δ : ℝ => ∫ t in Set.Ioo t₁ t₂, etaCut τ δ t * K t) (𝓝[>] 0)
      (𝓝 (∫ t in t₁..τ, K t)) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioo t₁ t₂)) (l := 𝓝[>] (0 : ℝ))
    (F := fun δ t => etaCut τ δ t * K t) (f := fun t => (Set.Iic τ).indicator K t)
    (bound := fun t => ‖K t‖) ?_ ?_ hK.norm ?_
  · have e : ∫ t in Set.Ioo t₁ t₂, (Set.Iic τ).indicator K t = ∫ t in t₁..τ, K t := by
      rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        intervalIntegral.integral_of_le hτ1]
      have : Set.Iic τ ∩ Set.Ioo t₁ t₂ = Set.Ioc t₁ τ := by
        ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioo, Set.mem_Ioc]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
      rw [this]
    rwa [e] at hlim
  · exact Eventually.of_forall fun δ =>
      ((etaCut_contDiff (t₁ := τ) (δ := δ)).continuous.aestronglyMeasurable).mul hK.aestronglyMeasurable
  · refine Eventually.of_forall fun δ => Eventually.of_forall fun t => ?_
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (etaCut_nonneg t)]
    exact mul_le_of_le_one_left (norm_nonneg _) (etaCut_le_one t)
  · refine Eventually.of_forall fun t => ?_
    by_cases ht : t ≤ τ
    · have : (Set.Iic τ).indicator K t = K t := Set.indicator_of_mem (show t ∈ Set.Iic τ from ht) K
      rw [this]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [etaCut_of_le ht hδ, one_mul]
    · have : (Set.Iic τ).indicator K t = 0 := Set.indicator_of_notMem (show t ∉ Set.Iic τ from ht) K
      rw [this]
      have hpos : 0 < t - τ := by linarith [not_le.1 ht]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
      rw [etaCut_of_ge (by linarith [hδ.2]) hδ.1, zero_mul]

theorem primitive_of_weak {A K : ℝ → ℝ} {t₁ t₂ c τ : ℝ} (hτ1 : t₁ ≤ τ) (hτ2 : τ < t₂)
    (hA : ContinuousOn A (Set.Icc t₁ t₂)) (hK : IntegrableOn K (Set.Ioo t₁ t₂))
    (hid : ∀ δ : ℝ, 0 < δ → τ + δ ≤ t₂ →
      ∫ t in Set.Ioo t₁ t₂, (A t * (-(kerCut τ δ t)) + etaCut τ δ t * K t) = -c) :
    A τ = c + ∫ t in t₁..τ, K t := by
  have h1 := tendsto_integral_kerCut hτ1 hτ2 hA
  have h2 := tendsto_integral_etaCut hτ1 hτ2 hK
  have hconst : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫ t in Set.Ioo t₁ t₂, A t * kerCut τ δ t) -
        (∫ t in Set.Ioo t₁ t₂, etaCut τ δ t * K t) = c := by
    filter_upwards [Ioo_mem_nhdsGT (show 0 < t₂ - τ by linarith)] with δ hδ
    have hkerInt : IntegrableOn (kerCut τ δ) (Set.Ioo t₁ t₂) :=
      (kerCut_continuous.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have haInt : IntegrableOn (fun t => A t * kerCut τ δ t) (Set.Ioo t₁ t₂) :=
      ((hA.mul kerCut_continuous.continuousOn).integrableOn_Icc).mono_set
        Set.Ioo_subset_Icc_self
    have h := hid δ hδ.1 (by linarith [hδ.2])
    have e : (fun t => A t * (-(kerCut τ δ t)) + etaCut τ δ t * K t) =
        fun t => -(A t * kerCut τ δ t) + etaCut τ δ t * K t := by
      funext t; ring
    rw [e, integral_add (f := fun t => -(A t * kerCut τ δ t)) (g := fun t => etaCut τ δ t * K t)
      haInt.neg (integrable_etaCut_mul hK τ δ), integral_neg] at h
    linarith
  have := tendsto_nhds_unique (h1.sub h2) (tendsto_const_nhds.congr' (hconst.mono fun δ h => h.symm))
  linarith

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity.Applications

/-! # Weak sequential compactness in `L²(𝕋²)`

A sequence bounded in `L²(unitCube)` has a weakly convergent subsequence, and the weak limit obeys
the same bound. -/

theorem l2NormSq_eq_inner (u : Lp ℝ 2 (volume.restrict unitCube)) :
    l2NormSq (u : Vec 2 → ℝ) = inner ℝ u u := by
  unfold l2NormSq
  have := integral_mul_lp_eq_inner (μ := volume.restrict unitCube) u (Lp.memLp u)
  rw [Lp.toLp_coeFn] at this
  rw [← this]
  exact integral_congr_ae (Eventually.of_forall fun x => sq _)

theorem exists_weak_subseq {F : ℝ} (f : ℕ → Vec 2 → ℝ)
    (hf : ∀ i, MemL2On unitCube (f i) ∧ Real.sqrt (l2NormSq (f i)) ≤ F) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ fstar : Vec 2 → ℝ, MemL2On unitCube fstar ∧
      Real.sqrt (l2NormSq fstar) ≤ F ∧
      ∀ g : Vec 2 → ℝ, MemL2On unitCube g →
        Tendsto (fun i => ∫ x in unitCube, f (σ i) x * g x) atTop
          (𝓝 (∫ x in unitCube, fstar x * g x)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  let u : ℕ → Lp ℝ 2 (volume.restrict unitCube) := fun n => (hf n).1.toLp (f n)
  have hnorm : ∀ n, ‖u n‖ ≤ F := by
    intro n
    have h1 : ‖u n‖ ^ 2 = l2NormSq (f n) := by
      rw [← real_inner_self_eq_norm_sq, ← l2NormSq_eq_inner]
      unfold l2NormSq
      refine integral_congr_ae ?_
      filter_upwards [(hf n).1.coeFn_toLp] with x hx
      simp only [u, hx]
    have h2 : ‖u n‖ = Real.sqrt (l2NormSq (f n)) := by
      rw [← h1, Real.sqrt_sq (norm_nonneg _)]
    rw [h2]; exact (hf n).2
  obtain ⟨v, σ, hσ, hlim⟩ := CoupledEnergy.Variational.exists_strictMono_tendsto_inner_of_norm_le
    u F hnorm
  refine ⟨σ, hσ, (v : Vec 2 → ℝ), Lp.memLp v, ?_, fun g hg => ?_⟩
  · have hv : ‖v‖ ≤ F := CoupledEnergy.Variational.norm_le_of_tendsto_inner (u := fun n => u (σ n))
      (fun n => hnorm _) hlim
    have hF0 : 0 ≤ F := (norm_nonneg _).trans hv
    rw [l2NormSq_eq_inner, real_inner_self_eq_norm_sq]
    rw [Real.sqrt_sq (norm_nonneg _)]
    exact hv
  · have h := hlim (hg.toLp g)
    have e1 : ∀ n, inner ℝ (u (σ n)) (hg.toLp g) = ∫ x in unitCube, f (σ n) x * g x := by
      intro n
      rw [real_inner_comm, ← integral_mul_lp_eq_inner (u (σ n)) hg]
      refine integral_congr_ae ?_
      filter_upwards [(hf (σ n)).1.coeFn_toLp] with x hx
      simp only [u, hx]
    have e2 : inner ℝ v (hg.toLp g) = ∫ x in unitCube, (v : Vec 2 → ℝ) x * g x := by
      rw [real_inner_comm, ← integral_mul_lp_eq_inner v hg]
    simp_rw [e1] at h
    rwa [e2] at h

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance Filter Topology
namespace AVRegularity.Applications

/-! # Integration by parts on `𝕋²` for `H¹` functions

For `u ∈ H¹(𝕋²)` with gradient `Du` and a smooth periodic `ψ`:

* `periodic_grad_ibp`: `∫ Duᵢ ψ = -∫ u ∂ᵢψ`;
* `periodic_drift_ibp`: for a bounded continuous periodic divergence-free `b`,
  `∫ (b·Du) ψ = -∫ u (b·∇ψ)`.

Both follow from the corresponding identities for the smooth Fourier projections of `u`
(`torus_exists_smooth_approx`) by weak convergence. -/

/-- A divergence-free periodic drift annihilates the gradient of every smooth periodic function. -/
theorem drift_periodic_test_zero {b : Vec 2 → Vec 2} (hbc : Continuous b)
    (hbB : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (hbp : IsZ2Periodic b)
    (hdiv : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b x) (spaceGrad φ x) = 0)
    {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgp : IsZ2Periodic g) :
    ∫ x in unitCube, vecDot (b x) (spaceGrad g x) = 0 := by
  have h := AVenhance.Infra.Parabolic.WeakUniqueness.isDivFree_integral_periodic_smooth_test
    hbc.aestronglyMeasurable hbB hbp hdiv hg hgp
  rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube] at h
  exact h

theorem spaceGrad_mul_apply {P ψ : Vec 2 → ℝ} (hP : ContDiff ℝ 1 P) (hψ : ContDiff ℝ 1 ψ)
    (x : Vec 2) (i : Fin 2) :
    spaceGrad (fun y => P y * ψ y) x i = P x * spaceGrad ψ x i + ψ x * spaceGrad P x i := by
  have h1 : DifferentiableAt ℝ P x := hP.differentiable (by simp) x
  have h2 : DifferentiableAt ℝ ψ x := hψ.differentiable (by simp) x
  have h3 : fderiv ℝ (fun y => P y * ψ y) x = P x • fderiv ℝ ψ x + ψ x • fderiv ℝ P x :=
    fderiv_mul h1 h2
  simp only [spaceGrad, h3, add_apply, smul_apply,
    smul_eq_mul]

/-- Partial derivatives of `C¹` periodic functions integrate to zero over the cell. -/
theorem integral_partial_periodic {F : Vec 2 → ℝ} (hF : ContDiff ℝ 1 F) (hp : IsZ2Periodic F)
    (i : Fin 2) : ∫ x in unitCube, spaceGrad F x i = 0 := by
  have hc : ContDiff ℝ 1 (fun _ : Vec 2 => (0 : ℝ)) := contDiff_const
  have hp0 : IsZ2Periodic (fun _ : Vec 2 => (0 : ℝ)) := fun _ _ => rfl
  fin_cases i
  · have := integral_div_periodic hF hc hp hp0
    simpa [spaceGrad] using this
  · have := integral_div_periodic hc hF hp0 hp
    simpa [spaceGrad] using this

/-- The gradient of an `H¹(𝕋²)` function integrates by parts against smooth periodic tests. -/
theorem periodic_grad_ibp {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : IsPeriodicH1With u Du)
    {ρ : Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρp : IsZ2Periodic ρ) (i : Fin 2) :
    ∫ x in unitCube, Du x i * ρ x = -∫ x in unitCube, u x * spaceGrad ρ x i := by
  obtain ⟨P, hPs, hPp, hP⟩ := torus_exists_smooth_approx hu
  have hP1 : ∀ N, ContDiff ℝ 1 (P N) := fun N => contDiff_one_of_top (hPs N)
  have hρ1 : ContDiff ℝ 1 ρ := contDiff_one_of_top hρ
  have hρg : Continuous fun x => spaceGrad ρ x i := continuous_spaceGrad_apply hρ1 i
  have hPg : ∀ N, Continuous fun x => spaceGrad (P N) x i := fun N =>
    continuous_spaceGrad_apply (hP1 N) i
  have key : ∀ N, (∫ x in unitCube, spaceGrad (P N) x i * ρ x) =
      -∫ x in unitCube, P N x * spaceGrad ρ x i := by
    intro N
    have hF : ContDiff ℝ 1 (fun y => P N y * ρ y) := (hP1 N).mul hρ1
    have hFp : IsZ2Periodic (fun y => P N y * ρ y) := fun n x => by
      simp [hPp N n x, hρp n x]
    have hz := integral_partial_periodic hF hFp i
    have i1 : Integrable (fun x => ρ x * spaceGrad (P N) x i) (volume.restrict unitCube) :=
      integrable_mul_memL2 (memL2_continuous hρ1.continuous) (memL2_continuous (hPg N))
    have i2 : Integrable (fun x => P N x * spaceGrad ρ x i) (volume.restrict unitCube) :=
      integrable_mul_memL2 (memL2_continuous (hP1 N).continuous) (memL2_continuous hρg)
    have e : ∀ x, spaceGrad (fun y => P N y * ρ y) x i =
        ρ x * spaceGrad (P N) x i + P N x * spaceGrad ρ x i := fun x => by
      rw [spaceGrad_mul_apply (hP1 N) hρ1]; ring
    simp_rw [e] at hz
    rw [integral_add i1 i2] at hz
    have : ∫ x in unitCube, spaceGrad (P N) x i * ρ x =
        ∫ x in unitCube, ρ x * spaceGrad (P N) x i :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    rw [this]; linarith
  have h1 := (hP _ (memL2_continuous hρ1.continuous)).2 i
  have h2 := (hP _ (memL2_continuous hρg)).1
  have h2' : Tendsto (fun N => -∫ x in unitCube, P N x * spaceGrad ρ x i) atTop
      (𝓝 (-∫ x in unitCube, u x * spaceGrad ρ x i)) := h2.neg
  exact tendsto_nhds_unique (h1.congr key) h2'

/-- The transport term of an `H¹(𝕋²)` function integrates by parts against smooth periodic tests,
for a bounded continuous periodic divergence-free drift. -/
theorem periodic_drift_ibp {b : Vec 2 → Vec 2} (hbc : Continuous b)
    (hbB : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (hbp : IsZ2Periodic b)
    (hdiv : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b x) (spaceGrad φ x) = 0)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : IsPeriodicH1With u Du)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) :
    ∫ x in unitCube, vecDot (b x) (Du x) * ψ x =
      -∫ x in unitCube, u x * vecDot (b x) (spaceGrad ψ x) := by
  obtain ⟨P, hPs, hPp, hP⟩ := torus_exists_smooth_approx hu
  have hP1 : ∀ N, ContDiff ℝ 1 (P N) := fun N => contDiff_one_of_top (hPs N)
  have hψ1 : ContDiff ℝ 1 ψ := contDiff_one_of_top hψ
  have hbi : ∀ i : Fin 2, Continuous fun x => b x i := fun i => (continuous_apply i).comp hbc
  have hψg : ∀ i, Continuous fun x => spaceGrad ψ x i := continuous_spaceGrad_apply hψ1
  have hPg : ∀ N i, Continuous fun x => spaceGrad (P N) x i := fun N =>
    continuous_spaceGrad_apply (hP1 N)
  have hcoef : ∀ i : Fin 2, Continuous fun x => b x i * ψ x := fun i => (hbi i).mul hψ1.continuous
  have hdotc : Continuous fun x => vecDot (b x) (spaceGrad ψ x) := by
    simp only [vecDot, Fin.sum_univ_two]
    exact ((hbi 0).mul (hψg 0)).add ((hbi 1).mul (hψg 1))
  have key : ∀ N, (∫ x in unitCube, vecDot (b x) (spaceGrad (P N) x) * ψ x) =
      -∫ x in unitCube, P N x * vecDot (b x) (spaceGrad ψ x) := by
    intro N
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun y => P N y * ψ y) := (hPs N).mul hψ
    have hFp : IsZ2Periodic (fun y => P N y * ψ y) := fun n x => by
      simp [hPp N n x, hψp n x]
    have hz := drift_periodic_test_zero hbc hbB hbp hdiv hF hFp
    have e : ∀ x, vecDot (b x) (spaceGrad (fun y => P N y * ψ y) x) =
        vecDot (b x) (spaceGrad (P N) x) * ψ x + P N x * vecDot (b x) (spaceGrad ψ x) := by
      intro x
      simp only [vecDot, Fin.sum_univ_two, spaceGrad_mul_apply (hP1 N) hψ1]
      ring
    have hc1 : Continuous fun x => vecDot (b x) (spaceGrad (P N) x) * ψ x := by
      simp only [vecDot, Fin.sum_univ_two]
      exact (((hbi 0).mul (hPg N 0)).add ((hbi 1).mul (hPg N 1))).mul hψ1.continuous
    have i1 : Integrable (fun x => vecDot (b x) (spaceGrad (P N) x) * ψ x)
        (volume.restrict unitCube) := integrableOn_cube_of_continuous hc1
    have i2 : Integrable (fun x => P N x * vecDot (b x) (spaceGrad ψ x))
        (volume.restrict unitCube) :=
      integrableOn_cube_of_continuous ((hP1 N).continuous.mul hdotc)
    simp_rw [e] at hz
    rw [integral_add i1 i2] at hz
    linarith
  -- the limit of the left side
  have hL : Tendsto (fun N => ∫ x in unitCube, vecDot (b x) (spaceGrad (P N) x) * ψ x) atTop
      (𝓝 (∫ x in unitCube, vecDot (b x) (Du x) * ψ x)) := by
    have hsum : ∀ (G : Vec 2 → Vec 2), (∀ i, MemL2On unitCube fun x => G x i) →
        ∫ x in unitCube, vecDot (b x) (G x) * ψ x =
          ∑ i : Fin 2, ∫ x in unitCube, G x i * (b x i * ψ x) := by
      intro G hG
      rw [← integral_finsetSum _ fun i _ => integrable_mul_memL2 (hG i)
        (memL2_continuous (hcoef i))]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [vecDot, Fin.sum_univ_two]
      ring
    have e1 : (fun N => ∫ x in unitCube, vecDot (b x) (spaceGrad (P N) x) * ψ x) =
        fun N => ∑ i : Fin 2, ∫ x in unitCube, spaceGrad (P N) x i * (b x i * ψ x) :=
      funext fun N => hsum (spaceGrad (P N)) fun i => memL2_continuous (hPg N i)
    rw [e1, hsum Du hu.2.2.2.1]
    exact tendsto_finsetSum _ fun i _ => (hP _ (memL2_continuous (hcoef i))).2 i
  have hR := (hP _ (memL2_continuous hdotc)).1
  have hR' : Tendsto (fun N => -∫ x in unitCube, P N x * vecDot (b x) (spaceGrad ψ x)) atTop
      (𝓝 (-∫ x in unitCube, u x * vecDot (b x) (spaceGrad ψ x))) := hR.neg
  exact tendsto_nhds_unique (hL.congr key) hR'

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity.Applications

/-! # `L²(𝕋²)` tools: Cauchy–Schwarz and density of smooth periodic functions -/

theorem volume_unitCube : volume (unitCube : Set (Vec 2)) = 1 := by
  rw [unitCube, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

theorem norm_toLp_sq {u : Vec 2 → ℝ} (hu : MemL2On unitCube u) :
    ‖hu.toLp u‖ ^ 2 = l2NormSq u := by
  rw [← real_inner_self_eq_norm_sq, ← l2NormSq_eq_inner]
  unfold l2NormSq
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  simp only [hx]

/-- Cauchy–Schwarz on the cube. -/
theorem abs_integral_mul_le_norms {u v : Vec 2 → ℝ} (hu : MemL2On unitCube u)
    (hv : MemL2On unitCube v) :
    |∫ x in unitCube, u x * v x| ≤ Real.sqrt (l2NormSq u) * Real.sqrt (l2NormSq v) := by
  have h := integral_mul_lp_eq_inner (μ := volume.restrict unitCube) (hu.toLp u) hv
  have e : ∫ x in unitCube, u x * v x = inner ℝ (hv.toLp v) (hu.toLp u) := by
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp] with x hx
    simp only [hx]
  rw [e]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [mul_comm, ← Real.sqrt_sq (norm_nonneg (hu.toLp u)), ← Real.sqrt_sq (norm_nonneg (hv.toLp v))]
  rw [norm_toLp_sq hu, norm_toLp_sq hv]

/-- Crude `L¹`–`L^∞` bound with an `L²` bound on the first factor. -/
theorem abs_integral_mul_le_l2 {g w : Vec 2 → ℝ} {W F : ℝ} (hg : MemL2On unitCube g)
    (hw : ∀ x, |w x| ≤ W) (hl2 : l2NormSq g ≤ F ^ 2) :
    |∫ x in unitCube, g x * w x| ≤ W * ((1 + F ^ 2) / 2) := by
  have hW : 0 ≤ W := (abs_nonneg _).trans (hw 0)
  have hgi : Integrable g (volume.restrict unitCube) := hg.integrable (by norm_num)
  have hg2 : Integrable (fun x => g x ^ 2) (volume.restrict unitCube) := hg.integrable_sq
  have hbd : ∀ x, |g x * w x| ≤ W * ((1 + g x ^ 2) / 2) := fun x => by
    rw [abs_mul]
    have h1 : |g x| ≤ (1 + g x ^ 2) / 2 := by
      have := sq_nonneg (|g x| - 1)
      have h2 : |g x| ^ 2 = g x ^ 2 := sq_abs _
      nlinarith
    calc |g x| * |w x| ≤ |g x| * W := mul_le_mul_of_nonneg_left (hw x) (abs_nonneg _)
      _ ≤ (1 + g x ^ 2) / 2 * W := mul_le_mul_of_nonneg_right h1 hW
      _ = W * ((1 + g x ^ 2) / 2) := by ring
  have hint : Integrable (fun x => W * ((1 + g x ^ 2) / 2)) (volume.restrict unitCube) :=
    ((integrable_const (1 : ℝ)).add hg2).div_const 2 |>.const_mul W
  have hm : (volume.restrict unitCube).real Set.univ = 1 := by
    simp [Measure.real, volume_unitCube]
  calc |∫ x in unitCube, g x * w x| ≤ ∫ x in unitCube, |g x * w x| := abs_integral_le_integral_abs
    _ ≤ ∫ x in unitCube, W * ((1 + g x ^ 2) / 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hint
          (Eventually.of_forall hbd)
    _ = W * ((1 + l2NormSq g) / 2) := by
        rw [integral_const_mul, integral_div, integral_add (integrable_const 1) hg2]
        simp [hm, l2NormSq]
    _ ≤ W * ((1 + F ^ 2) / 2) := by gcongr

open AVenhance.Infra.Parabolic.WeakUniqueness AVenhance.Infra.Parabolic.FourierGalerkin
  AVenhance.Infra.Torus AVenhance.Infra.Classical in
/-- Smooth periodic functions are dense in `L²(cube)`. -/
theorem exists_smooth_L2_approx {g : Vec 2 → ℝ} (hg : MemL2On unitCube g) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ IsZ2Periodic ψ ∧
      ∫ x in unitCube, (g x - ψ x) ^ 2 < ε := by
  let upath : ℝ → Vec 2 → ℝ := fun _ => g
  let P (N : ℕ) : Vec 2 → ℝ := weakFourierModeProjection N upath 0
  have hPCont (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (P N) := by
    have h := realFourierModeAmbientExpansion_contDiff N
      (weakFourierCoefficientPath N upath 0)
    have h' : ContDiff ℝ (⊤ : ℕ∞)
        (realFourierModeAmbientExpansion N (weakFourierCoefficientPath N upath 0)) :=
      h.of_le (m := (⊤ : ℕ∞)) (by simp)
    simpa [P, weakFourierModeProjection] using h'
  have hPPer (N : ℕ) : IsZ2Periodic (P N) := by
    change IsZ2Periodic
      (realFourierModeAmbientExpansion N (weakFourierCoefficientPath N upath 0))
    exact realFourierModeAmbientExpansion_periodic N _
  have hPmem (N : ℕ) : MemL2On unitCube (P N) :=
    weak_continuous_memL2On (hPCont N).continuous
  have hprojVal : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hPmem N)).toLp
        (periodicToTorus (P N))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp hg).toLp (periodicToTorus g))) := by
    have h := weakFourierProjectionL2_tendsto (u := upath) (t := 0) hg
    simpa [P, weakFourierProjectionL2_eq_expansionTransfer] using h
  set T := (weakProjection_realCellToTorus_memLp hg).toLp (periodicToTorus g) with hT
  have hn : Tendsto (fun N => ‖(weakProjection_realCellToTorus_memLp (hPmem N)).toLp
      (periodicToTorus (P N)) - T‖ ^ 2) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hprojVal).pow 2
    simpa using this
  obtain ⟨N, hN⟩ := (hn.eventually (gt_mem_nhds hε)).exists
  refine ⟨P N, hPCont N, hPPer N, ?_⟩
  refine lt_of_le_of_lt (le_of_eq ?_) hN
  have h1 := DivergenceFreeEnergy.divFree_torusInner_cell (hPmem N) (hPmem N)
  have h2 := DivergenceFreeEnergy.divFree_torusInner_cell (hPmem N) hg
  have h3 := DivergenceFreeEnergy.divFree_torusInner_cell hg hg
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    h1, h2, h3]
  simp only [integral_unitCell_eq_unitCube]
  have i1 : Integrable (fun x => P N x * P N x) (volume.restrict unitCube) :=
    integrable_mul_memL2 (hPmem N) (hPmem N)
  have i2 : Integrable (fun x => P N x * g x) (volume.restrict unitCube) :=
    integrable_mul_memL2 (hPmem N) hg
  have i3 : Integrable (fun x => g x * g x) (volume.restrict unitCube) :=
    integrable_mul_memL2 hg hg
  have e : ∀ x, (g x - P N x) ^ 2 = g x * g x - 2 * (P N x * g x) + P N x * P N x := fun x => by
    ring
  simp_rw [e]
  rw [integral_add (f := fun x => g x * g x - 2 * (P N x * g x)) (g := fun x => P N x * P N x)
      (i3.sub (i2.const_mul 2)) i1,
    integral_sub (f := fun x => g x * g x) (g := fun x => 2 * (P N x * g x))
      i3 (i2.const_mul 2), integral_const_mul]
  ring

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance Filter Topology
namespace AVRegularity.Applications

/-! # The slice identity for the weak form

For a time slice `u ∈ H¹(𝕋²)` with gradient `Du`, a periodic divergence-free drift `b`, a smooth
periodic test `ψ` and a continuous periodic function `c` (the time derivative of the test),
`∫ [-(u c) + (b·Du) ψ + κ Du·∇ψ] = -∫ u (c + b·∇ψ + κ Δψ)`. -/

/-- The spatial Laplacian `Δψ = Σⱼ ∂ⱼ∂ⱼψ`. -/
def lapl (ψ : Vec 2 → ℝ) (x : Vec 2) : ℝ :=
  ∑ j : Fin 2, spaceGrad (fun y => spaceGrad ψ y j) x j

theorem contDiff_spaceGrad_apply {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => spaceGrad ψ y j) :=
  contDiff_fderiv_apply_of_smooth hψ (basisVec j)

theorem continuous_lapl {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : Continuous (lapl ψ) := by
  unfold lapl
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_spaceGrad_apply (contDiff_one_of_top (contDiff_spaceGrad_apply hψ j)) j

theorem lapl_periodic {ψ : Vec 2 → ℝ} (hp : IsZ2Periodic ψ) : IsZ2Periodic (lapl ψ) := by
  intro n x
  unfold lapl
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : IsZ2Periodic (fun y => spaceGrad ψ y j) := fun m y => by
    simp [spaceGrad_periodic hp m y]
  simp [spaceGrad_periodic hj n x]

theorem slice_ibp {b : Vec 2 → Vec 2} (hbc : Continuous b)
    (hbB : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (hbp : IsZ2Periodic b)
    (hdiv : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b x) (spaceGrad φ x) = 0)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2} (hu : IsPeriodicH1With u Du)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ)
    {c : Vec 2 → ℝ} (hc : Continuous c) (κ : ℝ) :
    ∫ x in unitCube, (-(u x * c x) + vecDot (b x) (Du x) * ψ x +
        κ * vecDot (Du x) (spaceGrad ψ x)) =
      -∫ x in unitCube, u x * (c x + vecDot (b x) (spaceGrad ψ x) + κ * lapl ψ x) := by
  have hψ1 : ContDiff ℝ 1 ψ := contDiff_one_of_top hψ
  have huL : MemL2On unitCube u := hu.2.2.1
  have hDL : ∀ i, MemL2On unitCube fun x => Du x i := hu.2.2.2.1
  have hbi : ∀ i : Fin 2, Continuous fun x => b x i := fun i => (continuous_apply i).comp hbc
  have hψg : ∀ i, Continuous fun x => spaceGrad ψ x i := continuous_spaceGrad_apply hψ1
  have hdotc : Continuous fun x => vecDot (b x) (spaceGrad ψ x) := by
    simp only [vecDot, Fin.sum_univ_two]
    exact ((hbi 0).mul (hψg 0)).add ((hbi 1).mul (hψg 1))
  have hlapc : Continuous (lapl ψ) := continuous_lapl hψ
  -- integrability of the pieces
  have iuc : Integrable (fun x => u x * c x) (volume.restrict unitCube) :=
    integrable_mul_memL2 huL (memL2_continuous hc)
  have ibD : Integrable (fun x => vecDot (b x) (Du x) * ψ x) (volume.restrict unitCube) := by
    have : ∀ x, vecDot (b x) (Du x) * ψ x = Du x 0 * (b x 0 * ψ x) + Du x 1 * (b x 1 * ψ x) := by
      intro x; simp only [vecDot, Fin.sum_univ_two]; ring
    simp_rw [this]
    exact (integrable_mul_memL2 (hDL 0) (memL2_continuous ((hbi 0).mul hψ1.continuous))).add
      (integrable_mul_memL2 (hDL 1) (memL2_continuous ((hbi 1).mul hψ1.continuous)))
  have iDg : Integrable (fun x => vecDot (Du x) (spaceGrad ψ x)) (volume.restrict unitCube) := by
    have : ∀ x, vecDot (Du x) (spaceGrad ψ x) =
        Du x 0 * spaceGrad ψ x 0 + Du x 1 * spaceGrad ψ x 1 := by
      intro x; simp only [vecDot, Fin.sum_univ_two]
    simp_rw [this]
    exact (integrable_mul_memL2 (hDL 0) (memL2_continuous (hψg 0))).add
      (integrable_mul_memL2 (hDL 1) (memL2_continuous (hψg 1)))
  have iub : Integrable (fun x => u x * vecDot (b x) (spaceGrad ψ x)) (volume.restrict unitCube) :=
    integrable_mul_memL2 huL (memL2_continuous hdotc)
  have iul : Integrable (fun x => u x * lapl ψ x) (volume.restrict unitCube) :=
    integrable_mul_memL2 huL (memL2_continuous hlapc)
  -- the drift term
  have h1 := periodic_drift_ibp hbc hbB hbp hdiv hu hψ hψp
  -- the diffusion term
  have h2 : ∫ x in unitCube, vecDot (Du x) (spaceGrad ψ x) =
      -∫ x in unitCube, u x * lapl ψ x := by
    have hj : ∀ j : Fin 2, ∫ x in unitCube, Du x j * spaceGrad ψ x j =
        -∫ x in unitCube, u x * spaceGrad (fun y => spaceGrad ψ y j) x j := fun j =>
      periodic_grad_ibp hu (contDiff_spaceGrad_apply hψ j) (fun n x => by
        simp [spaceGrad_periodic hψp n x]) j
    have e1 : ∫ x in unitCube, vecDot (Du x) (spaceGrad ψ x) =
        ∑ j : Fin 2, ∫ x in unitCube, Du x j * spaceGrad ψ x j := by
      rw [← integral_finsetSum _ fun j _ => integrable_mul_memL2 (hDL j)
        (memL2_continuous (hψg j))]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [vecDot])
    have e2 : ∫ x in unitCube, u x * lapl ψ x =
        ∑ j : Fin 2, ∫ x in unitCube, u x * spaceGrad (fun y => spaceGrad ψ y j) x j := by
      rw [← integral_finsetSum _ fun j _ => integrable_mul_memL2 huL
        (memL2_continuous (continuous_spaceGrad_apply
          (contDiff_one_of_top (contDiff_spaceGrad_apply hψ j)) j))]
      exact integral_congr_ae (Eventually.of_forall fun x => by
        simp only [lapl, Fin.sum_univ_two]; ring)
    rw [e1, e2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hj j
  have ia : Integrable (fun x => -(u x * c x) + vecDot (b x) (Du x) * ψ x)
      (volume.restrict unitCube) := iuc.neg.add ibD
  have ik : Integrable (fun x => κ * vecDot (Du x) (spaceGrad ψ x)) (volume.restrict unitCube) :=
    iDg.const_mul κ
  rw [integral_add (f := fun x => -(u x * c x) + vecDot (b x) (Du x) * ψ x)
    (g := fun x => κ * vecDot (Du x) (spaceGrad ψ x)) ia ik,
    integral_add (f := fun x => -(u x * c x)) (g := fun x => vecDot (b x) (Du x) * ψ x)
      iuc.neg ibD, integral_neg, integral_const_mul, h1, h2]
  have e3 : ∀ x, u x * (c x + vecDot (b x) (spaceGrad ψ x) + κ * lapl ψ x) =
      u x * c x + u x * vecDot (b x) (spaceGrad ψ x) + κ * (u x * lapl ψ x) := fun x => by ring
  simp_rw [e3]
  rw [integral_add (f := fun x => u x * c x + u x * vecDot (b x) (spaceGrad ψ x))
    (g := fun x => κ * (u x * lapl ψ x)) (iuc.add iub) (iul.const_mul κ),
    integral_add (f := fun x => u x * c x) (g := fun x => u x * vecDot (b x) (spaceGrad ψ x))
      iuc iub, integral_const_mul]
  ring

/-! # The weak form in divergence form (iterated)

For a weak solution on `[t₁, t₂]` and a window test function `φ`,
`∫_{t₁}^{t₂} ⟨θ(t), ∂ₜφ + b·∇φ + κΔφ⟩ dt = -⟨f, φ(t₁)⟩`
(the weak form after moving the spatial derivatives of `θ` onto `φ`). -/

/-- A continuous bounded periodic divergence-free drift. -/
structure IsContDrift (b : ℝ → Vec 2 → Vec 2) : Prop where
  periodic : ∀ t, IsZ2Periodic (b t)
  continuous : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2)
  bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ t x, ‖b t x‖ ≤ B
  divFree : ∀ (t : ℝ) (φ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, vecDot (b t x) (spaceGrad φ x) = 0

theorem isContDrift_of_holder {α : ℝ} (hα : 0 < α) {b : ℝ → Vec 2 → Vec 2}
    (hb : IsHolderDivFreeVelocity α b) : IsContDrift b := by
  have hc := IsHolderDivFreeVelocity.continuous hα hb
  obtain ⟨hper, -, ⟨B, hB⟩, -, hdiv⟩ := hb
  exact ⟨hper, hc, ⟨max B 0, le_max_right _ _, fun t x => (hB t x).trans (le_max_left _ _)⟩,
    hdiv⟩

theorem IsContDrift.slice_continuous {b : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b) (t : ℝ) :
    Continuous (b t) :=
  hb.continuous.comp (continuous_const.prodMk continuous_id)

/-- The operator `∂ₜφ + b·∇φ + κΔφ` applied to a window test function. -/
def weakOp (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (φ : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  deriv (fun s => φ s x) t + vecDot (b t x) (spaceGrad (φ t) x) + κ * lapl (φ t) x

/-- Regularity and window bounds for a window test function and its derivatives. -/
theorem window_test_regular {t₂ : ℝ} {φ : ℝ → Vec 2 → ℝ} (hφ : IsWindowTestFunction t₂ φ)
    (t₁ : ℝ) :
    Continuous (fun p : ℝ × Vec 2 => φ p.1 p.2) ∧
    Continuous (fun p : ℝ × Vec 2 => deriv (fun s => φ s p.2) p.1) ∧
    (∀ j : Fin 2, Continuous (fun p : ℝ × Vec 2 => spaceGrad (φ p.1) p.2 j)) ∧
    ∃ C : ℝ, ∀ t ∈ Set.Icc t₁ t₂, ∀ x, |φ t x| ≤ C ∧ |deriv (fun s => φ s x) t| ≤ C ∧
      ∀ j : Fin 2, |spaceGrad (φ t) x j| ≤ C := by
  obtain ⟨hφs, hφp, -⟩ := hφ
  set ρ : ℝ × Vec 2 → ℝ := fun p => φ p.1 p.2 with hρ
  have hρ1 : ContDiff ℝ 1 ρ := hφs.of_le (by exact_mod_cast le_top)
  have hc0 : Continuous ρ := hφs.continuous
  have hdt : ∀ p : ℝ × Vec 2, deriv (fun s => φ s p.2) p.1 = fderiv ℝ ρ p (1, 0) := fun p =>
    deriv_slc_eq hφs p.1 p.2
  have hdx : ∀ (p : ℝ × Vec 2) (j : Fin 2),
      spaceGrad (φ p.1) p.2 j = fderiv ℝ ρ p (0, basisVec j) := fun p j =>
    spaceGrad_slc_eq (ρ := ρ) hφs p.1 p.2 j
  have hc1 : Continuous (fun p : ℝ × Vec 2 => deriv (fun s => φ s p.2) p.1) := by
    simp_rw [hdt]
    exact (hρ1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hc2 : ∀ j : Fin 2, Continuous (fun p : ℝ × Vec 2 => spaceGrad (φ p.1) p.2 j) := by
    intro j
    simp_rw [hdx]
    exact (hρ1.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨hc0, hc1, hc2, ?_⟩
  obtain ⟨C0, h0⟩ := bounded_periodic_window (F := ρ) hc0 (fun t n x => hφp t n x) t₁ t₂
  obtain ⟨C1, h1⟩ := bounded_periodic_window
    (F := fun p : ℝ × Vec 2 => deriv (fun s => φ s p.2) p.1) hc1 (fun t n x => by
      have : (fun s => φ s (x + latticeShift n)) = fun s => φ s x := funext fun s => hφp s n x
      simp only [this]) t₁ t₂
  obtain ⟨C2, h2⟩ := bounded_periodic_window
    (F := fun p : ℝ × Vec 2 => spaceGrad (φ p.1) p.2 0) (hc2 0) (fun t n x => by
      simp only [spaceGrad_periodic (hφp t) n x]) t₁ t₂
  obtain ⟨C3, h3⟩ := bounded_periodic_window
    (F := fun p : ℝ × Vec 2 => spaceGrad (φ p.1) p.2 1) (hc2 1) (fun t n x => by
      simp only [spaceGrad_periodic (hφp t) n x]) t₁ t₂
  refine ⟨max (max C0 C1) (max C2 C3), fun t ht x => ⟨?_, ?_, fun j => ?_⟩⟩
  · exact (h0 t ht x).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h1 t ht x).trans ((le_max_right _ _).trans (le_max_left _ _))
  · fin_cases j
    · exact (h2 t ht x).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h3 t ht x).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- **The weak form in divergence form**: iterated version. -/
theorem window_weak_iterated {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b)
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsWindowTestFunction t₂ φ) :
    ∫ t in Set.Ioo t₁ t₂, ∫ x in unitCube, θ t x * weakOp b κ φ t x =
      -∫ x in unitCube, f x * φ t₁ x := by
  obtain ⟨hslice, -, hL2, hDL2, hH1, hint, -, hweak⟩ := h
  have hw := hweak φ hφ
  obtain ⟨hc0, hc1, hc2, C, hC⟩ := window_test_regular hφ t₁
  obtain ⟨hφs, hφp, -⟩ := hφ
  obtain ⟨B, hB0, hB⟩ := hb.bounded
  set S : Set (ℝ × Vec 2) := Set.Ioo t₁ t₂ ×ˢ unitCube with hS
  have hSm : MeasurableSet S := measurableSet_Ioo.prod measurableSet_unitCube'
  have hθint : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2) (volume.restrict S) :=
    memLp_two_integrable_window hL2
  have hDint : ∀ i : Fin 2, Integrable (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) (volume.restrict S) :=
    fun i => memLp_two_integrable_window (hDL2 i)
  have hmem : ∀ᵐ p ∂(volume.restrict S), p.1 ∈ Set.Icc t₁ t₂ := by
    filter_upwards [ae_restrict_mem hSm] with p hp using ⟨hp.1.1.le, hp.1.2.le⟩
  -- integrability of the integrand
  set F : ℝ × Vec 2 → ℝ := fun p =>
    -(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1 + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
      + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2) with hF
  have hFint : Integrable F (volume.restrict S) := by
    have i1 : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * deriv (fun s => φ s p.2) p.1)
        (volume.restrict S) :=
      hθint.mul_bdd hc1.aestronglyMeasurable (c := C) (by
        filter_upwards [hmem] with p hp
        simpa using (hC p.1 hp p.2).2.1)
    have i2 : Integrable (fun p : ℝ × Vec 2 => vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2)
        (volume.restrict S) :=
      hint.mul_bdd hc0.aestronglyMeasurable (c := C) (by
        filter_upwards [hmem] with p hp
        simpa using (hC p.1 hp p.2).1)
    have i3 : ∀ j : Fin 2, Integrable
        (fun p : ℝ × Vec 2 => Dθ p.1 p.2 j * spaceGrad (φ p.1) p.2 j) (volume.restrict S) :=
      fun j => (hDint j).mul_bdd (hc2 j).aestronglyMeasurable (c := C) (by
        filter_upwards [hmem] with p hp
        simpa using (hC p.1 hp p.2).2.2 j)
    have i4 : Integrable (fun p : ℝ × Vec 2 =>
        κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2)) (volume.restrict S) := by
      have : (fun p : ℝ × Vec 2 => κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2)) =
          fun p => κ * (Dθ p.1 p.2 0 * spaceGrad (φ p.1) p.2 0 +
            Dθ p.1 p.2 1 * spaceGrad (φ p.1) p.2 1) := by
        funext p; simp only [vecDot, Fin.sum_univ_two]
      rw [this]
      exact ((i3 0).add (i3 1)).const_mul κ
    have : F = fun p => -(θ p.1 p.2 * deriv (fun s => φ s p.2) p.1) +
        vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2 +
        κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2) := by
      funext p; simp only [hF, neg_mul]
    rw [this]
    exact (i1.neg.add i2).add i4
  -- iterate
  have hFint' : Integrable F ((volume.restrict (Set.Ioo t₁ t₂)).prod (volume.restrict unitCube)) := by
    rw [← volume_restrict_prod_eq]; exact hFint
  have hit : ∫ p in S, F p = ∫ t in Set.Ioo t₁ t₂, ∫ x in unitCube, F (t, x) := by
    rw [hS, volume_restrict_prod_eq, integral_prod _ hFint']
  have hw' : ∫ t in Set.Ioo t₁ t₂, ∫ x in unitCube, F (t, x) = ∫ x in unitCube, f x * φ t₁ x := by
    rw [← hit]; exact hw
  -- slicewise integration by parts
  have hslicewise : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)),
      ∫ x in unitCube, F (t, x) = -∫ x in unitCube, θ t x * weakOp b κ φ t x := by
    filter_upwards [hH1] with t ht
    have hψ : ContDiff ℝ (⊤ : ℕ∞) (φ t) := hφs.comp (contDiff_const.prodMk contDiff_id)
    have hs := slice_ibp (hb.slice_continuous t) ⟨B, hB0, hB t⟩ (hb.periodic t)
      (hb.divFree t) ht hψ (hφp t) (c := fun x => deriv (fun s => φ s x) t) ?_ κ
    · unfold weakOp
      rw [← hs]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hF, neg_mul]
    · have := hc1.comp (continuous_const.prodMk continuous_id : Continuous fun x : Vec 2 => (t, x))
      exact this
  rw [integral_congr_ae hslicewise, integral_neg] at hw'
  linarith

theorem lapl_eq_stSpaceLap {φ : ℝ → Vec 2 → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (t : ℝ) (x : Vec 2) :
    lapl (φ t) x = ∑ j : Fin 2, fderiv ℝ (fun q : ℝ × Vec 2 =>
      fderiv ℝ (fun p : ℝ × Vec 2 => φ p.1 p.2) q (0, basisVec j)) (t, x) (0, basisVec j) := by
  unfold lapl
  refine Finset.sum_congr rfl fun j _ => ?_
  set ρ : ℝ × Vec 2 → ℝ := fun p => φ p.1 p.2 with hρ
  have h1 : (fun y => spaceGrad (φ t) y j) = fun y => fderiv ℝ ρ (t, y) (0, basisVec j) :=
    funext fun y => spaceGrad_slc_eq (ρ := ρ) hφs t y j
  rw [h1]
  exact spaceGrad_slc_eq (ρ := fun q => fderiv ℝ ρ q (0, basisVec j))
    (contDiff_fderiv_apply_of_smooth hφs _) t x j

theorem lapl_window_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφs : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) :
    Continuous (fun p : ℝ × Vec 2 => lapl (φ p.1) p.2) := by
  have : (fun p : ℝ × Vec 2 => lapl (φ p.1) p.2) = fun p => ∑ j : Fin 2,
      fderiv ℝ (fun q : ℝ × Vec 2 => fderiv ℝ (fun p : ℝ × Vec 2 => φ p.1 p.2) q (0, basisVec j))
        p (0, basisVec j) :=
    funext fun p => lapl_eq_stSpaceLap hφs p.1 p.2
  rw [this]
  refine continuous_finsetSum _ fun j _ => ?_
  exact (contDiff_fderiv_apply_of_smooth
    (contDiff_fderiv_apply_of_smooth hφs _) _).continuous

/-- Continuity and window bounds for `weakOp`. -/
theorem weakOp_regular {b : ℝ → Vec 2 → Vec 2} (hb : IsContDrift b) {t₂ : ℝ}
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsWindowTestFunction t₂ φ) (t₁ : ℝ) :
    (∀ κ : ℝ, Continuous fun p : ℝ × Vec 2 => weakOp b κ φ p.1 p.2) ∧
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ κ : ℝ, ∀ t ∈ Set.Icc t₁ t₂, ∀ x,
      |weakOp b κ φ t x| ≤ C₀ + |κ| * C₁ := by
  have hreg := window_test_regular hφ t₁
  obtain ⟨hc0, hc1, hc2, C, hC⟩ := hreg
  obtain ⟨hφs, hφp, -⟩ := hφ
  obtain ⟨B, hB0, hB⟩ := hb.bounded
  have hlc := lapl_window_continuous hφs
  have hbi : ∀ j : Fin 2, Continuous fun p : ℝ × Vec 2 => b p.1 p.2 j := fun j =>
    (continuous_apply j).comp hb.continuous
  refine ⟨fun κ => ?_, ?_⟩
  · have : (fun p : ℝ × Vec 2 => weakOp b κ φ p.1 p.2) = fun p =>
        deriv (fun s => φ s p.2) p.1 +
          (b p.1 p.2 0 * spaceGrad (φ p.1) p.2 0 + b p.1 p.2 1 * spaceGrad (φ p.1) p.2 1) +
          κ * lapl (φ p.1) p.2 := by
      funext p; simp only [weakOp, vecDot, Fin.sum_univ_two]
    rw [this]
    exact (hc1.add (((hbi 0).mul (hc2 0)).add ((hbi 1).mul (hc2 1)))).add
      (continuous_const.mul hlc)
  · obtain ⟨Cl, hCl⟩ := bounded_periodic_window
      (F := fun p : ℝ × Vec 2 => lapl (φ p.1) p.2) hlc
      (fun t n x => lapl_periodic (hφp t) n x) t₁ t₂
    refine ⟨max C 0 + 2 * B * max C 0, max Cl 0, by positivity, le_max_right _ _, ?_⟩
    intro κ t ht x
    obtain ⟨h1, h2, h3⟩ := hC t ht x
    have h4 : |lapl (φ t) x| ≤ max Cl 0 := (hCl t ht x).trans (le_max_left _ _)
    have hbj : ∀ j : Fin 2, |b t x j| ≤ B := fun j => by
      simpa using (norm_le_pi_norm (b t x) j).trans (hB t x)
    have hCm : ∀ j : Fin 2, |spaceGrad (φ t) x j| ≤ max C 0 := fun j =>
      (h3 j).trans (le_max_left _ _)
    have hmul : ∀ j : Fin 2, |b t x j * spaceGrad (φ t) x j| ≤ B * max C 0 := fun j => by
      rw [abs_mul]; exact mul_le_mul (hbj j) (hCm j) (abs_nonneg _) hB0
    simp only [weakOp, vecDot, Fin.sum_univ_two]
    calc |deriv (fun s => φ s x) t + (b t x 0 * spaceGrad (φ t) x 0 +
          b t x 1 * spaceGrad (φ t) x 1) + κ * lapl (φ t) x|
        ≤ |deriv (fun s => φ s x) t| + (|b t x 0 * spaceGrad (φ t) x 0| +
          |b t x 1 * spaceGrad (φ t) x 1|) + |κ * lapl (φ t) x| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add le_rfl (abs_add_le _ _))) le_rfl)
      _ ≤ max C 0 + (B * max C 0 + B * max C 0) + |κ| * max Cl 0 := by
          gcongr
          · exact h2.trans (le_max_left _ _)
          · exact hmul 0
          · exact hmul 1
          · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
      _ = max C 0 + 2 * B * max C 0 + |κ| * max Cl 0 := by ring

end AVRegularity.Applications
end
