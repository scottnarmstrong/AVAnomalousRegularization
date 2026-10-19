-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.ConstructedFullGalerkinAllOrderEnergy
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! All finite native energy levels use one polynomial contrast scale on the same frequency disc. -/

def constructedAllOrderPrice (K : ℕ) (R k Cw : ℝ) : ℝ :=
  match K with
  | 0 => 528 * R ^ 2 + 2 * (Cw * R + k) + 1 / 2
  | j + 1 => constructedHigherEnergyOrderPrice (j + 1) R k + 1 / 2

theorem constructedAllOrderPrice_nonneg (K : ℕ) (R k Cw : ℝ)
    (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw) : 0 ≤ constructedAllOrderPrice K R k Cw := by
  cases K with
  | zero =>
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg R))
        (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hCw hR) hk))) (by norm_num)
  | succ j => exact add_nonneg (constructedHigherEnergyOrderPrice_nonneg (j + 1) R k hk) (by norm_num)

theorem constructedAllOrderGrowth_polynomial_bound (K : ℕ) (R k η Cw : ℝ)
    (ξ : Fin 2 → ℂ) (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw)
    (hξ : fibreNorm ξ ≤ R) (hθ : ∀ i, ‖(Real.sqrt η : ℂ) * ξ i‖ ≤ R) :
    constructedAllOrderGrowth K R k η Cw ξ ≤ constructedAllOrderPrice K R k Cw * peFactor η ^ 2 := by
  have hp : 1 ≤ peFactor η := by
    unfold peFactor
    have hs := inv_nonneg.mpr (Real.sqrt_nonneg η)
    linarith
  have hp2 : 1 ≤ peFactor η ^ 2 := by nlinarith
  cases K with
  | zero =>
    have ht : (∑ i : Fin 2, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) ≤ 2 * R ^ 2 := by
      simp only [Fin.sum_univ_two]
      exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
    have hf := mul_le_mul_of_nonneg_left hξ hCw
    have he : constructedAllOrderGrowth 0 R k η Cw ξ ≤ constructedAllOrderPrice 0 R k Cw := by
      unfold constructedAllOrderGrowth cellFullZerothGrowth constructedAllOrderPrice
      linarith only [ht, hf]
    have hl := mul_le_mul_of_nonneg_left hp2 (constructedAllOrderPrice_nonneg 0 R k Cw hR hk hCw)
    exact he.trans (by simpa only [mul_one] using hl)
  | succ j =>
    simp only [constructedAllOrderGrowth, constructedAllOrderPrice]
    nlinarith only [hp2]

def constructedNativeWindowPrice (q : ℕ) (R k Cw : ℝ) : ℝ :=
  1 + ∑ j : Fin (q + 1), constructedAllOrderPrice j.val R k Cw

theorem constructedNativeWindowPrice_pos (q : ℕ) (R k Cw : ℝ)
    (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw) :
    0 < constructedNativeWindowPrice q R k Cw := by
  have hs : 0 ≤ ∑ j : Fin (q + 1), constructedAllOrderPrice j.val R k Cw :=
    Finset.sum_nonneg (fun _ _ => constructedAllOrderPrice_nonneg _ R k Cw hR hk hCw)
  unfold constructedNativeWindowPrice
  linarith

theorem constructedAllOrderPrice_le_window (q j : ℕ) (hj : j ≤ q) (R k Cw : ℝ)
    (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw) :
    constructedAllOrderPrice j R k Cw ≤ constructedNativeWindowPrice q R k Cw := by
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin (q + 1) => constructedAllOrderPrice i.val R k Cw)
    (fun i _ => constructedAllOrderPrice_nonneg i.val R k Cw hR hk hCw)
    (Finset.mem_univ (⟨j, by omega⟩ : Fin (q + 1)))
  exact hs.trans (le_add_of_nonneg_left (by norm_num))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Higher moments on actual source edges and on the preceding level produce
a genuine native forcing for one response component. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem geometryResponse_native_component_forcing (F : ChartedFamily ι h D P Ctx)
    (Ks J Kmax : ℕ) (π : ι → ℝ) (hπ : ∀ u, 0 < π u)
    (K : ι → ℕ) (hK : ∀ u, K u ≤ Kmax) (hdesc : F.IsDescending K)
    (dom : F.Domain) (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (Cmol : ℕ → ℝ) (Jmol : ℕ) (b₀ : ι → ι → ℝ) (hKs : Ks ≤ Jmol)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ Cmol Jmol b₀) (hmeas : F.IsTimeMeasurable)
    (hb₀ : ∀ v u, 0 ≤ b₀ v u) (hrow : ∀ v, ∑ u, b₀ v u ≤ 1) (hcol : ∀ u, ∑ v, b₀ v u ≤ 1)
    (p : P) (c : Ctx p) (s a b ϖ ζ g : ℝ) (hs : s ≠ 0)
    (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hg : 0 ≤ g) (hδ : e / E = ζ * ϖ) (X0 phase : Vec 2)
    (hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (CG : ℕ → ℝ) (hCG : ∀ r, 0 ≤ CG r)
    (hGm : ∀ X k l, Measurable (fun t => G t X k l))
    (hGs : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l))
    (hGj : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ CG r * g * (e / E) ^ r)
    (Uw : ∀ (_ : Fin (J + 1)) u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (hUw : ∀ j u, MemLp (Uw j u) 2 (volume.restrict (Set.Icc a b)))
    (j : Fin (J + 1)) (v : ι) (n : ℕ)
    (hsource : ∀ u, Nonempty (F.Γ v u) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (Uw j u t)) ≠ ⊤)
    (hprev : ∀ j', j.val = j'.val + 1 →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K v) (Uw j' v t)) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
      MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
        geometryResponseSourceFlux F J Ks K p c G s (e / E) X0 phase Uw j v t) := by
  obtain ⟨CT, _, hsourceFlux⟩ := originalTaylorRow_native_flux_exists_supported
    (ι := ι) (h := h) (D := D) (P := P) (Ctx := Ctx) Ks Kmax
  obtain ⟨Vsource, hVs, hVse, hVsv, _⟩ := hsourceFlux F π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol v p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ
    X0 phase hwindow n (Uw j) (hUw j) hsource
  obtain ⟨CM, _, hmetricFlux⟩ := metricPreviousResponse_native_flux_exists (E := h v) Ks Kmax CG hCG
  obtain ⟨Vmetric, hVm, hVme, hVmv, _⟩ := hmetricFlux (K v) (hK v) J G a b ϖ (ρ / e) (e / E)
    ζ g hGm hGs hϖ (div_pos hρ he) hscale hζ hζ1 hg hδ hGj j n
    (fun j' => Uw j' v) (fun j' => hUw j' v) hprev
  refine ⟨fun t => Vsource t + Vmetric t, nativeTime_add_memLp (volume.restrict (Set.Icc a b)) Vsource Vmetric hVs hVm, ?_, ?_⟩
  · exact integrated_weightedFactorialNormSq_add_ne_top n ϖ 0 (ρ / e)
      (volume.restrict (Set.Icc a b)) Vsource Vmetric hVs hVse hVme
  · filter_upwards [hVsv, hVmv] with t hs' hm'
    filter_upwards [planeValue_add_ae (Vsource t) (Vmetric t), hs', hm'] with z hz hs'' hm''
    rw [hz, hs'', hm'']
    rfl
end

/-! Higher moments on actual source edges and on the preceding level produce
a genuine native forcing for one response component. -/

theorem geometryResponse_native_component_forcing_quantitative_uniform (Ks Kmax : ℕ)
    (CG : ℕ → ℝ) (hCG : ∀ r, 0 ≤ CG r) :
    ∃ CT CM : ℝ, 0 ≤ CT ∧ 0 ≤ CM ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
    (J : ℕ) (π : ι → ℝ) (_hπ : ∀ u, 0 < π u)
    (K : ι → ℕ) (_hK : ∀ u, K u ≤ Kmax) (_hdesc : F.IsDescending K)
    (dom : F.Domain) (ν e E ρ : ℝ) (_hν : 0 < ν) (_he : 0 < e) (_hE : 0 < E) (_hρ : 0 < ρ)
    (Cmol : ℕ → ℝ) (Jmol : ℕ) (b₀ : ι → ι → ℝ) (_hKs : Ks ≤ Jmol)
    (_henv : IsMolecularEnvelope F π K dom ν e E ρ Cmol Jmol b₀) (_hmeas : F.IsTimeMeasurable)
    (_hb₀ : ∀ v u, 0 ≤ b₀ v u) (_hrow : ∀ v, ∑ u, b₀ v u ≤ 1) (_hcol : ∀ u, ∑ v, b₀ v u ≤ 1)
    (p : P) (c : Ctx p) (s a b ϖ ζ g : ℝ) (_hs : s ≠ 0)
    (_hϖ : 0 < ϖ) (_hscale : (ρ / e) * ϖ ≤ 1) (_hζ : 0 ≤ ζ) (_hζ1 : ζ ≤ 1)
    (_hg : 0 ≤ g) (_hδ : e / E = ζ * ϖ) (X0 phase : Vec 2)
    (_hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (_hGm : ∀ X k l, Measurable (fun t => G t X k l))
    (_hGs : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l))
    (_hGj : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ CG r * g * (e / E) ^ r)
    (Uw : ∀ (_ : Fin (J + 1)) u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (_hUw : ∀ j u, MemLp (Uw j u) 2 (volume.restrict (Set.Icc a b)))
    (j : Fin (J + 1)) (v : ι) (n : ℕ)
    (_hsource : ∀ u, Nonempty (F.Γ v u) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (Uw j u t)) ≠ ⊤)
    (_hprev : ∀ j', j.val = j'.val + 1 →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K v) (Uw j' v t)) ≠ ⊤) ,
    ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
      MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
      (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
        geometryResponseSourceFlux F J Ks K p c G s (e / E) X0 phase Uw j v t) ∧
      (ENNReal.ofReal ((π v)⁻¹) *
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≤
        2 * (ENNReal.ofReal (originalTaylorGraphConstant Ks Kmax CT Cmol) *
          ∑ u, ENNReal.ofReal ((Real.sqrt (π u / π v) *
            (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)) *
            (π u)⁻¹) *
            (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (Uw j u t))) +
        2 * (ENNReal.ofReal ((π v)⁻¹) *
          ENNReal.ofReal ((4 * Real.sqrt (multiplicationDensityBudget (K v)) * (CM * g * ζ)) ^ 2) *
          ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then
            (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K v) (Uw j' v t)) else 0)) := by
  classical
  obtain ⟨CT, hCT, hsourceFlux⟩ := originalTaylorRow_native_flux_exists_supported_uniform Ks Kmax
  obtain ⟨CM, hCM, hmetricFlux⟩ := metricPreviousResponse_native_flux_exists_uniform Ks Kmax CG hCG
  refine ⟨CT, CM, hCT, hCM, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F J π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1 hg hδ
    X0 phase hwindow G hGm hGs hGj Uw hUw j v n hsource hprev
  obtain ⟨Vsource, hVs, hVse, hVsv, hsourceDensity⟩ := hsourceFlux F π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol v p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ
    X0 phase hwindow n (Uw j) (hUw j) hsource
  obtain ⟨Vmetric, hVm, hVme, hVmv, hmetricBudget⟩ := hmetricFlux (K v) (hK v) J G a b ϖ (ρ / e) (e / E)
    ζ g hGm hGs hϖ (div_pos hρ he) hscale hζ hζ1 hg hδ hGj j n
    (fun j' => Uw j' v) (fun j' => hUw j' v) hprev
  refine ⟨fun t => Vsource t + Vmetric t, nativeTime_add_memLp (volume.restrict (Set.Icc a b)) Vsource Vmetric hVs hVm, ?_, ?_, ?_⟩
  · exact integrated_weightedFactorialNormSq_add_ne_top n ϖ 0 (ρ / e)
      (volume.restrict (Set.Icc a b)) Vsource Vmetric hVs hVse hVme
  · filter_upwards [hVsv, hVmv] with t hs' hm'
    filter_upwards [planeValue_add_ae (Vsource t) (Vmetric t), hs', hm'] with z hz hs'' hm''
    rw [hz, hs'', hm'']
    rfl
  · let price (u : ι) : ℝ := (Real.sqrt (π u / π v) *
        (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)) * (π u)⁻¹
    have hp (u : ι) : 0 ≤ price u := by
      apply mul_nonneg
      · apply mul_nonneg (Real.sqrt_nonneg _)
        exact Finset.sum_nonneg (fun α _ => originalTaylorPrice_nonneg F K Ks Kmax dom ν e E ρ CT
          hν.le hE.le hρ.le hCT v u α)
      · exact inv_nonneg.mpr (hπ u).le
    have hθ : 0 ≤ originalTaylorGraphConstant Ks Kmax CT Cmol := by
      unfold originalTaylorGraphConstant
      positivity
    have hsb := nativeFlux_row_time_moment_budget K n Ks ϖ (ρ / e) ((π v)⁻¹)
      (originalTaylorGraphConstant Ks Kmax CT Cmol) (inv_nonneg.mpr (hπ v).le) hθ price hp
      (volume.restrict (Set.Icc a b)) Vsource (Uw j) (hUw j)
      (by simpa only [price, mul_assoc] using hsourceDensity)
    have hab := integrated_weightedFactorialNormSq_add_le n ϖ 0 (ρ / e)
      (volume.restrict (Set.Icc a b)) Vsource Vmetric hVs
    have hmb := mul_le_mul_right (hmetricBudget n) (ENNReal.ofReal ((π v)⁻¹))
    calc
      _ ≤ ENNReal.ofReal ((π v)⁻¹) *
          (2 * ((∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (Vsource t)) +
                (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (Vmetric t)))) :=
        mul_le_mul_right hab _
      _ = 2 * (ENNReal.ofReal ((π v)⁻¹) *
              (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (Vsource t))) +
          2 * (ENNReal.ofReal ((π v)⁻¹) *
              (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (Vmetric t))) := by ring
      _ ≤ _ := by
        simpa only [price, mul_assoc] using add_le_add (mul_le_mul_right hsb 2) (mul_le_mul_right hmb 2)

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! A common short time for finitely many native orders has an explicit polynomial contrast price. -/

def constructedNativeSmoothingTime (J : ℕ) (R k Cw η : ℝ) : ℝ :=
  1 / (((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw * peFactor η ^ 2)

theorem constructedNativeWindowPrice_one_le (J : ℕ) (R k Cw : ℝ)
    (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw) :
    1 ≤ constructedNativeWindowPrice J R k Cw := by
  have hs := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin (J + 1))))
    (fun j _ => constructedAllOrderPrice_nonneg j.val R k Cw hR hk hCw)
  unfold constructedNativeWindowPrice
  linarith

theorem constructedNativeSmoothingTime_pos (J : ℕ) (R k Cw η : ℝ)
    (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw) :
    0 < constructedNativeSmoothingTime J R k Cw η := by
  have hM := constructedNativeWindowPrice_pos J R k Cw hR hk hCw
  have hp : 0 < peFactor η := lt_of_lt_of_le (by norm_num) (one_le_peFactor η)
  unfold constructedNativeSmoothingTime
  positivity

theorem constructedNativeSmoothingTime_budget (J : ℕ) (R k Cw η : ℝ)
    (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw) :
    (constructedNativeWindowPrice J R k Cw * peFactor η ^ 2) *
      constructedNativeSmoothingTime J R k Cw η ≤ 1 := by
  have hM := constructedNativeWindowPrice_pos J R k Cw hR hk hCw
  have hp : 0 < peFactor η := lt_of_lt_of_le (by norm_num) (one_le_peFactor η)
  have hj : 0 < (J : ℝ) + 1 := by positivity
  have he : (constructedNativeWindowPrice J R k Cw * peFactor η ^ 2) *
      constructedNativeSmoothingTime J R k Cw η = 1 / ((J : ℝ) + 1) := by
    unfold constructedNativeSmoothingTime
    field_simp
  rw [he]
  exact (div_le_one₀ hj).mpr (by have h := Nat.cast_nonneg (α := ℝ) J; linarith only [h])

theorem constructedNativeSmoothingTime_orders_le_one (J : ℕ) (R k Cw η : ℝ)
    (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw) :
    (J : ℝ) * constructedNativeSmoothingTime J R k Cw η ≤ 1 := by
  have hM := constructedNativeWindowPrice_one_le J R k Cw hR hk hCw
  have hp := one_le_peFactor_pow η 2
  have hA : 1 ≤ constructedNativeWindowPrice J R k Cw * peFactor η ^ 2 :=
    by simpa only [one_mul] using (mul_le_mul hM hp (by norm_num : (0 : ℝ) ≤ 1) ((by norm_num : (0 : ℝ) ≤ 1).trans hM))
  have hj : 0 < (J : ℝ) + 1 := by positivity
  have hd : 0 < ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw * peFactor η ^ 2 := by
    rw [mul_assoc]
    exact mul_pos hj (lt_of_lt_of_le (by norm_num) hA)
  unfold constructedNativeSmoothingTime
  rw [← div_eq_mul_one_div]
  apply (div_le_one₀ hd).mpr
  have hh := mul_le_mul_of_nonneg_left hA hj.le
  nlinarith only [hh]

theorem constructedNativeSmoothingTime_polynomial_price (J : ℕ) (R k Cw η : ℝ) :
    (Real.exp 1 * (2 * Real.exp 1) / constructedNativeSmoothingTime J R k Cw η) ^ J =
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor η ^ (2 * J) := by
  unfold constructedNativeSmoothingTime
  rw [div_div_eq_mul_div, div_one, ← mul_assoc, mul_pow, pow_mul]
  simp only [mul_assoc]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Every full finite native energy level uses one common short contrast-dependent window. -/

theorem constructedFullGalerkin_native_window (J N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩ hG V hv.1 hb t) (y t)))
    (hshort : (constructedNativeWindowPrice J R k Cw * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * (b - a) ≤ 1) :
    ∀ K ≤ J,
      ‖cellGalerkinNativeLiftCLM N K (y b)‖ ^ 2 ≤ Real.exp 1 * ‖cellGalerkinNativeLiftCLM N K (y a)‖ ^ 2 ∧
        (∫ t in a..b, ‖cellGalerkinNativeLiftCLM N (K + 1) (y t)‖ ^ 2) ≤
          (2 * Real.exp 1) * ‖cellGalerkinNativeLiftCLM N K (y a)‖ ^ 2 := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  have hk0 : 0 ≤ k := (norm_nonneg _).trans (hk a)
  have hA : 0 ≤ A := mul_nonneg (constructedNativeWindowPrice_pos J R k Cw hR hk0 hCw).le (sq_nonneg _)
  intro K hK
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk K ℂ) := inferInstance
  let : NormedAddCommGroup (TorusHk (K + 1) ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk (K + 1) ℂ) := inferInstance
  apply finiteObservable_short_window_bounds hab hy (cellGalerkinNativeLiftCLM N K)
    (cellGalerkinNativeLiftCLM N (K + 1)) A hA hshort
  apply Filter.Eventually.of_forall
  intro t
  have he := constructedFullGalerkin_all_order_energy K N hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hθ κ t k (hk t) (y t)
  have hprice : constructedAllOrderGrowth K R k η Cw ξ ≤ A :=
    (constructedAllOrderGrowth_polynomial_bound K R k η Cw ξ hR hk0 hCw hξ hθ).trans
      (mul_le_mul_of_nonneg_right (constructedAllOrderPrice_le_window J K hK R k Cw hR hk0 hCw) (sq_nonneg _))
  exact he.trans (mul_le_mul_of_nonneg_right hprice (sq_nonneg ‖cellGalerkinNativeLiftCLM N K (y t)‖))

end AVRegularity.CycleWords
end

section
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Full higher gap-transfer prices are polynomial in contrast on a fixed frequency disc. -/

def constructedNativeGapBasePrice (J : ℕ) (R k Cw γ : ℝ) : ℝ :=
  Real.exp γ * (Real.exp 1 +
    (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
      constructedNativeWindowPrice J R k Cw * (J : ℝ)) ^ J *
        Real.exp (constructedAllOrderPrice 0 R k Cw))

theorem constructedNativeGapBasePrice_nonneg (J : ℕ) (R k Cw γ : ℝ)
    (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw) :
    0 ≤ constructedNativeGapBasePrice J R k Cw γ := by
  have hM := (constructedNativeWindowPrice_pos J R k Cw hR hk hCw).le
  unfold constructedNativeGapBasePrice
  positivity

theorem constructedNativeGap_step_price (J : ℕ) (R k Cw η : ℝ) :
    (Real.exp 1 * (2 * Real.exp 1) / (constructedNativeSmoothingTime J R k Cw η / (J : ℝ))) ^ J =
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
        constructedNativeWindowPrice J R k Cw * (J : ℝ)) ^ J * peFactor η ^ (2 * J) := by
  have he : Real.exp 1 * (2 * Real.exp 1) /
      (constructedNativeSmoothingTime J R k Cw η / (J : ℝ)) =
      (Real.exp 1 * (2 * Real.exp 1) / constructedNativeSmoothingTime J R k Cw η) * (J : ℝ) := by
    rw [div_div_eq_mul_div]
    ring
  rw [he, mul_pow, constructedNativeSmoothingTime_polynomial_price]
  simp only [mul_pow]
  ring

theorem constructedNativeGap_polynomial_price (J : ℕ) (R k Cw η γ : ℝ)
    (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt η : ℂ) * ξ i‖ ≤ R) :
    Real.exp γ * (Real.exp 1 +
      (Real.exp 1 * (2 * Real.exp 1) / (constructedNativeSmoothingTime J R k Cw η / (J : ℝ))) ^ J *
        Real.exp (cellFullZerothGrowth η Cw ξ k)) ≤
      constructedNativeGapBasePrice J R k Cw γ * peFactor η ^ (2 * J) := by
  have ht : (∑ i : Fin 2, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hz : cellFullZerothGrowth η Cw ξ k ≤ constructedAllOrderPrice 0 R k Cw := by
    have hf := mul_le_mul_of_nonneg_left hξ hCw
    unfold cellFullZerothGrowth constructedAllOrderPrice
    linarith only [ht, hf]
  let B := (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
    constructedNativeWindowPrice J R k Cw * (J : ℝ)) ^ J
  have hM := (constructedNativeWindowPrice_pos J R k Cw hR hk hCw).le
  have hB : 0 ≤ B := by unfold B; positivity
  have hp := one_le_peFactor_pow η (2 * J)
  have hconst := mul_le_mul_of_nonneg_left hp (Real.exp_pos 1).le
  have hex := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz)
    (mul_nonneg hB (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) (2 * J)))
  rw [constructedNativeGap_step_price]
  have hh := mul_le_mul_of_nonneg_left (add_le_add hconst hex) (Real.exp_pos γ).le
  unfold constructedNativeGapBasePrice
  dsimp only [B] at hh
  convert hh using 1 <;> ring

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! Explicit polynomial contrast and elapsed-time prices for full short-tail smoothing. -/

def constructedGapSmoothingBasePrice (J : ℕ) (R k Cw : ℝ) : ℝ :=
  (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) ^ 2 *
    constructedNativeWindowPrice J R k Cw) ^ J +
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1)) ^ J

theorem constructedGapSmoothing_polynomial_square_price (J : ℕ) (R k Cw η τ : ℝ)
    (hR : 0 ≤ R) (hk : 0 ≤ k) (hCw : 0 ≤ Cw) (hτ : 0 < τ) :
    let C := Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1)
    (C / constructedNativeSmoothingTime J R k Cw η) ^ J + (C / τ) ^ J ≤
      (Real.sqrt (constructedGapSmoothingBasePrice J R k Cw) * peFactor η ^ J *
        (1 + τ ^ (-(J : ℝ) / 2))) ^ 2 := by
  let E := Real.exp 1 * (2 * Real.exp 1)
  let A := (E * ((J : ℝ) + 1) ^ 2 * constructedNativeWindowPrice J R k Cw) ^ J
  let B := (E * ((J : ℝ) + 1)) ^ J
  have hM := constructedNativeWindowPrice_pos J R k Cw hR hk hCw
  have hA : 0 ≤ A := by dsimp [A, E]; positivity
  have hB : 0 ≤ B := by dsimp [B, E]; positivity
  have he : (E * ((J : ℝ) + 1) / constructedNativeSmoothingTime J R k Cw η) ^ J =
      A * peFactor η ^ (2 * J) := by
    unfold constructedNativeSmoothingTime
    rw [div_div_eq_mul_div, div_one]
    have hh : E * ((J : ℝ) + 1) *
        (((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw * peFactor η ^ 2) =
        (E * ((J : ℝ) + 1) ^ 2 * constructedNativeWindowPrice J R k Cw) * peFactor η ^ 2 := by ring
    rw [hh, mul_pow, ← pow_mul]
  have hp := one_le_peFactor_pow η (2 * J)
  have hPb : 0 ≤ peFactor η ^ (2 * J) := (by norm_num : (0 : ℝ) ≤ 1).trans hp
  have htime : 0 ≤ B / τ ^ J := div_nonneg hB (pow_nonneg hτ.le J)
  have hb : B / τ ^ J ≤ (B / τ ^ J) * peFactor η ^ (2 * J) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp htime
  have hs := smoothingSingularity_sum_price J τ A B hτ hA hB
  have ht := mul_le_mul_of_nonneg_right hs hPb
  change (E * ((J : ℝ) + 1) / constructedNativeSmoothingTime J R k Cw η) ^ J +
    (E * ((J : ℝ) + 1) / τ) ^ J ≤ _
  rw [he, div_pow]
  have hh := (add_le_add le_rfl hb).trans_eq
    (show A * peFactor η ^ (2 * J) + B / τ ^ J * peFactor η ^ (2 * J) =
      (A + B / τ ^ J) * peFactor η ^ (2 * J) by ring)
  refine hh.trans (ht.trans_eq ?_)
  change _ = (Real.sqrt (A + B) * peFactor η ^ J * (1 + τ ^ (-(J : ℝ) / 2))) ^ 2
  simp only [mul_pow]
  rw [show 2 * J = J * 2 by omega, pow_mul]
  ring

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The full finite constructed equation smooths with polynomial contrast cost on a common frequency disc. -/

theorem constructedFullGalerkin_native_smoothing (J N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩ hG V hv.1 hb t) (y t)))
    (δ B : ℝ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hshort : (constructedNativeWindowPrice J R k Cw * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * δ ≤ 1)
    (hzero : ∀ t ∈ Icc a b, ‖cellGalerkinValue N (y t)‖ ^ 2 ≤ B)
    (t : ℝ) (ht : a + J * δ ≤ t) (htb : t ≤ b) :
    ‖cellGalerkinNativeLiftCLM N J (y t)‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J * B := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  let E := fun K s => ‖cellGalerkinNativeLiftCLM N K (y s)‖ ^ 2
  have hA : 0 ≤ A := mul_nonneg
    (constructedNativeWindowPrice_pos J R k Cw hR ((norm_nonneg _).trans (hk a)) hCw).le (sq_nonneg _)
  have hcontinuous : ContinuousOn y (Icc a b) := by simpa only [uIcc_of_le hab] using hy.ac.continuousOn
  have hlocal (s d : ℝ) (has : a ≤ s) (hsd : s ≤ d) (hdb : d ≤ b) (hds : d - s ≤ δ) :
      ∀ K ≤ J, E K d ≤ Real.exp 1 * E K s ∧
        (∫ u in s..d, E (K + 1) u) ≤ (2 * Real.exp 1) * E K s := by
    have hsub : uIcc s d ⊆ uIcc a b := by
      rw [uIcc_of_le hsd, uIcc_of_le hab]
      intro x hx
      exact ⟨has.trans hx.1, hx.2.trans hdb⟩
    have hsmall : A * (d - s) ≤ 1 := (mul_le_mul_of_nonneg_left hds hA).trans hshort
    exact constructedFullGalerkin_native_window J N hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk
      hsd y (hy.mono hsub) hsmall
  apply continuous_energy_short_window_polynomial_price E (2 * Real.exp 1) (Real.exp 1) B a b δ J
    hδ (by positivity) (Real.exp_pos 1).le
    (fun K _ => ((cellGalerkinNativeLiftCLM N K).continuous.comp_continuousOn hcontinuous).norm.pow 2)
    (fun s hs => by simpa only [E, cellGalerkinNativeLiftCLM_zero_norm_sq] using hzero s hs) hB
    (fun K hK s has hsb => (hlocal s (s + δ) has (by linarith only [hδ]) hsb
      (by simp only [add_sub_cancel_left, le_refl]) K (by omega)).2)
    (fun K _ hK s d has hsd hdb hds => (hlocal s d has hsd hdb hds K hK).1) t ht htb

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! A contrast-independent real constant covers both full forward and adjoint smoothing prices. -/

def constructedSmoothingPrice (J : ℕ) (R Cw : ℝ) : ℝ :=
  nativeSobolevWordPrice J * (13 * Real.sqrt (Real.exp (6 * Real.pi ^ 2) *
    constructedGapSmoothingBasePrice J R 0 Cw * Real.exp (constructedAllOrderPrice 0 R 0 Cw)))

theorem constructedSmoothingPrice_nonneg (J : ℕ) (R Cw : ℝ) :
    0 ≤ constructedSmoothingPrice J R Cw := by
  unfold constructedSmoothingPrice
  exact mul_nonneg (nativeSobolevWordPrice_nonneg J) (by positivity)

theorem constructedSmoothingPrice_bound (J : ℕ) (R Cw η τ : ℝ) (hτ : 0 ≤ τ) :
    nativeSobolevWordPrice J *
      (13 * ((Real.sqrt (Real.exp (6 * Real.pi ^ 2) * constructedGapSmoothingBasePrice J R 0 Cw *
        Real.exp (constructedAllOrderPrice 0 R 0 Cw)) * peFactor η ^ J *
        Real.exp (-(6 * Real.pi ^ 2) * τ / 2)) * (1 + τ ^ (-(J : ℝ) / 2)))) ≤
      constructedSmoothingPrice J R Cw * peFactor η ^ (2 * J) *
        (1 + τ ^ (-(J : ℝ) / 2)) * Real.exp (-(3 * Real.pi ^ 2) * τ) := by
  have hp : peFactor η ^ J ≤ peFactor η ^ (2 * J) :=
    pow_le_pow_right₀ (one_le_peFactor η) (by omega)
  have hs : 0 ≤ 1 + τ ^ (-(J : ℝ) / 2) :=
    add_nonneg (by norm_num) (Real.rpow_nonneg hτ _)
  calc
    _ = (constructedSmoothingPrice J R Cw * (1 + τ ^ (-(J : ℝ) / 2)) *
        Real.exp (-(3 * Real.pi ^ 2) * τ)) * peFactor η ^ J := by
      have hexp : -(6 * Real.pi ^ 2) * τ / 2 = -(3 * Real.pi ^ 2) * τ := by ring
      rw [hexp]
      dsimp only [constructedSmoothingPrice]
      ring
    _ ≤ (constructedSmoothingPrice J R Cw * (1 + τ ^ (-(J : ℝ) / 2)) *
        Real.exp (-(3 * Real.pi ^ 2) * τ)) * peFactor η ^ (2 * J) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg
        (mul_nonneg (constructedSmoothingPrice_nonneg J R Cw) hs) (Real.exp_nonneg _))
    _ = _ := by ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual plane generator has the opposite-drift generator as its adjoint. -/

theorem planeRealBlochGeneratorForm_opposite_drift
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (C' : ℝ) (hC'pos : 0 < C')
    (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun t x => -v t x) t i z‖ ≤ C')
    (t : ℝ) (u z : PlaneHk Set.univ 1 ℝ) :
    planeRealBlochGeneratorForm (G t) v hv t C (hC t) u z =
      planeRealBlochGeneratorForm (G t) (fun t x => -v t x) (cellDrift_neg hv)
        t C' (hC' t) z u := by
  rw [planeRealBlochGeneratorForm_cellIntegral G hG v hv V hb C hCpos hC,
    planeRealBlochGeneratorForm_cellIntegral G hG (fun t x => -v t x)
      (cellDrift_neg hv) V (cellDrift_neg_bound hb) C' hC'pos hC']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => by
    have he := congrArg Complex.re (cellComplexGenerator_opposite_drift
      ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv hb t
      (cellComplexH1RealEquiv (planeRealH1BlochTest u θ))
      (cellComplexH1RealEquiv (planeRealH1BlochTest z θ)))
    have hθ : (fun j => star (planePhysicalBlochShift θ j)) = planePhysicalBlochShift θ :=
      funext (planePhysicalBlochShift_real θ)
    have hκ : (fun t : ℝ => star ((0 : ℝ → ℂ) t)) = (0 : ℝ → ℂ) := by
      funext t
      exact star_zero ℂ
    dsimp only [cellAdjointCoefficients] at he
    rw [hθ, hκ] at he
    simpa only [Complex.star_def, Complex.conj_re, cellComplexGenerator_re] using he)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Higher energy of the original full finite cell system, uniformly in its Fourier cutoff. -/

theorem interiorPulseGalerkinOperator_higher_energy {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (u : CellGalerkinSpace (E := ℂ) N) :
    2 * inner ℝ (rangeSmoothFourierLiftCLM hK N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot, θ, κ⟩ hG V hv.1 hb t) u))
      (rangeSmoothFourierLiftCLM hK N u) +
      (1 / 2) * (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
        ‖cellGalerkinValue N u‖ ^ 2) ≤
      constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2 *
        ‖rangeSmoothFourierLiftCLM hK N u‖ ^ 2 := by
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk K ℂ) := inferInstance
  have hl := interiorPulseGalerkinOperator_higher_lift hK N hΛ hζ ν y₀ hslot hv V hb G hG θ κ t u
  have hi := torusHigherProjection_retained_inner K N
    (interiorPulseHigherFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))
    (rangeSmoothFourierLiftCLM hK N u) (rangeSmoothFourierLift_fixed hK N u)
  have hpair := (congrArg (fun z : TorusHk K ℂ =>
    inner ℝ z (rangeSmoothFourierLiftCLM hK N u)) hl).trans hi
  have he := cellGalerkinSmoothEnergyTransfer hK N u
    (interiorPulseHigherFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t)
    (constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2)
    (interiorPulseHigherFullGenerator_smooth_adjacent_energy K hΛ hζ hν hr y₀ hslot hv G hG θ R hθ κ t k hk
      (cellGalerkinSmoothValue N u) (cellGalerkinSmoothValue_contDiff N u) (cellGalerkinSmoothValue_periodic N u))
  exact (congrArg (fun x : ℝ => 2 * x + (1 / 2) *
    (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
      ‖cellGalerkinValue N u‖ ^ 2)) hpair).le.trans he

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedFullGalerkin_native_polynomial_smoothing (J N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩ hG V hv.1 hb t) (y t)))

    (hwindow : b - a ≤ 1) (t : ℝ)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t)
    (htb : t ≤ b) :
    ‖cellGalerkinNativeLiftCLM N J (y t)‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) *
          ‖cellGalerkinValue N (y a)‖ ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := cellFullZerothGrowth η Cw ξ k
  let B := Real.exp A * ‖cellGalerkinValue N (y a)‖ ^ 2
  have hA : 0 ≤ A := cellFullZerothGrowth_nonneg η Cw hCw ξ k ((norm_nonneg _).trans (hk a))
  have hzero : ∀ s ∈ Icc a b, ‖cellGalerkinValue N (y s)‖ ^ 2 ≤ B := by
    intro s hs
    have he := cellFullGalerkin_zeroth_propagation N η Cw hCw G hG hv hw V hb ξ κ k hk hab y hy s hs
    have hs1 : s - a ≤ 1 := (sub_le_sub_right hs.2 a).trans hwindow
    have hex : Real.exp (A * (s - a)) ≤ Real.exp A :=
      Real.exp_le_exp.mpr (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 hA)
    exact he.trans (by simpa only [B, mul_comm] using mul_le_mul_of_nonneg_left hex (sq_nonneg ‖cellGalerkinValue N (y a)‖))
  have he := constructedFullGalerkin_native_smoothing J N hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab y hy
    (constructedNativeSmoothingTime J R k Cw η) B
    (constructedNativeSmoothingTime_pos J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw)
    (mul_nonneg (Real.exp_pos A).le (sq_nonneg _))
    (constructedNativeSmoothingTime_budget J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw)
    hzero t ht htb
  rw [constructedNativeSmoothingTime_polynomial_price] at he
  exact he

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The actual full reflected finite equation has the same native energy hierarchy. -/

theorem constructedReflectedGalerkin_all_order_energy (K N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k) (u : CellGalerkinSpace (E := ℂ) N) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let θ := fun i => (Real.sqrt η : ℂ) * ξ i
    let A := cellGalerkinOperator N (cellGeneratorB
      ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x, θ, κ⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t)
    2 * inner ℝ (cellGalerkinNativeLiftCLM N K (A u)) (cellGalerkinNativeLiftCLM N K u) +
      (1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) u‖ ^ 2 ≤
      constructedAllOrderGrowth K R k η Cw ξ * ‖cellGalerkinNativeLiftCLM N K u‖ ^ 2 := by
  dsimp only
  cases K with
  | zero =>
    change _ + (1 / 2) * ‖cellGalerkinNativeLiftCLM N 1 u‖ ^ 2 ≤ _
    have he := cellFullGalerkin_zeroth_adjacent_energy N (ν / ocMeanFlux α q Λ ζ m ν)
      Cw hCw (fun s => G (-s)) (cellMetric_timeReverse hG)
      (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw) V
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) ξ κ t k hk u
    simpa only [constructedAllOrderGrowth, torusH0_inner_value,
      cellGalerkinNativeLiftCLM_value, cellGalerkinNativeLiftCLM_one,
      cellGalerkinNativeLiftCLM_zero_norm_sq] using he
  | succ j =>
    have he := constructedReflectedGalerkinOperator_higher_energy (by omega : 1 ≤ j + 1) N
      hΛ hζ hν hr y₀ hv V hb G hG
      (fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i) R hθ κ t k hk u
    have hv' := pow_le_pow_left₀ (norm_nonneg (cellGalerkinValue N u))
      (cellGalerkinRangeHigher_value_norm_le (by omega : 1 ≤ j + 1) N u) 2
    have hp := energyGradientDifference_absorb hv' he
    simpa only [constructedAllOrderGrowth,
      cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ j + 1),
      cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ (j + 1) + 1)] using hp

/-! The committed reflected finite cell system reads out its full higher generator. -/

theorem interiorPulseReflectedGalerkinOperator_higher_readout (K N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : CellGalerkinSpace (E := ℂ) N) :
    cellGalerkinOperator N (cellGeneratorB
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x, θ, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) u =
    cellGalerkinL2Initial N (torusHkValueCLM
      (interiorPulseReflectedFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
        (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))) := by
  apply cellGalerkinMass_injective N
  apply LinearMap.ext
  intro z
  change inner ℝ (cellGalerkinValue N (cellGalerkinOperator N _ u)) (cellGalerkinValue N z) =
    inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N _)) (cellGalerkinValue N z)
  rw [cellGalerkinOperator_pairing, cellGalerkinL2Initial_pairing]
  change cellGeneratorForm
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x, θ, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t u.val z.val =
    inner ℝ (torusHkValueCLM
      (interiorPulseReflectedFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
        (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))) (torusHkValueCLM z.val)
  rw [interiorPulseReflectedFullGeneratorCLM_pairing K hΛ hζ ν y₀ hslot hv V hb G hG θ κ t _ z.val]
  have he := rangeSmoothFourierLift_truncate (by omega : 1 ≤ K + 2) N u
  have hbase : cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2)
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)) = u.val := by
    exact he
  rw [hbase]

theorem interiorPulseReflectedGalerkinOperator_higher_lift {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : CellGalerkinSpace (E := ℂ) N) :
    rangeSmoothFourierLiftCLM hK N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x, θ, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) u) =
    galerkinProj N (interiorPulseReflectedFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)) := by
  rw [interiorPulseReflectedGalerkinOperator_higher_readout K N hΛ hζ ν y₀ hslot hv V hb G hG θ κ t u,
    cellGalerkinL2Initial_higher_lift]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Dissipation of the actual real plane metric generator for rough periodic drifts. -/

theorem planeRealBlochGeneratorDual_nonpositive
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (t : ℝ) (u : PlaneHk Set.univ 1 ℝ) :
    inner ℝ (planeRealBlochGeneratorDual (G t) v hv t C (hC t) u) u ≤ 0 := by
  rw [planeRealBlochGeneratorDual_pair,
    planeRealBlochGeneratorForm_cellIntegral G hG v hv V hb C hCpos hC]
  apply integral_nonpos_of_ae
  exact Filter.Eventually.of_forall (fun θ => by
    have he := cellComplexGenerator_re
      ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv.1 hb t
      (cellComplexH1RealEquiv (planeRealH1BlochTest u θ))
      (cellComplexH1RealEquiv (planeRealH1BlochTest u θ))
    exact he.symm.le.trans (cellComplexGenerator_real_nonpos hG hv V hb
      (planePhysicalBlochShift θ) (planePhysicalBlochShift_real θ) t
      (cellComplexH1RealEquiv (planeRealH1BlochTest u θ))))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Every full reflected finite native energy level uses one common short contrast-dependent window. -/

theorem constructedReflectedGalerkin_native_window (J N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
          (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
          (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) (y t)))
    (hshort : (constructedNativeWindowPrice J R k Cw * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * (b - a) ≤ 1) :
    ∀ K ≤ J,
      ‖cellGalerkinNativeLiftCLM N K (y b)‖ ^ 2 ≤ Real.exp 1 * ‖cellGalerkinNativeLiftCLM N K (y a)‖ ^ 2 ∧
        (∫ t in a..b, ‖cellGalerkinNativeLiftCLM N (K + 1) (y t)‖ ^ 2) ≤
          (2 * Real.exp 1) * ‖cellGalerkinNativeLiftCLM N K (y a)‖ ^ 2 := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  have hk0 : 0 ≤ k := (norm_nonneg _).trans (hk a)
  have hA : 0 ≤ A := mul_nonneg (constructedNativeWindowPrice_pos J R k Cw hR hk0 hCw).le (sq_nonneg _)
  intro K hK
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk K ℂ) := inferInstance
  let : NormedAddCommGroup (TorusHk (K + 1) ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk (K + 1) ℂ) := inferInstance
  apply finiteObservable_short_window_bounds hab hy (cellGalerkinNativeLiftCLM N K)
    (cellGalerkinNativeLiftCLM N (K + 1)) A hA hshort
  apply Filter.Eventually.of_forall
  intro t
  have he := constructedReflectedGalerkin_all_order_energy K N hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hθ κ t k (hk t) (y t)
  have hprice : constructedAllOrderGrowth K R k η Cw ξ ≤ A :=
    (constructedAllOrderGrowth_polynomial_bound K R k η Cw ξ hR hk0 hCw hξ hθ).trans
      (mul_le_mul_of_nonneg_right (constructedAllOrderPrice_le_window J K hK R k Cw hR hk0 hCw) (sq_nonneg _))
  exact he.trans (mul_le_mul_of_nonneg_right hprice (sq_nonneg ‖cellGalerkinNativeLiftCLM N K (y t)‖))

/-! The full reflected finite constructed equation smooths with polynomial contrast cost on a common frequency disc. -/

theorem constructedReflectedGalerkin_native_smoothing (J N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
          (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
          (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) (y t)))
    (δ B : ℝ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hshort : (constructedNativeWindowPrice J R k Cw * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * δ ≤ 1)
    (hzero : ∀ t ∈ Icc a b, ‖cellGalerkinValue N (y t)‖ ^ 2 ≤ B)
    (t : ℝ) (ht : a + J * δ ≤ t) (htb : t ≤ b) :
    ‖cellGalerkinNativeLiftCLM N J (y t)‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J * B := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  let E := fun K s => ‖cellGalerkinNativeLiftCLM N K (y s)‖ ^ 2
  have hA : 0 ≤ A := mul_nonneg
    (constructedNativeWindowPrice_pos J R k Cw hR ((norm_nonneg _).trans (hk a)) hCw).le (sq_nonneg _)
  have hcontinuous : ContinuousOn y (Icc a b) := by simpa only [uIcc_of_le hab] using hy.ac.continuousOn
  have hlocal (s d : ℝ) (has : a ≤ s) (hsd : s ≤ d) (hdb : d ≤ b) (hds : d - s ≤ δ) :
      ∀ K ≤ J, E K d ≤ Real.exp 1 * E K s ∧
        (∫ u in s..d, E (K + 1) u) ≤ (2 * Real.exp 1) * E K s := by
    have hsub : uIcc s d ⊆ uIcc a b := by
      rw [uIcc_of_le hsd, uIcc_of_le hab]
      intro x hx
      exact ⟨has.trans hx.1, hx.2.trans hdb⟩
    have hsmall : A * (d - s) ≤ 1 := (mul_le_mul_of_nonneg_left hds hA).trans hshort
    exact constructedReflectedGalerkin_native_window J N hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk
      hsd y (hy.mono hsub) hsmall
  apply continuous_energy_short_window_polynomial_price E (2 * Real.exp 1) (Real.exp 1) B a b δ J
    hδ (by positivity) (Real.exp_pos 1).le
    (fun K _ => ((cellGalerkinNativeLiftCLM N K).continuous.comp_continuousOn hcontinuous).norm.pow 2)
    (fun s hs => by simpa only [E, cellGalerkinNativeLiftCLM_zero_norm_sq] using hzero s hs) hB
    (fun K hK s has hsb => (hlocal s (s + δ) has (by linarith only [hδ]) hsb
      (by simp only [add_sub_cancel_left, le_refl]) K (by omega)).2)
    (fun K _ hK s d has hsd hdb hds => (hlocal s d has hsd hdb hds K hK).1) t ht htb

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Higher energy of the original full reflected finite cell system, uniformly in its Fourier cutoff. -/

theorem interiorPulseReflectedGalerkinOperator_higher_energy {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (u : CellGalerkinSpace (E := ℂ) N) :
    2 * inner ℝ (rangeSmoothFourierLiftCLM hK N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x, θ, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) u))
      (rangeSmoothFourierLiftCLM hK N u) +
      (1 / 2) * (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
        ‖cellGalerkinValue N u‖ ^ 2) ≤
      constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2 *
        ‖rangeSmoothFourierLiftCLM hK N u‖ ^ 2 := by
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk K ℂ) := inferInstance
  have hl := interiorPulseReflectedGalerkinOperator_higher_lift hK N hΛ hζ ν y₀ hslot hv V hb G hG θ κ t u
  have hi := torusHigherProjection_retained_inner K N
    (interiorPulseReflectedFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))
    (rangeSmoothFourierLiftCLM hK N u) (rangeSmoothFourierLift_fixed hK N u)
  have hpair := (congrArg (fun z : TorusHk K ℂ =>
    inner ℝ z (rangeSmoothFourierLiftCLM hK N u)) hl).trans hi
  have he := cellGalerkinSmoothEnergyTransfer hK N u
    (interiorPulseReflectedFullGeneratorCLM K hΛ hζ ν y₀ hslot hv G θ κ t)
    (constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2)
    (interiorPulseReflectedFullGenerator_smooth_adjacent_energy K hΛ hζ hν hr y₀ hslot hv G hG θ R hθ κ t k hk
      (cellGalerkinSmoothValue N u) (cellGalerkinSmoothValue_contDiff N u) (cellGalerkinSmoothValue_periodic N u))
  exact (congrArg (fun x : ℝ => 2 * x + (1 / 2) *
    (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
      ‖cellGalerkinValue N u‖ ^ 2)) hpair).le.trans he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The actual normalized row retains its scalar bounds after smooth representative selection. -/

variable (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
  (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
  (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
  (ell : ℕ × ℕ → ℝ → Vec 2 → ℂ)
  (he : ∀ p t, ell p t =ᵐ[volume.restrict AVenhance.unitCube]
    fibreAdjointRowCoefficients η Cw hη G hG hv hw p t)

include hCw he in
theorem constructedScalarRow_summable (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) :
    ∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * ⨆ t, cellL2Norm (ell p t) < ⊤ := by
  have hn : ∀ p t, cellL2Norm (ell p t) =
      cellL2Norm (fibreAdjointRowCoefficients η Cw hη G hG hv hw p t) :=
    fun p t => eLpNorm_congr_ae (he p t)
  simp only [hn]
  apply lt_of_le_of_lt _ (by norm_num : (4 : ℝ≥0∞) < ⊤)
  apply le_trans _ (fibreAdjointRowCoefficients_weighted_le_four η Cw hη hCw G hG hv hw)
  exact ENNReal.tsum_le_tsum (fun p => mul_le_mul'
    (fibreMonomial_weight_le _ ξ hξ p) le_rfl)

include hCw he in
theorem constructedScalarRow_sub_one_bound (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    cellL2Norm (fun x => fibreSeriesFun ell ξ t x - 1) ≤
      ENNReal.ofReal (constructedScalarGraphPrice Cw * fibreNorm ξ) := by
  rw [fibreRowReplacement_series_correction_norm_eq ell _ he]
  apply (fibreAdjointRowCoefficients_sub_one_le η Cw hη hCw G hG hv hw ξ hξ t).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (fibreNorm_nonneg ξ)
  have h : 4 / (fibreCoefficientMajorantRadius Cw / 16) =
      64 / fibreCoefficientMajorantRadius Cw := by ring
  rw [h]
  exact constructedScalarGraphPrice_linear Cw

include hCw he in
theorem constructedScalarRow_taylor_bound {δ : ℝ} (hδ : 0 < δ)
    (hδR : δ ≤ fibreCoefficientMajorantRadius Cw / 16)
    (n : ℕ) (ξ : Fin 2 → ℂ) (t : ℝ) :
    cellL2Norm (fibreHomogeneous ell ξ n t) ≤
      ENNReal.ofReal (constructedScalarGraphPrice Cw * (2 / δ) ^ n * fibreNorm ξ ^ n) := by
  rw [fibreRowReplacement_homogeneous_norm_eq ell _ he]
  apply (fibreAdjointRowCoefficients_homogeneous_le η Cw hη hCw G hG hv hw n ξ t).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (fibreNorm_nonneg ξ) n)
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hdiv : 2 / (fibreCoefficientMajorantRadius Cw / 16) ≤ 2 / δ :=
    div_le_div_of_nonneg_left (by norm_num) hδ hδR
  exact mul_le_mul (constructedScalarGraphPrice_four Cw)
    (pow_le_pow_left₀ (by positivity) hdiv n) (by positivity)
    (constructedScalarGraphPrice_pos Cw).le

end AVRegularity.CycleWords
end
