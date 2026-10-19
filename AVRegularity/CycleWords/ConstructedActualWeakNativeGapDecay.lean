-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleEvolution.CellLimitMoments
public import AVRegularity.CycleEvolution.FibreAdjointRowPairingNormalization
import AVRegularity.CycleWords.PlaneBlochEnergyRealStateIncrement
public import AVRegularity.CycleWords.ConstructedScalarRowBounds
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Native construction of the literal omitted geometry forcing. -/

theorem geometryError_remainder_native_forcing_uniform (Ks Kmax : ℕ)
    (CG : ℕ → ℝ) (hCG : ∀ r, 0 ≤ CG r) :
    ∃ CR CM CT : ℝ, 0 ≤ CR ∧ 0 ≤ CM ∧ 0 ≤ CT ∧
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {D : ℕ} {P : Type*} {Ctx : P → Type*},
    ∀ (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (_hπ : ∀ v, 0 < π v)
      (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax) (_hdesc : F.IsDescending K)
      (dom : F.Domain) (ν e E ρ : ℝ) (_hν : 0 < ν) (_he : 0 < e) (_hE : 0 < E) (_hρ : 0 < ρ)
      (Cmol : ℕ → ℝ) (Jmol : ℕ) (b₀ : ι → ι → ℝ) (_hKs : Ks + 1 ≤ Jmol)
      (_henv : IsMolecularEnvelope F π K dom ν e E ρ Cmol Jmol b₀) (_hmeas : F.IsTimeMeasurable)
      (_hb₀ : ∀ v u, 0 ≤ b₀ v u) (_hrow : ∀ v, ∑ u, b₀ v u ≤ 1) (_hcol : ∀ u, ∑ v, b₀ v u ≤ 1)
      (p : P) (c : Ctx p) (s a b ϖ ζ g : ℝ) (_hs : s ≠ 0) (_hϖ : 0 < ϖ)
      (_hscale : (ρ / e) * ϖ ≤ 1) (_hζ : 0 ≤ ζ) (_hζ1 : ζ ≤ 1) (_hg : 0 ≤ g)
      (_hδ : e / E = ζ * ϖ) (X0 phase : Vec 2)
      (_hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
      (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
      (_hGm : ∀ X k l, Measurable (fun t => G t X k l))
      (_hGs : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l))
      (_hGj : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, Ks + 1 ≤ r → r ≤ Ks + 1 + Kmax → ∀ y k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ CG r * g * (ζ * ϖ) ^ r)
      (_hGt : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ CG r * g * (e / E) ^ r)
      (J n : ℕ) (Z : ∀ (_ : Fin (J + 1)) v, ℝ → PlaneHk Set.univ (K v + 1) (h v))
      (_hZ : ∀ j v, MemLp (Z j v) 2 (volume.restrict (Set.Icc a b)))
      (_heR : ∀ j v, (∫⁻ t in Set.Icc a b,
        weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 (ρ / e) (K v) (Z j v t)) ≠ ⊤)
      (_heT : ∀ v, (∫⁻ t in Set.Icc a b,
        weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K v) (Z (Fin.last J) v t)) ≠ ⊤),
    ∃ V : ∀ v, ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
      (∀ v, MemLp (V v) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V v t) =ᵐ[volume]
        geometryErrorRemainderFlux F J Ks K p c G s (e / E) X0 phase (fun j u => Z j u t) v t) ∧
      (∀ m, (∑ v, ENNReal.ofReal ((π v)⁻¹) *
          ∫⁻ t in Set.Icc a b, weightedFactorialNormSq m ϖ 0 (ρ / e) (K v) (V v t)) ≤
        4 * (J + 1 : ℝ≥0∞) *
          (ENNReal.ofReal ((metricInsertionUniformPrice Kmax CM) ^ 2 * (g * ζ ^ (Ks + 1)) ^ 2) *
            (∑ j, ∫⁻ t in Set.Icc a b, (∑ v, ENNReal.ofReal ((π v)⁻¹) *
              weightedGradFactorialNormSq (m + (Ks + 1)) ϖ 0 (ρ / e) (K v) (Z j v t))) +
          ENNReal.ofReal ((originalRemainderGraphConstant (Ks + 1) Kmax CR Cmol * ζ ^ (Ks + 1)) ^ 2) *
            (∑ j, ∫⁻ t in Set.Icc a b, (∑ v, ENNReal.ofReal ((π v)⁻¹) *
              weightedGradFactorialNormSq (m + (Ks + 1)) ϖ 0 (ρ / e) (K v) (Z j v t)))) +
        2 * ENNReal.ofReal ((metricInsertionUniformPrice Kmax CT) ^ 2 * (g * ζ) ^ 2) *
          ∫⁻ t in Set.Icc a b, (∑ v, ENNReal.ofReal ((π v)⁻¹) *
            weightedGradFactorialNormSq (m + Ks) ϖ 0 (ρ / e) (K v) (Z (Fin.last J) v t))) := by
  classical
  obtain ⟨CR, hCR, hsource⟩ := originalRemainderFamily_native_flux_exists_uniform Ks Kmax
  obtain ⟨CM, hCM, hmetric⟩ := metricRemainder_native_insertion_exists_uniform Ks Kmax CG
  obtain ⟨CT, hCT, hterminal⟩ := metricTaylor_native_insertion_exists_uniform Ks Kmax CG hCG
  refine ⟨CR, CM, CT, hCR, hCM, hCT, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1 hg hδ
    X0 phase hwindow G hGm hGs hGj hGt J n Z hZ heR heT
  have hexs (j : Fin (J + 1)) := hsource F π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ hs hϖ hscale hζ hδ
    X0 phase hwindow n (Z j) (hZ j) (heR j)
  choose Vs hVs hVsv hVsb using hexs
  have hexm (j : Fin (J + 1)) (v : ι) := hmetric (K v) (hK v) G a b ϖ (ρ / e) ζ g
    hGm hGs hϖ (div_pos hρ he) hscale hζ hζ1 hg hGj n (Z j v) (hZ j v) (heR j v)
  choose Vm hVm hVme hVmv hVmb using hexm
  have hGst : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l) :=
    fun t ht k l => (hGs t ht k l).of_le (by exact_mod_cast (show Ks ≤ Ks + 1 + Kmax by omega))
  have hext (v : ι) := hterminal (K v) (hK v) G a b ϖ (ρ / e) (e / E) ζ g
    hGm hGst hϖ (div_pos hρ he) hscale hζ hζ1 hg hδ hGt n (Z (Fin.last J) v) (hZ (Fin.last J) v) (heT v)
  choose Vt hVt hVte hVtv hVtb using hext
  have hex (v : ι) := nativeRemainderForcing_assembly (volume.restrict (Set.Icc a b))
    (fun j => Vm j v) (fun j => Vs j v) (Vt v) (fun j => hVm j v) (fun j => hVs j v) (hVt v)
    (fun j t z => nativeMetricInsertionFlux (G t z - metricTaylor 0 Ks G t 0 z) (Z j v t) z)
    (fun j t z => originalRemainderNativeSourceFlux F Ks K p c s (e / E) X0 phase (fun u => Z j u t) v t z)
    (fun t z => nativeMetricInsertionFlux (metricTaylor 1 Ks G t 0 z) (Z (Fin.last J) v t) z)
    (fun j => hVmv j v) (fun j => hVsv j v) (hVtv v)
  choose V hV hVv hVb using hex
  refine ⟨V, hV, hVv, ?_⟩
  intro m
  let α := fun v => ENNReal.ofReal ((π v)⁻¹)
  let μ := volume.restrict (Set.Icc a b)
  have hm (j : Fin (J + 1)) := nativeMetric_mass_budget K Kmax hK α m (Ks + 1) ϖ (ρ / e)
    CM g (ζ ^ (Ks + 1)) hCM hg (pow_nonneg hζ _) μ (Vm j) (Z j) (hZ j) (fun v => hVmb j v m)
  have ht := nativeMetric_mass_budget K Kmax hK α m Ks ϖ (ρ / e)
    CT g ζ hCT hg hζ μ Vt (Z (Fin.last J)) (hZ (Fin.last J)) (fun v => hVtb v m)
  have hs (j : Fin (J + 1)) := hVsb j m
  have hs' (j : Fin (J + 1)) :
      (∑ v, α v * ∫⁻ t, weightedFactorialNormSq m ϖ 0 (ρ / e) (K v) (Vs j v t) ∂μ) ≤
      ENNReal.ofReal ((originalRemainderGraphConstant (Ks + 1) Kmax CR Cmol * ζ ^ (Ks + 1)) ^ 2) *
        ∫⁻ t, (∑ v, α v * weightedGradFactorialNormSq (m + (Ks + 1)) ϖ 0 (ρ / e) (K v) (Z j v t)) ∂μ := by
    rw [← weightedNativeMass_time_sum K α m ϖ 0 (ρ / e) μ (Vs j) (hVs j)]
    exact hs j
  have hmass := finiteRemainder_mass_budget α
    (fun v => ∫⁻ t, weightedFactorialNormSq m ϖ 0 (ρ / e) (K v) (V v t) ∂μ)
    (fun v => ∫⁻ t, weightedFactorialNormSq m ϖ 0 (ρ / e) (K v) (Vt v t) ∂μ)
    (fun j v => ∫⁻ t, weightedFactorialNormSq m ϖ 0 (ρ / e) (K v) (Vm j v t) ∂μ)
    (fun j v => ∫⁻ t, weightedFactorialNormSq m ϖ 0 (ρ / e) (K v) (Vs j v t) ∂μ)
    (Fintype.card (Fin (J + 1)) : ℝ≥0∞) (fun v => hVb v m ϖ 0 (ρ / e))
  have hms := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hm j)
  have hss := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs' j)
  simp_rw [← Finset.mul_sum] at hms hss
  have hh := hmass.trans (add_le_add
    (mul_le_mul_right (add_le_add hms hss) (4 * (Fintype.card (Fin (J + 1)) : ℝ≥0∞)))
    (mul_le_mul_right ht 2))
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, α, μ, mul_assoc] using hh

/-! Actual native remainder forcing with the response level decay inserted. -/

theorem geometryError_remainder_from_response_bounds_uniform (Ks Kmax J : ℕ)
    (CG Cmol : ℕ → ℝ) (hCG : ∀ r, 0 ≤ CG r) (Cresp : ℝ) (hCresp : 1 ≤ Cresp) :
    ∃ Cforce : ℝ, 1 ≤ Cforce ∧
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {D : ℕ} {P : Type*} {Ctx : P → Type*},
    ∀ (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (_hπ : ∀ v, 0 < π v)
      (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax) (_hdesc : F.IsDescending K)
      (dom : F.Domain) (ν e E ρ : ℝ) (_hν : 0 < ν) (_he : 0 < e) (_hE : 0 < E) (_hρ : 0 < ρ)
      (Jmol : ℕ) (b₀ : ι → ι → ℝ) (_hKs : Ks + 1 ≤ Jmol)
      (_henv : IsMolecularEnvelope F π K dom ν e E ρ Cmol Jmol b₀) (_hmeas : F.IsTimeMeasurable)
      (_hb₀ : ∀ v u, 0 ≤ b₀ v u) (_hrow : ∀ v, ∑ u, b₀ v u ≤ 1) (_hcol : ∀ u, ∑ v, b₀ v u ≤ 1)
      (p : P) (c : Ctx p) (s a b ϖ ζ g : ℝ) (_hs : s ≠ 0) (_hϖ : 0 < ϖ)
      (_hscale : (ρ / e) * ϖ ≤ 1) (_hζ : 0 ≤ ζ) (_hζ1 : ζ ≤ 1) (_hg : 0 ≤ g) (_hg1 : g ≤ 1)
      (_hδ : e / E = ζ * ϖ) (X0 phase : Vec 2)
      (_hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
      (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
      (_hGm : ∀ X k l, Measurable (fun t => G t X k l))
      (_hGs : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l))
      (_hGj : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, Ks + 1 ≤ r → r ≤ Ks + 1 + Kmax → ∀ y k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ CG r * g * (ζ * ϖ) ^ r)
      (_hGt : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ CG r * g * (e / E) ^ r)
      (n : ℕ) (Z : ∀ (_ : Fin (J + 1)) v, ℝ → PlaneHk Set.univ (K v + 1) (h v))
      (_hZ : ∀ j v, MemLp (Z j v) 2 (volume.restrict (Set.Icc a b)))
      (Ddata : ℝ≥0∞) (_hDdata : Ddata ≠ ⊤)
      (_hresp : ∀ j : Fin (J + 1), (∫⁻ t in Set.Icc a b,
        (∑ v, ENNReal.ofReal ((π v)⁻¹) *
          weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 (ρ / e) (K v) (Z j v t))) ≤
        (ENNReal.ofReal Cresp) ^ (j.val + 1) * (ENNReal.ofReal ((g * ζ) ^ 2)) ^ j.val * Ddata)
      (_hterminal : (∫⁻ t in Set.Icc a b,
        (∑ v, ENNReal.ofReal ((π v)⁻¹) *
          weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K v) (Z (Fin.last J) v t))) ≤
        (ENNReal.ofReal Cresp) ^ (J + 1) * (ENNReal.ofReal ((g * ζ) ^ 2)) ^ J * Ddata),
    ∃ V : ∀ v, ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
      (∀ v, MemLp (V v) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V v t) =ᵐ[volume]
        geometryErrorRemainderFlux F J Ks K p c G s (e / E) X0 phase (fun j u => Z j u t) v t) ∧
      ((∑ v, ENNReal.ofReal ((π v)⁻¹) *
        ∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V v t)) ≤
        ENNReal.ofReal Cforce * (ENNReal.ofReal ((ζ ^ (Ks + 1)) ^ 2) +
          (ENNReal.ofReal ((g * ζ) ^ 2)) ^ (J + 1)) * Ddata) := by
  classical
  obtain ⟨CR, CM, CT, hCR, hCM, hCT, hforcing⟩ := geometryError_remainder_native_forcing_uniform Ks Kmax CG hCG
  let Sprice := originalRemainderGraphConstant (Ks + 1) Kmax CR Cmol
  let Mprice := metricInsertionUniformPrice Kmax CM
  let Tprice := metricInsertionUniformPrice Kmax CT
  let Cforce := finiteResponseRemainderConstant J Cresp Mprice Sprice Tprice
  have hCf : 1 ≤ Cforce := finiteResponseRemainderConstant_ge_one J Cresp Mprice Sprice Tprice (zero_le_one.trans hCresp)
  refine ⟨Cforce, hCf, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1 hg hg1 hδ
    X0 phase hwindow G hGm hGs hGj hGt n Z hZ Ddata hDdata hresp hterminal
  let μ := volume.restrict (Set.Icc a b)
  let α := fun v => ENNReal.ofReal ((π v)⁻¹)
  let egrad := fun j : Fin (J + 1) => ∫⁻ t, (∑ v, α v *
    weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 (ρ / e) (K v) (Z j v t)) ∂μ
  let terminal := ∫⁻ t, (∑ v, α v *
    weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K v) (Z (Fin.last J) v t)) ∂μ
  have heR (j : Fin (J + 1)) (v : ι) :
      (∫⁻ t, weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 (ρ / e) (K v) (Z j v t) ∂μ) ≠ ⊤ := by
    have hf : egrad j ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) (hresp j)
    dsimp only [egrad] at hf
    rw [weightedNativeGradMass_time_sum K α (n + (Ks + 1)) ϖ 0 (ρ / e) μ (Z j) (hZ j)] at hf
    exact finitePositiveMass_ofReal_inv_component_ne_top π _ hπ hf v
  have heT (v : ι) :
      (∫⁻ t, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K v) (Z (Fin.last J) v t) ∂μ) ≠ ⊤ := by
    have hf : terminal ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hterminal
    dsimp only [terminal] at hf
    rw [weightedNativeGradMass_time_sum K α (n + Ks) ϖ 0 (ρ / e) μ (Z (Fin.last J)) (hZ (Fin.last J))] at hf
    exact finitePositiveMass_ofReal_inv_component_ne_top π _ hπ hf v
  obtain ⟨V, hV, hVv, hVb⟩ := hforcing F π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1 hg hδ
    X0 phase hwindow G hGm hGs hGj hGt J n Z hZ heR heT
  refine ⟨V, hV, hVv, ?_⟩
  let ε := ENNReal.ofReal ((g * ζ) ^ 2)
  let ζsq := ENNReal.ofReal ((ζ ^ (Ks + 1)) ^ 2)
  have hε : ε ≤ 1 := by
    have hgz : g * ζ ≤ 1 := (mul_le_mul_of_nonneg_right hg1 hζ).trans (by simpa only [one_mul] using hζ1)
    have hgz0 : 0 ≤ g * ζ := mul_nonneg hg hζ
    have hs : (g * ζ) ^ 2 ≤ 1 := by nlinarith
    exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by simp)
  have hm : ENNReal.ofReal (Mprice ^ 2 * (g * ζ ^ (Ks + 1)) ^ 2) ≤ ENNReal.ofReal (Mprice ^ 2) * ζsq :=
    metricRemainder_coefficient_le Mprice g (ζ ^ (Ks + 1)) hg hg1
  have hs : ENNReal.ofReal ((Sprice * ζ ^ (Ks + 1)) ^ 2) = ENNReal.ofReal (Sprice ^ 2) * ζsq :=
    ofReal_square_product Sprice (ζ ^ (Ks + 1))
  have ht : ENNReal.ofReal (Tprice ^ 2 * (g * ζ) ^ 2) = ENNReal.ofReal (Tprice ^ 2) * ε :=
    ENNReal.ofReal_mul (sq_nonneg Tprice)
  have hf : (∑ v, α v * ∫⁻ t, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V v t) ∂μ) ≤
      4 * (J + 1 : ℝ≥0∞) *
        ((ENNReal.ofReal (Mprice ^ 2) + ENNReal.ofReal (Sprice ^ 2)) * ζsq * ∑ j, egrad j) +
        2 * ENNReal.ofReal (Tprice ^ 2) * ε * terminal := by
    have hb := hVb n
    change (∑ v, α v * ∫⁻ t, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V v t) ∂μ) ≤
      4 * (J + 1 : ℝ≥0∞) *
        (ENNReal.ofReal (Mprice ^ 2 * (g * ζ ^ (Ks + 1)) ^ 2) * (∑ j, egrad j) +
          ENNReal.ofReal ((Sprice * ζ ^ (Ks + 1)) ^ 2) * (∑ j, egrad j)) +
        2 * ENNReal.ofReal (Tprice ^ 2 * (g * ζ) ^ 2) * terminal at hb
    rw [hs, ht] at hb
    have hh := hb.trans (add_le_add
      (mul_le_mul_right (add_le_add (mul_le_mul_left hm _) le_rfl) _) le_rfl)
    convert hh using 1; ring
  have hb := finiteResponse_remainder_budget J (ENNReal.ofReal Cresp) ε ζsq Ddata
    (ENNReal.ofReal (Mprice ^ 2)) (ENNReal.ofReal (Sprice ^ 2)) (ENNReal.ofReal (Tprice ^ 2))
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hCresp) hε egrad terminal _ hresp hterminal hf
  rw [finiteResponseRemainderConstant_ofReal J Cresp Mprice Sprice Tprice (zero_le_one.trans hCresp)] at hb
  exact hb

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Full-band contraction for every genuine public homogeneous real fibre solution. -/

theorem cellRaw_real_fibre_contraction (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hreal : ∀ i, (ξ i).im = 0)
    {s t : ℝ} (hst : s ≤ t) (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
      (fun _ _ => 0) (fun _ _ => 0) D) :
    cellL2Norm (cellValue D t) ≤ cellL2Norm (cellValue D s) := by
  have hh := cellRawHomogeneous_to_Hilbert hst (fun r _ => G r) hG v V hv.1 hb
    (fun j => (Real.sqrt η : ℂ) * ξ j) D (by
      simpa only [fibreCoefficients, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  have hn := hh.real_shift_contraction hst hG hv V hb _ (fibreBloch_real_star η ξ hreal)
  rw [cellL2Norm_eq_of_class _ _ (cellRawTrace_ae D t (hD.2.2.1 t ⟨hst, le_rfl⟩).1),
    cellL2Norm_eq_of_class _ _ (cellRawTrace_ae D s (hD.2.2.1 s ⟨le_rfl, hst⟩).1)]
  exact ENNReal.ofReal_le_ofReal hn

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! The actual Bloch reconstruction is a genuine real plane weak Hilbert time curve. -/

theorem planeBlochEnergyRealWeakCurve {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    let F := planeBlochEnergyField hab G hG v V hv.1 hb
      (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) f)
    PlaneWeakHilbertCurve a b
      (fun t => planeHkValueOperator 0 (cellEnergyPlaneRealTrace hab F t))
      (cellEnergyPlaneRealH1State hab F)
      (fun t => planeRealBlochGeneratorDual (G t) v hv t C (hC t)
        (cellEnergyPlaneRealH1State hab F t)) := by
  let F := planeBlochEnergyField hab G hG v V hv.1 hb
    (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) f)
  refine ⟨?_, Lp.memLp _, ?_, ?_, ?_⟩
  · exact ((planeHkValueOperator (E := ℝ) 0).continuous.comp
      (cellEnergyPlaneRealTrace_continuous hab F)).continuousOn
  · exact planeRealBlochGeneratorDual_timeMemLp _ G hG v hv C hCpos.le hC _ (Lp.memLp _)
  · filter_upwards [cellEnergyPlaneRealTrace_alignment hab F] with t ht
    rw [← ht, planeHkValueOperator_truncate]
  · intro s hs t ht hst φ
    simp only [cellEnergyPlaneRealTrace, planeL2ZeroCarrier_value]
    change inner ℝ
        (planeComplexRealPartL2
          ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
            ((cellEnergyTraceAtCLM a b (projIcc a b hab t)).compLp F)))
        (planeHkValueOperator 1 φ) -
      inner ℝ
        (planeComplexRealPartL2
          ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
            ((cellEnergyTraceAtCLM a b (projIcc a b hab s)).compLp F)))
        (planeHkValueOperator 1 φ) = _
    rw [projIcc_of_mem hab ht, projIcc_of_mem hab hs]
    have he := planeBlochEnergyRealStateIncrement hab G hG v hv V hb C hCpos hC f
      ⟨s, hs⟩ ⟨t, ht⟩ hst φ
    apply he.trans
    simp only [planeRealBlochGeneratorDual_pair]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev Filter
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped Topology
namespace AVRegularity.CycleWords

/-! Data of an actual weak scalar multiplier Galerkin limit. -/

structure CellScalarMultiplierLimitData
    (a b η : ℝ) (hab : a ≤ b) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ)
    (u₀ : ComplexCellL2) where
  curve : ∀ N, ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N)
  equation : ∀ N, IsLinearIntegralSolution
    ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ))
    0 (cellGalerkinL2Initial N u₀) a b (extendCurve hab (curve N))
  stateLp : ∀ N, MemLp (fun t => (extendCurve hab (curve N) t).val)
    2 (volume.restrict (Icc a b))
  budget : ℝ
  norm_bound : ∀ N, ‖(stateLp N).toLp (fun t => (extendCurve hab (curve N) t).val)‖ ≤ budget
  limit : CellBochnerH1 a b
  subsequence : ℕ → ℕ
  monotone : StrictMono subsequence
  weak : ∀ ell : CellBochnerH1 a b →L[ℝ] ℝ,
    Tendsto (fun n => ell ((stateLp (subsequence n)).toLp
      (fun t => (extendCurve hab (curve (subsequence n)) t).val))) atTop (𝓝 (ell limit))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedFullTrace_native_polynomial_smoothing (J : ℕ)
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a ≤ b)
    (initial : ComplexCellL2)
    (D : CellGalerkinLimitData a b hab
      ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩ hG V hv.1 hb 0 0 initial)
    (U : ℝ → ComplexCellL2)
    (hU : CellWeakHilbertCurve a b U D.limit
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        hG V hv.1 hb t (D.limit t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a ≤ 1) (t : ℝ) (htI : t ∈ Icc a b)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let P := (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
    peFactor η ^ (2 * J)
  have hM := constructedNativeWindowPrice_pos J R k Cw hR ((norm_nonneg _).trans (hk a)) hCw
  have hP : 0 ≤ P := by
    unfold P
    exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _)
  apply CellGalerkinLimitData.full_trace_native_of_uniform_bound hab _ hG V k hv.1 hb hκ hk initial D U hU hinitial J t htI
    (P * (Real.exp (cellFullZerothGrowth η Cw ξ k) * ‖initial‖ ^ 2))
    (mul_nonneg hP (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
  intro N
  have he := constructedFullGalerkin_native_polynomial_smoothing J N hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab
    (extendCurve hab (D.curve N)) (CellGalerkinLimitData.full_homogeneous_strongTime hab _ hG V hv.1 hb initial D N) hwindow t ht htI.2
  have hi : ‖cellGalerkinValue N (extendCurve hab (D.curve N) a)‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
    rw [D.initial_value N]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (cellGalerkinL2Initial_norm_le N initial)
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le) hP)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Actual finite scalar multiplier traces have a common L2 bound on their whole window. -/

theorem CellScalarMultiplierLimitData.uniform_trace_bound
    (a b η : ℝ) (hab : a ≤ b) (hη0 : 0 ≤ η) (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hκm : MemLp κ ⊤ (volume.restrict (Icc a b)))
    (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k)
    (hsmall : ∀ t ∈ Icc a b,
      264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) + 2 * ‖κ t‖ + 1 ≤ 2)
    (L : ℝ) (hL : 0 ≤ L)
    (hκq : ∀ t ∈ Icc a b, ‖κ t‖ ≤ L * fibreNorm ξ ^ 2)
    (hξ1 : fibreNorm ξ ≤ 1) (hwsmall : Cw * fibreNorm ξ ≤ 1)
    (u₀ : ComplexCellL2)    (D : CellScalarMultiplierLimitData a b η hab G hv ξ hc A hA hb κ u₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N t, t ∈ Icc a b →
      ‖cellGalerkinValue N (extendCurve hab (D.curve N) t)‖ ^ 2 ≤ E := by
  let B := ‖u₀ - cellConstantCLM 1‖ ^ 2 + (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2 / 2
  have hB : 0 ≤ B := add_nonneg (sq_nonneg _)
    (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num))
  refine ⟨2 * Real.exp (4 * (b - a)) * B + 2,
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hB) (by norm_num), ?_⟩
  intro N t ht
  let Y := extendCurve hab (D.curve N)
  have hn := cellGalerkin_initial_correction_norm_le hab N
    ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ))
    0 Y u₀ (D.equation N)
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn
  have hinitial := add_le_add hs (le_refl ((Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2 / 2))
  have hc0 := (cellTransverseGalerkin_correction_local_bounds N a b η hab hη0 hη G hG hv ξ
    hc A hA hb κ Cw hCw hw hκm k hκ hsmall L hL hκq hξ1 hwsmall
    (cellGalerkinL2Initial N u₀) (D.curve N) (D.equation N) a t ht.1
    (fun _ hu => ⟨hu.1, hu.2.trans ht.2⟩)).1
  have hc1 := hc0.trans (mul_le_mul_of_nonneg_left hinitial (Real.exp_pos _).le)
  have hc2 : ‖cellGalerkinValue N (Y t - cellGalerkinConstant N 1)‖ ^ 2 ≤
      Real.exp (4 * (b - a)) * B :=
    hc1.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by linarith only [ht.2])) hB)
  have hadd := native_norm_add_sq_le (cellGalerkinValue N (Y t - cellGalerkinConstant N 1))
    (cellConstantCLM 1)
  have hv0 : cellGalerkinValue N (Y t - cellGalerkinConstant N 1) + cellConstantCLM 1 =
      cellGalerkinValue N (Y t) := by
    simp only [map_sub, cellGalerkinConstant_value, sub_add_cancel]
  rw [hv0, cellConstantCLM_norm, norm_one, one_pow] at hadd
  exact hadd.trans ((mul_le_mul_of_nonneg_left (add_le_add hc2 (le_refl (1 : ℝ)))
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A periodic native entrance propagates on a short full-equation window without losing reserves. -/

theorem constructedActualWeak_native_short_propagation (J : ℕ)
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      hG V hv.1 hb t (slice t) 0 0))
    (initial : TorusHk J ℂ) (hi : U a = torusHkValueCLM initial)
    (hshort : (constructedNativeWindowPrice J R k Cw *
      peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * (b - a) ≤ 1) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧
      ‖W‖ ^ 2 ≤ Real.exp 1 * ‖initial‖ ^ 2 := by
  apply cellActualWeak_native_of_finite_bound hab _ hG V k hv.1 hb hκ hk
    (torusHkValueCLM initial) U slice hU hi J b ⟨hab.le, le_rfl⟩
    (Real.exp 1 * ‖initial‖ ^ 2) (mul_nonneg (Real.exp_pos 1).le (sq_nonneg _))
  intro N y hy hyinit
  have he := (constructedFullGalerkin_native_window J N hΛ hζ hν hr y₀ hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ κ k hk hab.le y hy hshort J le_rfl).1
  have hi' : cellGalerkinNativeLiftCLM N J (y a) =
      cellGalerkinNativeLiftCLM N J (cellGalerkinL2Initial N (torusHkValueCLM initial)) := by
    apply TorusHk.ext_value
    change torusHkValueCLM (cellGalerkinNativeLiftCLM N J (y a)) =
      torusHkValueCLM (cellGalerkinNativeLiftCLM N J
        (cellGalerkinL2Initial N (torusHkValueCLM initial)))
    simpa only [cellGalerkinNativeLiftCLM_value] using hyinit
  have hn : ‖cellGalerkinNativeLiftCLM N J (y a)‖ ≤ ‖initial‖ := by
    rw [hi']
    exact cellGalerkinHigherInitial_norm_le N J initial
  exact he.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hn 2) (Real.exp_pos 1).le)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The actual reversed Bloch evolution supplies backward scalar plane adjoint tests. -/

theorem planeBlochReversedDrift_bound
    {v : ℝ → Vec 2 → Vec 2} {V : ℝ}
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) :
    ∀ t x, ∑ i, (-v (-t) x) i ^ 2 ≤ V ^ 2 := by
  intro t x
  simpa only [Pi.neg_apply, neg_sq] using hb (-t) x

def planeBlochBackwardRealField {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    Lp (CellEnergySpace (-b) (-a)) 2 centeredPlaneFrequencyMeasure :=
  planeBlochEnergyField (neg_le_neg hab) (fun t => G (-t)) (cellMetric_timeReverse hG)
    (fun t x => -v (-t) x) V (cellDrift_timeReverse hv).1 (planeBlochReversedDrift_bound hb)
    (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) (ofRealL2 volume f))

theorem planeBlochBackwardReal_weakCurve {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (Cr : ℝ) (hCrpos : 0 < Cr)
    (hCr : ∀ t i z, ‖cellDriftTorusSymbol (fun r x => -v (-r) x) t i z‖ ≤ Cr)
    (C' : ℝ) (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun r x => -v r x) t i z‖ ≤ C')
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    let F := planeBlochBackwardRealField hab G hG v hv V hb f
    PlaneWeakHilbertCurve a b
      (fun t => planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab) F (-t)))
      (fun t => cellEnergyPlaneRealH1State (neg_le_neg hab) F (-t))
      (fun t => -planeRealBlochGeneratorDual (G t) (fun t x => -v t x)
        (cellDrift_neg hv) t C' (hC' t)
        (cellEnergyPlaneRealH1State (neg_le_neg hab) F (-t))) := by
  exact planeWeakCurve_reflectedAdjoint G v hv Cr C' hCr hC'
    (planeBlochEnergyRealWeakCurve (neg_le_neg hab) (fun t => G (-t))
      (cellMetric_timeReverse hG) (fun t x => -v (-t) x) (cellDrift_timeReverse hv)
      V (planeBlochReversedDrift_bound hb) Cr hCrpos hCr (ofRealL2 volume f))

theorem planeBlochBackwardReal_terminal {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab)
      (planeBlochBackwardRealField hab G hG v hv V hb f) (-b)) = f := by
  unfold planeBlochBackwardRealField
  rw [planeBlochEnergyRealTrace_initial (neg_le_neg hab) (fun t => G (-t))
    (cellMetric_timeReverse hG) (fun t x => -v (-t) x) V
    (cellDrift_timeReverse hv).1 (planeBlochReversedDrift_bound hb) f,
    planeL2ZeroCarrier_value]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! An arbitrary positive short step gives actual native smoothing without an entrance Sobolev premise. -/

theorem constructedActualWeak_native_smoothing_of_step (J : ℕ)
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        hG V hv.1 hb t (slice t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hshort : (constructedNativeWindowPrice J R k Cw *
      peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * δ ≤ 1)
    (hfit : J * δ ≤ b - a) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := cellFullZerothGrowth η Cw ξ k
  let P := (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J
  have hP : 0 ≤ P := pow_nonneg (div_nonneg (by positivity) hδ.le) _
  have hA : 0 ≤ A := cellFullZerothGrowth_nonneg η Cw hCw ξ k ((norm_nonneg _).trans (hk a))
  apply cellActualWeak_native_of_finite_bound hab _ hG V k hv.1 hb hκ hk
    initial U slice hU hinitial J b ⟨hab.le, le_rfl⟩
    (P * (Real.exp A * ‖initial‖ ^ 2))
    (mul_nonneg hP (mul_nonneg (Real.exp_pos A).le (sq_nonneg _)))
  intro N y hy hyinit
  let B := Real.exp A * ‖cellGalerkinValue N (y a)‖ ^ 2
  have hzero : ∀ t ∈ Icc a b, ‖cellGalerkinValue N (y t)‖ ^ 2 ≤ B := by
    intro t ht
    have he := cellFullGalerkin_zeroth_propagation N η Cw hCw G hG hv hw V hb ξ κ k hk hab.le y hy t ht
    have ht1 : t - a ≤ 1 := (sub_le_sub_right ht.2 a).trans hwindow
    have hx : Real.exp (A * (t - a)) ≤ Real.exp A := Real.exp_le_exp.mpr
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 hA)
    exact he.trans (by simpa only [B, mul_comm] using
      mul_le_mul_of_nonneg_left hx (sq_nonneg ‖cellGalerkinValue N (y a)‖))
  have he := constructedFullGalerkin_native_smoothing J N hΛ hζ hν hr y₀ hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ κ k hk hab.le y hy δ B hδ
    (mul_nonneg (Real.exp_pos A).le (sq_nonneg _)) hshort hzero b
    (by linarith only [hfit]) le_rfl
  have hi : ‖cellGalerkinValue N (y a)‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
    rw [hyinit]
    exact pow_le_pow_left₀ (norm_nonneg _) (cellGalerkinL2Initial_norm_le N initial) 2
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hi (Real.exp_pos A).le) hP)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedActualWeak_native_polynomial_smoothing (J : ℕ)
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        hG V hv.1 hb t (slice t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a ≤ 1) (t : ℝ) (htI : t ∈ Icc a b)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  let C : CellCoefficients :=
    ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
      fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
  obtain ⟨D⟩ := cellGalerkin_actual_limit_data hab.le C hG V k hv.1 hb hκ hk
    0 0 measurable_zero measurable_zero (by simp [cellL2Norm]) (by simp [cellL2Norm]) initial
  obtain ⟨Z, hZ, hi⟩ := D.exists_continuous_trace hab k hκ hk (by apply MemLp.zero) (by apply MemLp.zero)
  have hz : CellWeakHilbertCurve a b (extendCurve hab.le Z) D.limit
      (fun t => cellDualDerivative C hG V hv.1 hb t (D.limit t) 0 0) := by
    change CellWeakHilbertCurve a b (extendCurve hab.le Z) D.limit
      (fun t => cellDualDerivative C hG V hv.1 hb t (D.limit t)
        (cellSourceSlice 0 t) (fun j => cellSourceSlice (fun r x => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) t)) at hZ
    simpa only [PiLp.zero_apply, Pi.zero_def, cellSourceSlice_zero] using hZ
  have heq := cellActualWeak_unique hab.le C hG V k hv.1 hb hk 0 0 U
    (extendCurve hab.le Z) slice D.limit hU hz (hinitial.trans hi.symm) t htI
  obtain ⟨W, hwv, hwb⟩ := constructedFullTrace_native_polynomial_smoothing J hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab.le initial D
    (extendCurve hab.le Z) hz hi hwindow t htI ht
  exact ⟨W, hwv.trans heq.symm, hwb⟩

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedReflectedTrace_native_polynomial_smoothing (J : ℕ)
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a ≤ b)
    (initial : ComplexCellL2)
    (D : CellGalerkinLimitData a b hab
      ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩ (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) 0 0 initial)
    (U : ℝ → ComplexCellL2)
    (hU : CellWeakHilbertCurve a b U D.limit
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (D.limit t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a ≤ 1) (t : ℝ) (htI : t ∈ Icc a b)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let P := (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
    peFactor η ^ (2 * J)
  have hM := constructedNativeWindowPrice_pos J R k Cw hR ((norm_nonneg _).trans (hk a)) hCw
  have hP : 0 ≤ P := by
    unfold P
    exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _)
  apply CellGalerkinLimitData.full_trace_native_of_uniform_bound hab _ (cellMetric_timeReverse hG) V k (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) hκ hk initial D U hU hinitial J t htI
    (P * (Real.exp (cellFullZerothGrowth η Cw ξ k) * ‖initial‖ ^ 2))
    (mul_nonneg hP (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
  intro N
  have he := constructedReflectedGalerkin_native_polynomial_smoothing J N hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab
    (extendCurve hab (D.curve N)) (CellGalerkinLimitData.full_homogeneous_strongTime hab _ (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) initial D N) hwindow t ht htI.2
  have hi : ‖cellGalerkinValue N (extendCurve hab (D.curve N) a)‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
    rw [D.initial_value N]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (cellGalerkinL2Initial_norm_le N initial)
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le) hP)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Subtraction of a fixed multiple of the actual reversed graph solves the full reversed equation. -/

theorem canonicalAdjoint_mode_subtraction_weak (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve (-b) (-a) U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -v (-s) x, fun i => (Real.sqrt η : ℂ) * -ξ i, 0⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (c : ℂ) :
    let D := fibreAdjointGraphRaw η Cw hη G hG hv hw ξ
    let phase := fun τ => Complex.exp (∫ s in -b..τ, fibreAdjointGraphSymbol η Cw hη G hG hv hw ξ s)
    CellWeakHilbertCurve (-b) (-a)
      (fun τ => U τ - cellScalarCLM c (cellScalarCLM (phase τ)
        (cellRawTrace D τ + cellConstantCLM 1)))
      (fun τ => slice τ - cellH1Scalar c (cellH1Scalar (phase τ)
        (cellH1Slice D τ + cellH1One)))
      (fun τ => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -v (-s) x, fun i => (Real.sqrt η : ℂ) * -ξ i, 0⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) τ
        (slice τ - cellH1Scalar c (cellH1Scalar (phase τ) (cellH1Slice D τ + cellH1One))) 0 0) := by
  have hbref : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2 := by
    intro s x
    simpa only [Pi.neg_apply, neg_sq] using hb (-s) x
  have hξref : fibreNorm (fun i => -ξ i) ≤ fibreCoefficientMajorantRadius Cw := by
    simpa only [fibreNorm_neg] using hξ
  have hR := fibreCoefficientFamily_graph_homogeneous_evolution η Cw hη0 hη hCw
    (fun s => G (-s)) (cellMetric_timeReverse hG) (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_mean_zero hm) (cellDrift_timeReverse_scaled_bound hw)
    V hbref (fun i => -ξ i) hξref (by linarith : -b ≤ -a)
  have hc := hR.homogeneous_complex_scalar (fun s _ => G (-s)) (cellMetric_timeReverse hG)
    (fun s x => -v (-s) x) V (cellDrift_timeReverse hv).1 hbref
    (fun i => (Real.sqrt η : ℂ) * -ξ i) c
  have hh := cellWeakActual_sub_same_source
    ⟨fun s _ => G (-s), fun s x => -v (-s) x, fun i => (Real.sqrt η : ℂ) * -ξ i, 0⟩
    (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1 hbref 0 0 _ _ _ _ hU hc
  simpa only [fibreAdjointGraphRaw, fibreAdjointGraphSymbol,
    show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using hh

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev Filter
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped Topology
namespace AVRegularity.CycleWords

/-! Full test moments of actual scalar multiplier approximations converge to their PDE primitives. -/

theorem CellScalarMultiplierLimitData.moment_primitive_tendsto
    (a b η : ℝ) (hab : a ≤ b) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ)
    (u₀ : ComplexCellL2)    (D : CellScalarMultiplierLimitData a b η hab G hv ξ hc A hA hb κ u₀)
    (hG : IsCellMetric (fun t _ => G t)) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hκm : MemLp κ ⊤ (volume.restrict (Icc a b))) (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k)
    (z : TorusHk 1 ℂ) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun n => inner ℝ
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
      (torusHkValueCLM z)) atTop
      (𝓝 (inner ℝ u₀ (torusHkValueCLM z) + ∫ r in a..t,
        cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ r (D.limit r) z)) := by
  let B := cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ
  obtain ⟨M, hM, hMb⟩ := cellScalarMultiplierForm_uniform_bound η Cw hCw G hG hv hw ξ κ k hκ
  have hm := cellScalarMultiplierForm_pairing_aestronglyMeasurable η Cw hCw G hG hv hw ξ κ
    hκm.aestronglyMeasurable
  let L := cellBoundedFormIntegralTestCLM (a := a) (b := b) ⟨le_rfl, hab⟩ ht ht.1 B hm M hM hMb hab
  have htest := (L.continuous.tendsto z).comp
    ((galerkinProj_tendsto z).comp D.monotone.tendsto_atTop)
  have he := cellWeak_eval_perturbed_test
    (fun n => (D.stateLp (D.subsequence n)).toLp
      (fun r => (extendCurve hab (D.curve (D.subsequence n)) r).val)) D.limit D.budget
    (fun n => D.norm_bound (D.subsequence n)) D.weak
    (fun n => L (galerkinProj (D.subsequence n) z)) (L z) htest
  change Tendsto (fun n => cellBoundedFormIntegralCLM a b a t B hm M hM hMb
    (galerkinProj (D.subsequence n) z) ((D.stateLp (D.subsequence n)).toLp
      (fun r => (extendCurve hab (D.curve (D.subsequence n)) r).val))) atTop
    (𝓝 (cellBoundedFormIntegralCLM a b a t B hm M hM hMb z D.limit)) at he
  simp only [cellBoundedFormIntegralCLM_apply ⟨le_rfl, hab⟩ ht ht.1,
    cellBoundedFormIntegralCLM_apply_class ⟨le_rfl, hab⟩ ht ht.1] at he
  have hinit : Tendsto (fun n => inner ℝ u₀
      (torusHkValueCLM (galerkinProj (D.subsequence n) z))) atTop
      (𝓝 (inner ℝ u₀ (torusHkValueCLM z))) :=
    (tendsto_const_nhds (x := u₀)).inner
      (((torusHkValueCLM (E := ℂ) (K := 1)).continuous.tendsto z).comp
        ((galerkinProj_tendsto z).comp D.monotone.tendsto_atTop))
  apply (hinit.add he).congr'
  filter_upwards with n
  exact (cellTransverseGalerkin_full_test_primitive (D.subsequence n) a b η hab G hG hv ξ
    hc A hA hb κ Cw hCw hw hκm k hκ u₀ (D.curve (D.subsequence n))
    (D.equation (D.subsequence n)) z t ht).symm

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A proved L2 gap and periodic native entrance yield higher full-equation decay. -/

theorem constructedActualWeak_native_gap_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      hG V hv.1 hb t (slice t) 0 0))
    (initial : TorusHk J ℂ) (hi : U a = torusHkValueCLM initial)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hgap : ∀ s ∈ Icc a b, ‖U s‖ ^ 2 ≤ Real.exp (-γ * (s - a)) * ‖U a‖ ^ 2) :
    let δ₀ := constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν)
    let P := (Real.exp 1 * (2 * Real.exp 1) / (δ₀ / (J : ℝ))) ^ J
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧ ‖W‖ ^ 2 ≤
      (Real.exp γ * (Real.exp 1 + P * Real.exp
        (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k))) *
        Real.exp (-γ * (b - a)) * ‖initial‖ ^ 2 := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let δ₀ := constructedNativeSmoothingTime J R k Cw η
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  let P := (Real.exp 1 * (2 * Real.exp 1) / (δ₀ / (J : ℝ))) ^ J
  let Z := cellFullZerothGrowth η Cw ξ k
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hjpos : 0 < (J : ℝ) := lt_of_lt_of_le (by norm_num) hj
  have hd : 0 < δ₀ := constructedNativeSmoothingTime_pos J R k Cw η hR
    ((norm_nonneg _).trans (hk a)) hCw
  have hd1 : δ₀ ≤ 1 := by
    have he := constructedNativeSmoothingTime_orders_le_one J R k Cw η hR
      ((norm_nonneg _).trans (hk a)) hCw
    have hh : δ₀ ≤ (J : ℝ) * δ₀ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hj hd.le
    exact hh.trans he
  have hA : 0 ≤ A := mul_nonneg (constructedNativeWindowPrice_pos J R k Cw hR
    ((norm_nonneg _).trans (hk a)) hCw).le (sq_nonneg _)
  have hbudget : A * δ₀ ≤ 1 := constructedNativeSmoothingTime_budget J R k Cw η hR
    ((norm_nonneg _).trans (hk a)) hCw
  have hP : 0 ≤ P := pow_nonneg (div_nonneg (by positivity) (div_pos hd hjpos).le) _
  have hx (s : ℝ) (hs : b - s ≤ 1) :
      Real.exp (-γ * (s - a)) ≤ Real.exp γ * Real.exp (-γ * (b - a)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_left hs hγ
    nlinarith only [he]
  by_cases hsmall : b - a ≤ δ₀
  · obtain ⟨W, hwv, hwb⟩ := constructedActualWeak_native_short_propagation J hΛ hζ hν hr
      y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab U slice hU initial hi
      ((mul_le_mul_of_nonneg_left hsmall hA).trans hbudget)
    refine ⟨W, hwv, hwb.trans ?_⟩
    have he : (1 : ℝ) ≤ Real.exp γ * Real.exp (-γ * (b - a)) := by
      simpa only [sub_self, mul_zero, Real.exp_zero] using hx a (hsmall.trans hd1)
    have hp : Real.exp 1 ≤ Real.exp 1 + P * Real.exp Z :=
      le_add_of_nonneg_right (mul_nonneg hP (Real.exp_pos Z).le)
    have hm := mul_le_mul hp he (by norm_num : (0 : ℝ) ≤ 1)
      ((Real.exp_pos 1).le.trans hp)
    have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖initial‖)
    convert hm' using 1 <;> ring
  · let s := b - δ₀
    have has : a ≤ s := by dsimp only [s]; linarith only [hsmall]
    have hsb : s < b := by dsimp only [s]; linarith only [hd]
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc has le_rfl
    have hstep : 0 < δ₀ / (J : ℝ) := div_pos hd hjpos
    have hδ : δ₀ / (J : ℝ) ≤ δ₀ := div_le_self hd.le hj
    have hfit : (J : ℝ) * (δ₀ / (J : ℝ)) ≤ b - s := by
      dsimp only [s]
      rw [mul_div_cancel₀ δ₀ hjpos.ne']
      linarith
    obtain ⟨W, hwv, hwb⟩ := constructedActualWeak_native_smoothing_of_step J hΛ hζ hν hr
      y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hsb (U s) U slice
      (hU.mono hsub) rfl (by dsimp only [s]; linarith only [hd1])
      (δ₀ / (J : ℝ)) hstep ((mul_le_mul_of_nonneg_left hδ hA).trans hbudget) hfit
    refine ⟨W, hwv, hwb.trans ?_⟩
    have hiNorm : ‖U a‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
      rw [hi]
      exact pow_le_pow_left₀ (norm_nonneg _) (torusHigherValue_norm_le initial) 2
    have hg := hgap s ⟨has, hsb.le⟩
    have hxs := hx s (by dsimp only [s]; linarith only [hd1])
    have hupper : ‖U s‖ ^ 2 ≤
        (Real.exp γ * Real.exp (-γ * (b - a))) * ‖initial‖ ^ 2 :=
      hg.trans (mul_le_mul hxs hiNorm (sq_nonneg _)
        (mul_nonneg (Real.exp_pos γ).le (Real.exp_pos _).le))
    have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hupper (Real.exp_pos Z).le) hP
    have hp : P * Real.exp Z ≤ Real.exp 1 + P * Real.exp Z :=
      le_add_of_nonneg_left (Real.exp_pos 1).le
    have hf := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (mul_nonneg (Real.exp_pos γ).le
        (Real.exp_pos (-γ * (b - a))).le) (sq_nonneg ‖initial‖))
    exact hm.trans (by convert hf using 1 <;> ring)

end AVRegularity.CycleWords
end
