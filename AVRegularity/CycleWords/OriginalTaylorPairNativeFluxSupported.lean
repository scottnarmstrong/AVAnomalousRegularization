-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.OriginalRemainderPrice
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The original Taylor price sum is bounded by the molecular envelope without a constituent count. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def originalTaylorPrice (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (Ks Kmax : ℕ)
    (dom : F.Domain) (ν e E ρ CT : ℝ) (v u : ι) (α : OriginalSourceIndex F v u) : ℝ :=
  Real.sqrt (multiplicationDensityBudget (K v)) * CT *
    (∑ r ∈ Finset.range (Ks + 1),
      molecularTaylorPrefixPrice F K Kmax dom ν e E ρ v u α.1 α.2.1.1 α.2.2.1 r) *
        ‖(F.identity v u α.1).map‖

theorem originalTaylorPrice_nonneg (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (Ks Kmax : ℕ) (dom : F.Domain) (ν e E ρ CT : ℝ)
    (hν : 0 ≤ ν) (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hCT : 0 ≤ CT)
    (v u : ι) (α : OriginalSourceIndex F v u) :
    0 ≤ originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α := by
  unfold originalTaylorPrice
  apply mul_nonneg _ (norm_nonneg _)
  apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCT)
  apply Finset.sum_nonneg
  intro r _
  unfold molecularTaylorPrefixPrice
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE _))
    (molecularRealPrice_nonneg ν ρ hν hρ _ _ _)

theorem originalTaylorPrice_sum_envelope_le (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (Ks Kmax : ℕ) (dom : F.Domain)
    (ν e E ρ CT : ℝ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ) (hCT : 0 ≤ CT)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) (hKs : Ks ≤ J)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b) (v u : ι) (hb : 0 ≤ b v u) :
    Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) ≤
        (2 * Real.sqrt (multiplicationDensityBudget (K v)) * CT * (Kmax.factorial : ℝ) ^ 2 *
          (∑ r ∈ Finset.range (Ks + 1), |C r|)) * b v u := by
  classical
  let q := fun (γ : F.Γ v u) d (I : DerivativeWord2 (d - 1)) r =>
    E ^ r * molecularRealPrice ν ρ (K v) (d - 2)
      (molecularJet ρ e (K v) r (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  have hsum : (∑ α : OriginalSourceIndex F v u,
      originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) =
      (2 * Real.sqrt (multiplicationDensityBudget (K v)) * CT * (Kmax.factorial : ℝ) ^ 2) *
        ∑ r ∈ Finset.range (Ks + 1), ∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ *
          ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1), q γ d I r := by
    have hp (α : OriginalSourceIndex F v u) :
        originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α =
          (Real.sqrt (multiplicationDensityBudget (K v)) * CT * (Kmax.factorial : ℝ) ^ 2) *
            (∑ r ∈ Finset.range (Ks + 1), q α.1 α.2.1.1 α.2.2.1 r) * ‖(F.identity v u α.1).map‖ := by
      unfold originalTaylorPrice molecularTaylorPrefixPrice
      dsimp only [q]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      ring
    simp_rw [hp]
    have hh := originalConstituent_price_sum_eq F v u
      (fun γ d I => ∑ r ∈ Finset.range (Ks + 1), q γ d I r)
      (Real.sqrt (multiplicationDensityBudget (K v)) * CT * (Kmax.factorial : ℝ) ^ 2)
    rw [hh]
    rw [show 2 * (Real.sqrt (multiplicationDensityBudget (K v)) * CT * (Kmax.factorial : ℝ) ^ 2) =
      2 * Real.sqrt (multiplicationDensityBudget (K v)) * CT * (Kmax.factorial : ℝ) ^ 2 by ring]
    congr 1
    have hi (γ : F.Γ v u) (d : ℕ) :
        (∑ I : DerivativeWord2 (d - 1), ∑ r ∈ Finset.range (Ks + 1), q γ d I r) =
          ∑ r ∈ Finset.range (Ks + 1), ∑ I : DerivativeWord2 (d - 1), q γ d I r :=
      Finset.sum_comm
    have hg (γ : F.Γ v u) :
        ‖(F.identity v u γ).map‖ *
          (∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
            ∑ r ∈ Finset.range (Ks + 1), q γ d I r) =
        ∑ r ∈ Finset.range (Ks + 1), ‖(F.identity v u γ).map‖ *
          ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1), q γ d I r := by
      simp_rw [hi]
      rw [Finset.sum_comm, Finset.mul_sum]
    simp_rw [hg]
    exact Finset.sum_comm
  have hh := Finset.sum_le_sum (fun r hr => molecularRealEnvelope_scaled_sum_le F π K dom ν e E ρ
    hν hE hρ C J b henv v u hb r ((Nat.le_of_lt_succ (Finset.mem_range.mp hr)).trans hKs))
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hh
  have hm := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ 2 * Real.sqrt (multiplicationDensityBudget (K v)) * CT * (Kmax.factorial : ℝ) ^ 2)
  rw [hsum]
  convert hm using 1 <;> ring

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Full higher energy for the signed time-reflected constructed drift. -/

def constructedReflectedFullGeneratorCLM (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) :
    TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  torusHigherStrongDiffusionCLM K (fun s => G (-s)) θ t +
    constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ (-t) +
    (torusHigherScalarCLM K (κ t)).comp (truncateTorusHk (by omega : K ≤ K + 2))

theorem constructedReflectedFullGenerator_smooth_energy (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : IsZ2Periodic f) :
    2 * inner ℝ
        (constructedReflectedFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
          (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * finiteSmoothHigherGradientEnergy K f hf hp ≤
      constructedHigherEnergyGrowth K R (ν / ocMeanFlux α q Λ ζ m ν) k *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  let U := finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let W := finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp
  let B := ‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖
  let A := constructedAdvectionAdjacentPrice K R * peFactor (ν / ocMeanFlux α q Λ ζ m ν)
  have ha := constructedHigherAdvectionCLM_adjacent_polynomial_bound K hΛ hζ hν hr y₀ hv θ R hθ (-t) W
  rw [finiteSmoothPeriodicHk_truncate (K := K + 1) (L := K + 2) (by omega) f hf hp] at ha
  have hy := real_inner_transport_young
    (constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ (-t) W) U A B ha
  have hb := finiteSmoothHigher_adjacent_energy_le K f hf hp
  have hd := finiteSmoothHigherDiffusion_energy K f hf hp (fun s => G (-s)) (cellMetric_timeReverse hG) θ t
  have ht : (∑ i : Fin 2, ‖θ i‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hc : |inner ℝ (torusHigherScalarCLM K (κ t) U) U| ≤
      (k * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ ^ 2 := by
    exact ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        (((torusHigherScalarCLM K (κ t)).le_opNorm U).trans
          (mul_le_mul_of_nonneg_right (torusHigherScalarCLM_norm_le K (κ t) k hk) (norm_nonneg U)))
        (norm_nonneg U))).trans_eq (by ring)
  have hdt := mul_le_mul_of_nonneg_right ht (sq_nonneg ‖U‖)
  have hat := le_abs_self (inner ℝ (constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ (-t) W) U)
  have hct := le_abs_self (inner ℝ (torusHigherScalarCLM K (κ t) U) U)
  simp only [constructedReflectedFullGeneratorCLM, add_apply,
    ContinuousLinearMap.comp_apply, inner_add_left]
  rw [finiteSmoothPeriodicHk_truncate (K := K) (L := K + 2) (by omega) f hf hp]
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K (fun s => G (-s)) θ t W) U +
    inner ℝ (constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ (-t) W) U +
    inner ℝ (torusHigherScalarCLM K (κ t) U) U) + _ ≤ _
  change 2 * inner ℝ (torusHigherStrongDiffusionCLM K (fun s => G (-s)) θ t W) U + _ ≤ _ at hd
  change B ^ 2 ≤ ‖U‖ ^ 2 + _ at hb
  unfold constructedHigherEnergyGrowth
  change 2 * (inner ℝ (torusHigherStrongDiffusionCLM K (fun s => G (-s)) θ t W) U +
    inner ℝ (constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ (-t) W) U +
    inner ℝ (torusHigherScalarCLM K (κ t) U) U) + _ ≤
    (528 * R ^ 2 + 1 / 4 + 4 * A ^ 2 + 2 * k * (1 + ‖torusHigherScalarCLM K Complex.I‖)) * ‖U‖ ^ 2
  nlinarith

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.CycleWords

/-! The literal geometry fluxes telescope to the two omitted Taylor
remainders and precisely one terminal metric insertion. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem geometryResponse_flux_telescope (F : ChartedFamily ι h D P Ctx)
    (hD : 2 ≤ D) (J Ks : ℕ) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (p : P) (c : Ctx p) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (s δ : ℝ) (X0 phase : Vec 2)
    (Z : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u + 1) (h u))
    (v : ι) (t : ℝ) (z : Vec 2) :
    (∑ j : Fin (J + 1), geometryResponseOrderedFlux J Ks K G (F.cellFiber s phase p c) X0 δ Z j v t z) -
      (∑ j : Fin (J + 1), geometryActualFlux D G (F.cellFiber s phase p c) X0 δ
        (fun _ u => K u) (fun q => Z j q.2) (0, v) t z) =
    -((∑ j, nativeMetricInsertionFlux (G t z - metricTaylor 0 Ks G t 0 z) (Z j v) z) +
      (∑ j, originalRemainderNativeSourceFlux F Ks K p c s δ X0 phase (Z j) v t z) +
      nativeMetricInsertionFlux (metricTaylor 1 Ks G t 0 z) (Z (Fin.last J) v) z) := by
  let scalar := fun j => geometryScalarFlux D (fun t _ => G t 0) (fun _ u => K u)
    (fun q => Z j q.2) (0, v) t z
  let src := fun j => originalTaylorNativeSourceFlux F Ks K p c s δ X0 phase (Z j) v t z
  let met := fun j => nativeMetricInsertionFlux (metricTaylor 1 Ks G t 0 z) (Z j v) z
  let rem := fun j => nativeMetricInsertionFlux (G t z - metricTaylor 0 Ks G t 0 z) (Z j v) z
  let srem := fun j => originalRemainderNativeSourceFlux F Ks K p c s δ X0 phase (Z j) v t z
  have hresp (j : Fin (J + 1)) :
      geometryResponseOrderedFlux J Ks K G (F.cellFiber s phase p c) X0 δ Z j v t z =
        scalar j + src j + ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then met j' else 0 := by
    exact geometryResponseOrderedFlux_split F hD J Ks K hdesc p c G s δ X0 phase Z j v t z
  have hactual (j : Fin (J + 1)) :
      geometryActualFlux D G (F.cellFiber s phase p c) X0 δ (fun _ u => K u)
        (fun q => Z j q.2) (0, v) t z = scalar j + met j + rem j + src j + srem j := by
    rw [geometryActualFamilyFlux_split F K hdesc p c G s δ t X0 phase z v (Z j),
      geometryScalarFlux_taylor_split D hD Ks,
      originalSource_taylor_remainder_split F Ks K p c s δ X0 phase (Z j) v t z]
    change scalar j + met j + rem j + (src j + srem j) = _
    abel
  simp_rw [hresp, hactual]
  exact responseFlux_remainder_telescope J scalar src met rem srem

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal Topology
open Filter
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_polynomial_factorial_lower_supremum
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (hG : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc a b, ∀ k j,
      ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j))
    (M : ∀ i : Fin 1 × ι, Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ i, ∀ t ∈ Set.Icc a b, ∀ (l : Fin (κ i.1 i.2 + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M i l)
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, (∫⁻ t in Icc a b, ENNReal.ofReal (‖F i t‖ ^ 2)) < ⊤)
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι)
    (hG1 : ∀ t ∈ Set.Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (r L : ℝ) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : r * δ ≤ 1) (CG : ℕ → ℝ)
    (hreserve : Real.exp (18 * Cw m) *
      (1 + (metricRadiusConstant Kmax CG) ^ 2) / L ^ 2 ≤ 1 / 16)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    (⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)) +
      (∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc r (κ i.1 i.2) (w i s)) ≤
      ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
        (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
          ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
        (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
          16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) := by
  have hh := scalarChain_polynomial_factorial_lower_energy a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm r L hr hL
    hsmall hstrainSmall δ hδ hg hscale CG hreserve hmetricJets hdiv hwa hwb
  have hs := half_production_supremum_le (Icc a b) b ⟨hab, le_rfl⟩ _ _ _ hh
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hρ0 : 0 ≤ r / L := (div_pos hr hLp).le
  have hρr : r / L ≤ r := div_le_self hr.le hL
  have hpower : ENNReal.ofReal (L ^ (2 * κ i.1 i.2)) ≤ ENNReal.ofReal (L ^ (2 * Kmax)) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hL (Nat.mul_le_mul_left 2 (hκ i)))
  let A := ENNReal.ofReal (L ^ (2 * Kmax))
  have he t : weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t) ≤
      A * weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (u i t) :=
    (weightedFactorialNormSq_radius_reserve m ϖ zc r L hL _ _).trans
      (mul_le_mul' hpower le_rfl)
  have hd : (∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc r (κ i.1 i.2) (w i s)) ≤
      A * ∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (w i s) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro s
    exact (weightedGradFactorialNormSq_radius_reserve m ϖ zc r L hL _ _).trans
      (mul_le_mul' hpower le_rfl)
  have heSup : (⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)) ≤
      A * (⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (u i t)) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact (he t).trans (mul_le_mul' le_rfl (le_iSup_of_le t (le_iSup_of_le ht le_rfl)))
  have hi := weightedFactorialNormSq_radius_mono m ϖ zc hρ0 hρr (κ i.1 i.2) (f i)
  have hf : (∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (F i s)) ≤
      ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s) :=
    lintegral_mono (fun s => weightedFactorialNormSq_radius_mono m ϖ zc hρ0 hρr _ (F i s))
  calc
    _ ≤ A * ((⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (u i t)) +
        ∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc (r / L) (κ i.1 i.2) (w i s)) := by
      simpa only [mul_add] using add_le_add heSup hd
    _ ≤ A * (3 * ((ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
        ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
          (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
            16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)))) := by
      apply mul_le_mul' le_rfl
      apply hs.trans
      apply mul_le_mul' le_rfl
      apply mul_le_mul' le_rfl
      exact add_le_add hi (mul_le_mul' le_rfl hf)
    _ = _ := by dsimp [A]; ring

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The error forcing consists of the original source acting on the error,
the two omitted Taylor remainders, and the terminal metric insertion. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

def geometryErrorRemainderFlux (F : ChartedFamily ι h D P Ctx) (J Ks : ℕ) (K : ι → ℕ)
    (p : P) (c : Ctx p) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (s δ : ℝ) (X0 phase : Vec 2)
    (Z : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u + 1) (h u))
    (v : ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h v) :=
  (∑ j, nativeMetricInsertionFlux (G t z - metricTaylor 0 Ks G t 0 z) (Z j v) z) +
    (∑ j, originalRemainderNativeSourceFlux F Ks K p c s δ X0 phase (Z j) v t z) +
    nativeMetricInsertionFlux (metricTaylor 1 Ks G t 0 z) (Z (Fin.last J) v) z

def geometryErrorSourceFlux (F : ChartedFamily ι h D P Ctx) (J Ks : ℕ) (K : ι → ℕ)
    (p : P) (c : Ctx p) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (s δ : ℝ) (X0 phase : Vec 2)
    (Uerr : ∀ u, PlaneHk Set.univ (K u + 1) (h u))
    (Z : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u + 1) (h u))
    (v : ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h v) :=
  (∑ u, ∑ α : OriginalSourceIndex F v u,
    F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + δ • z) (z + phase) α.2.2.2 •
      Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
        (planeJetOrder (Uerr u) (α.2.1.1 - 1) α.2.2.1 z)) +
    geometryErrorRemainderFlux F J Ks K p c G s δ X0 phase Z v t z

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The exact real plane metric and transport form on actual H1 carriers. -/

def planeRealBlochGeneratorForm (G : Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t C : ℝ)
    (hC : ∀ i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (u z : PlaneHk Set.univ 1 ℝ) : ℝ :=
  -(∑ i : Fin 2, ∑ j : Fin 2,
    inner ℝ (G i j • planeRealH1TestGradient u i) (planeRealH1TestGradient z j)) -
    ∑ i : Fin 2, inner ℝ
      (planeRealDriftMultiplier v hv t i C (hC i) (planeRealH1TestGradient u i))
      (planeHkValueOperator 1 z)

theorem planeRealBlochGeneratorForm_readout {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (z : PlaneHk Set.univ 1 ℝ) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      -(∑ i : Fin 2, ∑ j : Fin 2, inner ℝ
        (planeComplexRealPartL2
          (G t i j • cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F t) i))
        (planeRealH1TestGradient z j)) -
      (∑ i : Fin 2, inner ℝ
        (planeComplexRealPartL2
          (planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol v t i)
            (cellDriftTorusSymbol_measurable v hv t i) C (hC t i)
            (cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F t) i)))
        (planeHkValueOperator 1 z)) =
      planeRealBlochGeneratorForm (G t) v hv t C (hC t)
        (cellEnergyPlaneRealH1State hab F t) z := by
  filter_upwards [cellEnergyPlaneRealH1State_testGradient hab F] with t ht
  simp only [planeRealBlochGeneratorForm, ht, map_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun f => inner ℝ f (planeHkValueOperator 1 z))
    (planeRealDriftMultiplier_realPart v hv t i C (hC t i)
      (cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F t) i))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The full reflected drift has the same quadratic polynomial adjacent-energy price. -/

 theorem constructedReflectedFullGenerator_smooth_adjacent_energy (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    2 * inner ℝ
        (constructedReflectedFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
          (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (1 / 2) * (‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 -
        ‖torusHkValueCLM (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)‖ ^ 2) ≤
      constructedHigherEnergyOrderPrice K R k * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2 *
        ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  have he := constructedReflectedFullGenerator_smooth_energy K hΛ hζ hν hr y₀ hv G hG θ R hθ κ t k hk f hf hp
  have hg := finiteSmoothHigherGradientEnergy_native_identity K f hf hp
  have hprice := mul_le_mul_of_nonneg_right
    (constructedHigherEnergyGrowth_polynomial_bound K R (ν / ocMeanFlux α q Λ ζ m ν) k
      ((norm_nonneg _).trans hk))
    (sq_nonneg ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖)
  apply le_trans ?_ hprice
  nlinarith only [he, hg]

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The signed reflected higher operator has the original reflected variational readout. -/

theorem cellDriftEntryCLM_reflected (v : ℝ → Vec 2 → Vec 2)
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ j, v t x j ^ 2 ≤ V ^ 2)
    (t : ℝ) (i : Fin 2) (u : ComplexCellL2) :
    cellDriftEntryCLM ⟨0, (fun s x => -v (-s) x), 0, 0⟩ V
      (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t i u =
      -cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb (-t) i u := by
  apply Lp.ext
  filter_upwards [cellDriftEntryCLM_ae ⟨0, (fun s x => -v (-s) x), 0, 0⟩ V
    (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t i u,
    cellDriftEntryCLM_ae ⟨0, v, 0, 0⟩ V hv.1 hb (-t) i u,
    Lp.coeFn_neg (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb (-t) i u)] with x hn hp he
  rw [hn, he]
  change ((-v (-t) x i : ℝ) : ℂ) * u x =
    -(cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb (-t) i u x)
  rw [hp, Complex.ofReal_neg, neg_mul]

theorem cellDriftEntryCLM_reflected_pair (v : ℝ → Vec 2 → Vec 2)
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ j, v t x j ^ 2 ≤ V ^ 2)
    (t : ℝ) (i : Fin 2) (u z : ComplexCellL2) :
    inner ℝ (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb (-t) i u) z =
      -inner ℝ (cellDriftEntryCLM ⟨0, (fun s x => -v (-s) x), 0, 0⟩ V
        (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t i u) z := by
  have h := congrArg (fun w : ComplexCellL2 => inner ℝ w z)
    (cellDriftEntryCLM_reflected v hv V hb t i u)
  rw [inner_neg_left] at h
  exact neg_eq_iff_eq_neg.mpr h |>.symm

 theorem constructedReflectedFullGeneratorCLM_pairing (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (U : TorusHk (K + 2) ℂ) (z : TorusHk 1 ℂ) :
    inner ℝ (torusHkValueCLM (constructedReflectedFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t U))
      (torusHkValueCLM z) =
    cellGeneratorForm ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x, θ, κ⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t
      (cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2) U)) z := by
  let C : CellCoefficients := ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x, θ, κ⟩
  let u := truncateTorusHk (by omega : 2 ≤ K + 2) U
  have hd : cellDiffusionForm C (cellMetric_timeReverse hG) t (cellH2BaseCLM u) z =
      inner ℝ (cellConstantMetricStrongDiffusionCLM (fun s => G (-s)) θ t u) (torusHkValueCLM z) := by
    have he := congrArg Complex.re (cellConstantMetricStrongDiffusionCLM_pair (fun s => G (-s)) (cellMetric_timeReverse hG) θ t u z)
    rw [cellComplexDiffusionForm_real_part C (cellMetric_timeReverse hG), cellComplexPair_re] at he
    exact he
  simp only [constructedReflectedFullGeneratorCLM, add_apply, ContinuousLinearMap.comp_apply,
    map_add, torusHigherStrongDiffusionCLM_value,
    constructedHigherAdvectionCLM_value K hΛ hζ ν y₀ hv V hb,
    torusHigherScalarCLM_value, inner_add_left, Fin.sum_univ_two]
  change _ = cellGeneratorForm C (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [C, Pi.neg_apply, neg_sq] using hb (-s) x) t (cellH2BaseCLM u) z
  simp only [cellGeneratorForm, add_apply, sub_apply, Fin.sum_univ_two,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]
  rw [hd]
  have h0 := cellDriftEntryCLM_reflected_pair _ hv V hb t 0
    (cellShiftedDerivativeCLM θ 0 (cellH2BaseCLM u)) (torusHkValueCLM z)
  have h1 := cellDriftEntryCLM_reflected_pair _ hv V hb t 1
    (cellShiftedDerivativeCLM θ 1 (cellH2BaseCLM u)) (torusHkValueCLM z)
  let d := inner ℝ (cellConstantMetricStrongDiffusionCLM (fun s => G (-s)) θ t u)
    (torusHkValueCLM z)
  let c := inner ℝ (cellScalarCLM (κ t) (torusHkValueCLM u)) (torusHkValueCLM z)
  let a (i : Fin 2) := inner ℝ
    (cellDriftEntryCLM ⟨0, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩ V hv.1 hb (-t) i
      (cellShiftedDerivativeCLM θ i (cellH2BaseCLM u))) (torusHkValueCLM z)
  let b (i : Fin 2) := inner ℝ
    (cellDriftEntryCLM C V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [C, Pi.neg_apply, neg_sq] using hb (-s) x) t i
      (cellShiftedDerivativeCLM θ i (cellH2BaseCLM u))) (torusHkValueCLM z)
  change d + (a 0 + a 1) + c = d - (b 0 + b 1) + c
  change a 0 = -b 0 at h0
  change a 1 = -b 1 at h1
  linarith only [h0, h1]

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The original molecular envelope supplies a graph budget uniform in the family and its masses. -/

section
def originalRemainderGraphConstant (j Kmax : ℕ) (CR : ℝ) (C : ℕ → ℝ) : ℝ :=
  2 * |CR| * (Kmax.factorial : ℝ) ^ 2 * |C j| *
    ∑ N ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget N)

theorem originalRemainderGraphConstant_nonneg (j Kmax : ℕ) (CR : ℝ) (C : ℕ → ℝ) :
    0 ≤ originalRemainderGraphConstant j Kmax CR C := by
  unfold originalRemainderGraphConstant
  positivity

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalRemainderPrice_graph_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (j Kmax : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (dom : F.Domain) (ν e E ρ CR : ℝ) (hCR : 0 ≤ CR) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) (hj : j ≤ J)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b)
    (hb : ∀ v u, 0 ≤ b v u) (hrow : ∀ v, ∑ u, b v u ≤ 1)
    (hcol : ∀ u, ∑ v, b v u ≤ 1) :
    (∀ v, ∑ u, Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalRemainderPrice F K j Kmax dom ν e E ρ CR v u α) ≤
        originalRemainderGraphConstant j Kmax CR C) ∧
    (∀ u, ∑ v, Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalRemainderPrice F K j Kmax dom ν e E ρ CR v u α) ≤
        originalRemainderGraphConstant j Kmax CR C) := by
  classical
  have hv (v : ι) : Real.sqrt (multiplicationDensityBudget (K v)) ≤
      ∑ N ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget N) :=
    Finset.single_le_sum (fun N _ => Real.sqrt_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hK v)))
  have hpoint (v u : ι) : Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalRemainderPrice F K j Kmax dom ν e E ρ CR v u α) ≤
        originalRemainderGraphConstant j Kmax CR C * b v u := by
    have hh := originalRemainderPrice_sum_envelope_le F π K j Kmax dom ν e E ρ CR hν hE hρ hCR
      C J b hj henv v u (hb v u)
    have hc := mul_le_mul_of_nonneg_left (hv v)
      (by positivity : 0 ≤ 2 * CR * (Kmax.factorial : ℝ) ^ 2 * |C j|)
    have hc' : 2 * Real.sqrt (multiplicationDensityBudget (K v)) * CR *
        (Kmax.factorial : ℝ) ^ 2 * |C j| ≤ originalRemainderGraphConstant j Kmax CR C := by
      simpa only [originalRemainderGraphConstant, abs_of_nonneg hCR, mul_assoc, mul_comm, mul_left_comm] using hc
    exact hh.trans (mul_le_mul_of_nonneg_right hc' (hb v u))
  constructor
  · intro v
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hpoint v u)
    rw [← Finset.mul_sum] at hh
    exact hh.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hrow v) (originalRemainderGraphConstant_nonneg j Kmax CR C))
  · intro u
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v u)
    rw [← Finset.mul_sum] at hh
    exact hh.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hcol u) (originalRemainderGraphConstant_nonneg j Kmax CR C))
end

/-! The original molecular envelope supplies a graph budget uniform in the family and its masses. -/

section
def originalTaylorGraphConstant (Ks Kmax : ℕ) (CT : ℝ) (C : ℕ → ℝ) : ℝ :=
  2 * |CT| * (Kmax.factorial : ℝ) ^ 2 * (∑ r ∈ Finset.range (Ks + 1), |C r|) *
    ∑ N ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget N)

theorem originalTaylorGraphConstant_nonneg (Ks Kmax : ℕ) (CT : ℝ) (C : ℕ → ℝ) :
    0 ≤ originalTaylorGraphConstant Ks Kmax CT C := by
  unfold originalTaylorGraphConstant
  positivity

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalTaylorPrice_graph_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (Ks Kmax : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (dom : F.Domain) (ν e E ρ CT : ℝ) (hCT : 0 ≤ CT) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) (hKs : Ks ≤ J)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b)
    (hb : ∀ v u, 0 ≤ b v u) (hrow : ∀ v, ∑ u, b v u ≤ 1)
    (hcol : ∀ u, ∑ v, b v u ≤ 1) :
    (∀ v, ∑ u, Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) ≤
        originalTaylorGraphConstant Ks Kmax CT C) ∧
    (∀ u, ∑ v, Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) ≤
        originalTaylorGraphConstant Ks Kmax CT C) := by
  classical
  have hv (v : ι) : Real.sqrt (multiplicationDensityBudget (K v)) ≤
      ∑ N ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget N) :=
    Finset.single_le_sum (fun N _ => Real.sqrt_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hK v)))
  have hpoint (v u : ι) : Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) ≤
        originalTaylorGraphConstant Ks Kmax CT C * b v u := by
    have hh := originalTaylorPrice_sum_envelope_le F π K Ks Kmax dom ν e E ρ CT hν hE hρ hCT
      C J b hKs henv v u (hb v u)
    have hc := mul_le_mul_of_nonneg_left (hv v)
      (by positivity : 0 ≤ 2 * CT * (Kmax.factorial : ℝ) ^ 2 * (∑ r ∈ Finset.range (Ks + 1), |C r|))
    have hc' : 2 * Real.sqrt (multiplicationDensityBudget (K v)) * CT *
        (Kmax.factorial : ℝ) ^ 2 * (∑ r ∈ Finset.range (Ks + 1), |C r|) ≤ originalTaylorGraphConstant Ks Kmax CT C := by
      simpa only [originalTaylorGraphConstant, abs_of_nonneg hCT, mul_assoc, mul_comm, mul_left_comm] using hc
    exact hh.trans (mul_le_mul_of_nonneg_right hc' (hb v u))
  constructor
  · intro v
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hpoint v u)
    rw [← Finset.mul_sum] at hh
    exact hh.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hrow v) (originalTaylorGraphConstant_nonneg Ks Kmax CT C))
  · intro u
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v u)
    rw [← Finset.mul_sum] at hh
    exact hh.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hcol u) (originalTaylorGraphConstant_nonneg Ks Kmax CT C))
end

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Weighted AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The literal real plane form has an actual bounded H1 Riesz operator. -/

def planeRealH1GradientCLM (i : Fin 2) :
    PlaneHk Set.univ 1 ℝ →L[ℝ] Lp ℝ 2 (volume : Measure (Vec 2)) :=
  (PiLp.proj (𝕜 := ℝ) 2
    (fun _ : Fin 2 => Lp ℝ 2 (volume : Measure (Vec 2))) i).comp planeH1GradientOperator

theorem planeRealH1GradientCLM_apply (u : PlaneHk Set.univ 1 ℝ) (i : Fin 2) :
    planeRealH1GradientCLM i u = planeRealH1TestGradient u i := rfl

def planeRealBlochGeneratorDual (G : Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t C : ℝ)
    (hC : ∀ i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C) :
    PlaneHk Set.univ 1 ℝ →L[ℝ] PlaneHk Set.univ 1 ℝ :=
  -(∑ i : Fin 2, ∑ j : Fin 2,
    G i j • (planeRealH1GradientCLM j).adjoint.comp (planeRealH1GradientCLM i)) -
    ∑ i : Fin 2, (planeHkValueOperator (E := ℝ) 1).adjoint.comp
      ((planeRealDriftMultiplier v hv t i C (hC i)).comp (planeRealH1GradientCLM i))

theorem planeRealBlochGeneratorDual_pair (G : Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t C : ℝ)
    (hC : ∀ i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (u z : PlaneHk Set.univ 1 ℝ) :
    inner ℝ (planeRealBlochGeneratorDual G v hv t C hC u) z =
      planeRealBlochGeneratorForm G v hv t C hC u z := by
  simp only [planeRealBlochGeneratorDual, planeRealBlochGeneratorForm,
    sub_apply, neg_apply, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, inner_sub_left, inner_neg_left,
    sum_inner, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
    planeRealH1GradientCLM_apply]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Actual sampled scalar coefficient jets sum against the original positive Schur price. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def letterScalarTaylor (L : CycleLetter ι h D) (v u : ι)
    (α : OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u)
    (ϖ ζ : ℝ) (t : ℝ) (φ X : Vec 2) (k : Fin 2) (z : Vec 2) : ℝ :=
  taylorSlow (if L.positive then 1 else 0) L.slow
    (fun Y => (ChartedFamily.ofFiber L.edge).flux () () v u α.1 α.2.1.1 α.2.2.1 t Y (z + φ) k)
    X ((ζ * ϖ) • z)

theorem letterScalarTaylor_fast_ae_matrix_price (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (dom : Set (ℝ × Vec 2)) (J H : ℕ)
    (hL : IsCycleLetter π L dom J H) (v u : ι)
    (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ∀ᵐ t ∂volume, (∀ Y : Vec 2, (t, Y) ∈ dom) → ∀ (φ X : Vec 2)
      (k : OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u → Fin 2) (j : ℕ), j ≤ J → ∀ z,
      Real.sqrt (π u / π v) *
        (∑ α : OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u,
          ‖((ChartedFamily.ofFiber L.edge).identity v u α.1).map‖ *
            ‖iteratedFDeriv ℝ j (letterScalarTaylor L v u α ϖ ζ t φ X (k α)) z‖) ≤
      originalFlaggedTaylorFastJetPriceConstant L.positive L.slow J *
        (if L.positive then ζ else 1) * polynomialMomentRoot ϖ z ^ L.slow *
          letterRetainedJetMatrix π L dom J v u := by
  have hh (α : OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u) :=
    (analyticOriginalSource_flagged_taylor_fast_price (ι := ι) (h := h) (D := D)
      (P := Unit) (Ctx := fun _ => Unit) L.positive L.slow J).2
      (ChartedFamily.ofFiber L.edge) π hπ (fun _ _ => dom) L.majorant hL.analytic
      v u α () () ϖ ζ hϖ hϖ1 hζ hζ1
  filter_upwards [ae_all_iff.mpr hh] with t ht
  intro hdom φ X k j hj z
  have he (α : OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u) :
      letterScalarTaylor L v u α ϖ ζ t φ X (k α) =
        (fun y => taylorSlow (if L.positive then 1 else 0) L.slow
          (fun Y => (ChartedFamily.ofFiber L.edge).flux () () v u α.1 α.2.1.1 α.2.2.1 t Y (y + φ) (k α))
          X ((ζ * ϖ) • y)) := rfl
  simp_rw [he]
  have hs := Finset.sum_le_sum (fun α (_ : α ∈ Finset.univ) => ht α hdom φ (k α) X j hj z)
  have hm := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (π u / π v))
  simpa only [letterScalarTaylor, letterRetainedJetMatrix, mul_assoc, mul_comm, mul_left_comm,
    ← Finset.mul_sum] using hm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Original Taylor constituents produce genuine native response forcings with their complete prefix prices. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalTaylorPair_native_flux_exists (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => ∑ α : OriginalSourceIndex F v u,
            taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + φ) α.2.2.2)
              X0 ((e / E) • z) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
                (planeJetOrder (U t) (α.2.1.1 - 1) α.2.2.1 z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e) (V t) z ≤
            (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) ^ 2 *
              (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  obtain ⟨CT, hCT, hflux⟩ := originalTaylorConstituent_native_flux_exists_all (ι := ι) (h := h)
    (D := D) (P := P) (Ctx := Ctx) Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ hwindow n U hU henergy
  have hex (α : OriginalSourceIndex F v u) := hflux F π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    C J b₀ hKs henv hmeas v u α.1 α.2.1.1 α.2.1.2 α.2.2.1 p c s a b ϖ ζ hs hϖ hscale
    hζ hζ1 hδ X0 φ α.2.2.2 hwindow n U hU henergy
  choose V hV hVe hvalue hdensity using hex
  have hp (α : OriginalSourceIndex F v u) : 0 ≤ originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α := by
    unfold originalTaylorPrice
    apply mul_nonneg _ (norm_nonneg _)
    apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCT)
    apply Finset.sum_nonneg
    intro r _
    unfold molecularTaylorPrefixPrice
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hE.le _))
      (molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _)
  have hdens : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e) (∑ α, V α t) z ≤
        (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) ^ 2 *
          (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z := by
    filter_upwards [ae_all_iff.mpr hdensity] with t ht
    have hh := nativeFactorialDensity_sum_price_le (ρ / e) (fun α => V α t)
      (fun α => originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) hp
      (fun z => (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z)
      (fun z => mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg (ρ / e) (U t) z))
      (fun α => by
        filter_upwards [ht α] with z hz
        simpa only [originalTaylorPrice, mul_pow,
          Real.sq_sqrt (multiplicationDensityBudget_nonneg (K v)), mul_assoc] using hz)
    simpa only [mul_assoc] using hh
  refine ⟨fun t => ∑ α, V α t, ?_, ?_, ?_, hdens⟩
  · exact memLp_finsetSum (ε' := PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
      (f := V) Finset.univ (fun α _ => hV α)
  · have hh := nativeFlux_time_moment_shift_budget n Ks ϖ (ρ / e)
      (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α)
      (volume.restrict (Set.Icc a b)) (fun t => ∑ α, V α t) U hdens
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top henergy) hh
  · filter_upwards [ae_all_iff.mpr hvalue] with t ht
    have hv := planeJetOrder_finite_sum_ae (Nat.zero_le (K v)) (fun α => V α t)
      (fun i : Fin 0 => Fin.elim0 i)
    filter_upwards [hv, ae_all_iff.mpr ht] with z hz hzs
    exact hz.trans (Finset.sum_congr rfl (fun α _ => hzs α))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual plane Riesz generator depends only on the consumed metric and drift. -/

theorem planeRealBlochGeneratorDual_congr_time
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (v v' : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hv' : IsCellDrift v')
    (t t' : ℝ) (ht : v t = v' t') (C C' : ℝ)
    (hC : ∀ i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (hC' : ∀ i z, ‖cellDriftTorusSymbol v' t' i z‖ ≤ C')
    (u : PlaneHk Set.univ 1 ℝ) :
    planeRealBlochGeneratorDual G v hv t C hC u =
      planeRealBlochGeneratorDual G v' hv' t' C' hC' u := by
  apply ext_inner_right ℝ
  intro z
  rw [planeRealBlochGeneratorDual_pair, planeRealBlochGeneratorDual_pair]
  unfold planeRealBlochGeneratorForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [planeRealDriftMultiplier_congr_time v v' hv hv' t t' ht i C C' (hC i) (hC' i)]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The genuine plane generator pairs to its literal integrable spatial PDE expression. -/

def planeRealBlochSpatialRhs (G : Matrix (Fin 2) (Fin 2) ℝ)
    (v : Vec 2 → Vec 2) (u z : PlaneHk Set.univ 1 ℝ) (x : Vec 2) : ℝ :=
  -(∑ i : Fin 2, ∑ j : Fin 2,
    G i j * inner ℝ (planeRealH1TestGradient u i x) (planeRealH1TestGradient z j x)) -
  ∑ i : Fin 2, v x i * inner ℝ (planeRealH1TestGradient u i x) (planeHkValueOperator 1 z x)

theorem planeRealBlochSpatialRhs_integrable (G : Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t C : ℝ)
    (hC : ∀ i y, ‖cellDriftTorusSymbol v t i y‖ ≤ C)
    (u z : PlaneHk Set.univ 1 ℝ) :
    Integrable (planeRealBlochSpatialRhs G (v t) u z) volume := by
  exact (integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (L2.integrable_inner (planeRealH1TestGradient u i) (planeRealH1TestGradient z j)).const_mul
        (G i j)))).neg.sub
    (integrable_finsetSum Finset.univ (fun i _ =>
      planeRealDriftMultiplier_pair_integrable v hv t i C (hC i)
        (planeRealH1TestGradient u i) (planeHkValueOperator 1 z)))

theorem planeRealBlochGeneratorDual_spatialPair (G : Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t C : ℝ)
    (hC : ∀ i y, ‖cellDriftTorusSymbol v t i y‖ ≤ C)
    (u z : PlaneHk Set.univ 1 ℝ) :
    inner ℝ (planeRealBlochGeneratorDual G v hv t C hC u) z =
      ∫ x, planeRealBlochSpatialRhs G (v t) u z x := by
  have hm (i j : Fin 2) : Integrable
      (fun x => G i j * inner ℝ (planeRealH1TestGradient u i x)
        (planeRealH1TestGradient z j x)) volume :=
    (L2.integrable_inner _ _).const_mul _
  have hd (i : Fin 2) : Integrable
      (fun x => v t x i * inner ℝ (planeRealH1TestGradient u i x)
        (planeHkValueOperator 1 z x)) volume :=
    planeRealDriftMultiplier_pair_integrable v hv t i C (hC i) _ _
  have hms := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hm i j))
  have hds := integrable_finsetSum Finset.univ (fun i _ => hd i)
  have hneg : Integrable (fun x => -(∑ i : Fin 2, ∑ j : Fin 2,
      G i j * inner ℝ (planeRealH1TestGradient u i x) (planeRealH1TestGradient z j x)))
      volume := hms.neg
  have hmi (i : Fin 2) :
      (∫ x, ∑ j : Fin 2, G i j * inner ℝ (planeRealH1TestGradient u i x)
        (planeRealH1TestGradient z j x)) =
      ∑ j : Fin 2, G i j * inner ℝ (planeRealH1TestGradient u i) (planeRealH1TestGradient z j) := by
    rw [integral_finsetSum Finset.univ (fun j _ => hm i j)]
    simp only [integral_const_mul, L2.inner_def]
  rw [planeRealBlochGeneratorDual_pair]
  unfold planeRealBlochSpatialRhs planeRealBlochGeneratorForm
  rw [integral_sub hneg hds, integral_neg,
    integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hm i j)),
    integral_finsetSum Finset.univ (fun i _ => hd i)]
  simp_rw [hmi, real_inner_smul_left, planeRealDriftMultiplier_pair]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Both Schur sums of the literal original Taylor fast jets are controlled before time integration. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def actualTaylorJetMatrix (π : ι → ℝ) (L : CycleLetter ι h D)
    (ϖ ζ t : ℝ) (φ X z : Vec 2) (j : ℕ) : Matrix ι ι ℝ := fun v u =>
  Real.sqrt (π u / π v) *
    ∑ α : OriginalSourceIndex (ChartedFamily.ofFiber L.edge) v u,
      ‖((ChartedFamily.ofFiber L.edge).identity v u α.1).map‖ *
        ‖iteratedFDeriv ℝ j (letterScalarTaylor L v u α ϖ ζ t φ X α.2.2.2) z‖

def actualTaylorJetMatrixPrice (L : CycleLetter ι h D) (J : ℕ) (ϖ ζ : ℝ) (z : Vec 2) : ℝ :=
  originalFlaggedTaylorFastJetPriceConstant L.positive L.slow J *
    (if L.positive then ζ else 1) * polynomialMomentRoot ϖ z ^ L.slow

theorem actualTaylorJetMatrix_schur_ae (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (dom : Set (ℝ × Vec 2)) (J H : ℕ)
    (hL : IsCycleLetter π L dom J H) (ϖ ζ : ℝ)
    (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ∀ᵐ t ∂volume, (∀ Y : Vec 2, (t, Y) ∈ dom) → ∀ φ X j, j ≤ J → ∀ z,
      (∀ v u, 0 ≤ actualTaylorJetMatrix π L ϖ ζ t φ X z j v u) ∧
      (∀ v, ∑ u, actualTaylorJetMatrix π L ϖ ζ t φ X z j v u ≤
        actualTaylorJetMatrixPrice L J ϖ ζ z * (2 * L.theta)) ∧
      (∀ u, ∑ v, actualTaylorJetMatrix π L ϖ ζ t φ X z j v u ≤
        actualTaylorJetMatrixPrice L J ϖ ζ z * (2 * L.theta)) := by
  have hh (vu : ι × ι) := letterScalarTaylor_fast_ae_matrix_price π hπ L dom J H hL
    vu.1 vu.2 ϖ ζ hϖ hϖ1 hζ hζ1
  filter_upwards [ae_all_iff.mpr hh] with t ht
  intro hdom φ X j hj z
  have he (v u : ι) : actualTaylorJetMatrix π L ϖ ζ t φ X z j v u ≤
      actualTaylorJetMatrixPrice L J ϖ ζ z * letterRetainedJetMatrix π L dom J v u :=
    ht (v, u) hdom φ X (fun α => α.2.2.2) j hj z
  have hprice : 0 ≤ actualTaylorJetMatrixPrice L J ϖ ζ z := by
    have hC := (analyticOriginalSource_flagged_taylor_fast_price
      (ι := ι) (h := h) (D := D) (P := Unit) (Ctx := fun _ => Unit) L.positive L.slow J).1
    have hflag : 0 ≤ (if L.positive then ζ else 1) := by split <;> positivity
    exact mul_nonneg (mul_nonneg hC hflag)
      (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) L.slow)
  have hb := letterRetainedJetMatrix_schur_budget π L dom J H hL
  refine ⟨fun v u => mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _))), ?_, ?_⟩
  · intro v
    have hs : (∑ u, actualTaylorJetMatrix π L ϖ ζ t φ X z j v u) ≤
        ∑ u, actualTaylorJetMatrixPrice L J ϖ ζ z * letterRetainedJetMatrix π L dom J v u :=
      Finset.sum_le_sum (fun u _ => he v u)
    rw [← Finset.mul_sum] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left (hb.2.1 v) hprice)
  · intro u
    have hs : (∑ v, actualTaylorJetMatrix π L ϖ ζ t φ X z j v u) ≤
        ∑ v, actualTaylorJetMatrixPrice L J ϖ ζ z * letterRetainedJetMatrix π L dom J v u :=
      Finset.sum_le_sum (fun v _ => he v u)
    rw [← Finset.mul_sum] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left (hb.2.2 u) hprice)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Only actual original source edges require higher weighted moments to construct a pair forcing. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalTaylorPair_native_flux_exists_supported (Ks Kmax : ℕ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ (F : ChartedFamily ι h D P Ctx)
      (π : ι → ℝ), (∀ v, 0 < π v) → ∀ (K : ι → ℕ), (∀ v, K v ≤ Kmax) →
      F.IsDescending K → ∀ (dom : F.Domain) (ν e E ρ : ℝ),
      0 < ν → 0 < e → 0 < E → 0 < ρ →
      ∀ (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ), Ks ≤ J →
      IsMolecularEnvelope F π K dom ν e E ρ C J b₀ → F.IsTimeMeasurable →
      ∀ (v u : ι) (p : P) (c : Ctx p) (s a b ϖ ζ : ℝ),
      s ≠ 0 → 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → e / E = ζ * ϖ →
      ∀ (X0 φ : Vec 2),
      (∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K u + 1) (h u)),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (Nonempty (F.Γ v u) →
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (U t)) ≠ ⊤) →
      ∃ V : ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => ∑ α : OriginalSourceIndex F v u,
            taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + φ) α.2.2.2)
              X0 ((e / E) • z) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
                (planeJetOrder (U t) (α.2.1.1 - 1) α.2.2.1 z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e) (V t) z ≤
            (∑ α : OriginalSourceIndex F v u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT v u α) ^ 2 *
              (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity (ρ / e) (U t) z) := by
  classical
  obtain ⟨CT, hCT, hflux⟩ := originalTaylorPair_native_flux_exists (ι := ι) (h := h)
    (D := D) (P := P) (Ctx := Ctx) Ks Kmax
  refine ⟨CT, hCT, ?_⟩
  intro F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
    v u p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ hwindow n U hU henergy
  by_cases hed : Nonempty (F.Γ v u)
  · exact hflux F π hπ K hK hdesc dom ν e E ρ hν he hE hρ C J b₀ hKs henv hmeas
      v u p c s a b ϖ ζ hs hϖ hscale hζ hζ1 hδ X0 φ hwindow n U hU (henergy hed)
  · have hempty : (Finset.univ : Finset (OriginalSourceIndex F v u)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro α _
      exact hed ⟨α.1⟩
    have hzero : MemLp
        (fun _ : ℝ => (0 : PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v))))
        2 (volume.restrict (Set.Icc a b)) :=
      Weighted.planeHk_zero_time_memLp (K v) (volume.restrict (Set.Icc a b))
    refine ⟨fun _ => 0, hzero, ?_, ?_, ?_⟩
    · simp only [Weighted.weightedFactorialNormSq_zero_carrier, lintegral_zero]
      exact ENNReal.zero_ne_top
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa only [hempty, Finset.sum_empty] using (planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v)))
    · exact Filter.Eventually.of_forall (fun _ => by
        filter_upwards [planeFactorialDensity_zero_ae
          (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) (ρ / e)] with z hz
        simp only [hz, hempty, Finset.sum_empty, zero_pow (by decide : 2 ≠ 0), zero_mul, le_refl])

end AVRegularity.CycleWords
end
