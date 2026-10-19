-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneForcedZeroInitialEndpointEnergy
public import AVRegularity.CycleJoint.PointwiseNativeTransportIdentityPrice
import AVRegularity.CycleJoint.PreparationTransportedWeightedPolynomialAllMomentMap

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual metric diffusion and triangular source depth preserve finite preparation lift moments. -/

theorem triangularMetric_weighted_lift_time_energy_ne_top
    (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (zc : Vec 2) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ zc n Cw)
        (_hr1 : rstar ≤ 1) (D : ℕ) (_hD : 2 ≤ D)
        (A : ∀ i j, (d : admissibleOrders Kslot D i j) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i j d, coefficientSeminorm rstar (Kslot i) ta tb (A i j d) ≠ ⊤)
        (_hc : ∀ i j d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i j d t))
        (_hAm : ∀ i j d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i j d p.1 p.2))
        (rank : ι → ℕ)
        (_hz : ∀ i j, ¬ rank j < rank i → ∀ d t x, A i j d t x = 0)
        (V₀ : ∀ i, PlaneHk Set.univ (Kslot i) (h i))
        (_hf : ∀ i, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i) ≠ ⊤)
        (V : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (Vw : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i)),
        IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
          (planeMetricSourceCoefficient Kslot D G A) V₀ (fun _ _ => 0) (fun _ _ => 0) V Vw →
        ∀ i, (∫⁻ t in Set.Icc ta tb,
          weightedFactorialNormSq n ϖ zc rstar (Kslot i + 1) (Vw i t)) ≠ ⊤ := by
  intro ι _ h _ _ _ _ _ _ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W hr1 D hD A hA hc hAm rank hz V₀ hf V Vw hsln
  let F := planeCouplingFluxRow ht rstar hrstar Kslot D A hA hc Vw
  have hF (i : ι) : MemLp (F i) 2 (volume.restrict (Set.Icc ta tb)) :=
    planeCouplingFluxRow_memLp ht rstar hrstar Kslot D A hA hc Vw hAm hsln.2.1 i
  have hchain : IsPlaneChainFrom (geometryScalarData 2 G) (fun _ i => Kslot i) ta tb v
      (fun _ i => V₀ i) (fun _ i => F i) (fun _ i => V i) (fun _ i => Vw i) := by
    simpa only [zero_add] using planeForced_metric_source_order_two_chain ht rstar hrstar
      Kslot D hD v A G hA hc V₀ (fun _ _ => 0) V Vw hsln
  have hsq : (fun x => planeMomentSquareRoot n ϖ zc x ^ 2) = planeMomentPolynomial n ϖ zc :=
    funext (planeMomentSquareRoot_sq n ϖ zc)
  have hAll (k : ℕ) : ∀ i, rank i = k →
      (∫⁻ t in Set.Icc ta tb,
        weightedFactorialNormSq n ϖ zc rstar (Kslot i + 1) (Vw i t)) ≠ ⊤ := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi
      have hLower (j : ι) (hlt : rank j < rank i) :
          (∫⁻ t in Set.Icc ta tb, storedChartFactorialEnergy rstar
            (fun x => planeMomentSquareRoot n ϖ zc x ^ 2) (Vw j t)) ≠ ⊤ := by
        simpa only [hsq, weightedFactorialNormSq_stored_readout] using
          ih (rank j) (by omega) j rfl
      have hrow := planeCouplingFluxRow_weighted_time_energy_ne_top_of_lower_depth
        ht rstar hrstar Kslot D A hA hc Vw hAm hsln.2.1
        (planeMomentSquareRoot n ϖ zc) (planeMomentSquareRoot_continuous n ϖ zc)
        (planeMomentSquareRoot_pos n ϖ zc) rank i (hz i) hLower
      have hFe : (∫⁻ t in Set.Icc ta tb,
          weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) ≠ ⊤ := by
        simpa only [hsq, weightedFactorialNormSq_stored_readout] using hrow
      have he := scalarPlane_weighted_value_gradient_energy_ne_top n Kmax CG Cw
        Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
        v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
        G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
        tw S ϖ zc htw htb W V₀ F hF V Vw hchain i (hf i) hFe
      have hsplit := ENNReal.add_ne_top.mp he
      let Vsup := ⨆ t ∈ Set.Icc ta tb, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i t)
      apply weightedFactorialNormSq_lift_time_ne_top n ϖ zc rstar ta tb hrstar hr1
        (V i) (Vw i) (hsln.2.2.1 i) Vsup.toReal _ hsplit.2
      intro t ht'
      rw [ENNReal.ofReal_toReal hsplit.1]
      exact le_iSup_of_le t (le_iSup_of_le ht' le_rfl)
  intro i
  exact hAll (rank i) i rfl

/-! The actual homogeneous reference metric equation preserves finite original-mass preparation energy. -/

theorem triangularMetric_weighted_geometry_energy_lt_top
    (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (zc : Vec 2) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ zc n Cw)
        (_hr1 : rstar ≤ 1) (D : ℕ) (_hD : 2 ≤ D)
        (A : ∀ i j, (d : admissibleOrders Kslot D i j) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i j d, coefficientSeminorm rstar (Kslot i) ta tb (A i j d) ≠ ⊤)
        (_hc : ∀ i j d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i j d t))
        (_hAm : ∀ i j d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i j d p.1 p.2))
        (rank : ι → ℕ)
        (_hz : ∀ i j, ¬ rank j < rank i → ∀ d t x, A i j d t x = 0)
        (V₀ : ∀ i, PlaneHk Set.univ (Kslot i) (h i))
        (_hf : ∀ i, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i) ≠ ⊤)
        (V : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (Vw : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i)),
        (π : ι → ℝ) →
        IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
          (planeMetricSourceCoefficient Kslot D G A) V₀ (fun _ _ => 0) (fun _ _ => 0) V Vw →
        geometryEnergyNorm π Kslot n ϖ zc rstar ta tb V Vw < ⊤ := by
  intro ι _ h _ _ _ _ _ _ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W hr1 D hD A hA hc hAm rank hz V₀ hf V Vw π hsln
  have hlift := triangularMetric_weighted_lift_time_energy_ne_top n Kmax CG Cw
    Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W hr1 D hD A hA hc hAm rank hz V₀ hf V Vw hsln
  let F := planeCouplingFluxRow ht rstar hrstar Kslot D A hA hc Vw
  have hF (i : ι) : MemLp (F i) 2 (volume.restrict (Set.Icc ta tb)) :=
    planeCouplingFluxRow_memLp ht rstar hrstar Kslot D A hA hc Vw hAm hsln.2.1 i
  have hchain : IsPlaneChainFrom (geometryScalarData 2 G) (fun _ i => Kslot i) ta tb v
      (fun _ i => V₀ i) (fun _ i => F i) (fun _ i => V i) (fun _ i => Vw i) := by
    simpa only [zero_add] using planeForced_metric_source_order_two_chain ht rstar hrstar
      Kslot D hD v A G hA hc V₀ (fun _ _ => 0) V Vw hsln
  have hsq : (fun x => planeMomentSquareRoot n ϖ zc x ^ 2) = planeMomentPolynomial n ϖ zc :=
    funext (planeMomentSquareRoot_sq n ϖ zc)
  have hstored (i : ι) : (∫⁻ t in Set.Icc ta tb, storedChartFactorialEnergy rstar
      (fun x => planeMomentSquareRoot n ϖ zc x ^ 2) (Vw i t)) ≠ ⊤ := by
    simpa only [hsq, weightedFactorialNormSq_stored_readout] using hlift i
  have hrow (i : ι) := planeCouplingFluxRow_weighted_time_energy_ne_top
    ht rstar hrstar Kslot D A hA hc Vw hAm hsln.2.1
    (planeMomentSquareRoot n ϖ zc) (planeMomentSquareRoot_continuous n ϖ zc)
    (planeMomentSquareRoot_pos n ϖ zc) hstored i
  have hFe (i : ι) : (∫⁻ t in Set.Icc ta tb,
      weightedFactorialNormSq n ϖ zc rstar (Kslot i) (F i t)) ≠ ⊤ := by
    simpa only [hsq, weightedFactorialNormSq_stored_readout] using hrow i
  have he (i : ι) := scalarPlane_weighted_value_gradient_energy_ne_top n Kmax CG Cw
    Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W V₀ F hF V Vw hchain i (hf i) (hFe i)
  apply lt_top_iff_ne_top.mpr
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
  apply ENNReal.sum_ne_top.mpr
  intro i _
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (he i)

end AVRegularity.CycleJointProofs
end

section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Genuine component response estimates sum with the original family masses and no cardinality factor. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance actualTaylorResponseBudgetFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => E i)) := componentCertificateFluxNormed
local instance actualTaylorResponseBudgetFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => E i)) := componentCertificateFluxInner
local instance actualTaylorResponseBudgetNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance actualTaylorResponseBudgetNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k
local instance actualTaylorResponseBudgetFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E i))) :=
  allMomentTimeNativeNormed k
local instance actualTaylorResponseBudgetFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E i))) :=
  allMomentTimeNativeModule k

theorem planeComponentAllMomentResponse_actualTaylor_gradient_budget
    (a b : ℝ) (hab : a ≤ b) (K : ι → ℕ) (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hMm : Measurable M)
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4)
    (hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (t₀ S ϖ : ℝ) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v t₀ S ϖ 0 N Cw) (hm : m ≤ N)
    (ρ L : ℝ) (hρ : 0 < ρ) (hL : 1 ≤ L)
    (hsmall : B * ρ / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * ρ ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S)
    (π : ι → ℝ) (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := E i) M v (K i) a b ϖ ρ (R i))
    (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => E j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (Tsource : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (hTsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun W t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (E := E j) (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (W j) t) i) (Tsource i))
    (hπ : ∀ i, 0 < π i) (θ : ℝ)
    (hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (Remainder : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (W : ∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Icc a b))) :
    planeAllMomentFamilyGradientEnergy K m ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => R i ((Tsource i - Remainder i) W)) ≤
      (ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
        (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
          ENNReal.ofReal (3 * Real.exp (18 * Cw m)))) *
      (16 * (2 * (ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * θ) ^ 2) *
        planeAllMomentFamilyGradientEnergy K m ϖ ρ (volume.restrict (Icc a b)) π W +
        planeAllMomentFamilyEnergy K m ϖ ρ (volume.restrict (Icc a b)) π
          (fun i => Remainder i W)))) := by
  have he := planeComponentAllMomentResponse_family_gradient_budget a b hab K Kmax hK
    v hvm hv V strain B lam hV ha hB hlam hbv hjets M hMm g hg hg4 hnear hsym
    t₀ S ϖ N m Cw C hm ρ L hρ hL hsmall hstrainSmall hreserve hdiv hwa hwb π R hR
    (fun i => (Tsource i - Remainder i) W)
  have hb := planeActual_sourceTaylor_mass_budget hab ϖ ρ hρ K D A hA hC Tsource hTsource
    π hπ θ hrow hcol Remainder W m
  apply le_trans he
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact mul_le_mul_of_nonneg_left hb zero_le

end AVRegularity.CycleJointProofs
end

section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Genuine component response estimates sum with the original family masses and no cardinality factor. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance shiftedTaylorResponseBudgetFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => E i)) := componentCertificateFluxNormed
local instance shiftedTaylorResponseBudgetFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => E i)) := componentCertificateFluxInner
local instance shiftedTaylorResponseBudgetNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance shiftedTaylorResponseBudgetNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k
local instance shiftedTaylorResponseBudgetFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E i))) :=
  allMomentTimeNativeNormed k
local instance shiftedTaylorResponseBudgetFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E i))) :=
  allMomentTimeNativeModule k

theorem planeComponentAllMomentResponse_actualTaylor_shifted_gradient_budget
    (a b : ℝ) (hab : a ≤ b) (K : ι → ℕ) (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hMm : Measurable M)
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4)
    (hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (t₀ S ϖ : ℝ) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v t₀ S ϖ 0 N Cw) (hm : m ≤ N)
    (ρ L : ℝ) (hρ : 0 < ρ) (hL : 1 ≤ L)
    (hsmall : B * ρ / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * ρ ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S)
    (π : ι → ℝ) (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := E i) M v (K i) a b ϖ ρ (R i))
    (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => E j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (Tsource : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (hTsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun W t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (E := E j) (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (W j) t) i) (Tsource i))
    (hπ : ∀ i, 0 < π i) (θ : ℝ)
    (hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (Remainder : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (W : ∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Icc a b)))
    (p : ℕ) (Br : ℝ≥0∞)
    (hrem : planeAllMomentFamilyEnergy K m ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => Remainder i W) ≤ Br *
        planeAllMomentFamilyGradientEnergy K (m + p) ϖ ρ (volume.restrict (Icc a b)) π W) :
    planeAllMomentFamilyGradientEnergy K m ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => R i ((Tsource i - Remainder i) W)) ≤
      (ENNReal.ofReal (L ^ (2 * Kmax)) * 3 *
        (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
          ENNReal.ofReal (3 * Real.exp (18 * Cw m)))) *
      (16 * (2 * ((ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * θ) ^ 2) + Br) *
        planeAllMomentFamilyGradientEnergy K (m + p) ϖ ρ (volume.restrict (Icc a b)) π W))) := by
  have he := planeComponentAllMomentResponse_actualTaylor_gradient_budget a b hab K Kmax hK
    v hvm hv V strain B lam hV ha hB hlam hbv hjets M hMm g hg hg4 hnear hsym
    t₀ S ϖ N m Cw C hm ρ L hρ hL hsmall hstrainSmall hreserve hdiv hwa hwb π R hR
    D A hA hC Tsource hTsource hπ θ hrow hcol Remainder W
  have hmono := planeAllMomentFamilyGradientEnergy_moment_mono K (Nat.le_add_right m p)
    ϖ ρ (volume.restrict (Icc a b)) π W
  apply le_trans he
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply mul_le_mul_of_nonneg_left _ zero_le
  rw [add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hmono zero_le) hrem

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Homogeneous coupled native endpoints have a uniform rank-discounted mass bound. Finite weighted gradient energy is derived from the actual triangular equation. -/

theorem planeHomogeneous_rank_discounted_endpoint_energy.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D H : ℕ) (Bsrc : ℝ) :
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (zc : Vec 2) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ zc n Cw)
        (_hr1 : rstar ≤ 1) (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
        (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (_hinit : ∀ i, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i) ≠ ⊤),
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A)
            V₀ (fun _ _ => 0) (fun _ _ => 0) V Vw →
          ∀ tp, tp ∈ Set.Icc ta tb →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i tp)) ≤
            ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax CG Cw D Bsrc) ^ (2 * H)) *
              (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) *
                ∑ i, ENNReal.ofReal ((π i)⁻¹) *
                  weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i)) := by
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W hr1 hD A hA hc hAm hrow hcol rank hrank hzero V₀ hinit
    V Vw hsln tp htp
  have hprepared := triangularMetric_weighted_geometry_energy_lt_top n Kmax CG Cw
    Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W hr1 D hD A hA hc hAm rank
    (fun i j hij d t x => by rw [hzero i j hij d]; rfl)
    V₀ hinit V Vw π hsln
  have he (i : ι) : (∫⁻ t in Set.Icc ta tb,
      weightedGradFactorialNormSq n ϖ zc rstar (Kslot i) (Vw i t)) ≠ ⊤ :=
    (finite_geometry_energy_component π hπ Kslot n ϖ zc rstar ta tb V Vw hprepared i).choose_spec.2.2
  have hforcing : (∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ zc rstar (Kslot i)
        (0 : PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i)))) ≠ ⊤ := by
    simp only [weightedFactorialNormSq_zero_carrier, mul_zero, Finset.sum_const_zero,
      lintegral_zero, ne_eq, ENNReal.zero_ne_top, not_false_eq_true]
  have hb := planeForced_rank_discounted_mass_energy n Kmax CG Cw D H Bsrc
    π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ zc htw htb W hD A hA hc hAm hrow hcol rank hrank hzero
    V₀ (fun _ _ => 0) (fun _ => by exact AVRegularity.CoupledEnergy.Variational.timeMemLp_zero _ _) hinit hforcing V Vw he hsln
  have hend := planeFamily_endpoint_le_energy Kslot n ϖ rstar zc ta tb π V Vw tp htp
  apply hend.trans
  apply hb.trans_eq
  simp only [weightedFactorialNormSq_zero_carrier, mul_zero, Finset.sum_const_zero,
    lintegral_zero, add_zero]

end AVRegularity.CycleJointProofs
end

section
open Set MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Genuine component response estimates sum with the original family masses and no cardinality factor. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

local instance uniformTaylorResponseBudgetFluxNormed (i : ι) :
    NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => E i)) := componentCertificateFluxNormed
local instance uniformTaylorResponseBudgetFluxInner (i : ι) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => E i)) := componentCertificateFluxInner
local instance uniformTaylorResponseBudgetNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (E i)) := allMomentTimeNativeNormed k
local instance uniformTaylorResponseBudgetNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (E i)) := allMomentTimeNativeModule k
local instance uniformTaylorResponseBudgetFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E i))) :=
  allMomentTimeNativeNormed k
local instance uniformTaylorResponseBudgetFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => E i))) :=
  allMomentTimeNativeModule k

theorem planeComponentAllMomentResponse_actualTaylor_uniform_gradient_budget
    (a b : ℝ) (hab : a ≤ b) (K : ι → ℕ) (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hMm : Measurable M)
    (g : ℝ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4)
    (hnear : IsMetricNearIdentity (fun t _ => M t) g)
    (hsym : ∀ t ∈ Icc a b, (M t).IsSymm)
    (t₀ S ϖ : ℝ) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights (fun t _ => M t) v t₀ S ϖ 0 N Cw) (hm : m ≤ N)
    (ρ L : ℝ) (hρ : 0 < ρ) (hL : 1 ≤ L)
    (hsmall : B * ρ / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * ρ ^ 2 ≤ 1 / 8)
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 16)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S)
    (π : ι → ℝ) (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
      (volume.restrict (Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0 (volume.restrict (Icc a b)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := E i) M v (K i) a b ϖ ρ (R i))
    (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => E j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (Tsource : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (hTsource : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun W t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (E := E j) (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (W j) t) i) (Tsource i))
    (hπ : ∀ i, 0 < π i) (Cprep Cgraph θ ζ : ℝ)
    (hθ : 0 ≤ θ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ Cprep * θ)
    (hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ Cprep * θ)
    (Remainder : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (W : ∀ j, PlaneTimeAllMomentCarrier (E := E j) (K j + 1) ϖ ρ 0
      (volume.restrict (Icc a b)))
    (p : ℕ)
    (hrem : planeAllMomentFamilyEnergy K m ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => Remainder i W) ≤ ENNReal.ofReal ((ζ ^ p * (Cgraph * θ)) ^ 2) *
        planeAllMomentFamilyGradientEnergy K (m + p) ϖ ρ (volume.restrict (Icc a b)) π W) :
    planeAllMomentFamilyGradientEnergy K m ϖ ρ (volume.restrict (Icc a b)) π
      (fun i => R i ((Tsource i - Remainder i) W)) ≤
      ((scalarResponseGradientReservePrice Kmax L Cw N *
        ENNReal.ofReal (actualTaylorSourceInsertionPrice D Cprep Cgraph)) * (ENNReal.ofReal θ) ^ 2) *
      planeAllMomentFamilyGradientEnergy K (m + p) ϖ ρ (volume.restrict (Icc a b)) π W := by
  have he := planeComponentAllMomentResponse_actualTaylor_shifted_gradient_budget a b hab K Kmax hK
    v hvm hv V strain B lam hV ha hB hlam hbv hjets M hMm g hg hg4 hnear hsym
    t₀ S ϖ N m Cw C hm ρ L hρ hL hsmall hstrainSmall hreserve hdiv hwa hwb π R hR
    D A hA hC Tsource hTsource hπ (Cprep * θ) hrow hcol Remainder W p
    (ENNReal.ofReal ((ζ ^ p * (Cgraph * θ)) ^ 2)) hrem
  have hprice := actualTaylorSourceInsertionPrice_le_response_reserve D p Kmax N m hm L Cw
    Cprep Cgraph θ ζ hθ hζ hζ1
  have hb := mul_le_mul_of_nonneg_right hprice
    (show 0 ≤ planeAllMomentFamilyGradientEnergy K (m + p) ϖ ρ
      (volume.restrict (Icc a b)) π W from zero_le)
  apply le_trans he
  simpa only [scalarResponseGradientPrice, mul_assoc] using hb

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Homogeneous coupled native endpoints have a uniform rank-discounted mass bound. Finite weighted gradient energy is derived from the actual triangular equation. -/

theorem planeHomogeneous_rank_discounted_endpoint_energy_on.{u, v} (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D H : ℕ) (Bsrc : ℝ) :
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : AVRegularity.CycleWords.IsMetricNearIdentityOn (Set.Icc ta tb) G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (ϖ : ℝ) (zc : Vec 2)
        (_W : ChartWeights G v ta (tb - ta) ϖ zc n Cw)
        (_hr1 : rstar ≤ 1) (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
        (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (_hinit : ∀ i, weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i) ≠ ⊤),
        ∀ (V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
            (Vw : ∀ x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x)),
          IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
            (planeMetricSourceCoefficient Kslot D G A)
            V₀ (fun _ _ => 0) (fun _ _ => 0) V Vw →
          ∀ tp, tp ∈ Set.Icc ta tb →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V i tp)) ≤
            ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax CG Cw D Bsrc) ^ (2 * H)) *
              (2 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) *
                ∑ i, ENNReal.ofReal ((π i)⁻¹) *
                  weightedFactorialNormSq n ϖ zc rstar (Kslot i) (V₀ i)) := by
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    ϖ zc W hr1 hD A hA hc hAm hrow hcol rank hrank hzero V₀ hinit V Vw hsln tp htp
  let Gc := AVRegularity.CycleWords.metricClamp ta tb G
  have hGeq t (htt : t ∈ Set.Icc ta tb) : Gc t = G t :=
    AVRegularity.CycleWords.metricClamp_of_mem G htt
  have hGcm : Measurable (fun p : Set.Icc ta tb × Vec 2 => Gc p.1 p.2) := by
    convert hG_meas using 1
    funext p
    exact congrFun (hGeq p.1 p.1.2) p.2
  have hsym t (htt : t ∈ Set.Icc ta tb) z : (Gc t z).IsSymm := by
    rw [hGeq t htt]
    exact hG_symm t htt z
  have hsmooth t (htt : t ∈ Set.Icc ta tb) r c :
      ContDiff ℝ (max Kmax 1 : ℕ) (fun z => Gc t z r c) := by
    rw [hGeq t htt]
    exact hG_smooth t htt r c
  have hj t (htt : t ∈ Set.Icc ta tb) z j (hj1 : 1 ≤ j) (hjk : j ≤ Kmax) r c :
      ‖iteratedFDeriv ℝ j (fun z' => Gc t z' r c) z‖ ≤ CG j * g * δ ^ j := by
    rw [hGeq t htt]
    exact hG_jets t htt z j hj1 hjk r c
  exact planeHomogeneous_rank_discounted_endpoint_energy n Kmax CG Cw D H Bsrc
    π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    Gc g hg hg4 hGcm hsym (AVRegularity.CycleWords.isMetricNearIdentity_metricClamp ht hG_near)
    hsmooth hj ta (tb - ta) ϖ zc le_rfl (by simp only [add_sub_cancel]; exact le_rfl)
    (chartWeightsMetricClamp W) hr1 hD A hA hc hAm hrow hcol rank hrank hzero V₀ hinit
    V Vw (planeMetricSource_coupled_solution_metricClamp hsln) tp htp

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The actual normalized material forcing is a genuine L2 flux with the exact computed coupled-array readout on every rough native energy state. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

variable (F : ChartedFamily ι h D P' Ctx) (K : ι → ℕ) (hab : a ≤ b)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (W : ∀ u, ℝ → PlaneHk univ (K u + 1) (h u)) (v : ι) (t : ℝ)

def preparationReferenceNormalizedFlux : PlaneFluxL2 (h v) :=
  (planeMaterialDiffusion (E := h v) a b hab hφ ((l₀ : ℝ) * ocTauPP α q Λ m) 1 (ν⁻¹ * t) -
    ContinuousLinearMap.id ℝ (PlaneFluxL2 (h v)))
      (planeH1GradientOperator (truncatePlaneHk (show 1 ≤ K v + 1 by omega) (W v (ν⁻¹ * t)))) +
    ν⁻¹ • (if ht : ν⁻¹ * t ∈ Icc a b then
      preparationReferenceNativeFluxOperator F K hprep hcover hTau ha hK ν e E n hs actual hT he
        (ν⁻¹ * t) ht v (fun u => W u (ν⁻¹ * t)) else 0)

theorem preparationReferenceNormalizedFlux_ae (hD : 2 ≤ D) (hdesc : F.IsDescending K)
    (hν : 0 < ν) (ht : t ∈ Icc (ν * a) (ν * b)) (k : Fin 2) :
    (preparationReferenceNormalizedFlux F K hab hprep hcover hTau ha hK ν e E n hs actual hT he W v t k
      : Vec 2 → h v) =ᵐ[volume] fun x =>
        planeRawCouplingFlux K D t
          (preparationReferenceNormalizedCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν e E actual K)
          (fun u => W u (ν⁻¹ * t)) v x k := by
  have htold := positiveTimeNormalization_mem_Icc hν ht
  let du := planeH1GradientOperator (truncatePlaneHk (show 1 ≤ K v + 1 by omega) (W v (ν⁻¹ * t)))
  let G := (planeMaterialDiffusion (E := h v) a b hab hφ ((l₀ : ℝ) * ocTauPP α q Λ m) 1 (ν⁻¹ * t) -
    ContinuousLinearMap.id ℝ (PlaneFluxL2 (h v))) du
  let Q := preparationReferenceNativeFluxOperator F K hprep hcover hTau ha hK ν e E n hs actual hT he
    (ν⁻¹ * t) htold v (fun u => W u (ν⁻¹ * t))
  have hG := planeMaterialDiffusion_deviation_ae a b hab hφ
    ((l₀ : ℝ) * ocTauPP α q Λ m) 1 (ν⁻¹ * t) htold du k
  have hQ := preparationReferenceNativeFluxOperator_reference_coupling_ae F K hdesc hprep hcover
    hTau ha hK ν e E n hs actual hT he (ν⁻¹ * t) htold v (fun u => W u (ν⁻¹ * t)) k
  have hgrad : ∀ᵐ x ∂volume, ∀ j : Fin 2,
      du j x = (W v (ν⁻¹ * t)).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K v))⟩, fun _ => j⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  unfold preparationReferenceNormalizedFlux
  rw [dite_eq_left htold]
  filter_upwards [Lp.coeFn_add (G k) (ν⁻¹ • Q k), Lp.coeFn_smul ν⁻¹ (Q k), hG, hQ, hgrad]
    with x hsum hsm hGx hQx hgradx
  rw [preparationReferenceNormalizedCoefficient_raw_flux F hφ
    ((l₀ : ℝ) * ocTauPP α q Λ m) ν e E actual K hD]
  have hmetric : G k x = ∑ j : Fin 2,
      (chartMetric hφ ((l₀ : ℝ) * ocTauPP α q Λ m) (ν⁻¹ * t) x k j - if k = j then 1 else 0) •
        (W v (ν⁻¹ * t)).toFunction.jet
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K v))⟩, fun _ => j⟩ x := by
    apply hGx.trans
    simp only [one_smul]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun z : h v =>
      (chartMetric hφ ((l₀ : ℝ) * ocTauPP α q Λ m) (ν⁻¹ * t) x k j - if k = j then 1 else 0) • z)
        (hgradx j))
  exact hsum.trans (congrArg₂ (fun z w : h v => z + w) hmetric
    (hsm.trans (congrArg (fun z : h v => ν⁻¹ • z) hQx)))

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The retained error endpoint estimate derives its finite preparation and forcing energies from actual solution and native response data. -/

theorem planeRetained_error_endpoint_energy.{u, v}
    (n Kmax : ℕ) (CG Cw : ℕ → ℝ) (D H : ℕ) (Bsrc : ℝ) :
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (ta tb : ℝ) (_ht : ta ≤ tb) (rstar δ : ℝ) (_hrstar : 0 < rstar) (_hδ : 0 ≤ δ)
        (_hrδ : rstar * δ ≤ 1)
        (v : ℝ → Vec 2 → Vec 2)
        (_hv_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ C)
        (_hv_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2)
        (_hv_smooth : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
        (_hv_div : ∀ t ∈ Set.Icc ta tb, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
        (a B₀ lam : ℝ) (_ha : 0 ≤ a) (_hB₀ : 1 ≤ B₀) (_hlam : 0 < lam)
        (_hjets : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax → ∀ t ∈ Set.Icc ta tb, ∀ x,
          ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
        (_hB : B₀ * rstar / lam ≤ 1 / 2) (_hab : a * B₀ * rstar ^ 2 ≤ 1 / 8)
        (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) (_hg : 0 ≤ g) (_hg4 : g ≤ 1 / 4)
        (_hG_meas : Measurable fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2)
        (_hG_symm : ∀ t ∈ Set.Icc ta tb, ∀ z, (G t z).IsSymm)
        (_hG_near : IsMetricNearIdentity G g)
        (_hG_smooth : ∀ t ∈ Set.Icc ta tb, ∀ a' k : Fin 2,
          ContDiff ℝ (max Kmax 1 : ℕ) (fun z => G t z a' k))
        (_hG_jets : ∀ t ∈ Set.Icc ta tb, ∀ z : Vec 2, ∀ j : ℕ, 1 ≤ j → j ≤ Kmax →
          ∀ a' k : Fin 2, ‖iteratedFDeriv ℝ j (fun z' => G t z' a' k) z‖ ≤ CG j * g * δ ^ j)
        (tw S ϖ : ℝ) (_htw : tw ≤ ta) (_htb : tb ≤ tw + S)
        (_W : ChartWeights G v tw S ϖ (0 : Vec 2) n Cw)
        (_hD : 2 ≤ D)
        (A : ∀ i u, (d : admissibleOrders Kslot D i u) → ℝ → Vec 2 →
          PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
            PiLp 2 (fun _ : Fin 2 => h i))
        (_hA : ∀ i u d, coefficientSeminorm rstar (Kslot i) ta tb (A i u d) ≠ ⊤)
        (_hc : ∀ i u d t, t ∈ Set.Icc ta tb → ContDiff ℝ (Kslot i : ℕ) (A i u d t))
        (_hAm : ∀ i u d, Measurable (fun p : Set.Icc ta tb × Vec 2 => A i u d p.1 p.2))
        (_hrow : ∀ i, ∑ u, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (_hcol : ∀ u, ∑ i, schurMatrix 1 rstar π Kslot D ta tb A i u ≤ Bsrc)
        (rank : ι → ℕ) (_hrank : ∀ i, rank i ≤ H)
        (_hzero : ∀ i j, ¬ rank j < rank i → ∀ d, A i j d = 0)
        (_hr1 : rstar ≤ 1)
        (V₀ : ∀ i, PlaneHk Set.univ (Kslot i) (h i))
        (_hf : ∀ i, weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (V₀ i) ≠ ⊤)
        (uH u : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
        (wH w : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
        (_hH : IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
          (planeMetricSourceCoefficient Kslot D G A) V₀ (fun _ _ => 0) (fun _ _ => 0) uH wH)
        (X : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i))
          (Kslot i) ϖ rstar 0 (volume.restrict (Set.Icc ta tb)))
        (F : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i)))
        (_hX : ∀ i, PlaneTimeAllMomentRepresents (Kslot i) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) (X i) (F i))
        (Y : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)))
        (_hY : ∀ i, PlaneTimeAllMomentRepresents (Kslot i + 1) ϖ rstar 0
          (volume.restrict (Set.Icc ta tb)) (Y i) (w i)),
        IsCoupledWeakSolutionPlane 1 ta tb v D Kslot
          (planeMetricSourceCoefficient Kslot D G A) (fun _ => 0) F (fun _ _ => 0)
          (fun i t => uH i t - u i t) (fun i t => wH i t - w i t) →
        ∀ tp, tp ∈ Set.Icc ta tb →
          (∑ i, ENNReal.ofReal ((π i)⁻¹) *
            weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (uH i tp - u i tp)) ≤
          ENNReal.ofReal ((planeSourceRankScale.{u, v} n Kmax CG Cw D Bsrc) ^ (2 * H)) *
            (64 * ENNReal.ofReal (planeScalarSquaredConstant.{u, v} n Kmax CG Cw) *
              planeAllMomentFamilyEnergy Kslot n ϖ rstar
                (volume.restrict (Set.Icc ta tb)) π X) := by
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ htw htb W hD A hA hc hAm hrow hcol rank hrank hzero hr1
    V₀ hf uH u wH w hH X F hX Y hY hsln tp htp
  have hz : ∀ i j, ¬ rank j < rank i → ∀ d t x, A i j d t x = 0 := by
    intro i j hnot d t x
    exact congrFun (congrFun (hzero i j hnot d) t) x
  have hprepared := triangularMetric_weighted_geometry_energy_lt_top n Kmax CG Cw
    Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ 0 htw htb W hr1 D hD A hA hc hAm rank hz V₀ hf uH wH π hH
  have hYe := planeAllMomentFamilyGradientEnergy_ne_top Kslot n ϖ rstar hrstar
    (volume.restrict (Set.Icc ta tb)) π Y
  have he := planeRetained_error_gradient_finite Kslot n ϖ rstar ta tb π hπ
    uH wH w hH.2.1 hprepared Y hY hYe
  have hF (i : ι) : MemLp (F i) 2 (volume.restrict (Set.Icc ta tb)) :=
    (memLp_congr_ae (hX i)).mp
      (planeTimeAllMomentCarrier_memLp (Kslot i) ϖ rstar 0
        (volume.restrict (Set.Icc ta tb)) (X i))
  have hforcing : (∫⁻ t in Set.Icc ta tb, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ 0 rstar (Kslot i) (F i t)) ≠ ⊤ := by
    rw [← planeAllMomentFamilyEnergy_represented Kslot n ϖ rstar
      (volume.restrict (Set.Icc ta tb)) π X F hX]
    exact planeAllMomentFamilyEnergy_ne_top Kslot n ϖ rstar
      (volume.restrict (Set.Icc ta tb)) π X
  have hb := planeForced_zero_initial_endpoint_energy n Kmax CG Cw D H Bsrc
    π hπ Kslot hKslot ta tb ht rstar δ hrstar hδ hrδ
    v hv_bdd hv_meas hv_smooth hv_div strain B₀ lam ha hB₀ hlam hjets hB hab
    G g hg hg4 hG_meas hG_symm hG_near hG_smooth hG_jets
    tw S ϖ 0 htw htb W hD A hA hc hAm hrow hcol rank hrank hzero F hF hforcing
    (fun i t => uH i t - u i t) (fun i t => wH i t - w i t) he hsln tp htp
  rw [← planeAllMomentFamilyEnergy_represented Kslot n ϖ rstar
    (volume.restrict (Set.Icc ta tb)) π X F hX] at hb
  exact hb

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The actual normalized material forcing is a genuine L2 flux with the exact computed coupled-array readout on every rough native energy state. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

variable (F : ChartedFamily ι h D P' Ctx) (K : ι → ℕ) (c d : ℝ) (hcd : c ≤ d)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ u, K u ≤ Jchart) (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (W : ∀ u, ℝ → PlaneHk univ (K u + 1) (h u)) (v : ι) (t : ℝ)

def preparationWindowReferenceSubwindowNormalizedFlux : PlaneFluxL2 (h v) :=
  (planeMaterialDiffusion (E := h v) c d hcd hφ σ 1 (ν⁻¹ * t) -
    ContinuousLinearMap.id ℝ (PlaneFluxL2 (h v)))
      (planeH1GradientOperator (truncatePlaneHk (show 1 ≤ K v + 1 by omega) (W v (ν⁻¹ * t)))) +
    ν⁻¹ • (if ht : ν⁻¹ * t ∈ Icc a b then
      preparationWindowReferenceNativeFluxOperator F K hprep hcover σ hσ ha hK ν e E n hs actual hT he
        (ν⁻¹ * t) ht v (fun u => W u (ν⁻¹ * t)) else 0)

theorem preparationWindowReferenceSubwindowNormalizedFlux_ae (hsub : Icc c d ⊆ Icc a b) (hD : 2 ≤ D) (hdesc : F.IsDescending K)
    (hν : 0 < ν) (ht : t ∈ Icc (ν * c) (ν * d)) (k : Fin 2) :
    (preparationWindowReferenceSubwindowNormalizedFlux F K c d hcd hprep hcover σ hσ ha hK ν e E n hs actual hT he W v t k
      : Vec 2 → h v) =ᵐ[volume] fun x =>
        planeRawCouplingFlux K D t
          (preparationReferenceNormalizedCoefficient F hφ σ ν e E actual K)
          (fun u => W u (ν⁻¹ * t)) v x k := by
  have htsub := positiveTimeNormalization_mem_Icc hν ht
  have htold := hsub htsub
  let du := planeH1GradientOperator (truncatePlaneHk (show 1 ≤ K v + 1 by omega) (W v (ν⁻¹ * t)))
  let G := (planeMaterialDiffusion (E := h v) c d hcd hφ σ 1 (ν⁻¹ * t) -
    ContinuousLinearMap.id ℝ (PlaneFluxL2 (h v))) du
  let Q := preparationWindowReferenceNativeFluxOperator F K hprep hcover σ hσ ha hK ν e E n hs actual hT he
    (ν⁻¹ * t) htold v (fun u => W u (ν⁻¹ * t))
  have hG := planeMaterialDiffusion_deviation_ae c d hcd hφ
    σ 1 (ν⁻¹ * t) htsub du k
  have hQ := preparationWindowReferenceNativeFluxOperator_reference_coupling_ae F K hdesc hprep hcover
    σ hσ ha hK ν e E n hs actual hT he (ν⁻¹ * t) htold v (fun u => W u (ν⁻¹ * t)) k
  have hgrad : ∀ᵐ x ∂volume, ∀ j : Fin 2,
      du j x = (W v (ν⁻¹ * t)).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K v))⟩, fun _ => j⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  unfold preparationWindowReferenceSubwindowNormalizedFlux
  rw [dite_eq_left htold]
  filter_upwards [Lp.coeFn_add (G k) (ν⁻¹ • Q k), Lp.coeFn_smul ν⁻¹ (Q k), hG, hQ, hgrad]
    with x hsum hsm hGx hQx hgradx
  rw [preparationReferenceNormalizedCoefficient_raw_flux F hφ
    σ ν e E actual K hD]
  have hmetric : G k x = ∑ j : Fin 2,
      (chartMetric hφ σ (ν⁻¹ * t) x k j - if k = j then 1 else 0) •
        (W v (ν⁻¹ * t)).toFunction.jet
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K v))⟩, fun _ => j⟩ x := by
    apply hGx.trans
    simp only [one_smul]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun z : h v =>
      (chartMetric hφ σ (ν⁻¹ * t) x k j - if k = j then 1 else 0) • z)
        (hgradx j))
  exact hsum.trans (congrArg₂ (fun z w : h v => z + w) hmetric
    (hsm.trans (congrArg (fun z : h v => ν⁻¹ • z) hQx)))

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! The source Schur budget is uniform over reference times in the covered preparation window. -/

/-- The same family-independent Schur constant applies at every covered reference time. -/
theorem preparation_window_reference_cell_source_schur_budget (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (b : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ b v u),
        IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
        ∀ σ ∈ Set.Icc tS tZ,
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b →
        ∀ yc : Vec 2, ∀ v u,
          schurMatrix 1 (ρ / e) π K D ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ))
            (preparationReferenceCellSourceCoefficient F hφ σ
              ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * b v u := by
  obtain ⟨Cprep, hC, hsamp⟩ := preparation_window_reference_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart _hmol Cm Cchart
  refine ⟨Cprep, hC, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ P' Ctx F π hπ K hK actual b hb hc hcover σ hσ henv yc v u
  have he : 0 < e := hρ.trans_le hρe
  have hs := hsamp α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ
    hν hρ hρe heE F π hπ K hK actual b hb hc hcover σ hσ henv
  rw [preparationReferenceCellSourceCoefficient_schurMatrix F hφ _ ν e _ tS tZ ρ hν he hρ]
  exact sampledEnvelope_schurMatrix_le (referenceChartedFamily F hφ σ)
    π hπ K actual tS tZ ν e _ ρ Cprep hν hρ b hs v u
    (mul_nonneg (zero_le_one.trans hC) (hb v u))

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The homogeneous coupled system transfers to a genuine native material weak curve in every row. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeHomogeneous_material_weak_curve {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d t, t ∈ Icc a b → ContDiff ℝ (K i : ℕ) (A i i' d t))
    (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hp : ∀ t, IsZ2Periodic (v t))
    (hvc : ∀ t ∈ Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (hAm : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => A i i' d p.1 p.2))
    (f : ∀ i, PlaneHk univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i))
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0)
      (fun _ _ => 0) u w) (i : ι) :
    PlaneWeakHilbertCurve a b
      (fun t => planeL2FlowPull hφ t s (coupledPlaneL2Trace u i t))
      (fun t => planeH1ChartPull hφ t s (coupledPlaneH1Slice w i t))
      (fun t => planeWeakDualRepresentative (planeMaterialTransport a b hab hφ s v hv hp t)
        (planeMaterialDiffusion a b hab hφ s ν t)
        (planeH1ChartPull hφ t s (coupledPlaneH1Slice w i t))
        (planeFluxChartPull hφ t s (planeFluxValueOperator (E := h i) (K i)
          (planeCouplingFluxRow hab ρ hρ K D A hA hc w i t)))) := by
  have hM : 0 ≤ M := (norm_nonneg (v a 0)).trans (hvb a ⟨le_rfl, hab⟩ 0)
  apply planeMaterial_weak_curve hab hφ s ν v hv hp hvc hM hvb
  · exact planeFluxValueOperator_memLp (K i) _
      (planeCouplingFluxRow_memLp hab ρ hρ K D A hA hc w hAm hs.2.1 i)
  · exact planeHomogeneous_coupledWeakHilbertCurve hab ρ hρ K D A hA hc w
      ν v hvc hvm M hvb hAm f u hs i

end AVRegularity.CycleJointProofs
end
