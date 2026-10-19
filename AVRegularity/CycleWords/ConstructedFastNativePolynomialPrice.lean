-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.CellComplexH1Separability
import AVRegularity.CycleWords.GeometryErrorPieceMassBudget
import AVRegularity.Weighted.WordNativeSolutionPack
import AVRegularity.CycleWords.InteriorPulseActualWeakNativeShortPropagation
public import AVRegularity.CycleWords.ConstructedActualWeakNativeGapDecay
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite graded initial moments propagate through the actual response chain,
by the response level and the original descending graph rank. -/

theorem geometryResponse_component_lower_apriori (q Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
    (_hD : 2 ≤ D) (J Ks : ℕ) (K : ι → ℕ) (_hK : ∀ u, K u ≤ Kmax)
    (_hdesc : F.IsDescending K) (p : P) (c : Ctx p)
    (s a b ρ δ ϖ g : ℝ) (X0 phase : Vec 2)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (strain B lam : ℝ)
    (_HC : ScalarCoefficientInputs Kmax CG a b ρ δ v strain B lam (fun t _ => G t 0) g)
    (tw S : ℝ) (_htw : tw ≤ a) (_htb : b ≤ tw + S)
    (_W : ChartWeights (fun t _ => G t 0) v tw S ϖ 0 q Cw)
    (f : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u) (h u))
    (U : ∀ (_ : Fin (J + 1)) u, ℝ → PlaneHk Set.univ (K u) (h u))
    (Uw : ∀ (_ : Fin (J + 1)) u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (_hsol : IsPlaneChainFrom (geometryResponseData J Ks G 0 (F.cellFiber s phase p c) X0 δ)
      (fun _ u => K u) a b v f (fun _ _ _ => 0) U Uw)
    (j : Fin (J + 1)) (x : ι)
    (V : ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (_hV : MemLp V 2 (volume.restrict (Set.Icc a b)))
    (_hv : ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
      geometryResponseSourceFlux F J Ks K p c G s δ X0 phase Uw j x t),
    nativeComponentEnergy q ϖ ρ a b (U j x) (Uw j x) ≤
      ENNReal.ofReal A * (weightedFactorialNormSq q ϖ 0 ρ (K x) (f j x) +
        16 * ∫⁻ t in Set.Icc a b, weightedFactorialNormSq q ϖ 0 ρ (K x) (V t)) := by
  obtain ⟨A, hA, henergy⟩ := weighted_energy_plane_component_lower_apriori q Kmax CG Cw
  refine ⟨A, hA, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F hD J Ks K hK hdesc p c s a b ρ δ ϖ g X0 phase v G
    strain B lam HC tw S htw htb W f U Uw hsol j x V hV hv
  obtain ⟨Mv, hMv, hvc, hvb, _, hGb⟩ := scalarCoefficientInputs_spatial_bounds HC
  have hscalar := geometryResponse_scalar_component_redistribution F hD J Ks K hdesc p c a b s δ
    X0 phase v G Mv (5 / 4) hMv (by norm_num) hvc hvb
    (fun t ht k l => hGb t ht k l 0) f U Uw hsol j x V
    (by
    filter_upwards [hv] with t ht
    filter_upwards [ht] with z hz
    exact hz)
  have hscalar2 := geometryScalarSolution_order_two D hD (h := fun _ : Unit => h x)
    (fun t _ => G t 0) (fun _ _ => K x) a b v (fun _ _ => f j x) (fun _ _ => V)
    (fun _ _ => U j x) (fun _ _ => Uw j x) hscalar
  have hbudget := henergy (h := fun _ : Unit => h x) (fun _ => K x) (fun _ => hK x)
    a b HC.time ρ δ HC.radius HC.delta HC.scale
    v HC.drift_bounded HC.drift_measurable HC.drift_smooth HC.drift_divergence
    strain B lam HC.strain HC.drift_constant HC.drift_length HC.drift_jets HC.drift_scale HC.drift_small
    (fun t _ => G t 0) g HC.metric_size HC.metric_small HC.metric_measurable HC.metric_symmetric HC.metric_near
    HC.metric_smooth HC.metric_jets tw S ϖ 0 htw htb W
    (fun _ => f j x) (fun _ => V) (fun _ => nativeTimeNorm_lower_integral_lt_top hV)
    (fun _ => U j x) (fun _ => Uw j x) hscalar2 ()
  exact hbudget

/-! Finite graded initial moments propagate through the actual response chain,
by the response level and the original descending graph rank. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem response_weighted_carrier_energy_ne_top (F : ChartedFamily ι h D P Ctx)
    (hD : 2 ≤ D) (Hdepth Ks J Kmax M : ℕ) (hdepth : F.HasDepthAtMost Hdepth)
    (π : ι → ℝ) (hπ : ∀ u, 0 < π u) (K : ι → ℕ) (hK : ∀ u, K u ≤ Kmax)
    (hdesc : F.IsDescending K) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (Cmol : ℕ → ℝ) (Jmol : ℕ) (b₀ : ι → ι → ℝ) (hKs : Ks ≤ Jmol)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ Cmol Jmol b₀) (hmeas : F.IsTimeMeasurable)
    (hb₀ : ∀ v u, 0 ≤ b₀ v u) (hrow : ∀ v, ∑ u, b₀ v u ≤ 1) (hcol : ∀ u, ∑ v, b₀ v u ≤ 1)
    (p : P) (c : Ctx p) (s a b ϖ ζ g : ℝ) (hs : s ≠ 0)
    (hϖ : 0 < ϖ) (hscale : (ρ / e) * ϖ ≤ 1) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hδ : e / E = ζ * ϖ) (X0 phase : Vec 2)
    (hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (CG Cw : ℕ → ℝ) (hCG : ∀ r, 0 ≤ CG r)
    (hGm : ∀ X k l, Measurable (fun t => G t X k l))
    (hGs : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l))
    (hGj : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ CG r * g * (e / E) ^ r)
    (strain B lam : ℝ)
    (HC : ScalarCoefficientInputs Kmax CG a b (ρ / e) (e / E) v strain B lam
      (fun t _ => G t 0) g)
    (tw S : ℝ) (htw : tw ≤ a) (htb : b ≤ tw + S)
    (W : ∀ q ≤ M, ChartWeights (fun t _ => G t 0) v tw S ϖ 0 q Cw)
    (f : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u) (h u))
    (U : ∀ (_ : Fin (J + 1)) u, ℝ → PlaneHk Set.univ (K u) (h u))
    (Uw : ∀ (_ : Fin (J + 1)) u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (hd : ∀ j x q, q + (j.val + familyDepthRank F Hdepth x) * Ks ≤ M →
      weightedFactorialNormSq q ϖ 0 (ρ / e) (K x) (f j x) ≠ ⊤)
    (hsol : IsPlaneChainFrom (geometryResponseData J Ks G 0 (F.cellFiber s phase p c) X0 (e / E))
      (fun _ u => K u) a b v f (fun _ _ _ => 0) U Uw) :
    ∀ j x q, q + (j.val + familyDepthRank F Hdepth x) * Ks ≤ M →
      nativeComponentEnergy q ϖ (ρ / e) a b (U j x) (Uw j x) ≠ ⊤ := by
  have hw (j : Fin (J + 1)) (u : ι) : MemLp (Uw j u) 2 (volume.restrict (Set.Icc a b)) :=
    hsol.2.1 (j, u)
  obtain ⟨Mv, hMv, hvc, hvb, _, hGb⟩ := scalarCoefficientInputs_spatial_bounds HC
  have hfinish (j : Fin (J + 1)) (x : ι) (q : ℕ)
      (hq : q + (j.val + familyDepthRank F Hdepth x) * Ks ≤ M)
      (hedge : ∀ u, Nonempty (F.Γ x u) →
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (q + Ks) ϖ 0 (ρ / e) (K u) (Uw j u t)) ≠ ⊤)
      (hprev : ∀ j', j.val = j'.val + 1 →
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (q + Ks) ϖ 0 (ρ / e) (K x) (Uw j' x t)) ≠ ⊤) :
      nativeComponentEnergy q ϖ (ρ / e) a b (U j x) (Uw j x) ≠ ⊤ := by
    obtain ⟨V, hV, hVe, hv⟩ := geometryResponse_native_component_forcing F Ks J Kmax π hπ K hK hdesc dom
      ν e E ρ hν he hE hρ Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1
      HC.metric_size hδ X0 phase hwindow G CG hCG hGm hGs hGj Uw hw j x q hedge hprev
    have hscalar := geometryResponse_scalar_component_redistribution F hD J Ks K hdesc p c a b s (e / E)
      X0 phase v G Mv (5 / 4) hMv (by norm_num) hvc hvb
      (fun t ht k l => hGb t ht k l 0) f U Uw hsol j x V
      (by
        filter_upwards [hv] with t ht
        filter_upwards [ht] with z hz
        exact hz)
    have hscalar2 := geometryScalarSolution_order_two D hD (h := fun _ : Unit => h x)
      (fun t _ => G t 0) (fun _ _ => K x) a b v (fun _ _ => f j x) (fun _ _ => V)
      (fun _ _ => U j x) (fun _ _ => Uw j x) hscalar
    obtain ⟨A, _, henergy⟩ := weighted_energy_plane_component_lower_apriori q Kmax CG Cw
    have hbudget := henergy (h := fun _ : Unit => h x) (fun _ => K x) (fun _ => hK x)
      a b HC.time (ρ / e) (e / E) HC.radius HC.delta HC.scale
      v HC.drift_bounded HC.drift_measurable HC.drift_smooth HC.drift_divergence
      strain B lam HC.strain HC.drift_constant HC.drift_length HC.drift_jets HC.drift_scale HC.drift_small
      (fun t _ => G t 0) g HC.metric_size HC.metric_small HC.metric_measurable HC.metric_symmetric HC.metric_near
      HC.metric_smooth HC.metric_jets tw S ϖ 0 htw htb (W q (by omega))
      (fun _ => f j x) (fun _ => V) (fun _ => nativeTimeNorm_lower_integral_lt_top hV)
      (fun _ => U j x) (fun _ => Uw j x) hscalar2 ()
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hd j x q hq, ENNReal.mul_ne_top (by norm_num) hVe⟩)) hbudget
  have hlevels : ∀ l, ∀ hl : l < J + 1, ∀ x q,
      q + (l + familyDepthRank F Hdepth x) * Ks ≤ M →
      nativeComponentEnergy q ϖ (ρ / e) a b (U ⟨l, hl⟩ x) (Uw ⟨l, hl⟩ x) ≠ ⊤ := by
    intro l
    induction l using Nat.strong_induction_on with
    | h l ih =>
      intro hl
      have hvertices : ∀ r, ∀ x, familyDepthRank F Hdepth x = r → ∀ q,
          q + (l + familyDepthRank F Hdepth x) * Ks ≤ M →
          nativeComponentEnergy q ϖ (ρ / e) a b (U ⟨l, hl⟩ x) (Uw ⟨l, hl⟩ x) ≠ ⊤ := by
        intro r
        induction r using Nat.strong_induction_on with
        | h r ihr =>
          intro x hx q hq
          refine hfinish ⟨l, hl⟩ x q hq ?_ ?_
          · intro u hu
            have hr := familyDepthRank_strict F Hdepth hdepth hu
            have hc : l + familyDepthRank F Hdepth u + 1 ≤ l + familyDepthRank F Hdepth x := by omega
            have hm := Nat.mul_le_mul_right Ks hc
            have hcost : q + Ks + (l + familyDepthRank F Hdepth u) * Ks ≤ M := by
              have ht := (Nat.add_le_add_left hm q).trans hq
              simpa only [Nat.add_mul, one_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht
            exact nativeComponentEnergy_gradient_ne_top (q + Ks) ϖ (ρ / e) a b
              (U ⟨l, hl⟩ u) (Uw ⟨l, hl⟩ u)
              (ihr (familyDepthRank F Hdepth u) (by omega) u rfl (q + Ks) hcost)
          · intro j' hj'
            have hlt : j'.val < l := by change l = j'.val + 1 at hj'; omega
            have hc : j'.val + familyDepthRank F Hdepth x + 1 = l + familyDepthRank F Hdepth x := by
              change l = j'.val + 1 at hj'
              omega
            have hcost : q + Ks + (j'.val + familyDepthRank F Hdepth x) * Ks ≤ M := by
              have heq : q + Ks + (j'.val + familyDepthRank F Hdepth x) * Ks =
                  q + (l + familyDepthRank F Hdepth x) * Ks := by
                calc
                  _ = q + (j'.val + familyDepthRank F Hdepth x + 1) * Ks := by ring
                  _ = _ := by rw [hc]
              rw [heq]
              exact hq
            exact nativeComponentEnergy_gradient_ne_top (q + Ks) ϖ (ρ / e) a b
              (U j' x) (Uw j' x) (ih j'.val hlt j'.isLt x (q + Ks) hcost)
      intro x q hq
      exact hvertices (familyDepthRank F Hdepth x) x rfl q hq
  intro j x q hq
  exact hlevels j.val j.isLt x q hq
end

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.CycleWords

theorem cycle_geometry_energy_proof (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (D n Kmax qJ : ℕ), 2 ≤ D → Kmax + 1 ≤ qJ →
      ∀ (CG : ℕ → ℝ) (Cb CT g0 : ℝ), g0 ≤ 1 / 4 →
      ∃ Cn : ℝ, 0 ≤ Cn ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ' : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ')
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmM : m ≤ M') (ν B : ℝ) (_hν : κ' m = ν) (_hB : κ' (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (ta T ρs g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsGeometryCover α q Λ m ζ Φ hφ ν B T ta ρs g g0 a B₀ lam Cb CT qJ Kmax CG l₀ P y₀)
        (ϖ rstar : ℝ) (_hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * T))
        (_hrstar : rstar = ρs / ocEpsilon q Λ m)
        (Gs : Fin P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
        (_hGs : ∀ i : Fin P,
          Gs i = ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) ∨
            Gs i = fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t 0)
        (V₀ : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (Fl : ∀ (_ : Fin P) (x : ι), ℝ →
          PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
        (fV : ∀ (_ : Fin P) (x : ι), PlaneHk Set.univ (Kslot x) (h x))
        (V : ∀ (_ : Fin P) (_ : Fin 1) (x : ι), ℝ → PlaneHk Set.univ (Kslot x) (h x))
        (Vw : ∀ (_ : Fin P) (_ : Fin 1) (x : ι), ℝ → PlaneHk Set.univ (Kslot x + 1) (h x))
        (_hV : ∀ i : Fin P, IsPlaneChainFrom (geometryScalarData D (Gs i)) (fun _ x => Kslot x)
          (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i))
          (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
          (fun _ x => fV i x) (fun _ x => Fl i x) (V i) (Vw i))
        (_hfV0 : ∀ i : Fin P, i.val = 0 → fV i = V₀)
        (_hfV : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ x, planeValue (fV i' x) =ᵐ[volume]
          fun z => planeValue (V i 0 x (ocPieceEnd α q Λ m ν ta T (l₀ + i)))
            (ocCellTransition α q Λ m (Φ (m - 1)) hφ (l₀ + i)
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i') z)),
      ∀ i : Fin P,
        geometryEnergyNorm π Kslot n ϖ 0 rstar (ocPieceStart α q Λ m ν ta (l₀ + i))
            (ocPieceEnd α q Λ m ν ta T (l₀ + i)) (fun x => V i 0 x) (fun x => Vw i 0 x) ≤
          ENNReal.ofReal Cn *
            (geometryDataNorm π Kslot n ϖ 0 rstar V₀ +
              ∑ i' : Fin P, geometryFluxNorm π Kslot n ϖ 0 rstar
                (ocPieceStart α q Λ m ν ta (l₀ + i')) (ocPieceEnd α q Λ m ν ta T (l₀ + i'))
                (Fl i')) := by
  obtain ⟨Cw, Λ₀, hΛ₀, hw⟩ := geometryCover_uniform_adjoint_weights hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ D n Kmax qJ hD hqJ CG Cb CT g0 hg0
  obtain ⟨A, hA, hp⟩ := geometryPiece_lower_energy n Kmax CG Cw
  let R : ℝ := (uniformPullbackSquareBudget cellTransitionJetBudget Kmax *
    (1 + 4 * (2 * ((2 : ℝ) ^ 23 + 1)) ^ 2) ^ n) ^ (1 / 2 : ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg (mul_nonneg (uniformPullbackSquareBudget_nonneg _ _) (by positivity)) _
  let H : ℝ := 1 + A * (R + 1)
  have hH : 1 ≤ H := by
    exact le_add_of_nonneg_right (mul_nonneg hA (by positivity : 0 ≤ R + 1))
  have hAH : A ≤ H := by dsimp [H]; nlinarith [mul_nonneg hA hR]
  have hARH : A * R + A ≤ H := by dsimp [H]; nlinarith
  let N := Nat.ceil (CT + 2)
  refine ⟨H ^ N, by positivity, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot Φ hΦ M' κ' hband m hm2 hmM ν B hν hB hφ
    ta T ρs g a B₀ lam l₀ P y₀ cov ϖ rstar hϖ hrstar Gs hGs V₀ Fl fV V Vw hV hfV0 hfV
  subst ϖ
  subst rstar
  let ϖ := ocEpsilon q Λ m / Real.sqrt (B * T)
  let r := ρs / ocEpsilon q Λ m
  let left := fun i : Fin P => ocPieceStart α q Λ m ν ta (l₀ + i)
  let right := fun i : Fin P => ocPieceEnd α q Λ m ν ta T (l₀ + i)
  let E := fun i : Fin P => geometryEnergyNorm π Kslot n ϖ 0 r (left i) (right i)
    (fun x => V i 0 x) (fun x => Vw i 0 x)
  let F := fun i : Fin P => geometryFluxNorm π Kslot n ϖ 0 r (left i) (right i) (Fl i)
  let Dt := geometryDataNorm π Kslot n ϖ 0 r V₀
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ1
  have hr : 0 < r := div_pos cov.pos.2.2.2 he
  have hr1 : r ≤ 1 := (div_le_one he).mpr cov.rho_e
  have hcount : P ≤ N := by
    have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ1
    have hb := renewal_piece_count_bound (ocTauPP α q Λ m) ta T CT l₀ P hh
      cov.window.2.1 cov.window.2.2.1 cov.comparable.1
    have hc : CT + 2 ≤ (N : ℝ) := Nat.le_ceil _
    exact_mod_cast hb.le.trans hc
  by_cases hfinite : Dt + ∑ i, F i = ⊤
  · intro i
    change E i ≤ ENNReal.ofReal (H ^ N) * (Dt + ∑ j, F j)
    rw [hfinite, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (pow_pos (lt_of_lt_of_le zero_lt_one hH) N)).ne']
    exact le_top
  have hforce : ∀ i x, (∫⁻ t in Set.Icc (left i) (right i), ENNReal.ofReal (‖Fl i x t‖ ^ 2)) < ⊤ := by
    intro i x
    have hf : F i ≠ ⊤ := ne_top_of_le_ne_top hfinite
      ((Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ i)).trans (le_add_left le_rfl))
    exact geometryFluxNorm_lower_component_finite π hπ Kslot n ϖ 0 r (left i) (right i) hr (Fl i) hf x
  have hpiece : ∀ i, E i ≤ ENNReal.ofReal A *
      (geometryDataNorm π Kslot n ϖ 0 r (fV i) + F i) := by
    intro i
    obtain ⟨W⟩ := hw Λ hΛ Φ M' κ' hband m hm2 hmM ν B hν hB hφ T ta ρs g g0 a B₀ lam Cb CT
      qJ Kmax CG l₀ P y₀ cov hg0 i (Gs i) (hGs i) n
    exact hp π hπ Kslot hKslot hΛ1 hζ hφ hqJ cov hg0 i (Gs i) (hGs i) W D hD
      (fV i) (Fl i) (hforce i) (V i) (Vw i) (hV i)
  change ∀ i : Fin P, E i ≤ ENNReal.ofReal (H ^ N) * (Dt + ∑ j, F j)
  rw [ENNReal.ofReal_pow (le_trans zero_le_one hH)]
  apply finite_renewal_budget hcount E Dt (∑ i, F i) (ENNReal.ofReal A) (ENNReal.ofReal R)
    (ENNReal.ofReal H)
  · simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hH
  · exact ENNReal.ofReal_le_ofReal hAH
  · rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add (mul_nonneg hA hR) hA]
    exact ENNReal.ofReal_le_ofReal hARH
  · intro i hi
    have hz := hfV0 i hi
    have hb := hpiece i
    rw [hz] at hb
    exact hb.trans (mul_le_mul_right (add_le_add le_rfl
      (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ i))) _)
  · intro i j hij
    have heq : (j.val : ℕ) = i.val + 1 := hij
    have hc : ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ j =
        ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ (i.val + 1) := by rw [heq]
    have hrenew := cellTransition_family_data_norm α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ
      m (by omega) hφ l₀ y₀ i.val ϖ n π Kslot Kmax hKslot
      (fun x => V i 0 x (right i)) (fV j) r hr.le hr1
      (by intro x; simpa only [hc] using hfV i j hij x)
    have hend := geometryCover_piece_nonempty hΛ1 cov i
    have hd := geometryDataNorm_at_time_le_energy π Kslot n ϖ 0 r (left i) (right i) (right i)
      ⟨hend, le_rfl⟩ (fun x => V i 0 x) (fun x => Vw i 0 x)
    have hdata : geometryDataNorm π Kslot n ϖ 0 r (fV j) ≤ ENNReal.ofReal R * E i :=
      hrenew.trans (mul_le_mul_right hd _)
    exact (hpiece j).trans (mul_le_mul_right (add_le_add hdata
      (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ j))) _)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Higher moments on actual source edges and on the preceding level produce
a genuine native forcing for one response component. -/

theorem geometryResponse_component_budget_moments_uniform (Ks Kmax M : ℕ)
    (CG Cw : ℕ → ℝ) (hCG : ∀ r, 0 ≤ CG r) :
    ∃ CT CM A : ℝ, 0 ≤ CT ∧ 0 ≤ CM ∧ 0 ≤ A ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
    (_hD : 2 ≤ D) (J : ℕ) (π : ι → ℝ) (_hπ : ∀ u, 0 < π u)
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
    (j : Fin (J + 1)) (vtx : ι) (n : ℕ) (_hn : n ≤ M)
    (_hsource : ∀ u, Nonempty (F.Γ vtx u) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (Uw j u t)) ≠ ⊤)
    (_hprev : ∀ j', j.val = j'.val + 1 →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K vtx) (Uw j' vtx t)) ≠ ⊤) 
    (vdrift : ℝ → Vec 2 → Vec 2) (strain B lam : ℝ)
    (_HC : ScalarCoefficientInputs Kmax CG a b (ρ / e) (e / E) vdrift strain B lam
      (fun t _ => G t 0) g)
    (tw S : ℝ) (_htw : tw ≤ a) (_htb : b ≤ tw + S)
    (_W : ChartWeights (fun t _ => G t 0) vdrift tw S ϖ 0 n Cw)
    (f : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u) (h u))
    (U : ∀ (_ : Fin (J + 1)) u, ℝ → PlaneHk Set.univ (K u) (h u))
    (_hsol : IsPlaneChainFrom (geometryResponseData J Ks G 0 (F.cellFiber s phase p c) X0 (e / E))
      (fun _ u => K u) a b vdrift f (fun _ _ _ => 0) U Uw),
    ENNReal.ofReal ((π vtx)⁻¹) * nativeComponentEnergy n ϖ (ρ / e) a b (U j vtx) (Uw j vtx) ≤
      ENNReal.ofReal A * (ENNReal.ofReal ((π vtx)⁻¹) *
        weightedFactorialNormSq n ϖ 0 (ρ / e) (K vtx) (f j vtx) +
        32 * ENNReal.ofReal (originalTaylorGraphConstant Ks Kmax CT Cmol) *
          ∑ u, ENNReal.ofReal ((Real.sqrt (π u / π vtx) *
            (∑ α : OriginalSourceIndex F vtx u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT vtx u α)) *
            (π u)⁻¹) *
            (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (Uw j u t)) +
        32 * (ENNReal.ofReal ((π vtx)⁻¹) *
          ENNReal.ofReal ((4 * Real.sqrt (multiplicationDensityBudget (K vtx)) * (CM * g * ζ)) ^ 2) *
          ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then
            (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K vtx) (Uw j' vtx t)) else 0)) := by
  obtain ⟨CT, CM, hCT, hCM, hflux⟩ := geometryResponse_native_component_forcing_quantitative_uniform Ks Kmax CG hCG
  classical
  choose Aq hAq henergy using (fun q => geometryResponse_component_lower_apriori q Kmax CG Cw)
  let A := ∑ q ∈ Finset.range (M + 1), Aq q
  have hA : 0 ≤ A := Finset.sum_nonneg (fun q _ => hAq q)
  refine ⟨CT, CM, A, hCT, hCM, hA, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F hD J π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1 hg hδ
    X0 phase hwindow G hGm hGs hGj Uw hUw j vtx n hn hsource hprev vdrift strain B lam HC tw S htw htb W f U hsol
  obtain ⟨V, hV, hVe, hv, hbudget⟩ := hflux F J π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1 hg hδ
    X0 phase hwindow G hGm hGs hGj Uw hUw j vtx n hsource hprev
  have he := henergy n F hD J Ks K hK hdesc p c s a b (ρ / e) (e / E) ϖ g X0 phase
    vdrift G strain B lam HC tw S htw htb W f U Uw hsol j vtx V hV hv
  have hb := normalized_forced_component_budget ((π vtx)⁻¹) (Aq n)
    (originalTaylorGraphConstant Ks Kmax CT Cmol) (hAq n) _ _ _ _ _ he hbudget

  apply hb.trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact Finset.single_le_sum (fun q _ => hAq q) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-! Higher moments on actual source edges and on the preceding level produce
a genuine native forcing for one response component. -/

theorem geometryResponse_component_recurrence_uniform (Ks Kmax M : ℕ)
    (CG Cw Cmol : ℕ → ℝ) (hCG : ∀ r, 0 ≤ CG r) :
    ∃ CT CM Bprice : ℝ, 0 ≤ CT ∧ 0 ≤ CM ∧ 1 ≤ Bprice ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
    (_hD : 2 ≤ D) (J : ℕ) (π : ι → ℝ) (_hπ : ∀ u, 0 < π u)
    (K : ι → ℕ) (_hK : ∀ u, K u ≤ Kmax) (_hdesc : F.IsDescending K)
    (dom : F.Domain) (ν e E ρ : ℝ) (_hν : 0 < ν) (_he : 0 < e) (_hE : 0 < E) (_hρ : 0 < ρ)
    (Jmol : ℕ) (b₀ : ι → ι → ℝ) (_hKs : Ks ≤ Jmol)
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
    (j : Fin (J + 1)) (vtx : ι) (n : ℕ) (_hn : n ≤ M)
    (_hsource : ∀ u, Nonempty (F.Γ vtx u) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (Uw j u t)) ≠ ⊤)
    (_hprev : ∀ j', j.val = j'.val + 1 →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K vtx) (Uw j' vtx t)) ≠ ⊤) 
    (vdrift : ℝ → Vec 2 → Vec 2) (strain B lam : ℝ)
    (_HC : ScalarCoefficientInputs Kmax CG a b (ρ / e) (e / E) vdrift strain B lam
      (fun t _ => G t 0) g)
    (tw S : ℝ) (_htw : tw ≤ a) (_htb : b ≤ tw + S)
    (_W : ChartWeights (fun t _ => G t 0) vdrift tw S ϖ 0 n Cw)
    (f : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u) (h u))
    (U : ∀ (_ : Fin (J + 1)) u, ℝ → PlaneHk Set.univ (K u) (h u))
    (_hsol : IsPlaneChainFrom (geometryResponseData J Ks G 0 (F.cellFiber s phase p c) X0 (e / E))
      (fun _ u => K u) a b vdrift f (fun _ _ _ => 0) U Uw),
    let θ := originalTaylorGraphConstant Ks Kmax CT Cmol
    let price := fun u => Real.sqrt (π u / π vtx) *
      (∑ α : OriginalSourceIndex F vtx u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT vtx u α)
    ENNReal.ofReal ((π vtx)⁻¹) * nativeComponentEnergy n ϖ (ρ / e) a b (U j vtx) (Uw j vtx) ≤
      ENNReal.ofReal Bprice * (ENNReal.ofReal ((π vtx)⁻¹) *
        weightedFactorialNormSq n ϖ 0 (ρ / e) (K vtx) (f j vtx)) +
      ENNReal.ofReal Bprice * ENNReal.ofReal ((g * ζ) ^ 2) *
        (∑ j' : Fin (J + 1), if j.val = j'.val + 1 then
          ENNReal.ofReal ((π vtx)⁻¹) * nativeComponentEnergy (n + Ks) ϖ (ρ / e) a b (U j' vtx) (Uw j' vtx) else 0) +
      ENNReal.ofReal Bprice * ∑ u, ENNReal.ofReal (price u / (1 + θ)) *
        (ENNReal.ofReal ((π u)⁻¹) * nativeComponentEnergy (n + Ks) ϖ (ρ / e) a b (U j u) (Uw j u)) := by
  classical
  obtain ⟨CT, CM, A, hCT, hCM, hA, hbudget⟩ := geometryResponse_component_budget_moments_uniform Ks Kmax M CG Cw hCG
  let θ := originalTaylorGraphConstant Ks Kmax CT Cmol
  let Sprice := 32 * θ * (1 + θ)
  let Mprice := 32 * (metricInsertionUniformPrice Kmax CM) ^ 2
  let Bprice := 1 + A + A * Sprice + A * Mprice
  have hθ : 0 ≤ θ := originalTaylorGraphConstant_nonneg Ks Kmax CT Cmol
  have hS : 0 ≤ Sprice := by dsimp [Sprice]; positivity
  have hMp : 0 ≤ Mprice := by dsimp [Mprice]; positivity
  have hB : 1 ≤ Bprice := by dsimp [Bprice]; nlinarith only [hA, mul_nonneg hA hS, mul_nonneg hA hMp]
  have hAB : A ≤ Bprice := by dsimp [Bprice]; nlinarith only [hA, mul_nonneg hA hS, mul_nonneg hA hMp]
  have hSB : A * Sprice ≤ Bprice := by dsimp [Bprice]; nlinarith only [hA, mul_nonneg hA hMp]
  have hMB : A * Mprice ≤ Bprice := by dsimp [Bprice]; nlinarith only [hA, mul_nonneg hA hS]
  refine ⟨CT, CM, Bprice, hCT, hCM, hB, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F hD J π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1 hg hδ
    X0 phase hwindow G hGm hGs hGj Uw hUw j vtx n hn hsource hprev vdrift strain B lam HC tw S htw htb W f U hsol
  have hb := hbudget F hD J π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1 hg hδ
    X0 phase hwindow G hGm hGs hGj Uw hUw j vtx n hn hsource hprev vdrift strain B lam HC tw S htw htb W f U hsol
  let price := fun u => Real.sqrt (π u / π vtx) *
      (∑ α : OriginalSourceIndex F vtx u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT vtx u α)
  have hp (u : ι) : 0 ≤ price u := mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun α _ =>
    originalTaylorPrice_nonneg F K Ks Kmax dom ν e E ρ CT hν.le hE.le hρ.le hCT vtx u α))
  have hgrad (jj : Fin (J + 1)) (u : ι) :
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K u) (Uw jj u t)) ≤
        nativeComponentEnergy (n + Ks) ϖ (ρ / e) a b (U jj u) (Uw jj u) := le_add_self
  have hsb := normalized_response_source_budget θ hθ price (fun u => (π u)⁻¹) hp
    (fun u => inv_nonneg.mpr (hπ u).le) _ _ (hgrad j)
  have hmb := normalized_response_metric_budget ((π vtx)⁻¹)
    ((4 * Real.sqrt (multiplicationDensityBudget (K vtx)) * (CM * g * ζ)) ^ 2)
    ((metricInsertionUniformPrice Kmax CM) ^ 2) ((g * ζ) ^ 2) (sq_nonneg _)
    (metricInsertion_price_le (hK vtx) CM g ζ hCM hg hζ)
    (fun j' : Fin (J + 1) => if j.val = j'.val + 1 then
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 (ρ / e) (K vtx) (Uw j' vtx t)) else 0)
    (fun j' : Fin (J + 1) => if j.val = j'.val + 1 then
      nativeComponentEnergy (n + Ks) ϖ (ρ / e) a b (U j' vtx) (Uw j' vtx) else 0)
    (fun j' => by split_ifs; exact hgrad j' vtx; exact le_rfl)
  have hmrew : (∑ j' : Fin (J + 1), ENNReal.ofReal ((π vtx)⁻¹) *
        (if j.val = j'.val + 1 then nativeComponentEnergy (n + Ks) ϖ (ρ / e) a b (U j' vtx) (Uw j' vtx) else 0)) =
      ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then ENNReal.ofReal ((π vtx)⁻¹) *
        nativeComponentEnergy (n + Ks) ϖ (ρ / e) a b (U j' vtx) (Uw j' vtx) else 0 := by
    apply Finset.sum_congr rfl
    intro j' _
    split_ifs <;> simp only [mul_zero]
  rw [hmrew] at hmb
  apply response_row_coefficient_budget (ENNReal.ofReal A) (ENNReal.ofReal Sprice)
    (ENNReal.ofReal Mprice) (ENNReal.ofReal Bprice) (ENNReal.ofReal ((g * ζ) ^ 2))
    _ _ _ _ (ENNReal.ofReal_le_ofReal hAB)
    (by rw [← ENNReal.ofReal_mul hA]; exact ENNReal.ofReal_le_ofReal hSB)
    (by rw [← ENNReal.ofReal_mul hA]; exact ENNReal.ofReal_le_ofReal hMB)
  apply hb.trans
  apply mul_le_mul_right
  exact add_le_add (add_le_add le_rfl hsb) hmb

/-! Finite graded initial moments propagate through the actual response chain,
by the response level and the original descending graph rank. -/

theorem geometryResponse_piece_mass_budget_uniform (Hdepth Ks J Kmax M n : ℕ)
    (hreserve : n + (J + Hdepth) * Ks ≤ M) (CG Cw Cmol : ℕ → ℝ) (hCG : ∀ r, 0 ≤ CG r) :
    ∃ Bprice : ℝ, 1 ≤ Bprice ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
    (_hD : 2 ≤ D) (_hdepth : F.HasDepthAtMost Hdepth)
    (π : ι → ℝ) (_hπ : ∀ u, 0 < π u) (K : ι → ℕ) (_hK : ∀ u, K u ≤ Kmax)
    (_hdesc : F.IsDescending K) (dom : F.Domain)
    (ν e E ρ : ℝ) (_hν : 0 < ν) (_he : 0 < e) (_hE : 0 < E) (_hρ : 0 < ρ)
    (Jmol : ℕ) (b₀ : ι → ι → ℝ) (_hKs : Ks ≤ Jmol)
    (_henv : IsMolecularEnvelope F π K dom ν e E ρ Cmol Jmol b₀) (_hmeas : F.IsTimeMeasurable)
    (_hb₀ : ∀ v u, 0 ≤ b₀ v u) (_hrow : ∀ v, ∑ u, b₀ v u ≤ 1) (_hcol : ∀ u, ∑ v, b₀ v u ≤ 1)
    (p : P) (c : Ctx p) (s a b ϖ ζ g : ℝ) (_hs : s ≠ 0)
    (_hϖ : 0 < ϖ) (_hscale : (ρ / e) * ϖ ≤ 1) (_hζ : 0 ≤ ζ) (_hζ1 : ζ ≤ 1)
    (_hδ : e / E = ζ * ϖ) (X0 phase : Vec 2)
    (_hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (_hGm : ∀ X k l, Measurable (fun t => G t X k l))
    (_hGs : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l))
    (_hGj : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ CG r * g * (e / E) ^ r)
    (strain B lam : ℝ)
    (_HC : ScalarCoefficientInputs Kmax CG a b (ρ / e) (e / E) v strain B lam
      (fun t _ => G t 0) g)
    (tw S : ℝ) (_htw : tw ≤ a) (_htb : b ≤ tw + S)
    (_W : ∀ q ≤ M, ChartWeights (fun t _ => G t 0) v tw S ϖ 0 q Cw)
    (f : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u) (h u))
    (U : ∀ (_ : Fin (J + 1)) u, ℝ → PlaneHk Set.univ (K u) (h u))
    (Uw : ∀ (_ : Fin (J + 1)) u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (_hd : ∀ j x q, q + (j.val + familyDepthRank F Hdepth x) * Ks ≤ M →
      weightedFactorialNormSq q ϖ 0 (ρ / e) (K x) (f j x) ≠ ⊤)
    (_hsol : IsPlaneChainFrom (geometryResponseData J Ks G 0 (F.cellFiber s phase p c) X0 (e / E))
      (fun _ u => K u) a b v f (fun _ _ _ => 0) U Uw),
    ∀ j : Fin (J + 1), (∑ x, ENNReal.ofReal ((π x)⁻¹) *
      nativeComponentEnergy (n + (J - j.val + Hdepth - familyDepthRank F Hdepth x) * Ks)
        ϖ (ρ / e) a b (U j x) (Uw j x)) ≤
      ennResponseMassMajorant ((1 + ENNReal.ofReal Bprice) ^ (Hdepth + 1))
        (ENNReal.ofReal ((g * ζ) ^ 2))
        (fun l => ENNReal.ofReal Bprice * ∑ x, ENNReal.ofReal ((π x)⁻¹) *
          weightedFactorialNormSq (n + (J - l + Hdepth - familyDepthRank F Hdepth x) * Ks)
            ϖ 0 (ρ / e) (K x) (f ⟨min l J, by omega⟩ x)) j.val := by
  classical
  obtain ⟨CT, CM, Bprice, hCT, hCM, hB, hcomponent⟩ :=
    geometryResponse_component_recurrence_uniform Ks Kmax M CG Cw Cmol hCG
  refine ⟨Bprice, hB, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F hD hdepth π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1 hδ
    X0 phase hwindow v G hGm hGs hGj strain B lam HC tw S htw htb W f U Uw hd hsol
  let rank := familyDepthRank F Hdepth
  let θ := originalTaylorGraphConstant Ks Kmax CT Cmol
  let price := fun vtx u => Real.sqrt (π u / π vtx) *
    (∑ α : OriginalSourceIndex F vtx u, originalTaylorPrice F K Ks Kmax dom ν e E ρ CT vtx u α)
  let bgraph := normalizedFiniteGraph θ price
  obtain ⟨hbgraph, _, hcgraph, hsgraph⟩ := originalTaylor_normalized_graph_budget F Hdepth hdepth π K
    Ks Kmax hK dom ν e E ρ CT hCT hν hE hρ Cmol Jmol b₀ hKs henv hb₀ hrow hcol
  have hf := response_weighted_carrier_energy_ne_top F hD Hdepth Ks J Kmax M hdepth π hπ K hK hdesc dom
    ν e E ρ hν he hE hρ Cmol Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1
    hδ X0 phase hwindow v G CG Cw hCG hGm hGs hGj strain B lam HC tw S htw htb W f U Uw hd hsol
  let ji := fun l : ℕ => (⟨min l J, by omega⟩ : Fin (J + 1))
  let energy := fun l x q => ENNReal.ofReal ((π x)⁻¹) *
    nativeComponentEnergy q ϖ (ρ / e) a b (U (ji l) x) (Uw (ji l) x)
  let data := fun l x q => ENNReal.ofReal Bprice * ENNReal.ofReal ((π x)⁻¹) *
    weightedFactorialNormSq q ϖ 0 (ρ / e) (K x) (f (ji l) x)
  have hw (jj : Fin (J + 1)) (x : ι) : MemLp (Uw jj x) 2 (volume.restrict (Set.Icc a b)) := hsol.2.1 (jj, x)
  have hrowbudget (jj : Fin (J + 1)) (x : ι) (q : ℕ)
      (hq : q + (jj.val + rank x) * Ks ≤ M) :
      ENNReal.ofReal ((π x)⁻¹) * nativeComponentEnergy q ϖ (ρ / e) a b (U jj x) (Uw jj x) ≤
      ENNReal.ofReal Bprice * (ENNReal.ofReal ((π x)⁻¹) * weightedFactorialNormSq q ϖ 0 (ρ / e) (K x) (f jj x)) +
      ENNReal.ofReal Bprice * ENNReal.ofReal ((g * ζ) ^ 2) *
        (∑ j' : Fin (J + 1), if jj.val = j'.val + 1 then
          ENNReal.ofReal ((π x)⁻¹) * nativeComponentEnergy (q + Ks) ϖ (ρ / e) a b (U j' x) (Uw j' x) else 0) +
      ENNReal.ofReal Bprice * ∑ u, ENNReal.ofReal (bgraph x u) *
        (ENNReal.ofReal ((π u)⁻¹) * nativeComponentEnergy (q + Ks) ϖ (ρ / e) a b (U jj u) (Uw jj u)) := by
    apply hcomponent F hD J π hπ K hK hdesc dom ν e E ρ hν he hE hρ
      Jmol b₀ hKs henv hmeas hb₀ hrow hcol p c s a b ϖ ζ g hs hϖ hscale hζ hζ1 HC.metric_size hδ
      X0 phase hwindow G hGm hGs hGj Uw hw jj x q (by omega)
      ?_ ?_ v strain B lam HC tw S htw htb (W q (by omega)) f U hsol
    · intro u hu
      have hr := familyDepthRank_strict F Hdepth hdepth hu
      have hc : jj.val + rank u + 1 ≤ jj.val + rank x := by dsimp [rank]; omega
      have hcost : q + Ks + (jj.val + rank u) * Ks ≤ M := by
        have ht := (Nat.add_le_add_left (Nat.mul_le_mul_right Ks hc) q).trans hq
        simpa only [Nat.add_mul, one_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht
      exact nativeComponentEnergy_gradient_ne_top (q + Ks) ϖ (ρ / e) a b (U jj u) (Uw jj u)
        (hf jj u (q + Ks) hcost)
    · intro j' hj'
      have hc : j'.val + rank x + 1 = jj.val + rank x := by omega
      have hcost : q + Ks + (j'.val + rank x) * Ks ≤ M := by
        have heq : q + Ks + (j'.val + rank x) * Ks = q + (jj.val + rank x) * Ks := by
          calc
            _ = q + (j'.val + rank x + 1) * Ks := by ring
            _ = _ := by rw [hc]
        rw [heq]
        exact hq
      exact nativeComponentEnergy_gradient_ne_top (q + Ks) ϖ (ρ / e) a b (U j' x) (Uw j' x)
        (hf j' x (q + Ks) hcost)
  have hzero : ∀ x q, q + rank x * Ks ≤ M →
      energy 0 x q ≤ data 0 x q + ENNReal.ofReal Bprice * ∑ u, ENNReal.ofReal (bgraph x u) * energy 0 u (q + Ks) := by
    intro x q hq
    have hz : (ji 0).val = 0 := by simp only [ji, Nat.zero_min]
    have hh := hrowbudget (ji 0) x q (by simpa only [hz, Nat.zero_add] using hq)
    simpa only [responsePreviousLevel_sum_zero (ji 0) hz, mul_zero, add_zero, data, energy, mul_assoc] using hh
  have hsucc : ∀ l x q, l + 1 ≤ J → q + (l + 1 + rank x) * Ks ≤ M →
      energy (l + 1) x q ≤ data (l + 1) x q + ENNReal.ofReal Bprice * ENNReal.ofReal ((g * ζ) ^ 2) *
        energy l x (q + Ks) + ENNReal.ofReal Bprice * ∑ u, ENNReal.ofReal (bgraph x u) * energy (l + 1) u (q + Ks) := by
    intro l x q hl hq
    have hval : (ji (l + 1)).val = l + 1 := Nat.min_eq_left hl
    have hh := hrowbudget (ji (l + 1)) x q (by simpa only [hval] using hq)
    rw [responsePreviousLevel_sum_eq (ji (l + 1)) (by omega)] at hh
    have heq : (⟨(ji (l + 1)).val - 1, by have hi := (ji (l + 1)).isLt; omega⟩ : Fin (J + 1)) = ji l := by
      apply Fin.ext
      dsimp [ji]
      omega
    rw [heq] at hh
    simpa only [data, energy, mul_assoc] using hh
  have hc : ∀ u, ∑ x, ENNReal.ofReal (bgraph x u) ≤ 1 := by
    intro u
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hbgraph x u)]
    exact (ENNReal.ofReal_le_ofReal (hcgraph u)).trans_eq ENNReal.ofReal_one
  have hsupport : ∀ x u, ENNReal.ofReal (bgraph x u) ≠ 0 → rank u < rank x := by
    intro x u hne
    apply hsgraph x u
    intro hz
    change bgraph x u = 0 at hz
    exact hne (by rw [hz, ENNReal.ofReal_zero])
  have hh := ennResponse_initial_moment_mass_bounded_le rank Hdepth J n Ks M hreserve
    (fun x => familyDepthRank_le F Hdepth x) (fun x u => ENNReal.ofReal (bgraph x u))
    (fun _ _ => zero_le) hc hsupport (ENNReal.ofReal Bprice) (ENNReal.ofReal ((g * ζ) ^ 2)) zero_le zero_le
    data (fun _ _ _ => zero_le) energy
    (fun l x q q' hqq => mul_le_mul_right (nativeComponentEnergy_moment_mono hqq ϖ (ρ / e) a b
      (U (ji l) x) (Uw (ji l) x)) _) hzero hsucc
  intro jj
  have hji : ji jj.val = jj := by apply Fin.ext; exact Nat.min_eq_left (Nat.le_of_lt_succ jj.isLt)
  have ht := hh jj.val (Nat.le_of_lt_succ jj.isLt)
  simpa only [energy, data, hji, ← Finset.mul_sum, mul_assoc, rank] using ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! Each actual successor word level has a genuine native source and the backward Bloch formula, derived from its previous weighted moments. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainSuccessor_l2_duhamel (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (j : Fin N) (x : ι) (J H : ℕ)
    (hL : IsCycleLetter π (letters j) (Set.Icc a b ×ˢ Set.univ) J H)
    (hm : ∀ u o (k : Fin ((letters j).edge x u o).length), ∀ w X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff w t X z))
    (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ)
    (he : ∀ u, (∫⁻ r in Set.Icc a b,
      weightedGradFactorialNormSq (letters j).slow ϖ 0 ρ (κ j.castSucc u)
        (Uw (j.castSucc, u) r)) ≠ ⊤) :
    ∃ S : ℝ → PlaneFluxL2 (h x), MemLp S 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, S r k =ᵐ[volume]
        fun z => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) (j.succ, x) r z k) ∧
      ∀ (e : h x) (g : Lp ℝ 2 (volume : Measure (Vec 2))),
    let B := planeBlochBackwardRealField hab G hG v hv M hb g
    inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ j.succ x) (U (j.succ, x) b))) g =
      inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ j.succ x) (f (j.succ, x))))
        (planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab) B (-a))) -
      ∫ r in a..b, inner ℝ (planeFluxFiberCoordinateCLM e (S r))
        (planeH1GradientOperator (cellEnergyPlaneRealH1State (neg_le_neg hab) B (-r))) := by
  obtain ⟨S, hSl, hS⟩ := wordChainPrevious_l2_flux_exists π hπ letters a b J H j x hL κ
    X0 δ hm ϖ ρ hϖ hρ Uw (fun u => hsol.2.1 (j.castSucc, u)) he
  refine ⟨S, hSl, hS, ?_⟩
  intro e g
  exact wordChainCoordinateNative_duhamel hD G hG letters X0 δ κ a b hab v hv M hb
    f U Uw hsol (j.succ, x) S hSl hS e g

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite initial polynomial budgets propagate along a given chronological word chain. -/

section
open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChain_capped_finite_polynomial_energy (hD : 2 ≤ D)
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (J H : ℕ)
    (a b : ℝ) (hab : a ≤ b)
    (hL : ∀ j, IsCycleLetter π (letters j) (Icc a b ×ˢ Set.univ) J H)
    (κ : Fin (N + 1) → ι → ℕ) (K : ℕ) (d : Fin N → ℕ)
    (hd : ∀ j, (letters j).order = d j) (hreserve : (K + ∑ j, d j) ≤ J)
    (hc : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (X0 : Vec 2) (δ : ℝ)
    (hm : ∀ j x u o (k : Fin ((letters j).edge x u o).length), ∀ wd X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff wd t X z))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (strain r ϖ : ℝ) (ha : 0 ≤ strain) (hr : 0 < r) (hϖ : 0 < ϖ)
    (hrh : r ≤ 1 / 2) (hsmall : strain * r ^ 2 ≤ 1 / 8)
    (hjets : ∀ l, 1 ≤ l → l ≤ (K + ∑ j, d j) → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (tw S : ℝ) (Cw : ℕ → ℝ)
    (W : ∀ n, ChartWeights (fun t _ => G t) v tw S ϖ 0 n Cw)
    (hwa : tw ≤ a) (hwb : b ≤ tw + S) (m : ℕ)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (U : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (h x))
    (Uw : ∀ j x, ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hsol : IsPlaneChain (wordChainData G letters X0 δ) κ a b v f (fun _ _ _ => 0) U Uw)
    (hf : ∀ x n, weightedFactorialNormSq n ϖ 0 r
      (cappedWordSlots κ K d 0 x)
      (truncatePlaneHk (cappedWordSlots_le_original κ K d 0 x) (f x)) ≠ ⊤) :
    ∀ j x,
      ((⨆ t ∈ Icc a b, weightedFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) j) ϖ 0 r (cappedWordSlots κ K d j x)
        (truncatePlaneHk (cappedWordSlots_le_original κ K d j x) (U j x t))) +
      (∫⁻ t in Icc a b, weightedGradFactorialNormSq
        (wordMomentSlot m (fun j => (letters j).slow) j) ϖ 0 r (cappedWordSlots κ K d j x)
        (truncatePlaneHk (Nat.succ_le_succ (cappedWordSlots_le_original κ K d j x))
          (Uw j x t)))) ≠ ⊤ := by
  classical
  apply wordChainFrom_capped_finite_polynomial_energy hD π hπ letters J H a b hab
    hL κ K d hd hreserve hc X0 δ hm v hv hvs strain r ϖ ha hr hϖ hrh hsmall hjets
    G hG tw S Cw W hwa hwb m (fun p => wordLevelDatum κ f p.1 p.2)
    (fun p => U p.1 p.2) (fun p => Uw p.1 p.2) hsol
  intro j x
  by_cases hj : j = 0
  · subst j
    simpa only [wordLevelDatum_zero] using hf x (wordMomentSlot m (fun j => (letters j).slow) 0)
  · have hz : wordLevelDatum κ f j x = 0 := by simp [wordLevelDatum, hj]
    rw [hz, map_zero, weightedFactorialNormSq_zero_carrier]
    exact ENNReal.zero_ne_top
end

/-! Finite initial polynomial budgets propagate along a given chronological word chain. -/

section
open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChain_capped_previous_gradient_moments (hD : 2 ≤ D)
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (J H : ℕ)
    (a b : ℝ) (hab : a ≤ b)
    (hL : ∀ j, IsCycleLetter π (letters j) (Icc a b ×ˢ Set.univ) J H)
    (κ : Fin (N + 1) → ι → ℕ) (K : ℕ) (d : Fin N → ℕ)
    (hd : ∀ j, (letters j).order = d j) (hreserve : (K + ∑ j, d j) ≤ J)
    (hc : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (X0 : Vec 2) (δ : ℝ)
    (hm : ∀ j x u o (k : Fin ((letters j).edge x u o).length), ∀ wd X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff wd t X z))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (strain r ϖ : ℝ) (ha : 0 ≤ strain) (hr : 0 < r) (hϖ : 0 < ϖ)
    (hrh : r ≤ 1 / 2) (hsmall : strain * r ^ 2 ≤ 1 / 8)
    (hjets : ∀ l, 1 ≤ l → l ≤ (K + ∑ j, d j) → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (tw S : ℝ) (Cw : ℕ → ℝ)
    (W : ∀ n, ChartWeights (fun t _ => G t) v tw S ϖ 0 n Cw)
    (hwa : tw ≤ a) (hwb : b ≤ tw + S) (m : ℕ)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (U : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (h x))
    (Uw : ∀ j x, ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hsol : IsPlaneChain (wordChainData G letters X0 δ) κ a b v f (fun _ _ _ => 0) U Uw)
    (hf : ∀ x n, weightedFactorialNormSq n ϖ 0 r
      (cappedWordSlots κ K d 0 x)
      (truncatePlaneHk (cappedWordSlots_le_original κ K d 0 x) (f x)) ≠ ⊤) :
    ∀ (j : Fin N) x,
      (∫⁻ t in Icc a b, weightedGradFactorialNormSq (letters j).slow ϖ 0 r
        (cappedWordSlots κ K d j.castSucc x)
        (truncatePlaneHk (Nat.succ_le_succ (cappedWordSlots_le_original κ K d j.castSucc x))
          (Uw j.castSucc x t))) ≠ ⊤ := by
  have he := wordChain_capped_finite_polynomial_energy hD π hπ letters J H a b hab
    hL κ K d hd hreserve hc X0 δ hm v hv hvs strain r ϖ ha hr hϖ hrh hsmall hjets
    G hG tw S Cw W hwa hwb m f U Uw hsol hf
  intro j x
  apply ne_top_of_le_ne_top (he j.castSucc x)
  apply le_trans _ (le_add_left le_rfl)
  apply lintegral_mono
  intro t
  apply weightedGradFactorialNormSq_moment_mono
  rw [wordMomentSlot_castSucc]
  exact Nat.le_add_left _ _
end

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

def constructedGraphNativeSquareBudget (J : ℕ) (R Cg Cw η : ℝ) : ℝ :=
  (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
    constructedNativeWindowPrice J R ((8 + Cw * Cg) * R ^ 2) Cw) ^ J *
    peFactor η ^ (2 * J) *
    (Real.exp (constructedAllOrderPrice 0 R ((8 + Cw * Cg) * R ^ 2) Cw) * (1 + Cg * R) ^ 2)

theorem constructedFibreGraph_uniform_native_orders
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
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀) ξ₀ Cg r lam)
    (hdisc : fibreNorm ξ < ξ₀) (t : ℝ) :
    ∀ J : ℕ, ∃ W : TorusHk J ℂ,
      torusHkValueCLM W = cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1 ∧
      ‖W‖ ^ 2 ≤
        (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
          constructedNativeWindowPrice J R ((8 + Cw * Cg) * R ^ 2) Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (constructedAllOrderPrice 0 R ((8 + Cw * Cg) * R ^ 2) Cw) * (1 + Cg * R) ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let k := (8 + Cw * Cg) * R ^ 2
  have hk : 0 ≤ k := by unfold k; positivity
  have hκ : ∀ s, ‖-fibreSeriesC lam ξ s‖ ≤ k := by
    intro s
    rw [norm_neg]
    exact (fibreGraph_symbol_quadratic_bound hgraph hη0 hη hCg hCw hG hv hw ξ hdisc s).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (fibreNorm_nonneg ξ) hξ 2) (by positivity))
  have hκm : AEStronglyMeasurable (fun s => -fibreSeriesC lam ξ s)
      (volume.restrict (Icc (t - 1) t)) :=
    ((CycleDamping.graph_symbol_aestronglyMeasurable hG hv hgraph ξ hdisc).neg).mono_measure
      Measure.restrict_le_self
  have he := fibreGraph_actual_weak_evolution hgraph hη0 hη hCw hG hv hm hw V hb ξ hdisc
    (by linarith : t - 1 ≤ t)
  have hn : ‖cellRawTrace (fibreSeriesJet r ξ) (t - 1) + cellConstantCLM 1‖ ≤ 1 + Cg * R :=
    (fibreGraph_normalized_mode_norm_le hgraph hCg ξ hdisc (t - 1)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hξ hCg))
  have ht : (∑ i : Fin 2, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hA : cellFullZerothGrowth η Cw ξ k ≤ constructedAllOrderPrice 0 R k Cw := by
    have hf := mul_le_mul_of_nonneg_left hξ hCw
    unfold cellFullZerothGrowth constructedAllOrderPrice
    linarith only [ht, hf]
  have hall := constructedActualWeak_unit_window_all_native_orders hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ
    (fun s => -fibreSeriesC lam ξ s) k hκ
    (by linarith : t - 1 < t) hκm
    (cellRawTrace (fibreSeriesJet r ξ) (t - 1) + cellConstantCLM 1)
    (fun s => cellRawTrace (fibreSeriesJet r ξ) s + cellConstantCLM 1)
    (fun s => cellH1Slice (fibreSeriesJet r ξ) s + cellH1One) he rfl (by ring)
  intro J
  obtain ⟨W, hwv, hwb⟩ := hall J
  refine ⟨W, hwv, hwb.trans ?_⟩
  have hM := constructedNativeWindowPrice_pos J R k Cw hR hk hCw
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul (Real.exp_le_exp.mpr hA)
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn) (sq_nonneg _) (Real.exp_pos _).le
  · change 0 ≤ (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
      constructedNativeWindowPrice J R k Cw) ^ J * peFactor η ^ (2 * J)
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _)

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! The graph square budget has an explicit polynomial native norm price. -/

def constructedGraphNativeBaseSquareBudget (J : ℕ) (R Cg Cw : ℝ) : ℝ :=
  (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
    constructedNativeWindowPrice J R ((8 + Cw * Cg) * R ^ 2) Cw) ^ J *
    (Real.exp (constructedAllOrderPrice 0 R ((8 + Cw * Cg) * R ^ 2) Cw) * (1 + Cg * R) ^ 2)

theorem constructedGraphNativeSquareBudget_factor (J : ℕ) (R Cg Cw η : ℝ) :
    constructedGraphNativeSquareBudget J R Cg Cw η =
      constructedGraphNativeBaseSquareBudget J R Cg Cw * peFactor η ^ (2 * J) := by
  unfold constructedGraphNativeSquareBudget constructedGraphNativeBaseSquareBudget
  ring

theorem constructedGraphNativeSquareBudget_sqrt (J : ℕ) (R Cg Cw η : ℝ) :
    Real.sqrt (constructedGraphNativeSquareBudget J R Cg Cw η) =
      Real.sqrt (constructedGraphNativeBaseSquareBudget J R Cg Cw) * peFactor η ^ J := by
  rw [constructedGraphNativeSquareBudget_factor, Nat.mul_comm 2 J, pow_mul,
    Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq]
  exact pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) J

theorem constructedGraphNativeCorrection_polynomial_price (J : ℕ) (R Cg Cw η : ℝ) :
    Real.sqrt (constructedGraphNativeSquareBudget J R Cg Cw η) + ‖torusHigherConstant J 1‖ ≤
      (Real.sqrt (constructedGraphNativeBaseSquareBudget J R Cg Cw) + ‖torusHigherConstant J 1‖) *
        peFactor η ^ J := by
  rw [constructedGraphNativeSquareBudget_sqrt, add_mul]
  apply add_le_add le_rfl
  have h := mul_le_mul_of_nonneg_left (one_le_peFactor_pow η J) (norm_nonneg (torusHigherConstant J 1))
  simpa only [mul_one] using h

/-! The initial slow projection and final smoothing have one polynomial contrast price. -/

theorem constructedFastNativeEntrance_polynomial_price (J : ℕ) (R Cg Cw η : ℝ) :
    1 + 4 * Real.sqrt (constructedGraphNativeSquareBudget J R Cg Cw η) ≤
      (1 + 4 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R Cg Cw)) *
        peFactor η ^ J := by
  rw [constructedGraphNativeSquareBudget_sqrt, add_mul, one_mul]
  have hp := one_le_peFactor_pow η J
  linarith only [hp]

theorem constructedFastNativeDecay_polynomial_price (J : ℕ) (R Cg Cw η γ τ : ℝ) :
    (Real.sqrt (constructedNativeGapBasePrice J R 0 Cw γ) * peFactor η ^ J *
      Real.exp (-γ * τ / 2)) *
        (1 + 4 * Real.sqrt (constructedGraphNativeSquareBudget J R Cg Cw η)) ≤
      (Real.sqrt (constructedNativeGapBasePrice J R 0 Cw γ) *
        (1 + 4 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R Cg Cw))) *
          peFactor η ^ (2 * J) * Real.exp (-γ * τ / 2) := by
  have hp : 0 ≤ peFactor η := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)
  have he := mul_le_mul_of_nonneg_left
    (constructedFastNativeEntrance_polynomial_price J R Cg Cw η)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg (constructedNativeGapBasePrice J R 0 Cw γ))
      (pow_nonneg hp J)) (Real.exp_pos (-γ * τ / 2)).le)
  calc
    _ ≤ _ := he
    _ = _ := by rw [show 2 * J = J + J by omega, pow_add]; ring

end AVRegularity.CycleWords
end
