-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.BlockTransportedRemainderTime
public import AVRegularity.CycleJoint.Assembly.PeriodizedSum
import AVRegularity.CycleWords.GeometryErrorPieceMassBudget
import AVRegularity.CycleJoint.Assembly.ScalarResidualContraction
public import AVRegularity.CycleJoint.Assembly.PatchBridges
import AVRegularity.CycleJoint.Assembly.BlockEdgeSlowSample
public import AVRegularity.CycleJoint.PlaneRetainedLiteralConstructedErrorEndpointEnergy
import AVRegularity.CycleComparison.Charts.ChartDeviation
import AVRegularity.Weighted.ScalarChainClippedFactorialENNReal

section
/-! **Uniqueness of word chains: the source of a level**.

`wordChain_source`: the finite-energy admissible letter flux
(`exists_admissible_letter_flux_time`) of the fields of level `j` is a time-`L²` source whose
value is the previous-letter flux of level `j + 1`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.Weighted

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

section Source

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChain_source (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ) (J H : ℕ)
    (letters : Fin N → CycleLetter ι h D)
    (hL : ∀ j, IsCycleLetter π (letters j) (Set.Icc a b ×ˢ Set.univ) J H)
    (hm : ∀ j x y o, ∀ γ ∈ (letters j).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z)
    (X0 : Vec 2) (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ) (hκJ : ∀ j x, κ j x ≤ J)
    (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ)
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hUw : ∀ p, MemLp (Uw p) 2 (volume.restrict (Set.Icc a b)))
    (he : ∀ j x n,
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ 0 ρ (κ j x) (Uw (j, x) t)) ≠ ⊤)
    (j : Fin N) (x : ι) :
    ∃ V : ℝ → PlaneHk Set.univ (κ (j.succ, x).1 (j.succ, x).2)
        (PiLp 2 (fun _ : Fin 2 => h (j.succ, x).2)),
      MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
        wordChainPreviousFlux letters X0 δ κ (fun p => Uw p t) (j.succ, x) t := by
  obtain ⟨V, hVt, -, hVr⟩ := exists_admissible_letter_flux_time π hπ (letters j)
    a b J H (hL j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
    (j.succ, x) (fun u => (j.castSucc, u)) x (hκJ j.succ x)
    (if (letters j).positive then 1 else 0) 0 X0 δ
    (fun u o k w X z => hm j x u o _ (List.get_mem _ k) w X z)
    ϖ hϖ ρ hρ (fun u => Uw (j.castSucc, u)) (fun u => hUw _)
    (fun u => he j.castSucc u _)
  refine ⟨V, hVt, ?_⟩
  filter_upwards [hVr] with t ht
  rw [planeValue_eq_stored]
  refine (planeJetReadout_ae_raw (V t) (valueIndex2 (κ j.succ x))).symm.trans ?_
  have heq : wordChainPreviousFlux letters X0 δ κ (fun p => Uw p t) (j.succ, x) t =
      letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
        (j.succ, x) (fun u => (j.castSucc, u)) x
        (if (letters j).positive then 1 else 0) X0 δ (fun u => Uw (j.castSucc, u) t) t :=
    funext (fun z => wordChainPreviousFlux_succ letters X0 δ κ _ j x t z)
  rw [heq]
  exact ht

end Source

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs.Assembly

/-! Actual raw linear maps for the ordinary transported Taylor remainders,
including the density estimate with the partition weight retained. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ} {s σ : ℝ}
  {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {K : ι → ℕ} {Kmax : ℕ}
  {ν e ρ : ℝ} {Cm : ℕ → ℝ} {J : ℕ} {B : ι → ι → ℝ}

local notation "E₀" => ocEpsilon q Λ (m - 1)
local notation "dom₀" => ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)

/-- The generic polynomial multiplier construction realizes the transported
remainder and preserves its square partition-weight density bound. -/
theorem exists_blockTransportedRemainder_density_map
    (data : BlockMolecularInputs F π K Kmax dom₀ ν e E₀ ρ Cm J B)
    (chart : BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart s σ)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (timeScale a b : ℝ) (htime : ∀ τ ∈ Set.Icc a b, timeScale * τ ∈ Set.Icc tS tZ)
    (yc : Vec 2) (Ks N M r : ℕ) (hslot : K v + r ≤ K u + 1)
    (hN : N ≤ Jchart) (hMN : M + D ≤ N) (hr : 1 ≤ r)
    (hKM : K v ≤ M) (hLM : Ks + 1 ≤ M) (hLJ : Ks + 1 ≤ J)
    (hρE : ρ ≤ E₀) (ζ ϖ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hϖ : 0 < ϖ)
    (hδ : e / E₀ = ζ * ϖ) (hfit : (ρ / e) * ϖ ≤ 1) (μ : Measure ℝ) :
    let price := blockTransportedTaylorJetPrice F K Kmax dom₀ ν e E₀ ρ Ks N M Jchart Cchart ζ v u γ r
    let coeff := fun k I τ z => blockTransportedTimeRemainder Ks F hφ p c v u γ
      s σ e E₀ timeScale a b yc r I k τ z
    let densityPrice := 2 ^ (r + 1) * Real.sqrt (multiplicationDensityBudget (K v)) *
      (price * derivativeReserveFactor (ρ / e) (K v) (r - 1) * ‖(F.identity v u γ).map‖)
    ∃ T : PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ,
      IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
        (fun x τ z => nativeArrayAssembly r (F.identity v u γ).map
          (fun k I => F.weight p (timeScale * τ) * coeff k I τ z)
          (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) r I z))) T ∧
      ∀ x : PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ,
        ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e)
            (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (T x) τ) z ≤
          F.weight p (timeScale * τ) ^ 2 *
            (densityPrice ^ 2 * ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
              planeGradFactorialDensity (ρ / e)
                (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) z)) := by
  classical
  dsimp only
  let price := blockTransportedTaylorJetPrice F K Kmax dom₀ ν e E₀ ρ Ks N M Jchart Cchart ζ v u γ r
  let coeff := fun k I τ z => blockTransportedTimeRemainder Ks F hφ p c v u γ
    s σ e E₀ timeScale a b yc r I k τ z
  have hprice : 0 ≤ price := blockTransportedTaylorJetPrice_nonneg data Ks N M Jchart Cchart ζ hζ.le v u γ r
  have hcm k I z : Measurable (fun τ => coeff k I τ z) :=
    blockTransportedTimeRemainder_measurable data hw hm p c v u γ timeScale a b htime yc r I k Ks (by omega) z
  have hcs k I τ : ContDiff ℝ (K v : ℕ) (coeff k I τ) :=
    blockTransportedTimeRemainder_contDiff data p c v u γ timeScale a b htime yc r I k Ks (K v) (by omega) τ
  have hcb k I : ∀ᵐ τ ∂μ, ∀ j ≤ K v, ∀ z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (coeff k I τ) z‖ ≤ price * polynomialMomentRoot ϖ z ^ (Ks + 1) :=
    Filter.Eventually.of_forall (fun τ => blockTransportedTimeRemainder_jet_bound data chart p c v u γ hγ
      timeScale a b htime yc Ks N M r I k hN hMN hr hKM hLM hLJ hρE ζ ϖ hζ hζ1 hϖ hδ hfit τ)
  let w := fun τ : ℝ => F.weight p (timeScale * τ)
  have hwm : Measurable w := (hw p).comp (measurable_const.mul measurable_id)
  have hw1 : ∀ τ, |w τ| ≤ 1 := fun τ => family_weight_abs_le_one F p (timeScale * τ)
  obtain ⟨T, hT⟩ := exists_planeWeightedNativeArrayPolynomial_allMoment_map hslot hr (Ks + 1)
    ϖ (ρ / e) hϖ (div_pos data.radius_pos data.cell_pos) μ coeff hcm hcs
    (F.identity v u γ).map (fun _ _ => price) (fun _ _ => hprice) hcb w hwm hw1
  refine ⟨T, hT, ?_⟩
  intro x
  have hd := planeWeightedNativeArrayPolynomial_allMoment_density hslot hr (Ks + 1)
    ϖ (ρ / e) hϖ (div_pos data.radius_pos data.cell_pos) μ coeff hcm hcs
    (F.identity v u γ).map (fun _ _ => price) (fun _ _ => hprice) hcb w hwm hw1 T hT x
  have hcount (A : ℝ) : (∑ _β : Fin 2 × DerivativeWord2 r, A) = 2 ^ (r + 1) * A := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    ring
  simpa only [hcount, mul_assoc] using hd

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs.Assembly

/-! Analytic jets of an aligned or transported source coefficient in a renewal block. -/

/-- A finite common price for every source order and reserved derivative order. -/
def blockSourceTransportPrice (N D Ks : ℕ) (C : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (D + 1), ∑ n ∈ Finset.range (Ks + 1),
    transportedPolynomialJetPrice N D r n C 1 (fun _ _ => 1)

theorem blockSourceTransportPrice_nonneg (N D Ks : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ blockSourceTransportPrice N D Ks C := by
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro n hn
  exact transportedPolynomialJetPrice_nonneg N D r n C 1 hC zero_le_one _ (fun _ _ => zero_le_one)

/-- At a sampling radius at least one the extra Piola inverse powers are bounded by one. -/
theorem blockSource_transport_price_le (N Dγ D Ks r n : ℕ) (hD : Dγ ≤ D)
    (hr : r ≤ D) (hn : n ≤ Ks) (C R S : ℝ) (hC : 0 ≤ C) (hR : 1 ≤ R) (hS : 0 ≤ S) :
    transportedPolynomialJetPrice N Dγ r n C R (fun _ _ => S) ≤
      blockSourceTransportPrice N D Ks C * S := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hi : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  have hi1 : R⁻¹ ≤ 1 := (inv_le_one₀ hRpos).mpr hR
  have hfirst : transportedPolynomialJetPrice N Dγ r n C R (fun _ _ => S) ≤
      transportedPolynomialJetPrice N D r n C 1 (fun _ _ => S) := by
    unfold transportedPolynomialJetPrice
    apply (Finset.sum_le_sum (fun d hd => ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc le_rfl hD) (fun d hd hnot => ?_))
    · apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro k hk
      simp only [inv_one, one_pow, mul_one]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (by positivity) (pow_le_one₀ hi hi1)) (by positivity)
    · positivity
  have hfactor : transportedPolynomialJetPrice N D r n C 1 (fun _ _ => S) =
      transportedPolynomialJetPrice N D r n C 1 (fun _ _ => 1) * S := by
    unfold transportedPolynomialJetPrice
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hterm : transportedPolynomialJetPrice N D r n C 1 (fun _ _ => 1) ≤
      blockSourceTransportPrice N D Ks C := by
    have hn' : transportedPolynomialJetPrice N D r n C 1 (fun _ _ => 1) ≤
        ∑ n ∈ Finset.range (Ks + 1), transportedPolynomialJetPrice N D r n C 1 (fun _ _ => 1) :=
      Finset.single_le_sum (fun n _ => transportedPolynomialJetPrice_nonneg N D r n C 1 hC
        zero_le_one _ (fun _ _ => zero_le_one)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    exact hn'.trans (Finset.single_le_sum (f := fun r =>
      ∑ n ∈ Finset.range (Ks + 1), transportedPolynomialJetPrice N D r n C 1 (fun _ _ => 1))
      (fun r _ => Finset.sum_nonneg (fun n _ => transportedPolynomialJetPrice_nonneg N D r n C 1 hC
        zero_le_one _ (fun _ _ => zero_le_one))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr)))
  rw [hfactor] at hfirst
  exact hfirst.trans (mul_le_mul_of_nonneg_right hterm hS)

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {W : Set ℝ}
  {E Ca : ℝ} {Ks Ls : ℕ} {B : ι → ι → ℝ}

/-- The transported slow field retains every available qualitative slow derivative. -/
theorem blockTransportedSlowCoefficient_analytic_contDiff
    (data : BlockLetterAnalyticInputs F π W E Ca Ks Ls B)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p)
    (v u : ι) (γ : F.Γ v u) (σ : ℝ) (yc : Vec 2) (e : ℝ)
    (r : ℕ) (I : DerivativeWord2 r) (t : ℝ)
    (ht : t ∈ (F.piece p).output ∩ W) (n : ℕ) (hn : n ≤ Ks + Ls) :
    ContDiff ℝ (n : ℕ) (blockTransportedSlowCoefficient F hφ p c v u γ
      (F.piece p).anchor σ e E yc r I t) := by
  have hf (d : ℕ) (I : DerivativeWord2 (d - 1)) : ContDiff ℝ (n : ℕ)
      (fun w : Vec 2 × Vec 2 => F.flux p c v u γ d I t w.1 w.2) :=
    (molecular_joint_contDiff F (ChartedFamily.Domain.onWindow F W) E data.slow_pos.ne'
      (fun _ => Ks + Ls) data.envelope.1 p c t
      (fun _ => ⟨ht, Set.mem_univ _⟩) v u γ d I).of_le (by exact_mod_cast hn)
  have hJac a b : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => naturalPreparationJacobian hφ (F.piece p).anchor σ (yc + e • x) a b) :=
    ((naturalPreparationJacobian_entry_smooth hφ (F.piece p).anchor a b).comp
      (contDiff_const.prodMk contDiff_id)).comp (contDiff_const.add (contDiff_id.const_smul e))
  have hY : ContDiff ℝ (n : ℕ) (fun x : Vec 2 => E⁻¹ •
      streamFlow φ hφ (F.piece p).anchor (yc + e • x) σ) :=
    (((streamFlow_spatial_smooth hφ _ _).of_le (by simp)).comp
      (contDiff_const.add (contDiff_id.const_smul e))).const_smul _
  apply contDiff_pi.mpr
  intro k
  exact transportedCoeff_spatial_smooth _ hJac (F.identity v u γ).maxOrder n
    (fun d I x => F.flux p c v u γ d I t
      (E⁻¹ • streamFlow φ hφ (F.piece p).anchor (yc + e • x) σ) 0)
    (fun d I k => ((ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ).contDiff.comp
      ((hf d I).comp (hY.prodMk (contDiff_const (c := (0 : Vec 2))))))) r I k

/-- The qualitative joint reserve is retained by a block coefficient at every active time. -/
theorem blockLetterCoefficient_joint_contDiff
    (data : BlockLetterAnalyticInputs F π W E Ca Ks Ls B)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (p : P) (c : Ctx p)
    (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ : ℝ) (yc : Vec 2) (e timeScale : ℝ)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ)
    (ht : timeScale * t ∈ (F.piece p).output ∩ W) (n : ℕ) (hn : n ≤ Ks + Ls) :
    ContDiff ℝ (n : ℕ) (fun w : Vec 2 × Vec 2 =>
      blockLetterCoefficient F hφ p c v u γ l σ yc e E timeScale d I t w.1 w.2) := by
  have hf (d : ℕ) (I : DerivativeWord2 (d - 1)) : ContDiff ℝ (n : ℕ)
      (fun w : Vec 2 × Vec 2 => F.flux p c v u γ d I (timeScale * t) w.1 w.2) :=
    (molecular_joint_contDiff F (ChartedFamily.Domain.onWindow F W) E data.slow_pos.ne'
      (fun _ => Ks + Ls) data.envelope.1 p c (timeScale * t)
      (fun _ => ⟨ht, Set.mem_univ _⟩) v u γ d I).of_le (by exact_mod_cast hn)
  unfold blockLetterCoefficient
  split_ifs
  · exact (hf d I).comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  · let f := fun x : Vec 2 => blockTransportedSlowCoefficient F hφ p c v u γ
      (F.piece p).anchor σ e E yc (d - 1) I (timeScale * t) x
    have hfs : ContDiff ℝ (n : ℕ) f :=
      blockTransportedSlowCoefficient_analytic_contDiff data hφ p c v u γ σ yc e
        (d - 1) I (timeScale * t) ht n hn
    exact hfs.comp ((contDiff_fst.sub contDiff_const).const_smul (e / E)⁻¹)

/-- The pointwise scalar transport bound uses only the reserved pure slow jets. -/
theorem blockTransportedSlowCoefficient_analytic_scaled_bound
    {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}
    (data : BlockLetterAnalyticInputs F π W (ocEpsilon q Λ (m - 1)) Ca Ks Ls B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (σ : ℝ)
    (chart : BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart (F.piece p).anchor σ)
    (e : ℝ) (he : 0 < e) (heE : e ≤ ocEpsilon q Λ (m - 1)) (yc : Vec 2)
    (t : ℝ) (ht : t ∈ (F.piece p).output ∩ W) (S : ℝ) (hS : 0 ≤ S)
    (hf : ∀ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
      ∀ I k j, j ≤ Ks → ∀ X, ‖iteratedFDeriv ℝ j (fun Y => F.flux p c v u γ d I t Y 0 k) X‖ ≤ S)
    (N r n : ℕ) (hN : N ≤ Jchart) (hmax : (F.identity v u γ).maxOrder ≤ D)
    (hn : n ≤ Ks) (hnN : Ks + D ≤ N) (hr : 1 ≤ r) (hrD : r ≤ D)
    (I : DerivativeWord2 r) (k : Fin 2) (x : Vec 2) :
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let Cpi := compConst Cflow N * Cflow
    (ocEpsilon q Λ (m - 1) / e) ^ n * ‖iteratedFDeriv ℝ n (fun y =>
      blockTransportedSlowCoefficient F hφ p c v u γ (F.piece p).anchor σ e
        (ocEpsilon q Λ (m - 1)) yc r I t y k) x‖ ≤
      (blockSourceTransportPrice N D Ks Cpi * blockEdgeSamplingPrice Ks Jchart Cchart) * S := by
  dsimp only
  let E₀ := ocEpsilon q Λ (m - 1)
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let Cpi := compConst Cflow N * Cflow
  let Csample := blockEdgeSamplingPrice Ks Jchart Cchart
  have hCf : 1 ≤ Cflow := one_le_jetConst _ _
  have hCp : 0 ≤ Cpi := mul_nonneg (compConst_nonneg hCf N) (zero_le_one.trans hCf)
  have hCs : 0 ≤ Csample := blockEdgeSamplingPrice_nonneg Ks Jchart Cchart
  have hR : 1 ≤ E₀ / e := (one_le_div he).mpr heE
  have hjoint (d : ℕ) (A : DerivativeWord2 (d - 1)) :
      ContDiff ℝ (Ks : ℕ) (fun w : Vec 2 × Vec 2 => F.flux p c v u γ d A t w.1 w.2) :=
    (molecular_joint_contDiff F (ChartedFamily.Domain.onWindow F W) E₀ data.slow_pos.ne'
      (fun _ => Ks + Ls) data.envelope.1 p c t (fun _ => ⟨ht, Set.mem_univ _⟩) v u γ d A).of_le
      (by exact_mod_cast (Nat.le_add_right Ks Ls))
  have hslow d (A : DerivativeWord2 (d - 1)) k :
      ContDiff ℝ (Ks : ℕ) (fun Y : Vec 2 => F.flux p c v u γ d A t Y 0 k) :=
    (ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ).contDiff.comp
      ((hjoint d A).comp (contDiff_id.prodMk (contDiff_const (c := (0 : Vec 2)))))
  have hY : ContDiff ℝ (Ks : ℕ) (fun x : Vec 2 =>
      E₀⁻¹ • streamFlow φ hφ (F.piece p).anchor (yc + e • x) σ) :=
    (((streamFlow_spatial_smooth hφ _ _).of_le (by simp)).comp
      (contDiff_const.add (contDiff_id.const_smul e))).const_smul _
  let Bsample := fun d (A : DerivativeWord2 (d - 1)) (x : Vec 2) =>
    F.flux p c v u γ d A t (E₀⁻¹ • streamFlow φ hφ (F.piece p).anchor (yc + e • x) σ) 0
  have hBj : ∀ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder, ∀ A k j, j ≤ n → ∀ y,
      (E₀ / e) ^ j * ‖iteratedFDeriv ℝ j (fun x => Bsample d A x k) y‖ ≤
        (Csample * S) * polynomialMomentRoot 0 y ^ 0 := by
    intro d hd A k j hj y
    rw [pow_zero, mul_one]
    have hh := blockEdge_sample_cell_jets chart.flow chart.amplitude_nonneg (F.piece p).anchor σ
      chart.anchor_padded chart.reference_padded chart.age Ks (by omega) e E₀ he data.slow_pos
      le_rfl yc _ (hslow d A k) S hS (fun a ha X => by
        rw [div_self data.slow_pos.ne', one_pow, one_mul]
        exact hf d (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega,
          (Finset.mem_Icc.mp hd).2⟩) A k a ha X) j (hj.trans hn) y
    simpa only [blockEdgeSamplingPrice, Csample, mul_assoc] using hh
  have hh := preparation_cell_transported_polynomial_jet_bound chart.flow chart.amplitude_nonneg
    data.slow_pos (F.piece p).anchor σ chart.anchor_padded chart.reference_padded
    (by simpa only [abs_sub_comm] using chart.age) N (F.identity v u γ).maxOrder n r hN (by omega)
    e (E₀ / e) he (div_pos data.slow_pos he).le le_rfl yc Bsample
    (fun d A k => (((ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ).contDiff.comp
      ((hjoint d A).comp (hY.prodMk (contDiff_const (c := (0 : Vec 2))))))).of_le
        (by exact_mod_cast hn)) (fun _ _ => Csample * S) 0 0 hBj I k x
  dsimp only at hh
  rw [pow_zero, mul_one] at hh
  have hp := blockSource_transport_price_le N (F.identity v u γ).maxOrder D Ks r n hmax hrD hn
    Cpi (E₀ / e) (Csample * S) hCp hR (mul_nonneg hCs hS)
  exact hh.trans (hp.trans_eq (by ring))

/-- The uniform source coefficient price includes the untransported case. -/
def blockSourceAnalyticJetPrice (Ks D Jchart : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  1 + blockSourceTransportPrice (Ks + D) D Ks (compConst Cflow (Ks + D) * Cflow) *
    blockEdgeSamplingPrice Ks Jchart Cchart

theorem blockSourceAnalyticJetPrice_one_le (Ks D Jchart : ℕ) (Cchart : ℕ → ℝ) :
    1 ≤ blockSourceAnalyticJetPrice Ks D Jchart Cchart := by
  have hC := one_le_jetConst (preparationFlowJetConstant Cchart) (Jchart + 1)
  have ht := blockSourceTransportPrice_nonneg (Ks + D) D Ks
    (compConst _ (Ks + D) * _) (mul_nonneg (compConst_nonneg hC _) (zero_le_one.trans hC))
  have hs := blockEdgeSamplingPrice_nonneg Ks Jchart Cchart
  exact le_add_of_nonneg_right (mul_nonneg ht hs)

/-- A block coefficient is bounded by the same original jet price in either label case. -/
theorem blockLetterCoefficient_analytic_mixed_bound
    {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
    {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}
    (data : BlockLetterAnalyticInputs F π W (ocEpsilon q Λ (m - 1)) Ca Ks Ls B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ : ℝ)
    (chart : BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart (F.piece p).anchor σ)
    (e : ℝ) (he : 0 < e) (heE : e ≤ ocEpsilon q Λ (m - 1)) (yc : Vec 2)
    (timeScale t : ℝ) (ht : timeScale * t ∈ (F.piece p).output ∩ W)
    (S : ℝ) (hS : 0 ≤ S)
    (hf : ∀ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∀ I j k,
      j ≤ Ks → k ≤ Ls → ∀ X z,
        ‖iteratedFDeriv ℝ j (fun Y => iteratedFDeriv ℝ k (F.flux p c v u γ d I (timeScale * t) Y) z) X‖ ≤ S)
    (hchart : Ks + D ≤ Jchart) (d : ℕ) (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (n qfast : ℕ) (hn : n ≤ Ks) (hq : qfast ≤ Ls)
    (X z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun Y => iteratedFDeriv ℝ qfast
      (blockLetterCoefficient F hφ p c v u γ l σ yc e (ocEpsilon q Λ (m - 1)) timeScale d I t Y) z) X‖ ≤
      blockSourceAnalyticJetPrice Ks D Jchart Cchart * S := by
  let E₀ := ocEpsilon q Λ (m - 1)
  have hprice := blockSourceAnalyticJetPrice_one_le Ks D Jchart Cchart
  by_cases hl : (F.piece p).label = l
  · unfold blockLetterCoefficient
    simp only [hl, ite_true]
    rw [block_fastShift_mixed_norm]
    exact (hf d hd I n qfast hn hq X (z + e⁻¹ • yc)).trans
      (le_mul_of_one_le_left hS hprice)
  · let f := blockTransportedSlowCoefficient F hφ p c v u γ (F.piece p).anchor σ e E₀ yc
      (d - 1) I (timeScale * t)
    let R := E₀ / e
    let X₀ := E₀⁻¹ • yc
    have hR : 0 < R := div_pos data.slow_pos he
    have hfs : ContDiff ℝ (n : ℕ) f :=
      blockTransportedSlowCoefficient_analytic_contDiff data hφ p c v u γ σ yc e
        (d - 1) I (timeScale * t) ht n (by omega)
    have hfn : ContDiff ℝ (n : ℕ) (fun Y => f (R • (Y - X₀))) :=
      hfs.comp ((contDiff_id.sub contDiff_const).const_smul R)
    have hseed : ∀ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∀ A k j, j ≤ Ks → ∀ Y,
        ‖iteratedFDeriv ℝ j (fun X => F.flux p c v u γ d A (timeScale * t) X 0 k) Y‖ ≤ S := by
      intro d hd A k j hj Y
      have hF : ContDiff ℝ (j : ℕ) (fun X => F.flux p c v u γ d A (timeScale * t) X 0) :=
        ((molecular_joint_contDiff F (ChartedFamily.Domain.onWindow F W) E₀ data.slow_pos.ne'
          (fun _ => Ks + Ls) data.envelope.1 p c _ (fun _ => ⟨ht, Set.mem_univ _⟩)
          v u γ d A).of_le (by exact_mod_cast (by omega : j ≤ Ks + Ls))).comp
            (contDiff_id.prodMk (contDiff_const (c := (0 : Vec 2))))
      have hh := hf d hd A j 0 hj (Nat.zero_le _) Y 0
      rw [block_fastZero_mixed_norm] at hh
      exact (iteratedJet_coordinate_norm_le _ hF le_rfl k Y).trans hh
    unfold blockLetterCoefficient
    simp only [hl, ite_false, inv_div]
    change ‖iteratedFDeriv ℝ n (fun Y => iteratedFDeriv ℝ qfast
      (fun _ : Vec 2 => f (R • (Y - X₀))) z) X‖ ≤ _
    rw [block_fastConstant_mixed_norm]
    split_ifs
    · let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
      let Ct := blockSourceTransportPrice (Ks + D) D Ks (compConst Cflow (Ks + D) * Cflow) *
        blockEdgeSamplingPrice Ks Jchart Cchart
      have hCt : 0 ≤ Ct := by
        have hCf := one_le_jetConst (preparationFlowJetConstant Cchart) (Jchart + 1)
        exact mul_nonneg (blockSourceTransportPrice_nonneg _ _ _ _
          (mul_nonneg (compConst_nonneg hCf _) (zero_le_one.trans hCf)))
          (blockEdgeSamplingPrice_nonneg _ _ _)
      have hv : ‖iteratedFDeriv ℝ n (fun Y => f (R • (Y - X₀))) X‖ ≤ Ct * S := by
        apply block_vector_jet_norm_le _ n hfn _ (mul_nonneg hCt hS)
        intro k Y
        have hscalar : ContDiff ℝ (n : ℕ) (fun x => f x k) :=
          (ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ).contDiff.comp hfs
        rw [block_affine_slow_jet_norm _ n hscalar R hR.le X₀ Y]
        exact blockTransportedSlowCoefficient_analytic_scaled_bound data p c v u γ σ chart e he heE yc
          (timeScale * t) ht S hS hseed (Ks + D) (d - 1) n hchart (F.identity v u γ).le_D hn le_rfl
          (by have := (Finset.mem_Icc.mp hd).1; omega)
          (by have := (Finset.mem_Icc.mp hd).2; have := (F.identity v u γ).le_D; omega)
          I k (R • (Y - X₀))
      exact hv.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hS)
    · exact mul_nonneg (zero_le_one.trans hprice) hS

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Uniqueness of word chains: the component step**.

Proofs of `PlaneTruncEqStatement` and `WordChainFluxCongrStatement` (`planeTruncEq`,
`wordChainFluxCongr`), and the component step `wordChain_component_unique`: it applies the Duhamel
formula of the component on `[a, t]` to both chains (which have the same datum and the same source),
and reads the value at `t` off its pairings with all `L²` functions in all fibre directions. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

theorem planeTruncEq : PlaneTruncEqStatement.{v} := by
  intro E _ _ _ _ _ _ K a b w w' u u' hw hw' hu
  filter_upwards [hw, hw', ae_restrict_mem measurableSet_Icc] with s h1 h2 hs
  exact truncatePlaneHk_injective (Nat.le_succ K) (h1.trans ((hu s hs).trans h2.symm))

theorem wordChainFluxCongr : WordChainFluxCongrStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ D N letters X0 δ κ U U' j x hU t
  funext z
  rw [wordChainPreviousFlux_succ, wordChainPreviousFlux_succ]
  have hf : (fun y => U (j.castSucc, y)) = fun y => U' (j.castSucc, y) := funext hU
  rw [hf]

/-- Two `L²` classes with the same pairings of all fibre coordinates agree. -/
theorem lp_eq_of_fiberCoordinate_pairing {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] (p q : Lp E 2 (volume : Measure (Vec 2)))
    (hpq : ∀ (e : E) (g : Lp ℝ 2 (volume : Measure (Vec 2))),
      inner ℝ (planeFiberCoordinateCLM e p) g = inner ℝ (planeFiberCoordinateCLM e q) g) :
    p = q := by
  have hcoord : ∀ e : E, ∀ᵐ x ∂(volume : Measure (Vec 2)), inner ℝ e (p x) = inner ℝ e (q x) := by
    intro e
    have hz : planeFiberCoordinateCLM e p - planeFiberCoordinateCLM e q = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      rw [inner_sub_left, hpq e (planeFiberCoordinateCLM e p - planeFiberCoordinateCLM e q),
        sub_self]
    have hz' : planeFiberCoordinateCLM e p = planeFiberCoordinateCLM e q := sub_eq_zero.mp hz
    filter_upwards [(InnerProductSpace.toDual ℝ E e).coeFn_compLpL p,
      (InnerProductSpace.toDual ℝ E e).coeFn_compLpL q, Lp.ext_iff.mp hz'] with x h1 h2 h3
    change planeFiberCoordinateCLM e p x = inner ℝ e (p x) at h1
    change planeFiberCoordinateCLM e q x = inner ℝ e (q x) at h2
    rw [← h1, ← h2]
    exact h3
  apply Lp.ext
  have hall : ∀ᵐ x ∂(volume : Measure (Vec 2)), ∀ i, inner ℝ (Module.finBasis ℝ E i) (p x) =
      inner ℝ (Module.finBasis ℝ E i) (q x) := ae_all_iff.mpr fun i => hcoord _
  filter_upwards [hall] with x hx
  exact InnerProductSpace.ext_inner_left_basis (Module.finBasis ℝ E) hx

section Component

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChain_component_unique (hD : 2 ≤ D) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2)
    (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (_hab : a ≤ b) (vd : ℝ → Vec 2 → Vec 2)
    (hv : IsCellDrift vd)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U U' : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw Uw' : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b vd
      (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (hsol' : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b vd
      (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U' (j, x)) (fun j x => Uw' (j, x)))
    (i : Fin (N + 1) × ι)
    (V : ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hVl : MemLp V 2 (volume.restrict (Set.Icc a b)))
    (hV : ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
      wordChainPreviousFlux letters X0 δ κ (fun p => Uw p t) i t)
    (hV' : ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
      wordChainPreviousFlux letters X0 δ κ (fun p => Uw' p t) i t) :
    ∀ t ∈ Set.Icc a b, U i t = U' i t := by
  intro t ht
  obtain ⟨M, hb⟩ := hv.2.1
  have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl ht.2
  have hres (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
      (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
      (hs : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b vd
        (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U (j, x)) (fun j x => Uw (j, x))) :
      IsPlaneChainFrom (wordChainData G letters X0 δ) κ a t vd
        (fun j x => f (j, x)) (fun _ _ _ => 0) (fun j x => U (j, x)) (fun j x => Uw (j, x)) :=
    ⟨fun i => (hs.1 i).mono hsub,
      fun i => (hs.2.1 i).mono_measure (Measure.restrict_mono hsub le_rfl),
      fun i => ae_restrict_of_ae_restrict_of_subset hsub (hs.2.2.1 i), hs.2.2.2.1,
      fun i s hs' φ => hs.2.2.2.2 i s (hsub hs') φ⟩
  have hVl' : MemLp V 2 (volume.restrict (Set.Icc a t)) :=
    hVl.mono_measure (Measure.restrict_mono hsub le_rfl)
  have h1 := fun e g => wordChain_component_duhamel hD G hG letters X0 δ κ a t ht.1 vd hv M hb
    f U Uw (hres U Uw hsol) i V hVl' (ae_restrict_of_ae_restrict_of_subset hsub hV) e g
  have h2 := fun e g => wordChain_component_duhamel hD G hG letters X0 δ κ a t ht.1 vd hv M hb
    f U' Uw' (hres U' Uw' hsol') i V hVl' (ae_restrict_of_ae_restrict_of_subset hsub hV') e g
  have hp : planeHkValueOperator (κ i.1 i.2) (U i t) = planeHkValueOperator (κ i.1 i.2) (U' i t) :=
    lp_eq_of_fiberCoordinate_pairing _ _ fun e g => by
      have e1 := h1 e g
      have e2 := h2 e g
      dsimp only at e1 e2
      exact e1.trans e2.symm
  rw [planeHkValueOperator_apply, planeHkValueOperator_apply] at hp
  apply PlaneHk.ext_value isOpen_univ
  exact univToPlane.injective hp

end Component

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport AVRegularity.CycleComparison.Charts
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs.Assembly

/-! The block Taylor readout is the finite weighted sum of the literal piece
readouts. Aligned pieces use the native array; other pieces use the ordinary
Taylor polynomial of their complete transported slow field. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- Expansion commutes with the actual piece weights wherever those weights are nonzero. -/
theorem blockLetterNativeArray_eq_sum (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (S : Finset P) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l : ℤ) (σ e E timeScale : ℝ) (yc z : Vec 2) (r : ℕ) (τ : ℝ)
    (hf : ∀ p ∈ S, F.weight p (timeScale * τ) ≠ 0 → ∀ k I,
      ContDiff ℝ (Ks : ℕ)
        (fun X => blockLetterCoefficient F hφ p (actual p) v u γ l σ yc e E timeScale (r + 1) I τ X z k)) :
    blockLetterNativeArray (h := h) Ks F S actual v u γ timeScale hφ l σ e E yc r τ z =
      ∑ p ∈ S, F.weight p (timeScale * τ) • nativeArrayAssembly r (F.identity v u γ).map
        (fun (k : Fin 2) (I : DerivativeWord2 r) => taylorSlow 0 Ks
          (fun X => blockLetterCoefficient F hφ p (actual p) v u γ l σ yc e E timeScale (r + 1) I τ X z k)
          (E⁻¹ • yc) ((e / E) • z)) := by
  classical
  have he : (fun (k : Fin 2) (I : DerivativeWord2 r) => taylorSlow 0 Ks
      (fun X => blockLetterAggCoeff F S actual hφ l σ yc e E timeScale v u γ (r + 1) I τ X z k)
      (E⁻¹ • yc) ((e / E) • z)) =
      ∑ p ∈ S, F.weight p (timeScale * τ) • (fun (k : Fin 2) (I : DerivativeWord2 r) => taylorSlow 0 Ks
        (fun X => blockLetterCoefficient F hφ p (actual p) v u γ l σ yc e E timeScale (r + 1) I τ X z k)
        (E⁻¹ • yc) ((e / E) • z)) := by
    funext k I
    simp only [blockLetterAggCoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact blockEdge_taylor_sum_active S Ks (fun p => F.weight p (timeScale * τ)) _
      (fun p hp hw => hf p hp hw k I) _ _
  unfold blockLetterNativeArray
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [map_smul]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {K : ι → ℕ} {Kmax : ℕ}
  {dom : F.Domain} {ν e ρ : ℝ} {Cm : ℕ → ℝ} {J : ℕ} {B : ι → ι → ℝ}

local notation "E₀" => ocEpsilon q Λ (m - 1)

/-- The molecular smoothness premise supplies the regularity needed by finite Taylor additivity. -/
theorem blockLetterCoefficient_contDiff
    (data : BlockMolecularInputs F π K Kmax dom ν e E₀ ρ Cm J B)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ timeScale : ℝ)
    (yc z : Vec 2) (r Ks : ℕ) (I : DerivativeWord2 r) (τ : ℝ)
    (hdom : ∀ Y : Vec 2, (timeScale * τ, Y) ∈ dom p c) (hn : Ks ≤ K v + J) (k : Fin 2) :
    ContDiff ℝ (Ks : ℕ) (fun X =>
      blockLetterCoefficient F hφ p c v u γ l σ yc e E₀ timeScale (r + 1) I τ X z k) := by
  by_cases hl : (F.piece p).label = l
  · have hf := molecular_cell_coefficient_contDiff F dom E₀ data.slow_pos.ne'
      (fun v => K v + J) data.molecular.1 p c (timeScale * τ) hdom v u γ (r + 1) I (e⁻¹ • yc) k
    have hh := hf.comp (contDiff_id.prodMk (contDiff_const (c := z)))
    simpa only [blockLetterCoefficient, ite_eq_left hl, Function.comp_def, id_eq] using hh.of_le (by exact_mod_cast hn)
  · have hf := blockTransportedSlowCoefficient_contDiff (hφ := hφ)
      (s := (F.piece p).anchor) (σ := σ) data p c v u γ yc r I (timeScale * τ) hdom Ks hn k
    have hh := hf.comp ((contDiff_id.sub (contDiff_const (c := E₀⁻¹ • yc))).const_smul (e / E₀)⁻¹)
    convert hh using 1
    funext X
    simp only [blockLetterCoefficient, ite_eq_right hl, blockTransportedSlowCoefficient,
      Function.comp_def, id_eq]
    rfl

/-- For a piece anchored at the reference time, the block and native Taylor arrays coincide. -/
theorem blockEdge_aligned_taylor (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l : ℤ) (hl : (F.piece p).label = l) (σ e E timeScale : ℝ) (he : e ≠ 0)
    (hanchor : (F.piece p).anchor = σ) (yc z : Vec 2) (r : ℕ) (τ : ℝ) :
    F.weight p (timeScale * τ) • nativeArrayAssembly r (F.identity v u γ).map
      (fun (k : Fin 2) (I : DerivativeWord2 r) => taylorSlow 0 Ks
        (fun X => blockLetterCoefficient F hφ p c v u γ l σ yc e E timeScale (r + 1) I τ X z k)
        (E⁻¹ • yc) ((e / E) • z)) =
    naturalFamilyTaylorNativeArray Ks F p c v u γ timeScale hφ
      (F.piece p).anchor σ e E yc r τ z := by
  have hfast : e⁻¹ • (yc + e • z) = z + e⁻¹ • yc := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ he, one_smul, add_comm]
  have hslow : E⁻¹ • (yc + e • z - yc) = (e / E) • z := by
    rw [add_sub_cancel_left, smul_smul]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  unfold naturalFamilyTaylorNativeArray
  rw [hanchor]
  simp only [streamFlow_self, blockEdge_naturalJacobian_self]
  congr 2
  funext k I
  rw [blockEdge_transported_identity]
  by_cases hord : r + 1 ≤ (F.identity v u γ).maxOrder
  · simp only [ite_eq_left hord, blockLetterCoefficient, ite_eq_left hl, hfast, hslow]
  · have hf : F.flux p c v u γ (r + 1) I = 0 := F.flux_zero p c v u γ (r + 1) I (by omega)
    simp only [ite_eq_right hord, Pi.zero_apply, blockLetterCoefficient, ite_eq_left hl, hf]
    simp only [taylorSlow, Pi.zero_apply, iteratedFDeriv_fun_zero, zero_apply, mul_zero, Finset.sum_const_zero]

/-- The natural Taylor and remainder arrays sum to the complete pulled-back array. -/
theorem blockEdge_native_full_split (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s σ e E timeScale a b : ℝ) (yc z : Vec 2) (r : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc a b) :
    naturalFamilyTaylorNativeArray Ks F p c v u γ timeScale hφ s σ e E yc r τ z +
      naturalFamilyRemainderNativeArray Ks F p c v u γ timeScale a b hφ s σ e E yc r τ z =
    F.weight p (timeScale * τ) • nativeArrayAssembly r (F.identity v u γ).map
      (fun (k : Fin 2) (I : DerivativeWord2 r) => transportedCoeff
        (fun y => naturalPreparationJacobian hφ s σ (yc + e • y))
        (F.identity v u γ).maxOrder (fun d W => F.flux p c v u γ d W (timeScale * τ)
          (E⁻¹ • streamFlow φ hφ s (yc + e • z) σ)
          (e⁻¹ • streamFlow φ hφ s (yc + e • z) σ)) r I z k) := by
  let Jac := fun y => naturalPreparationJacobian hφ s σ (yc + e • y)
  let Bf := fun d W => F.flux p c v u γ d W (timeScale * τ)
    (E⁻¹ • streamFlow φ hφ s (yc + e • z) σ)
    (e⁻¹ • streamFlow φ hφ s (yc + e • z) σ)
  let Tf := fun d W k => taylorSlow 0 Ks
    (fun X => F.flux p c v u γ d W (timeScale * τ) X
      (e⁻¹ • streamFlow φ hφ s (yc + e • z) σ) k)
    (E⁻¹ • streamFlow φ hφ s yc σ)
    (E⁻¹ • (streamFlow φ hφ s (yc + e • z) σ - streamFlow φ hφ s yc σ))
  have hrw : naturalFamilyRemainderNativeArray Ks F p c v u γ timeScale a b hφ s σ e E yc r τ z =
      F.weight p (timeScale * τ) • nativeArrayAssembly r (F.identity v u γ).map
        (fun (k : Fin 2) (I : DerivativeWord2 r) => transportedCoeff Jac (F.identity v u γ).maxOrder (fun d W => Bf d W - Tf d W) r I z k) := by
    unfold naturalFamilyRemainderNativeArray
    simp only [naturalSlowRemainderTimeCoefficient, ite_eq_left hτ]
    rw [← map_smul]
    rfl
  rw [hrw]
  change F.weight p (timeScale * τ) • nativeArrayAssembly r (F.identity v u γ).map
      (fun (k : Fin 2) (I : DerivativeWord2 r) => transportedCoeff Jac (F.identity v u γ).maxOrder Tf r I z k) + _ = _
  simpa only [smul_add, Jac, Bf] using
    (congrArg (fun A => F.weight p (timeScale * τ) • A)
      (nativeArrayAssembly_transported_remainder_split Jac (F.identity v u γ).maxOrder Bf Tf r
        (F.identity v u γ).map z)).symm

/-- A misaligned piece's two native arrays equal its block Taylor array plus the
ordinary transported remainder at a fast-independent active output time. -/
theorem blockEdge_misaligned_split (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l : ℤ) (hl : (F.piece p).label ≠ l) (σ e E timeScale a b : ℝ)
    (hδ : e / E ≠ 0) (yc z : Vec 2) (r : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc a b)
    (hfast : F.weight p (timeScale * τ) ≠ 0 → ∀ d W X y, F.flux p c v u γ d W (timeScale * τ) X y =
      F.flux p c v u γ d W (timeScale * τ) X 0) :
    naturalFamilyTaylorNativeArray Ks F p c v u γ timeScale hφ
        (F.piece p).anchor σ e E yc r τ z +
      naturalFamilyRemainderNativeArray Ks F p c v u γ timeScale a b hφ
        (F.piece p).anchor σ e E yc r τ z =
    F.weight p (timeScale * τ) • nativeArrayAssembly r (F.identity v u γ).map
      (fun (k : Fin 2) (I : DerivativeWord2 r) => taylorSlow 0 Ks
        (fun X => blockLetterCoefficient F hφ p c v u γ l σ yc e E timeScale (r + 1) I τ X z k)
        (E⁻¹ • yc) ((e / E) • z)) +
      nativeArrayAssembly r (F.identity v u γ).map
        (fun (k : Fin 2) (I : DerivativeWord2 r) => F.weight p (timeScale * τ) * blockTransportedTimeRemainder Ks F hφ p c v u γ
          (F.piece p).anchor σ e E timeScale a b yc r I k τ z) := by
  rw [blockEdge_native_full_split Ks F p c v u γ hφ (F.piece p).anchor σ e E timeScale a b yc z r τ hτ]
  by_cases hw : F.weight p (timeScale * τ) = 0
  · ext W k
    simp [nativeArrayAssembly, hw]
  · have ht : τ ∈ Set.Icc a b ∧ F.weight p (timeScale * τ) ≠ 0 := ⟨hτ, hw⟩
    have hsum : (fun (k : Fin 2) (I : DerivativeWord2 r) => transportedCoeff
        (fun y => naturalPreparationJacobian hφ (F.piece p).anchor σ (yc + e • y))
        (F.identity v u γ).maxOrder (fun d W => F.flux p c v u γ d W (timeScale * τ)
          (E⁻¹ • streamFlow φ hφ (F.piece p).anchor (yc + e • z) σ)
          (e⁻¹ • streamFlow φ hφ (F.piece p).anchor (yc + e • z) σ)) r I z k) =
        (fun (k : Fin 2) (I : DerivativeWord2 r) => taylorSlow 0 Ks
          (fun X => blockLetterCoefficient F hφ p c v u γ l σ yc e E timeScale (r + 1) I τ X z k)
          (E⁻¹ • yc) ((e / E) • z)) +
        (fun (k : Fin 2) (I : DerivativeWord2 r) => blockTransportedTimeRemainder Ks F hφ p c v u γ
          (F.piece p).anchor σ e E timeScale a b yc r I k τ z) := by
      funext k I
      simp only [Pi.add_apply]
      rw [blockEdge_misaligned_taylor F hφ p c v u γ l hl σ e E timeScale hδ yc z Ks r I τ k]
      have hct : blockTransportedTimeCoefficient F hφ p c v u γ
          (F.piece p).anchor σ e E timeScale a b yc r I k τ =
          fun x => blockTransportedSlowCoefficient F hφ p c v u γ
            (F.piece p).anchor σ e E yc r I (timeScale * τ) x k := by
        funext x
        simp only [blockTransportedTimeCoefficient, ite_eq_left ht]
      unfold blockTransportedTimeRemainder
      dsimp only
      rw [hct]
      simp only [blockTransportedSlowCoefficient]
      simp_rw [hfast hw]
      ring
    rw [hsum, map_add, smul_add]
    congr 1
    rw [← map_smul]
    congr 1

/-- The remainder array selected by the block label. -/
def blockPieceRemainderNativeArray (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (l : ℤ) (σ e E timeScale a b : ℝ) (yc : Vec 2) (r : ℕ) (τ : ℝ) (z : Vec 2) :=
  if (F.piece p).label = l then
    naturalFamilyRemainderNativeArray Ks F p c v u γ timeScale a b hφ
      (F.piece p).anchor σ e E yc r τ z
  else nativeArrayAssembly r (F.identity v u γ).map
    (fun k I => F.weight p (timeScale * τ) * blockTransportedTimeRemainder Ks F hφ p c v u γ
      (F.piece p).anchor σ e E timeScale a b yc r I k τ z)

section FamilyReadout

variable [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

/-- The literal full source splits into the aggregate block readout and the
selected piece remainders, using fast independence only on the supplied S. -/
theorem blockReferenceCellSourceFlux_split
    (data : BlockMolecularInputs F π K Kmax
      (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) ν e E₀ ρ Cm J B)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ Pcover F)
    (hΛ : 1 ≤ Λ) (actual : ∀ p, Ctx p) (hdesc : F.IsDescending K)
    (Ks : ℕ) (hKs : Ks + 1 ≤ J) (l : ℤ) (σ : ℝ) (hσ : σ = (l : ℝ) * ocTauPP α q Λ m)
    (S : Set ℝ) (hcore : IsCoreOutside α q Λ m F tS tZ S)
    (hquiet : F.IsFastIndependentOn (S ∩ Set.Icc tS tZ))
    (yc z : Vec 2) (a b τ : ℝ) (hτ : τ ∈ Set.Icc a b)
    (htime : (ν⁻¹ * e ^ 2) * τ ∈ Set.Icc tS tZ)
    (hblock : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ (ν⁻¹ * e ^ 2) * τ ∧
      (ν⁻¹ * e ^ 2) * τ ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (v : ι) :
    planeRawCouplingFlux K D τ
      (preparationReferenceCellSourceCoefficient F hφ σ ν e E₀ actual K yc) U v z =
    (∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D,
      blockLetterNativeArray (h := h) Ks F (F.locally_finite tS tZ).toFinset actual
        v u γ (ν⁻¹ * e ^ 2) hφ l σ e E₀ yc (j.val + 1) τ z
        (WithLp.toLp 2 (fun I => planeJetOrder (U u) (j.val + 1) I z))) +
    (∑ u, ∑ γ : F.Γ v u, ∑ j : Fin D, ∑ p ∈ (F.locally_finite tS tZ).toFinset,
      blockPieceRemainderNativeArray Ks F p (actual p) v u γ hφ l σ e E₀ (ν⁻¹ * e ^ 2) a b yc
        (j.val + 1) τ z (WithLp.toLp 2 (fun I => planeJetOrder (U u) (j.val + 1) I z))) := by
  classical
  let pieces := (F.locally_finite tS tZ).toFinset
  have hp (p : P) (hpm : p ∈ pieces) (u : ι) (γ : F.Γ v u) (r : ℕ) :
      naturalFamilyTaylorNativeArray Ks F p (actual p) v u γ (ν⁻¹ * e ^ 2) hφ
          (F.piece p).anchor σ e E₀ yc r τ z +
        naturalFamilyRemainderNativeArray Ks F p (actual p) v u γ (ν⁻¹ * e ^ 2) a b hφ
          (F.piece p).anchor σ e E₀ yc r τ z =
      F.weight p ((ν⁻¹ * e ^ 2) * τ) • nativeArrayAssembly r (F.identity v u γ).map
        (fun (k : Fin 2) (I : DerivativeWord2 r) => taylorSlow 0 Ks
          (fun X => blockLetterCoefficient F hφ p (actual p) v u γ l σ yc e E₀ (ν⁻¹ * e ^ 2)
            (r + 1) I τ X z k) (E₀⁻¹ • yc) ((e / E₀) • z)) +
        blockPieceRemainderNativeArray Ks F p (actual p) v u γ hφ l σ e E₀ (ν⁻¹ * e ^ 2) a b yc r τ z := by
    by_cases hl : (F.piece p).label = l
    · have ha := hc.schedule.anchor_label p ((F.locally_finite tS tZ).mem_toFinset.mp hpm)
      rw [hl] at ha
      have hanchor : (F.piece p).anchor = σ := ha.trans hσ.symm
      rw [blockEdge_aligned_taylor Ks F p (actual p) v u γ hφ l hl σ e E₀ (ν⁻¹ * e ^ 2)
        data.cell_pos.ne' hanchor yc z r τ]
      simp only [blockPieceRemainderNativeArray, ite_eq_left hl]
    · simp only [blockPieceRemainderNativeArray, ite_eq_right hl]
      apply blockEdge_misaligned_split Ks F p (actual p) v u γ hφ l hl σ e E₀ (ν⁻¹ * e ^ 2) a b
        (div_pos data.cell_pos data.slow_pos).ne' yc z r τ hτ
      intro hw d I X y
      have hout := inactiveTimeZeroFamily_weight_ne_zero_mem_output F p ((ν⁻¹ * e ^ 2) * τ) hw
      have hS := blockEdge_misaligned_quiet hΛ F S hcore p l hl _ ⟨hout, htime⟩ hblock
      exact hquiet p (actual p) v u γ d I _ ⟨⟨hS, htime⟩, hout⟩ X y 0
  have harray (u : ι) (γ : F.Γ v u) (r : ℕ) := blockLetterNativeArray_eq_sum Ks F pieces actual v u γ
    hφ l σ e E₀ (ν⁻¹ * e ^ 2) yc z r τ (by
      intro p _ hw k I
      have hout := inactiveTimeZeroFamily_weight_ne_zero_mem_output F p ((ν⁻¹ * e ^ 2) * τ) hw
      exact blockLetterCoefficient_contDiff data p (actual p) v u γ l σ (ν⁻¹ * e ^ 2)
        yc z r Ks I τ (fun _ => ⟨⟨hout, htime⟩, Set.mem_univ _⟩) (by omega) k)
  have hbase := preparationReferenceCellSourceFlux_constructed_split F hc ν e E₀ data.nu_pos.ne'
    data.cell_pos actual K hdesc v Ks σ yc z a b τ hτ (by simpa only [mul_assoc] using htime) U
  rw [hbase]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro j _
  rw [harray u γ (j.val + 1)]
  simp only [sum_apply, smul_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpm
  have hh := congrArg (fun L => L (WithLp.toLp 2 (fun I => planeJetOrder (U u) (j.val + 1) I z)))
    (hp p hpm u γ (j.val + 1))
  simpa only [add_apply, smul_apply] using hh

end FamilyReadout

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The route to `cycle_joint` with the proved ingredients discharged**.

Proved: periodized sums `periodizedSum`, centre counting `centreCounting`, scalar contraction `scalarContraction`, mean conservation
`meanConservation`, normalization `meanNormalization`. Remaining: the one-patch statement `PatchJointStatement`
(level C), the plane-solution statement `PlaneTorusStatement`, path reduction `PathReductionStatement`. -/

@[expose] public section

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- `cycle_joint` from the three remaining ingredients. -/
theorem cycle_joint_of_remaining (hB1 : PatchJointStatement.{0, v, w, x})
    (hB2 : PlaneTorusStatement.{0, v, w, x}) (hpath : PathReductionStatement.{u, v, w, x}) :
    CycleJointStatement.{u, v, w, x} :=
  cycle_joint_route hB1 hB2 periodizedSum.{v, 0} centreCounting scalarContraction.{0, v} hpath
    meanConservation.{u, v} meanNormalization.{u, v, w, x}

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Level C, letters: statement**.

`BlockLettersStatement`: on a cell window inside one renewal block `l` (reference time
`σ = l τ''`, chart centre and cell metric of the chart window `ic`), the two letters of the block
(`blockMetricLetter`, `blockSourceLetter`, restricted to the family window `[tS, tZ]`), with
majorants `CL · √(π_u/π_v) A_{vu}` (source, `θ = CL · Cth Θ`) and `CL · g` on the diagonal
(metric, `θ = CL · g`), are cycle letters (`IsCycleLetter`) with fast reserve `Jstar`; they are
transverse on every family of regions inside the enlarged odd pulses with the pulses' orientation,
quiet on every set of cell times where the cell drift vanishes and whose physical times lie in
the set `S` on which the family is fast independent (in the application, `S` is the trimmed
quiet set), and measurable in time. The
constant `CL` is fixed before the family. The premise `0 ≤ Cth * Θ` keeps the source letter's
`θ` nonnegative for every family: a nonempty family gets it from its envelope (`IsEnvelope.nonneg`,
`row_sum`), but for an empty index type the envelope is vacuous. Pieces of another label than `l` enter the source letter
through their transported slow fields; they are fast independent there. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- **The letters of a renewal block.** -/
def BlockLettersStatement : Prop :=
  ∀ (D Kmax Ks Ls Jm Jchart qJ Jstar : ℕ) (_hJs : Jstar ≤ Ls) (_hqJ : Ks + Jstar ≤ qJ)
    (_hJchart : Ks + Jstar + D ≤ Jchart) (Ca : ℝ) (Cm Cchart CG : ℕ → ℝ),
    ∃ CL : ℝ, 0 ≤ CL ∧
    ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
      (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
      (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (y₀ : Vec 2)
      (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG
        l₀ P y₀)
      (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
      (_ha : 0 ≤ ocA α q Λ (m - 1)) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
      [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
      (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
      (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
      (actual : ∀ p, Ctx p) (A : Matrix ι ι ℝ) (Θ Cth : ℝ) (H : ℕ),
      0 ≤ Cth * Θ →
      IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
      (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
      IsEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) ν
        (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ
        (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm →
      F.HasDepthAtMost H →
      F.IsTransverseOnPulses
        (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
          (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS tZ)
        (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1) →
      ∀ S : Set ℝ, F.IsFastIndependentOn (S ∩ Set.Icc tS tZ) →
      ∀ (ic : Fin (P + 2)) (a b : ℝ), a ≤ b →
      Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
      ∀ (l : ℤ) (σ : ℝ), σ = (l : ℝ) * ocTauPP α q Λ m → (l = l₀ ∨ σ ∈ Set.Icc tS tZ) →
      (∀ t ∈ Set.Icc a b, ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
        ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let vd := ocCellDrift α q Λ ζfast m ν yc
    let X₀ := (ocEpsilon q Λ (m - 1))⁻¹ • yc
    let δ := ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)
    let Sl := blockSourceLetter F (F.locally_finite tS tZ).toFinset actual hφ (Set.Icc tS tZ) l σ yc
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ν⁻¹ * ocEpsilon q Λ m ^ 2) Ks (CL * (Cth * Θ))
      (fun v u => CL * (Real.sqrt (π u / π v) * A v u))
    let Ml := blockMetricLetter (D := D) (h := h) G X₀ δ Ks (CL * g)
      (fun v u => if v = u then CL * g else 0)
    IsCycleLetter π Sl (Set.Icc a b ×ˢ Set.univ) Jstar H ∧
    IsCycleLetter π Ml (Set.Icc a b ×ˢ Set.univ) Jstar H ∧
    (∀ {κ : Type} (pulse : κ → Set ℝ) (orient : κ → Fin 2),
      (∀ p, ∃ k : ℤ, Odd k ∧
        (∀ t ∈ pulse p, |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
        orient p = (if k % 4 = 3 then 0 else 1)) →
      IsTransverseOnPulses Sl.edge pulse orient ∧ IsTransverseOnPulses Ml.edge pulse orient) ∧
    (∀ Q : Set ℝ, (∀ t ∈ Q, ν⁻¹ * ocEpsilon q Λ m ^ 2 * t ∈ S) → (∀ t ∈ Q, ∀ z, vd t z = 0) →
      IsQuietOn Sl.edge vd Q ∧ IsQuietOn Ml.edge vd Q) ∧
    (∀ x y o, ∀ γ ∈ Sl.edge x y o, ∀ α X z, Measurable fun t => γ.coeff α t X z) ∧
    (∀ x y o, ∀ γ ∈ Ml.edge x y o, ∀ α X z, Measurable fun t => γ.coeff α t X z)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! Exact assembly of the block-letter statement from its quantitative analytic
bounds and the remaining qualitative and finite-graph properties. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The finite-order, Schur-sum and depth fields of a cycle letter. -/
structure BlockLetterSkeleton {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
    (L : CycleLetter ι h D) (H : ℕ) : Prop where
  order_ge : 2 ≤ L.order
  order_le : L.order ≤ D
  edge_order : ∀ v u (o : Finset.Icc 2 D), L.order < o.1 → L.edge v u o = []
  theta_nonneg : 0 ≤ L.theta
  nonneg : ∀ v u, 0 ≤ L.majorant v u
  row_sum : ∀ v, ∑ u, L.majorant v u ≤ L.theta
  col_sum : ∀ u, ∑ v, L.majorant v u ≤ L.theta
  depth : L.positive = false → HasDepthAtMost L.edge H

/-- Add the analytic estimate to the remaining cycle-letter fields. -/
theorem BlockLetterSkeleton.toIsCycleLetter {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
    {π : ι → ℝ} {L : CycleLetter ι h D} {H J : ℕ} {dom : Set (ℝ × Vec 2)}
    (hs : BlockLetterSkeleton L H)
    (ha : IsAnalyticEnvelope (ChartedFamily.ofFiber L.edge) π (fun _ _ => dom)
      1 1 L.slow J L.majorant) : IsCycleLetter π L dom J H :=
  { hs with analytic := ha }

/-- A uniform common price for the two analytic envelopes, before the family. -/
def BlockLettersAnalyticStatement : Prop :=
  ∀ (D Kmax Ks Ls Jm Jchart qJ Jstar : ℕ) (_hJs : Jstar ≤ Ls) (_hqJ : Ks + Jstar ≤ qJ)
    (_hJchart : Ks + Jstar + D ≤ Jchart) (Ca : ℝ) (Cm Cchart CG : ℕ → ℝ),
    ∃ CL : ℝ, 0 ≤ CL ∧
    ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
      (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
      (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (y₀ : Vec 2)
      (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG
        l₀ P y₀)
      (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
      (_ha : 0 ≤ ocA α q Λ (m - 1)) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
      [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
      (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
      (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
      (actual : ∀ p, Ctx p) (A : Matrix ι ι ℝ) (Θ Cth : ℝ) (H : ℕ),
      0 ≤ Cth * Θ →
      IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
      (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
      IsEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) ν
        (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ
        (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm →
      F.HasDepthAtMost H →
      F.IsTransverseOnPulses
        (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
          (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS tZ)
        (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1) →
      ∀ S : Set ℝ, F.IsFastIndependentOn (S ∩ Set.Icc tS tZ) →
      ∀ (ic : Fin (P + 2)) (a b : ℝ), a ≤ b →
      Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
      ∀ (l : ℤ) (σ : ℝ), σ = (l : ℝ) * ocTauPP α q Λ m → (l = l₀ ∨ σ ∈ Set.Icc tS tZ) →
      (∀ t ∈ Set.Icc a b, ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
        ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let X₀ := (ocEpsilon q Λ (m - 1))⁻¹ • yc
    let δ := ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)
    let Sl := blockSourceLetter F (F.locally_finite tS tZ).toFinset actual hφ (Set.Icc tS tZ) l σ yc
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ν⁻¹ * ocEpsilon q Λ m ^ 2) Ks (CL * (Cth * Θ))
      (fun v u => CL * (Real.sqrt (π u / π v) * A v u))
    let Ml := blockMetricLetter (D := D) (h := h) G X₀ δ Ks (CL * g)
      (fun v u => if v = u then CL * g else 0)
    IsAnalyticEnvelope (ChartedFamily.ofFiber Sl.edge) π
      (fun _ _ => Set.Icc a b ×ˢ Set.univ) 1 1 Ks Jstar Sl.majorant ∧
    IsAnalyticEnvelope (ChartedFamily.ofFiber Ml.edge) π
      (fun _ _ => Set.Icc a b ×ˢ Set.univ) 1 1 Ks Jstar Ml.majorant

/-- The remaining properties hold at every nonnegative common price. -/
def BlockLettersStructuralStatement : Prop :=
  ∀ (D Kmax Ks Ls Jm Jchart qJ Jstar : ℕ) (_hJs : Jstar ≤ Ls) (_hqJ : Ks + Jstar ≤ qJ)
    (_hJchart : Ks + Jstar + D ≤ Jchart) (Ca : ℝ) (Cm Cchart CG : ℕ → ℝ),
    ∀ CL : ℝ, 0 ≤ CL →
    ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
      (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
      (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (y₀ : Vec 2)
      (_cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG
        l₀ P y₀)
      (_hΛ : 1 ≤ Λ) (_heE : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1))
      (_ha : 0 ≤ ocA α q Λ (m - 1)) (_hg0 : g0 ≤ 1 / 4) (_hD : 2 ≤ D),
    ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
      [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
      (_hmeas : F.IsTimeMeasurable) (_hwmeas : ∀ p, Measurable (F.weight p))
      (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
      (actual : ∀ p, Ctx p) (A : Matrix ι ι ℝ) (Θ Cth : ℝ) (H : ℕ),
      0 ≤ Cth * Θ →
      IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
      (Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output) →
      IsEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) ν
        (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρ
        (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm →
      F.HasDepthAtMost H →
      F.IsTransverseOnPulses
        (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
          (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS tZ)
        (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1) →
      ∀ S : Set ℝ, F.IsFastIndependentOn (S ∩ Set.Icc tS tZ) →
      ∀ (ic : Fin (P + 2)) (a b : ℝ), a ≤ b →
      Set.Icc a b ⊆ windowCoverChartWindow α q Λ m ν tS tZ l₀ P ic →
      ∀ (l : ℤ) (σ : ℝ), σ = (l : ℝ) * ocTauPP α q Λ m → (l = l₀ ∨ σ ∈ Set.Icc tS tZ) →
      (∀ t ∈ Set.Icc a b, ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
        ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) →
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
    let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
    let vd := ocCellDrift α q Λ ζfast m ν yc
    let X₀ := (ocEpsilon q Λ (m - 1))⁻¹ • yc
    let δ := ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)
    let Sl := blockSourceLetter F (F.locally_finite tS tZ).toFinset actual hφ (Set.Icc tS tZ) l σ yc
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ν⁻¹ * ocEpsilon q Λ m ^ 2) Ks (CL * (Cth * Θ))
      (fun v u => CL * (Real.sqrt (π u / π v) * A v u))
    let Ml := blockMetricLetter (D := D) (h := h) G X₀ δ Ks (CL * g)
      (fun v u => if v = u then CL * g else 0)
    BlockLetterSkeleton Sl H ∧
    BlockLetterSkeleton Ml H ∧
    (∀ {κ : Type} (pulse : κ → Set ℝ) (orient : κ → Fin 2),
      (∀ p, ∃ k : ℤ, Odd k ∧
        (∀ t ∈ pulse p, |ocEll q Λ m ν ^ 2 * t - k * ocTau α q Λ m| ≤ 3 / 4 * ocTau α q Λ m) ∧
        orient p = (if k % 4 = 3 then 0 else 1)) →
      IsTransverseOnPulses Sl.edge pulse orient ∧ IsTransverseOnPulses Ml.edge pulse orient) ∧
    (∀ Q : Set ℝ, (∀ t ∈ Q, ν⁻¹ * ocEpsilon q Λ m ^ 2 * t ∈ S) → (∀ t ∈ Q, ∀ z, vd t z = 0) →
      IsQuietOn Sl.edge vd Q ∧ IsQuietOn Ml.edge vd Q) ∧
    (∀ x y o, ∀ γ ∈ Sl.edge x y o, ∀ α X z, Measurable fun t => γ.coeff α t X z) ∧
    (∀ x y o, ∀ γ ∈ Ml.edge x y o, ∀ α X z, Measurable fun t => γ.coeff α t X z)

/-- Assemble the exact block-letter conclusion with one common price. -/
theorem blockLetters_of_ingredients
    (hanalytic : BlockLettersAnalyticStatement.{u, v, w, x})
    (hstructural : BlockLettersStructuralStatement.{u, v, w, x}) :
    BlockLettersStatement.{u, v, w, x} := by
  intro D Kmax Ks Ls Jm Jchart qJ Jstar hJs hqJ hJchart Ca Cm Cchart CG
  obtain ⟨CL, hCL, ha⟩ := hanalytic D Kmax Ks Ls Jm Jchart qJ Jstar hJs hqJ hJchart Ca Cm Cchart CG
  have hs := hstructural D Kmax Ks Ls Jm Jchart qJ Jstar hJs hqJ hJchart Ca Cm Cchart CG CL hCL
  refine ⟨CL, hCL, ?_⟩
  intro α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb y₀
    cov hΛ heE haOld hg0 hD
    ι instFintype instDecidable h instNorm instInner instFinite instMeas instBorel instComplete
    P' Ctx F hmeas hwmeas π hπ K hK actual A Θ Cth H hθ hc hcoverage henv hdepth htransverse
    S hquiet ic a b hab hwindow l σ hσ hσmem hblock
  obtain ⟨haS, haM⟩ := ha α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0
    strain B₀ lam Cb y₀ cov hΛ heE haOld hg0 hD F hmeas hwmeas π hπ K hK actual A Θ Cth H
    hθ hc hcoverage henv hdepth htransverse S hquiet ic a b hab hwindow l σ hσ hσmem hblock
  obtain ⟨hsS, hsM, hrest⟩ := hs α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0
    strain B₀ lam Cb y₀ cov hΛ heE haOld hg0 hD F hmeas hwmeas π hπ K hK actual A Θ Cth H
    hθ hc hcoverage henv hdepth htransverse S hquiet ic a b hab hwindow l σ hσ hσmem hblock
  exact ⟨hsS.toIsCycleLetter haS, hsM.toIsCycleLetter haM, hrest⟩

end AVRegularity.CycleJointProofs.Assembly
end
end
