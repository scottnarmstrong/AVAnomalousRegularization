-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.CellEnergyPlaneH1Gradient
public import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal Topology
open Filter
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem constantMetric_scalarChain_polynomial_factorial_supremum
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
    (hCell : IsCellMetric G)
    (hconstant : ∀ t x, G t x = G t 0)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
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
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 2)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    (⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)) +
      (∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc r (κ i.1 i.2) (w i s)) ≤
      ENNReal.ofReal (L ^ (2 * Kmax)) * 5 *
        (ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
          ENNReal.ofReal (3 * Real.exp (18 * Cw m))) *
        (weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) +
          16 * ∫⁻ s in Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) := by
  have hh := constantMetric_scalarChain_polynomial_factorial_energy a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb hCell hconstant hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm r L hr hL
    hsmall hstrainSmall hreserve hdiv hwa hwb
  have hs := quarter_production_supremum_le (Icc a b) b ⟨hab, le_rfl⟩ _ _ _ hh
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
    _ ≤ A * (5 * ((ENNReal.ofReal (Cw m) * ENNReal.ofReal (Cw m) *
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
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Each original nonzero sampled constituent produces a genuine native forcing with its molecular price. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalFamily_native_flux_normalized_rows_exists (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hdesc : F.IsDescending K) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b₀) (hmeas : F.IsTimeMeasurable)
    (hb₀ : ∀ v u, 0 ≤ b₀ v u) (hrow : ∀ v, ∑ u, b₀ v u ≤ 1) (hcol : ∀ u, ∑ v, b₀ v u ≤ 1)
    (p : P) (c : Ctx p)
    (s a b ϖ : ℝ) (hs : s ≠ 0) (hϖ : 0 < ϖ) (X0 φ : Vec 2)
    (hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
    (U : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (hU : ∀ u, MemLp (U u) 2 (volume.restrict (Set.Icc a b))) :
    ∃ V : ∀ v, ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
      (∀ v, MemLp (V v) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V v t) =ᵐ[volume]
        (fun z => ∑ u, ∑ α : OriginalSourceIndex F v u,
          F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + (e / E) • z) (z + φ) α.2.2.2 •
            Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
              (planeJetOrder (U u t) (α.2.1.1 - 1) α.2.2.1 z))) ∧
      (∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
        (π v)⁻¹ * planeFactorialDensity (ρ / e) (V v t) z ≤
          originalSourceGraphConstant Kmax (C 0) *
            ∑ u, (Real.sqrt (π u / π v) *
              (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α)) *
                ((π u)⁻¹ * planeGradFactorialDensity (ρ / e) (U u t) z)) := by
  classical
  have hpairs (v u : ι) := originalPair_native_flux_exists F π hπ K Kmax hK hdesc dom
    ν e E ρ hν he hE hρ C J b₀ henv hmeas v u p c s a b ϖ hs hϖ X0 φ hwindow (U u) (hU u)
  choose V hV hvalue hdensity using hpairs
  refine ⟨fun v t => ∑ u, V v u t, ?_, ?_, ?_⟩
  · intro v
    exact memLp_finsetSum (ε' := PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
      (f := V v) Finset.univ (fun u _ => hV v u)
  · intro v
    filter_upwards [ae_all_iff.mpr (hvalue v)] with t ht
    have hv := planeJetOrder_finite_sum_ae (Nat.zero_le (K v)) (fun u => V v u t)
      (fun i : Fin 0 => Fin.elim0 i)
    filter_upwards [hv, ae_all_iff.mpr ht] with z hz hzs
    exact hz.trans (Finset.sum_congr rfl (fun u _ => hzs u))
  · obtain ⟨hr, _⟩ := originalSourcePrice_graph_budget F π K Kmax hK dom ν e E ρ
      hν hE hρ C J b₀ henv hb₀ hrow hcol
    intro v
    filter_upwards [ae_all_iff.mpr (hdensity v)] with t ht
    have hh := nativeFlux_normalized_row_density_budget (ρ / e) (fun u => V v u t) π hπ v
      (fun u => ∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α)
      (fun u => Finset.sum_nonneg (fun α _ =>
        originalSourcePrice_nonneg F K Kmax dom ν e E ρ hν.le hρ.le v u α))
      (originalSourceGraphConstant Kmax (C 0)) (hr v)
      (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
      (fun u z => planeGradFactorialDensity (ρ / e) (U u t) z)
      (fun u z => planeGradFactorialDensity_nonneg (ρ / e) (U u t) z)
      (fun u => by simpa only [one_mul] using ht u)
    simpa only [mul_one] using hh

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal Topology
open Filter
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem constantMetric_scalarChain_polynomial_energy_ne_top
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
    (hCell : IsCellMetric G)
    (hconstant : ∀ t x, G t x = G t 0)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
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
    (hreserve : Real.exp (18 * Cw m) / L ^ 2 ≤ 1 / 2)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S)
    (hf : weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (f i) ≠ ⊤)
    (hFe : (∫⁻ s in Icc a b,
      weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (F i s)) ≠ ⊤) :
    ((⨆ t ∈ Icc a b, weightedFactorialNormSq m ϖ zc r (κ i.1 i.2) (u i t)) +
      (∫⁻ s in Icc a b, weightedGradFactorialNormSq m ϖ zc r (κ i.1 i.2) (w i s))) ≠ ⊤ := by
  have hh := constantMetric_scalarChain_polynomial_factorial_supremum a b hab κ Kmax hκ
    v hvm hv V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb hCell hconstant hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm r L hr hL
    hsmall hstrainSmall hreserve hdiv hwa hwb
  apply ne_top_of_le_ne_top _ hh
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top)
  · exact ENNReal.add_ne_top.mpr ⟨hf, ENNReal.mul_ne_top (by norm_num) hFe⟩

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The original molecular envelope supplies a graph budget uniform in the family and its masses. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalSource_normalized_graph_budget (F : ChartedFamily ι h D P Ctx)
    (Hdepth : ℕ) (hdepth : F.HasDepthAtMost Hdepth) (π : ι → ℝ) (K : ι → ℕ) (Kmax : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (dom : F.Domain) (ν e E ρ : ℝ) (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b)
    (hb : ∀ v u, 0 ≤ b v u) (hrow : ∀ v, ∑ u, b v u ≤ 1)
    (hcol : ∀ u, ∑ v, b v u ≤ 1) :
    let price := fun v u => Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α)
    let θ := originalSourceGraphConstant Kmax (C 0)
    (∀ v u, 0 ≤ normalizedFiniteGraph θ price v u) ∧
    (∀ v, ∑ u, normalizedFiniteGraph θ price v u ≤ 1) ∧
    (∀ u, ∑ v, normalizedFiniteGraph θ price v u ≤ 1) ∧
    (∀ v u, normalizedFiniteGraph θ price v u ≠ 0 →
      familyDepthRank F Hdepth u < familyDepthRank F Hdepth v) := by
  classical
  let price := fun v u => Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α)
  have hp (v u : ι) : 0 ≤ price v u := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun α _ =>
      originalSourcePrice_nonneg F K Kmax dom ν e E ρ hν.le hρ.le v u α))
  obtain ⟨hr, hc⟩ := originalSourcePrice_graph_budget F π K Kmax hK dom ν e E ρ
    hν hE hρ C J b henv hb hrow hcol
  obtain ⟨hn, hnr, hnc⟩ := normalizedFiniteGraph_budget
    (originalSourceGraphConstant Kmax (C 0)) (originalSourceGraphConstant_nonneg Kmax (C 0))
    price hp hr hc
  refine ⟨hn, hnr, hnc, ?_⟩
  apply normalizedFiniteGraph_support
  intro v u hne
  by_contra hlt
  have hz := originalSource_sum_zero_of_rank F Hdepth hdepth v u (Nat.le_of_not_gt hlt)
    (fun α => originalSourcePrice F K Kmax dom ν e E ρ v u α)
  exact hne (by simp only [hz, mul_zero])

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! Genuine real plane H1 time states obtained from the complex Bloch evolution. -/

def cellEnergyPlaneRealH1State {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    Lp (PlaneHk Set.univ 1 ℝ) 2 (volume.restrict (Set.Icc a b)) :=
  (planeComplexRealPart 1).compLp (cellEnergyPlaneH1State hab F)

theorem cellEnergyPlaneRealH1State_value {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      planeHkValueOperator 1 (cellEnergyPlaneRealH1State hab F t) =
        planeComplexRealPartL2
          ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
            ((cellEnergyTraceAtCLM a b (projIcc a b hab t)).compLp F)) := by
  filter_upwards [(planeComplexRealPart 1).coeFn_compLp (cellEnergyPlaneH1State hab F),
    cellEnergyPlaneH1State_value hab F] with t ht hv
  change cellEnergyPlaneRealH1State hab F t =
    planeComplexRealPart 1 (cellEnergyPlaneH1State hab F t) at ht
  rw [ht, planeComplexRealPart_value, hv]

theorem cellEnergyPlaneRealH1State_gradient {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i : Fin 2,
      univToPlane ((cellEnergyPlaneRealH1State hab F t).val ⟨⟨1, by decide⟩, fun _ => i⟩) =
        planeComplexRealPartL2
          (cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F t) i) := by
  filter_upwards [(planeComplexRealPart 1).coeFn_compLp (cellEnergyPlaneH1State hab F),
    cellEnergyPlaneH1State_gradient hab F] with t ht hg i
  change cellEnergyPlaneRealH1State hab F t =
    planeComplexRealPart 1 (cellEnergyPlaneH1State hab F t) at ht
  rw [ht, planeComplexRealPart_component, hg i]

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual chain's flux is its scalar metric flux plus the literal original-family forcing. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem geometryActualFamilyFlux_split (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (hdesc : F.IsDescending K) (p : P) (c : Ctx p)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (s δ t : ℝ) (X0 φ z : Vec 2) (v : ι)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) :
    geometryActualFlux D G (F.cellFiber s φ p c) X0 δ (fun _ u => K u)
        (fun q => U q.2) (0, v) t z =
      geometryScalarFlux D G (fun _ u => K u) (fun q => U q.2) (0, v) t z +
        ∑ u, ∑ α : OriginalSourceIndex F v u,
          F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + δ • z) (z + φ) α.2.2.2 •
            Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
              (planeJetOrder (U u) (α.2.1.1 - 1) α.2.2.1 z) := by
  classical
  rw [geometryActualFlux_split]
  congr 1
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro u _
  exact originalCellSource_order_flux F K hdesc p c v u s δ t X0 φ z (U u)

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_clipped_factorial_lower_absorption
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
    (clip r L : ℝ) (hclip : 0 < clip) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : r * δ ≤ 1) (CG : ℕ → ℝ)
    (hreserve : Real.exp (18 * Cw m) *
      (1 + (metricRadiusConstant Kmax CG) ^ 2) / L ^ 2 ≤ 1 / 16)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    let q := fun t x => clipWeight clip (C.W m t x)
    ∀ t ∈ Icc a b,
      rawWeightedFactorialEnergy (r / L) (q t) (u i t).toFunction.jet +
      (∫ s in a..b, rawWeightedGradientEnergy (r / L) (q s) (w i s).toFunction.jet) / 2 ≤
      3 * Real.exp (18 * Cw m) *
        (rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet +
          16 * (∫⁻ s in Icc a b, ENNReal.ofReal (rawWeightedFactorialEnergy (r / L) (q s) (F i s).toFunction.jet)).toReal) := by
  dsimp only
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hν : 0 < 1 / L ^ 2 := one_div_pos.mpr (sq_pos_of_pos hLp)
  have hρ : 0 < r / L := div_pos hr hLp
  have hs : B * (r / L) / lam ≤ 1 / 2 :=
    (reducedRadius_drift_scale hlam hLp hsmall).trans
      (div_le_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hL)
  have hst : strain * B * (r / L) ^ 2 ≤ (1 / L ^ 2) / 8 := by
    convert reducedRadius_strain_scale (L := L) hstrainSmall using 1
    ring
  have hsc : (r / L) * δ ≤ 1 :=
    (reducedRadius_metric_scale hLp hscale).trans (by simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hL)
  have hh := scalarChain_clipped_factorial_real_lower_budget a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip (r / L) hclip
    hρ (1 / L ^ 2) hν hs hst δ hδ hg hsc CG hmetricJets hdiv hwa hwb
  dsimp only at hh
  let q := fun t x => clipWeight clip (C.W m t x)
  let e := fun t => rawWeightedFactorialEnergy (r / L) (q t) (u i t).toFunction.jet
  let d := fun t => rawWeightedGradientEnergy (r / L) (q t) (w i t).toFunction.jet
  let ff := fun t => rawWeightedFactorialEnergy (r / L) (q t) (F i t).toFunction.jet
  let A := Real.exp (18 * Cw m)
  let c := 16 * (metricRadiusConstant (κ i.1 i.2) CG * g * ((r / L) * δ)) ^ 2 +
    (1 / L ^ 2) / 2
  have hq0 t x : 0 ≤ q t x := (clipWeight_pos hclip (C.pos m hm t x)).le
  have he0 t : 0 ≤ e t := rawWeightedFactorialEnergy_nonneg _ _ (hq0 t) _
  have hd0 t : 0 ≤ d t := rawWeightedGradientEnergy_nonneg _ _ (hq0 t) _
  have hD0 : 0 ≤ ∫ s in a..b, d s :=
    intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hd0)
  have hF0 : 0 ≤ (∫⁻ s in Icc a b, ENNReal.ofReal (ff s)).toReal := ENNReal.toReal_nonneg
  have hI0 : 0 ≤ rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet :=
    rawWeightedFactorialEnergy_nonneg _ _ (hq0 a) _
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : A * c ≤ 1 / 2 := maximalSlot_radius_source_reserve (hκ i) CG
    (Real.exp_pos _).le hL hreserve hr.le hδ hg hg4 hscale
  have hCw : 0 ≤ Cw m := (by norm_num : (0 : ℝ) ≤ 1).trans
    (chartWeights_constant_ge_one C m hm a ⟨hwa, hab.trans hwb⟩)
  have hbudget0 : 0 ≤ rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet +
      16 * (∫⁻ s in Icc a b, ENNReal.ofReal (ff s)).toReal + c * (∫ s in a..b, d s) := by positivity
  have hbound t (ht : t ∈ Icc a b) : e t + (∫ s in a..t, d s) ≤
      A * (rawWeightedFactorialEnergy (r / L) (q a) (f i).toFunction.jet +
        16 * (∫⁻ s in Icc a b, ENNReal.ofReal (ff s)).toReal + c * (∫ s in a..b, d s)) := by
    have hexp := chart_interval_rate_exp_bound hwa hab hwb ht
      (C.lam_bound m hm).1 hCw (C.lam_bound m hm).2
    exact (hh t ht).trans (by
      rw [mul_comm A]
      exact mul_le_mul_of_nonneg_left hexp hbudget0)
  intro t ht
  have hpart0 : 0 ≤ ∫ s in a..t, d s :=
    intervalIntegral.integral_nonneg_of_ae_restrict ht.1 (Filter.Eventually.of_forall hd0)
  have het := (le_add_of_nonneg_right hpart0).trans (hbound t ht)
  exact retained_full_interval_energy (he0 b) hD0 hc het (hbound b ⟨hab, le_rfl⟩)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.CycleWords

/-! The literal response flux has one same-level Taylor source and one previous-level metric insertion. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

def geometryResponseOrderedFlux (J Ks : ℕ) (K : ι → ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (edge : ConstituentEdges D h)
    (X0 : Vec 2) (δ : ℝ)
    (U : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u + 1) (h u))
    (j : Fin (J + 1)) (v : ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ j' : Fin (J + 1), ∑ u, ∑ d : admissibleOrders K D v u,
    planeChainCoefficient (geometryResponseData J Ks G 0 edge X0 δ) (fun _ v => K v)
      (j, v) (j', u) d t z
      (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) => planeJetOrder (U j' u) (d.1 - 1) word z))

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem geometryResponseOrderedFlux_split (F : ChartedFamily ι h D P Ctx)
    (hD : 2 ≤ D) (J Ks : ℕ) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (p : P) (c : Ctx p) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (s δ : ℝ) (X0 φ : Vec 2)
    (U : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u + 1) (h u))
    (j : Fin (J + 1)) (v : ι) (t : ℝ) (z : Vec 2) :
    geometryResponseOrderedFlux J Ks K G (F.cellFiber s φ p c) X0 δ U j v t z =
      geometryScalarFlux D (fun t _ => G t 0) (fun _ v => K v) (fun q => U j q.2) (0, v) t z +
      (∑ u, ∑ α : OriginalSourceIndex F v u,
        taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + φ) α.2.2.2)
          X0 (δ • z) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
            (planeJetOrder (U j u) (α.2.1.1 - 1) α.2.2.1 z)) +
      ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then
        WithLp.toLp 2 (fun k : Fin 2 => ∑ l : Fin 2, metricTaylor 1 Ks G t 0 z k l •
          (U j' v).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) else 0 := by
  classical
  let ev : (Vec 2 → ℝ) → Vec 2 → ℝ := fun f z => taylorSlow 0 Ks f X0 (δ • z)
  let self := fun j' : Fin (J + 1) =>
    ∑ u, ∑ d : admissibleOrders K D v u,
      if j = j' then
        planeChainCoefficient (geometryScalarData D (fun t _ => G t 0)) (fun _ v => K v)
          (0, v) (0, u) d t z
          (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) => planeJetOrder (U j' u) (d.1 - 1) word z)) +
        slowEvalCoefficient ev (F.cellFiber s φ p c v u ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) t z
          (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) => planeJetOrder (U j' u) (d.1 - 1) word z)) else 0
  let prev := fun j' : Fin (J + 1) =>
    ∑ u, ∑ d : admissibleOrders K D v u,
      if j.val = j'.val + 1 then
        (if hv : v = u ∧ d.1 = 2 then
          metricFlux (metricTaylor 1 Ks G t 0 z) (d.1 - 1) hv.1 (by omega)
            (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) => planeJetOrder (U j' u) (d.1 - 1) word z))
          else 0) else 0
  have hsplit : geometryResponseOrderedFlux J Ks K G (F.cellFiber s φ p c) X0 δ U j v t z =
      (∑ j', self j') + ∑ j', prev j' := by
    unfold geometryResponseOrderedFlux
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j' _
    dsimp only [self, prev]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [geometryResponseCoefficient_split, add_apply]
    split_ifs <;> simp_all [ev, add_apply]
  rw [hsplit]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_eq_single j]
    · dsimp only [self]
      simp only [ite_true, Finset.sum_add_distrib]
      apply congrArg₂ (· + ·)
      · unfold geometryScalarFlux admissibleOrders
        rw [Fintype.sum_prod_type, Fin.sum_univ_one]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro d _
        congr 2
        funext word
        dsimp only
        have hd := (Finset.mem_filter.mp d.2).2
        rw [planeJetOrder_eq_stored (show d.1 - 1 ≤ K u + 1 by omega)]
      · apply Finset.sum_congr rfl
        intro u _
        exact originalCellSource_eval_order_flux F K hdesc p c v u ev s t φ z (U j u)
    · intro j' _ hne
      simp only [self, Ne.symm hne, ite_false, Finset.sum_const_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_univ j))
  · apply Finset.sum_congr rfl
    intro j' _
    by_cases hj : j.val = j'.val + 1
    · simp only [prev, ite_eq_left hj]
      have hh := metricOrderFlux_sum_eq D hD K (metricTaylor 1 Ks G t 0 z) (U j') v z
      convert hh using 1
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro d _
      by_cases hv : v = u ∧ d.1 = 2
      · simp only [dite_eq_left hv]
      · simp only [dite_eq_right hv, zero_apply]
    · simp only [prev, ite_eq_right hj, Finset.sum_const_zero]

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Taylor splitting is performed on each original constituent flux before
summing the family; no cancellation between constituents is used. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

def originalTaylorNativeSourceFlux (F : ChartedFamily ι h D P Ctx) (Ks : ℕ) (K : ι → ℕ)
    (p : P) (c : Ctx p) (s δ : ℝ) (X0 phase : Vec 2)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (v : ι) (t : ℝ) (z : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ u, ∑ α : OriginalSourceIndex F v u,
    taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + phase) α.2.2.2)
      X0 (δ • z) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
        (planeJetOrder (U u) (α.2.1.1 - 1) α.2.2.1 z)

def originalRemainderNativeSourceFlux (F : ChartedFamily ι h D P Ctx) (Ks : ℕ) (K : ι → ℕ)
    (p : P) (c : Ctx p) (s δ : ℝ) (X0 phase : Vec 2)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (v : ι) (t : ℝ) (z : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ u, ∑ α : OriginalSourceIndex F v u,
    (F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + δ • z) (z + phase) α.2.2.2 -
      taylorSlow 0 Ks (fun X => F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) X (z + phase) α.2.2.2)
        X0 (δ • z)) • Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
          (planeJetOrder (U u) (α.2.1.1 - 1) α.2.2.1 z)

theorem originalSource_taylor_remainder_split (F : ChartedFamily ι h D P Ctx) (Ks : ℕ) (K : ι → ℕ)
    (p : P) (c : Ctx p) (s δ : ℝ) (X0 phase : Vec 2)
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (v : ι) (t : ℝ) (z : Vec 2) :
    (∑ u, ∑ α : OriginalSourceIndex F v u,
      F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + δ • z) (z + phase) α.2.2.2 •
        Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
          (planeJetOrder (U u) (α.2.1.1 - 1) α.2.2.1 z)) =
    originalTaylorNativeSourceFlux F Ks K p c s δ X0 phase U v t z +
      originalRemainderNativeSourceFlux F Ks K p c s δ X0 phase U v t z := by
  classical
  unfold originalTaylorNativeSourceFlux originalRemainderNativeSourceFlux
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [← add_smul, add_sub_cancel]

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_clipped_factorial_lower_ennreal
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
    (clip r L : ℝ) (hclip : 0 < clip) (hr : 0 < r) (hL : 1 ≤ L)
    (hsmall : B * r / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * r ^ 2 ≤ 1 / 8)
    (δ : ℝ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : r * δ ≤ 1) (CG : ℕ → ℝ)
    (hreserve : Real.exp (18 * Cw m) *
      (1 + (metricRadiusConstant Kmax CG) ^ 2) / L ^ 2 ≤ 1 / 16)
    (hmetricJets : ∀ t ∈ Set.Icc a b, ∀ x l, 1 ≤ l → l ≤ Kmax → ∀ k j,
      ‖iteratedFDeriv ℝ l (fun y => G t y k j) x‖ ≤ CG l * g * δ ^ l)
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hwa : t₀ ≤ a) (hwb : b ≤ t₀ + S) :
    let q := fun t x => clipWeight clip (C.W m t x)
    ∀ t ∈ Icc a b,
      storedChartFactorialEnergy (r / L) (q t) (u i t) +
      ENNReal.ofReal (1 / 2 : ℝ) *
        (∫⁻ s in Icc a b, storedChartGradientEnergy (r / L) (q s) (w i s)) ≤
      ENNReal.ofReal (3 * Real.exp (18 * Cw m)) *
        (storedChartFactorialEnergy (r / L) (q a) (f i) +
          16 * ∫⁻ s in Icc a b, storedChartFluxEnergy (r / L) (q s) (F i s)) := by
  dsimp only
  have hh := scalarChain_clipped_factorial_lower_absorption a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha hB hlam hbv hjets G hGm hG M hb g hg4 hGnear hGs
    f F hF u w hsln i hG1 t₀ S ϖ zc N m Cw C hm clip r L hclip hr hL
    hsmall hstrainSmall δ hδ hg hscale CG hreserve hmetricJets hdiv hwa hwb
  dsimp only at hh
  let q := fun t x => clipWeight clip (C.W m t x)
  have hq0 t x : 0 ≤ q t x := (clipWeight_pos hclip (C.pos m hm t x)).le
  obtain ⟨hqc, _, hqb⟩ := chartWeights_clipped_time_coefficient C m hm clip hclip
  have hd0 s : 0 ≤ rawWeightedGradientEnergy (r / L) (q s) (w i s).toFunction.jet :=
    rawWeightedGradientEnergy_nonneg _ _ (hq0 s) _
  have hdi := rawWeightedGradient_time_integrable C m hm clip hclip (r / L) _
    (w i) (hsln.2.1 i)
  have hfi := bounded_raw_factorial_lower_integral_finite (r / L) q hqc clip hclip.le
    hq0 (fun t x => clipWeight_le_bound hclip (C.pos m hm t x))
    (volume.restrict (Icc a b)) (F i) (hF i)
  have hdlim := ofReal_intervalIntegral_nonneg hab _ hdi hd0
  have hflim := ENNReal.ofReal_toReal (ne_of_lt hfi)
  have heq s := storedChartFactorialEnergy_eq_ofReal (E := h i.2) (K := κ i.1 i.2) (r / L) (q s) (hqc s) (hqb s) (hq0 s)
  have hdeq s := storedChartGradientEnergy_eq_ofReal (E := h i.2) (K := κ i.1 i.2) (r / L) (q s) (hqc s) (hqb s) (hq0 s)
  have hfeq s := storedChartFluxEnergy_eq_ofReal (E := h i.2) (K := κ i.1 i.2) (r / L) (q s) (hqc s) (hqb s) (hq0 s)
  intro t ht
  have hh' := retained_factorial_energy_to_ennreal
    (rawWeightedFactorialEnergy_nonneg _ _ (hq0 t) (u i t).toFunction.jet)
    (intervalIntegral.integral_nonneg_of_ae_restrict hab (Filter.Eventually.of_forall hd0))
    (rawWeightedFactorialEnergy_nonneg _ _ (hq0 a) (f i).toFunction.jet)
    ENNReal.toReal_nonneg (hh t ht)
  rw [hdlim, hflim] at hh'
  have hdEq := lintegral_congr (μ := volume.restrict (Icc a b)) (fun s => hdeq s (w i s))
  have hfEq := lintegral_congr (μ := volume.restrict (Icc a b)) (fun s => hfeq s (F i s))
  change storedChartFactorialEnergy (r / L) (q t) (u i t) +
    ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ s in Icc a b, storedChartGradientEnergy (r / L) (q s) (w i s)) ≤
    ENNReal.ofReal (3 * Real.exp (18 * Cw m)) *
      (storedChartFactorialEnergy (r / L) (q a) (f i) +
        16 * ∫⁻ s in Icc a b, storedChartFluxEnergy (r / L) (q s) (F i s))
  rw [heq t (u i t), heq a (f i), hdEq, hfEq]
  exact hh' 

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The real H1 time state and the continuous order-zero trace represent the same solution. -/

def cellEnergyPlaneRealTrace {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) (t : ℝ) :
    PlaneHk Set.univ 0 ℝ :=
  planeL2ZeroCarrier (planeComplexRealPartL2
    ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
      ((cellEnergyTraceAtCLM a b (projIcc a b hab t)).compLp F)))

theorem cellEnergyPlaneRealTrace_alignment {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (show 0 ≤ 1 by omega) (cellEnergyPlaneRealH1State hab F t) =
        cellEnergyPlaneRealTrace hab F t := by
  filter_upwards [cellEnergyPlaneRealH1State_value hab F] with t ht
  apply PlaneHk.ext_value isOpen_univ
  apply univToPlane.injective
  change planeHkValueOperator 0
    (truncatePlaneHk (show 0 ≤ 1 by omega) (cellEnergyPlaneRealH1State hab F t)) =
      planeHkValueOperator 0 (cellEnergyPlaneRealTrace hab F t)
  rw [planeHkValueOperator_truncate, ht]
  exact (planeL2ZeroCarrier_value _).symm

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Stored jets in the response identity agree with the ordered flux expansion. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

def geometryResponseRawFlux (J Ks : ℕ) (K : ι → ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (edge : ConstituentEdges D h)
    (X0 : Vec 2) (δ : ℝ)
    (U : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u + 1) (h u))
    (j : Fin (J + 1)) (v : ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ i' : Fin (J + 1) × ι, ∑ d : admissibleOrders (fun p => K p.2) D (j, v) i',
    planeChainCoefficient (geometryResponseData J Ks G 0 edge X0 δ) (fun _ v => K v)
      (j, v) i' d t z
      (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
        (U i'.1 i'.2).toFunction.jet
          ⟨⟨d.1 - 1, by
            have hd := (Finset.mem_filter.mp d.2).2
            dsimp only at hd
            omega⟩, word⟩ z))

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem geometryResponseRawFlux_eq_ordered (J Ks : ℕ) (K : ι → ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (edge : ConstituentEdges D h)
    (X0 : Vec 2) (δ : ℝ)
    (U : ∀ (_ : Fin (J + 1)) u, PlaneHk Set.univ (K u + 1) (h u))
    (j : Fin (J + 1)) (v : ι) (t : ℝ) (z : Vec 2) :
    geometryResponseRawFlux J Ks K G edge X0 δ U j v t z =
      geometryResponseOrderedFlux J Ks K G edge X0 δ U j v t z := by
  classical
  unfold geometryResponseRawFlux geometryResponseOrderedFlux admissibleOrders
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j' _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  congr 2
  funext word
  have hd := (Finset.mem_filter.mp d.2).2
  change K v + d.1 ≤ K u + 2 at hd
  exact (congrFun (planeJetOrder_eq_stored (show d.1 - 1 ≤ K u + 1 by omega)
    (U j' u) word) z).symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Each original nonzero sampled constituent produces a genuine native forcing with its molecular price. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem originalSource_with_native_remainder_exists (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hdesc : F.IsDescending K) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b₀) (hmeas : F.IsTimeMeasurable)
    (hb₀ : ∀ v u, 0 ≤ b₀ v u) (hrow : ∀ v, ∑ u, b₀ v u ≤ 1) (hcol : ∀ u, ∑ v, b₀ v u ≤ 1)
    (p : P) (c : Ctx p)
    (s a b ϖ : ℝ) (hs : s ≠ 0) (hϖ : 0 < ϖ) (X0 φ : Vec 2)
    (hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
    (U : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (hU : ∀ u, MemLp (U u) 2 (volume.restrict (Set.Icc a b)))
    (R : ∀ v, ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (hR : ∀ v, MemLp (R v) 2 (volume.restrict (Set.Icc a b)))
    (Rval : ∀ v, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (hRv : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (R v t) =ᵐ[volume] Rval v t) :
    ∃ V : ∀ v, ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => h v)),
      (∀ v, MemLp (V v) 2 (volume.restrict (Set.Icc a b))) ∧
      (∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V v t) =ᵐ[volume]
        (fun z => (∑ u, ∑ α : OriginalSourceIndex F v u,
          F.flux p c v u α.1 α.2.1.1 α.2.2.1 (s * t) (X0 + (e / E) • z) (z + φ) α.2.2.2 •
            Weighted.fluxCoordinateInjection α.2.2.2 (F.identity v u α.1).map
              (planeJetOrder (U u t) (α.2.1.1 - 1) α.2.2.1 z)) + Rval v t z)) ∧
      (∀ n v, ENNReal.ofReal ((π v)⁻¹) *
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (V v t)) ≤
        2 * (ENNReal.ofReal (originalSourceGraphConstant Kmax (C 0)) *
          ∑ u, ENNReal.ofReal ((Real.sqrt (π u / π v) *
            (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α)) * (π u)⁻¹) *
            (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ 0 (ρ / e) (K u) (U u t))) +
        2 * (ENNReal.ofReal ((π v)⁻¹) *
          ∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (R v t))) := by
  classical
  obtain ⟨Vs, hVs, hVsv, hVsd⟩ := originalFamily_native_flux_normalized_rows_exists F π hπ K Kmax hK hdesc dom
    ν e E ρ hν he hE hρ C J b₀ henv hmeas hb₀ hrow hcol p c s a b ϖ hs hϖ X0 φ hwindow U hU
  refine ⟨fun v t => Vs v t + R v t, fun v => nativeTime_add_memLp _ (Vs v) (R v) (hVs v) (hR v), ?_, ?_⟩
  · intro v
    filter_upwards [hVsv v, hRv v] with t hst hrt
    filter_upwards [planeValue_add_ae (Vs v t) (R v t), hst, hrt] with z hz hs' hr'
    rw [hz, hs', hr']
  · intro n v
    let price := fun u => (Real.sqrt (π u / π v) *
      (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α)) * (π u)⁻¹
    have hp (u : ι) : 0 ≤ price u := by
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun α _ =>
        originalSourcePrice_nonneg F K Kmax dom ν e E ρ hν.le hρ.le v u α))) (inv_nonneg.mpr (hπ u).le)
    have hsb := nativeFlux_row_time_moment_budget K n 0 ϖ (ρ / e) ((π v)⁻¹)
      (originalSourceGraphConstant Kmax (C 0)) (inv_nonneg.mpr (hπ v).le)
      (originalSourceGraphConstant_nonneg Kmax (C 0)) price hp (volume.restrict (Set.Icc a b))
      (Vs v) U hU (by simpa only [pow_zero, one_pow, one_mul, mul_one, price, mul_assoc] using hVsd v)
    have hab := integrated_weightedFactorialNormSq_add_le n ϖ 0 (ρ / e)
      (volume.restrict (Set.Icc a b)) (Vs v) (R v) (hVs v)
    calc
      _ ≤ ENNReal.ofReal ((π v)⁻¹) *
          (2 * ((∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (Vs v t)) +
            ∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (R v t))) :=
        mul_le_mul_right hab _
      _ = 2 * (ENNReal.ofReal ((π v)⁻¹) *
          (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (Vs v t))) +
          2 * (ENNReal.ofReal ((π v)⁻¹) *
            ∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K v) (R v t)) := by ring
      _ ≤ _ := by
        simpa only [Nat.add_zero, price] using add_le_add (mul_le_mul_right hsb 2) le_rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The real plane time state's gradients are the real physical Bloch gradients. -/

theorem cellEnergyPlaneRealH1State_testGradient {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i : Fin 2,
      planeRealH1TestGradient (cellEnergyPlaneRealH1State hab F t) i =
        planeComplexRealPartL2
          (cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F t) i) :=
  cellEnergyPlaneRealH1State_gradient hab F

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite polynomial energy for a given constant-metric scalar component. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem constantMetric_scalar_component_energy_ne_top
    (a b : ℝ) (hab : a ≤ b) (K Kmax n : ℕ) (hK : K ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (strain r : ℝ) (ha : 0 ≤ strain) (hr : 0 < r)
    (hrh : r ≤ 1 / 2) (hsmall : strain * r ^ 2 ≤ 1 / 8)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (tw S ϖ : ℝ) (zc : Vec 2) (Cw : ℕ → ℝ)
    (W : ChartWeights (fun t _ => G t) v tw S ϖ zc n Cw)
    (hwa : tw ≤ a) (hwb : b ≤ tw + S)
    (f : PlaneHk Set.univ K E)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (u : ℝ → PlaneHk Set.univ K E) (w : ℝ → PlaneHk Set.univ (K + 1) E)
    (hsol : IsPlaneChainFrom (h := fun _ : Unit => E)
      (geometryScalarData 2 (fun t _ => G t)) (fun _ _ => K) a b v
      (fun _ _ => f) (fun _ _ => F) (fun _ _ => u) (fun _ _ => w))
    (hf : weightedFactorialNormSq n ϖ zc r K f ≠ ⊤)
    (hFe : (∫⁻ t in Icc a b, weightedFactorialNormSq n ϖ zc r K (F t)) ≠ ⊤) :
    ((⨆ t ∈ Icc a b, weightedFactorialNormSq n ϖ zc r K (u t)) +
      (∫⁻ t in Icc a b, weightedGradFactorialNormSq n ϖ zc r K (w t))) ≠ ⊤ := by
  obtain ⟨Mv, hMv⟩ := hv.2.1
  have hbv : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ |Mv| := by
    intro t _ x
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg Mv)).mpr
    intro k
    simpa only [Real.norm_eq_abs] using CycleEvolution.cellDrift_entry_bound hMv t x k
  have hmmap : Measurable (fun p : Icc a b × Vec 2 => ((p.1 : ℝ), p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  obtain ⟨L, hL, hreserve⟩ := exists_half_radius_reserve (Real.exp (18 * Cw n))
    (Real.exp_pos _).le
  exact constantMetric_scalarChain_polynomial_energy_ne_top
    (h := fun _ : Unit => E) a b hab (fun _ _ => K) Kmax (fun _ => hK)
    v (hv.1.comp hmmap) (fun t _ => hvs t) |Mv| strain 1 1 (abs_nonneg _) ha
    (by norm_num) (by norm_num) hbv
    (fun t _ l hl hlK x => by simpa only [one_pow, one_zpow, mul_one] using hjets l hl hlK t x)
    (fun t _ => G t) (hG.1.comp hmmap) (fun _ _ _ _ _ => contDiff_const)
    (fun _ _ => 2) (fun _ t _ l x k j => constantCellMetric_spatial_jet_bound G hG t l x k j)
    hG (fun _ _ => rfl) (fun t _ x => hG.2.2.1 t x)
    (fun _ => f) (fun _ => F) (fun _ => hF) (fun _ => u) (fun _ => w) hsol (0, ())
    (fun _ _ _ _ => contDiff_const) tw S ϖ zc n n Cw W le_rfl r L hr hL
    (by simpa only [one_mul, div_one] using hrh)
    (by simpa only [mul_one] using hsmall) hreserve
    (fun t _ => cellDrift_classical_divergence_zero hv hvs t) hwa hwb hf hFe

end AVRegularity.CycleWords
end
