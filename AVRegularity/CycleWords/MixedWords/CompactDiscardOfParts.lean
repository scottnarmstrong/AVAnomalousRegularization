-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.Assembly.MixedWordsB1Transfer
import AVRegularity.CycleWords.Assembly.SeamNorms
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.CycleWords.Assembly.MixedWordsB1Statements
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Limits of jet and moment norms

The weighted jet norm is lower semicontinuous under pointwise convergence of the jets (Fatou in
each `L²` norm, then a monotone continuous combination of finitely many norms), and the moment norm
of an approximating sequence converges to the moment norm of the limit. -/

section
/-- A monotone continuous function of doubly indexed families commutes with `liminf` from
below. -/
theorem map_liminf_le_liminf {X Y : Type*} (Φ : (X → Y → ℝ≥0∞) → ℝ≥0∞) (hmono : Monotone Φ)
    (hcont : Continuous Φ) (y : ℕ → X → Y → ℝ≥0∞) :
    Φ (fun b c => liminf (fun k => y k b c) atTop) ≤ liminf (fun k => Φ (y k)) atTop := by
  set z : ℕ → X → Y → ℝ≥0∞ := fun N b c => ⨅ k ∈ Set.Ici N, y k b c with hz
  have hzmono : Monotone z := fun N N' hN b c =>
    biInf_mono fun k hk => le_trans hN (Set.mem_Ici.1 hk)
  have hzlim : Tendsto z atTop (𝓝 fun b c => liminf (fun k => y k b c) atTop) := by
    rw [tendsto_pi_nhds]
    intro b
    rw [tendsto_pi_nhds]
    intro c
    have hb : liminf (fun k => y k b c) atTop = ⨆ N, z N b c := by
      rw [liminf_eq_iSup_iInf_of_nat]
      rfl
    rw [hb]
    exact tendsto_atTop_iSup fun N N' hN => hzmono hN b c
  have hle : ∀ N, Φ (z N) ≤ liminf (fun k => Φ (y k)) atTop := by
    intro N
    rw [liminf_eq_iSup_iInf_of_nat]
    refine le_trans ?_ (le_iSup _ N)
    refine le_iInf₂ fun k hk => hmono fun b c => ?_
    exact iInf₂_le k (Set.mem_Ici.2 hk)
  exact le_of_tendsto' ((hcont.tendsto _).comp hzlim) hle

section Jets

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]

/-- The combination of the component norms that defines `weightedJetNorm`. -/
noncomputable def jetNormCombination (π : ι → ℝ) (j : ℕ) (r : ℝ) (N : ι → ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ a ∈ Finset.range (j + 1), ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
    (∑ v, ENNReal.ofReal ((π v)⁻¹) * N v a ^ 2) ^ (1 / 2 : ℝ)

theorem jetNormCombination_monotone (π : ι → ℝ) (j : ℕ) (r : ℝ) :
    Monotone (jetNormCombination π j r) := by
  intro N N' hN
  unfold jetNormCombination
  gcongr with a _ v
  exact hN v a

theorem jetNormCombination_continuous (π : ι → ℝ) (j : ℕ) (r : ℝ) :
    Continuous (jetNormCombination π j r) := by
  unfold jetNormCombination
  refine continuous_finsetSum _ fun a _ => ?_
  refine (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp ?_
  refine ENNReal.continuous_rpow_const.comp ?_
  refine continuous_finsetSum _ fun v _ => ?_
  refine (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp ?_
  exact (ENNReal.continuous_pow 2).comp ((continuous_apply a).comp (continuous_apply v))

/-- **Lower semicontinuity of the weighted jet norm** under pointwise convergence of measurable
jets. -/
theorem weightedJetNorm_le_liminf (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ)
    (J : ℕ → ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (Jlim : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (hJ : ∀ k v a w, AEStronglyMeasurable (J k v a w) volume)
    (hJlim : ∀ v a w, AEStronglyMeasurable (Jlim v a w) volume)
    (hlim : ∀ v a w z, Tendsto (fun k => J k v a w z) atTop (𝓝 (Jlim v a w z))) :
    weightedJetNorm π p j s r Jlim ≤ liminf (fun k => weightedJetNorm π p j s r (J k)) atTop := by
  let N : ℕ → ι → ℕ → ℝ≥0∞ := fun k v a =>
    eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
      Real.sqrt (∑ w : DerivativeWord2 a, ‖J k v a w z‖ ^ 2)) 2 volume
  let Nlim : ι → ℕ → ℝ≥0∞ := fun v a =>
    eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
      Real.sqrt (∑ w : DerivativeWord2 a, ‖Jlim v a w z‖ ^ 2)) 2 volume
  have hfatou : ∀ v a, Nlim v a ≤ liminf (fun k => N k v a) atTop := by
    intro v a
    refine Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun k => weighted_word_norm_aestronglyMeasurable s p _ (hJ k v a))
      _ (weighted_word_norm_aestronglyMeasurable s p _ (hJlim v a)) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    refine tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp ?_)
    refine tendsto_finsetSum _ fun w _ => ?_
    exact ((hlim v a w z).norm).pow 2
  have h1 : weightedJetNorm π p j s r Jlim = jetNormCombination π j r Nlim := rfl
  have h2 : ∀ k, weightedJetNorm π p j s r (J k) = jetNormCombination π j r (N k) := fun _ => rfl
  rw [h1]
  simp only [h2]
  exact le_trans (jetNormCombination_monotone π j r fun v a => hfatou v a)
    (map_liminf_le_liminf _ (jetNormCombination_monotone π j r)
      (jetNormCombination_continuous π j r) N)

end Jets

section Moments

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem momentNorm_sub_comm (π : ι → ℝ) (n : ℕ) (s : ℝ) (F G : ∀ v, Vec 2 → h v) :
    momentNorm π n s (fun v z => F v z - G v z) = momentNorm π n s (fun v z => G v z - F v z) := by
  have key : ∀ (β : ℕ × ℕ) v, eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) •
      (F v z - G v z)) 2 volume = eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) •
      (G v z - F v z)) 2 volume := by
    intro β v
    conv_lhs => rw [← eLpNorm_neg]
    congr 1
    funext z
    simp only [Pi.neg_apply, smul_sub, neg_sub]
  simp only [momentNorm, key]

/-- Moment norms converge along a sequence converging in that moment norm. -/
theorem momentNorm_tendsto (π : ι → ℝ) (n : ℕ) (s : ℝ) (F : ∀ v, Vec 2 → h v)
    (φ : ℕ → ∀ v, Vec 2 → h v) (hF : momentNorm π n s F < ⊤)
    (hφ : Tendsto (fun k => momentNorm π n s (fun v z => F v z - φ k v z)) atTop (𝓝 0)) :
    Tendsto (fun k => momentNorm π n s (φ k)) atTop (𝓝 (momentNorm π n s F)) := by
  have hup : ∀ k, momentNorm π n s (φ k) ≤
      momentNorm π n s F + momentNorm π n s (fun v z => F v z - φ k v z) := by
    intro k
    rw [momentNorm_sub_comm]
    have he : φ k = fun v z => F v z + (φ k v z - F v z) := by
      funext v z
      abel
    conv_lhs => rw [he]
    exact momentNorm_add_le π n s F _
  have hlo : ∀ k, momentNorm π n s F ≤
      momentNorm π n s (φ k) + momentNorm π n s (fun v z => F v z - φ k v z) := by
    intro k
    have he : F = fun v z => φ k v z + (F v z - φ k v z) := by
      funext v z
      abel
    conv_lhs => rw [he]
    exact momentNorm_add_le π n s _ _
  rw [ENNReal.tendsto_nhds hF.ne]
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hφ) ε hε] with k hk
  refine ⟨?_, (hup k).trans (by gcongr)⟩
  rw [tsub_le_iff_right]
  exact (hlo k).trans (by gcongr)

end Moments
end

/-! # Derivatives of a retained map are controlled by the moment norm

Every amplitude pair can be replaced by an even/odd one. With band-limited calculus
(`AmplitudePlancherelStatement`) and the `bounded` field of a retained map, every ordered derivative
of `R G` is bounded pointwise by a constant times the moment norm of order `∑K_i` of `G`; along a
sequence converging in that norm the derivatives converge at every point. -/

section
section Symmetrize

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vecDot_neg_neg (θ : Vec 2) : vecDot (-θ) (-θ) = vecDot θ θ := by
  simp only [vecDot, Pi.neg_apply, neg_mul_neg]

/-- The closed ball of the amplitudes is symmetric. -/
theorem neg_preimage_amplitudeBall (r : ℝ) :
    Neg.neg ⁻¹' {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} = {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} := by
  ext θ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, vecDot_neg_neg]

theorem amplitudeBall_measurable (r : ℝ) : MeasurableSet {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} :=
  measurableSet_le (by unfold vecDot; fun_prop) measurable_const

/-- A set integral over the amplitude ball is invariant under `θ ↦ -θ`. -/
theorem setIntegral_amplitudeBall_neg (r : ℝ) (F : Vec 2 → E) :
    ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, F (-θ) =
      ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, F θ := by
  have hS := amplitudeBall_measurable r
  rw [← integral_indicator hS, ← integral_indicator hS]
  have hind : (Set.indicator {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} fun θ => F (-θ)) =
      fun θ => Set.indicator {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} F (-θ) := by
    funext θ
    simp only [Set.indicator, Set.mem_ofPred_eq, vecDot_neg_neg]
  rw [hind]
  exact integral_neg_eq_self _ volume

omit [NormedSpace ℝ E] in
theorem integrableOn_amplitudeBall_neg {r : ℝ} {A : Vec 2 → E}
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) :
    IntegrableOn (fun θ => A (-θ)) {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} := by
  have hmp := Measure.measurePreserving_neg (volume : Measure (Vec 2))
  have := (hmp.integrableOn_comp_preimage measurableEmbedding_neg
    (s := {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (f := A)).2 hA
  rwa [neg_preimage_amplitudeBall] at this

/-- The even/odd part of an amplitude pair represents the same function. -/
theorem IsRetainedAmplitude.symmetrize {g : Vec 2 → E} {r : ℝ} {A B : Vec 2 → E}
    (hA : IsRetainedAmplitude g r A B) :
    IsRetainedAmplitude g r (fun θ => (1 / 2 : ℝ) • (A θ + A (-θ)))
      (fun θ => (1 / 2 : ℝ) • (B θ - B (-θ))) := by
  obtain ⟨hvan, hAi, hBi, hrep⟩ := hA
  have hAn := integrableOn_amplitudeBall_neg hAi
  have hBn := integrableOn_amplitudeBall_neg hBi
  refine ⟨fun θ hθ => ?_, (hAi.add hAn).smul _, (hBi.sub hBn).smul _, fun z => ?_⟩
  · have h1 := hvan θ hθ
    have h2 := hvan (-θ) (by rwa [vecDot_neg_neg])
    simp only [h1.1, h2.1, h1.2, h2.2, add_zero, sub_zero, smul_zero, and_self]
  · have hc : Continuous fun θ : Vec 2 => Real.cos (vecDot θ z) := by unfold vecDot; fun_prop
    have hs : Continuous fun θ : Vec 2 => Real.sin (vecDot θ z) := by unfold vecDot; fun_prop
    have hbdd : ∀ {f : Vec 2 → ℝ}, Continuous f → (∀ θ, |f θ| ≤ 1) →
        MemLp f ⊤ (volume.restrict {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) := fun hf h1 =>
      memLp_top_of_bound hf.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun θ => by simpa [Real.norm_eq_abs] using h1 θ)
    set F : Vec 2 → E := fun θ => Real.cos (vecDot θ z) • A θ + Real.sin (vecDot θ z) • B θ
      with hFdef
    have hF : IntegrableOn F {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} :=
      (hAi.smul_of_top_right (hbdd hc fun θ => Real.abs_cos_le_one _)).add
        (hBi.smul_of_top_right (hbdd hs fun θ => Real.abs_sin_le_one _))
    have hFn : IntegrableOn (fun θ => F (-θ)) {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} :=
      integrableOn_amplitudeBall_neg hF
    have hneg : ∀ θ : Vec 2, vecDot (-θ) z = -vecDot θ z := fun θ => by
      simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    have hpt : (fun θ => Real.cos (vecDot θ z) • ((1 / 2 : ℝ) • (A θ + A (-θ))) +
        Real.sin (vecDot θ z) • ((1 / 2 : ℝ) • (B θ - B (-θ)))) =
        fun θ => (1 / 2 : ℝ) • F θ + (1 / 2 : ℝ) • F (-θ) := by
      funext θ
      simp only [hFdef, hneg, Real.cos_neg, Real.sin_neg]
      module
    rw [hpt, integral_add (f := fun θ => (1 / 2 : ℝ) • F θ)
      (g := fun θ => (1 / 2 : ℝ) • F (-θ)) (hF.smul _) (hFn.smul _), integral_smul, integral_smul,
      setIntegral_amplitudeBall_neg r F, ← add_smul, ← hrep z]
    norm_num

end Symmetrize

universe u v

section Retained

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

omit [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The moment norm of order `0` controls each component in `L²`. -/
theorem eLpNorm_le_momentNorm_zero [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ)
    (F : ∀ v, Vec 2 → h v) (x : ι) (hπx : 0 < π x) :
    eLpNorm (F x) 2 volume ≤ ENNReal.ofReal (Real.sqrt (π x)) * momentNorm π 0 1 F := by
  have hidx : momentIndices 0 = {(0, 0)} := by decide
  have hm : momentNorm π 0 1 F =
      (∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (F v) 2 volume ^ 2) ^ (1 / 2 : ℝ) := by
    simp [momentNorm, hidx]
  rw [hm]
  set T := ∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (F v) 2 volume ^ 2 with hT
  have hx : ENNReal.ofReal ((π x)⁻¹) * eLpNorm (F x) 2 volume ^ 2 ≤ T :=
    Finset.single_le_sum (f := fun v => ENNReal.ofReal ((π v)⁻¹) * eLpNorm (F v) 2 volume ^ 2)
      (fun v _ => zero_le) (Finset.mem_univ x)
  have hsq : eLpNorm (F x) 2 volume ^ 2 ≤ ENNReal.ofReal (π x) * T := by
    calc eLpNorm (F x) 2 volume ^ 2
        = ENNReal.ofReal (π x) * (ENNReal.ofReal ((π x)⁻¹) * eLpNorm (F x) 2 volume ^ 2) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hπx.le, mul_inv_cancel₀ hπx.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (π x) * T := by gcongr
  calc eLpNorm (F x) 2 volume = (eLpNorm (F x) 2 volume ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ (ENNReal.ofReal (π x) * T) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (π x)) * T ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hπx.le (by norm_num), Real.sqrt_eq_rpow]

/-- The amplitude ball has finite volume. -/
theorem amplitudeBall_volume_lt_top (r : ℝ) : volume {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} < ⊤ := by
  refine (measure_mono ?_).trans_lt (measure_closedBall_lt_top (x := (0 : Vec 2)) (r := |r|))
  intro θ hθ
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (abs_nonneg r)]
  intro i
  have hi : θ i * θ i ≤ vecDot θ θ :=
    Finset.single_le_sum (f := fun j => θ j * θ j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  exact sq_le_sq.mp (by nlinarith [hθ.out])

/-- **Pointwise bound of the derivatives of a retained map** by the moment norm of order `∑K_i`
(band-limited calculus, Hölder on the amplitude ball, Plancherel, and the `bounded` field). -/
theorem retainedMap_orderedDerivative_le (hB0 : AmplitudePlancherelStatement.{v})
    {K : ScalarConstants} {χlo : Vec 2 → ℝ} {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D}
    {η S ηg t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {X₀ : Vec 2}
    {R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)}
    (hR : IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R)
    (hr : 0 < 2 * K.ξlo * Real.sqrt η) (hπ : ∀ x, 0 < π x) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (F x) volume) →
      ∀ x (a : ℕ) (wd : DerivativeWord2 a) (z : Vec 2),
        ENNReal.ofReal ‖orderedDerivative wd (R F x) z‖ ≤
          ENNReal.ofReal (C * (2 * K.ξlo * Real.sqrt η) ^ a) *
            momentNorm π (wordReserveN 0 fun i => (letters i).slow) ϖ F := by
  obtain ⟨Cb, hCb, hbd⟩ := hR.bounded
  set r := 2 * K.ξlo * Real.sqrt η with hrdef
  set Sb := {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} with hSb
  have hvol := amplitudeBall_volume_lt_top r
  set V := (volume Sb).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set Pi := ∑ x, Real.sqrt (π x) with hPi
  have hPi0 : 0 ≤ Pi := Finset.sum_nonneg fun x _ => Real.sqrt_nonneg _
  refine ⟨Cb * 2 * Real.sqrt V * (2 * Real.pi)⁻¹ * Pi + 1, by positivity, ?_⟩
  intro F hF x a wd z
  set n0 := wordReserveN 0 fun i => (letters i).slow
  by_cases hfin : momentNorm π n0 ϖ F = ⊤
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top
  obtain ⟨A, B, hAB⟩ := (hR.band F x).2
  have hsym := IsRetainedAmplitude.symmetrize (g := R F x) (r := r) hAB
  set A' : Vec 2 → h x := fun θ => (1 / 2 : ℝ) • (A θ + A (-θ)) with hA'
  set B' : Vec 2 → h x := fun θ => (1 / 2 : ℝ) • (B θ - B (-θ)) with hB'
  have hB0x := hB0 r (R F x) A' B' hr hsym
  have hpar : ∀ θ, A' (-θ) = A' θ ∧ B' (-θ) = -B' θ := fun θ => by
    simp only [hA', hB', neg_neg]
    constructor
    · rw [add_comm]
    · rw [← smul_neg, neg_sub]
  have hL2 : eLpNorm (R F x) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (π x)) * (ENNReal.ofReal Cb * momentNorm π n0 ϖ F) :=
    (eLpNorm_le_momentNorm_zero π (R F) x (hπ x)).trans (by gcongr; exact hbd F hF)
  have hfinL2 : eLpNorm (R F x) 2 volume < ⊤ :=
    lt_of_le_of_lt hL2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfin)))
  have hmem : MemLp (R F x) 2 volume := hfinL2
  obtain ⟨hiff, heq⟩ := hB0x.2.2 hpar
  obtain ⟨hAm, hBm⟩ := hiff.1 hmem
  have heq' := heq hmem
  have hderiv := hB0x.2.1 a wd z
  -- the `L¹` norms of the amplitudes on the ball
  have hL1 : ∀ {C : Vec 2 → h x}, IntegrableOn C Sb → MemLp C 2 volume →
      ENNReal.ofReal (∫ θ in Sb, ‖C θ‖) ≤ eLpNorm C 2 volume * ENNReal.ofReal (Real.sqrt V) := by
    intro C hCi hCm
    have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
    have hmeas : (volume.restrict Sb) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal -
        1 / (2 : ℝ≥0∞).toReal) = ENNReal.ofReal (Real.sqrt V) := by
      rw [Measure.restrict_apply_univ, hexp, hV, Real.sqrt_eq_rpow,
        ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
        ENNReal.ofReal_toReal hvol.ne]
    rw [ofReal_integral_norm_eq_lintegral_enorm hCi,
      ← eLpNorm_one_eq_lintegral_enorm hCi.aestronglyMeasurable]
    calc eLpNorm C 1 (volume.restrict Sb)
        ≤ eLpNorm C 2 (volume.restrict Sb) * (volume.restrict Sb) Set.univ ^
            (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hCi.aestronglyMeasurable
      _ ≤ eLpNorm C 2 volume * ENNReal.ofReal (Real.sqrt V) := by
          rw [hmeas]
          gcongr
          exact Measure.restrict_le_self
  have hsumsq : eLpNorm A' 2 volume + eLpNorm B' 2 volume ≤
      2 * (eLpNorm A' 2 volume ^ 2 + eLpNorm B' 2 volume ^ 2) ^ (1 / 2 : ℝ) := by
    have h1 : ∀ e e' : ℝ≥0∞, e ≤ (e ^ 2 + e' ^ 2) ^ (1 / 2 : ℝ) := fun e e' => by
      calc e = (e ^ 2) ^ (1 / 2 : ℝ) := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            norm_num
        _ ≤ (e ^ 2 + e' ^ 2) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow le_self_add (by norm_num)
    rw [two_mul]
    refine add_le_add (h1 _ _) ?_
    rw [add_comm (eLpNorm A' 2 volume ^ 2)]
    exact h1 _ _
  have hamp : (eLpNorm A' 2 volume ^ 2 + eLpNorm B' 2 volume ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (2 * Real.pi)⁻¹ * eLpNorm (R F x) 2 volume := by
    rw [heq', ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
      ENNReal.ofReal_one, one_mul]
  have hIA := hL1 hsym.2.1 hAm
  have hIB := hL1 hsym.2.2.1 hBm
  calc ENNReal.ofReal ‖orderedDerivative wd (R F x) z‖
      ≤ ENNReal.ofReal (r ^ a) * (ENNReal.ofReal (∫ θ in Sb, ‖A' θ‖) +
          ENNReal.ofReal (∫ θ in Sb, ‖B' θ‖)) := by
        rw [← ENNReal.ofReal_add (integral_nonneg fun _ => norm_nonneg _)
          (integral_nonneg fun _ => norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hderiv
    _ ≤ ENNReal.ofReal (r ^ a) * ((eLpNorm A' 2 volume + eLpNorm B' 2 volume) *
          ENNReal.ofReal (Real.sqrt V)) := by
        rw [add_mul]
        gcongr
    _ ≤ ENNReal.ofReal (r ^ a) * (2 * (ENNReal.ofReal (2 * Real.pi)⁻¹ *
          (ENNReal.ofReal (Real.sqrt (π x)) * (ENNReal.ofReal Cb * momentNorm π n0 ϖ F))) *
          ENNReal.ofReal (Real.sqrt V)) := by
        gcongr
        refine hsumsq.trans ?_
        rw [hamp]
        gcongr
    _ ≤ ENNReal.ofReal ((Cb * 2 * Real.sqrt V * (2 * Real.pi)⁻¹ * Pi + 1) * r ^ a) *
          momentNorm π n0 ϖ F := by
        have hsq : Real.sqrt (π x) ≤ Pi :=
          Finset.single_le_sum (f := fun x => Real.sqrt (π x))
            (fun x _ => Real.sqrt_nonneg _) (Finset.mem_univ x)
        have hra : 0 ≤ r ^ a := by positivity
        calc ENNReal.ofReal (r ^ a) * (2 * (ENNReal.ofReal (2 * Real.pi)⁻¹ *
              (ENNReal.ofReal (Real.sqrt (π x)) * (ENNReal.ofReal Cb * momentNorm π n0 ϖ F))) *
              ENNReal.ofReal (Real.sqrt V))
            = ENNReal.ofReal (Cb * 2 * Real.sqrt V * (2 * Real.pi)⁻¹ * Real.sqrt (π x) * r ^ a) *
                momentNorm π n0 ϖ F := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
              ring
          _ ≤ _ := by
              gcongr
              nlinarith [mul_le_mul_of_nonneg_left hsq
                (by positivity : (0 : ℝ) ≤ Cb * 2 * Real.sqrt V * (2 * Real.pi)⁻¹)]

/-- Along a sequence converging in the moment norm of order `∑K_i`, every ordered derivative of the
retained map converges at every point. -/
theorem retainedMap_orderedDerivative_tendsto (hB0 : AmplitudePlancherelStatement.{v})
    {K : ScalarConstants} {χlo : Vec 2 → ℝ} {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D}
    {η S ηg t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {X₀ : Vec 2}
    {R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)}
    (hR : IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R)
    (hr : 0 < 2 * K.ξlo * Real.sqrt η) (hπ : ∀ x, 0 < π x) (F : ∀ x, Vec 2 → h x)
    (φ : ℕ → ∀ x, Vec 2 → h x) (hF : ∀ x, AEStronglyMeasurable (F x) volume)
    (hφ : ∀ k x, AEStronglyMeasurable (φ k x) volume)
    (hlim : Tendsto (fun k => momentNorm π (wordReserveN 0 fun i => (letters i).slow) ϖ
      (fun x z => F x z - φ k x z)) atTop (𝓝 0)) (x : ι) (a : ℕ) (wd : DerivativeWord2 a)
    (z : Vec 2) :
    Tendsto (fun k => orderedDerivative wd (R (φ k) x) z) atTop
      (𝓝 (orderedDerivative wd (R F x) z)) := by
  obtain ⟨C, hC, hbound⟩ := retainedMap_orderedDerivative_le hB0 hR hr hπ
  have hdiff : ∀ k, orderedDerivative wd (R F x) z - orderedDerivative wd (R (φ k) x) z =
      orderedDerivative wd (R (fun x z => F x z - φ k x z) x) z := by
    intro k
    have hsub : R (fun x z => F x z - φ k x z) = R F - R (φ k) := by
      rw [← map_sub]
      rfl
    rw [hsub]
    exact (congrFun (orderedDerivative_sub wd ((hR.band F x).1 a) ((hR.band (φ k) x).1 a)) z).symm
  have hmeas : ∀ k x, AEStronglyMeasurable (fun z => F x z - φ k x z) volume :=
    fun k x => (hF x).sub (hφ k x)
  have hE : Tendsto (fun k => ENNReal.ofReal
      ‖orderedDerivative wd (R F x) z - orderedDerivative wd (R (φ k) x) z‖) atTop (𝓝 0) := by
    have hc := ENNReal.Tendsto.const_mul hlim
      (Or.inr (ENNReal.ofReal_ne_top (r := C * (2 * K.ξlo * Real.sqrt η) ^ a)))
    rw [mul_zero] at hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun k => zero_le) fun k => ?_
    rw [hdiff k]
    exact hbound _ (hmeas k) x a wd z
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hR' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
  simp only [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_zero] at hR'
  refine hR'.congr fun k => ?_
  rw [norm_sub_rev]

end Retained
end

/-! # The molecular output norm: triangle inequality, a.e. congruence, Fatou

`jetOutputNorm` is subadditive in the jet array (`jetOutputNorm_add_le`, Minkowski in the words,
the cell `L²` norms and the components), depends only on the jets of order `≤ K` up to null sets
(`jetOutputNorm_congr_ae`), and is lower semicontinuous under pointwise convergence of measurable
jets (`jetOutputNorm_le_liminf`, Fatou in each `L²` norm and a monotone continuous combination). -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]

/-- The moment and scale weight of `jetOutputNorm`. -/
def outputWeight (s r : ℝ) (β : ℕ × ℕ) (a : ℕ) (z : Vec 2) : ℝ :=
  (s * z 0) ^ β.1 * (s * z 1) ^ β.2 * r ^ a

theorem outputWeight_continuous (s r : ℝ) (β : ℕ × ℕ) (a : ℕ) :
    Continuous (outputWeight s r β a) := by
  unfold outputWeight
  fun_prop

/-- The combination of the component norms that defines `jetOutputNorm`. -/
noncomputable def outputCombination (π : ι → ℝ) (m K : ℕ)
    (N : ι → (ℕ × ℕ) × ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ β ∈ momentIndices m, ∑ a ∈ Finset.range (K + 1),
    ENNReal.ofReal ((((β.1.factorial * β.2.factorial * a.factorial : ℕ)) : ℝ)⁻¹) *
      (∑ v, ENNReal.ofReal ((π v)⁻¹) * N v (β, a) ^ 2) ^ (1 / 2 : ℝ)

theorem jetOutputNorm_eq_combination (π : ι → ℝ) (m K : ℕ) (s r : ℝ)
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) :
    jetOutputNorm π m K s r J = outputCombination π m K (fun v βa =>
      eLpNorm (fun z => outputWeight s r βa.1 βa.2 z *
        Real.sqrt (∑ w : DerivativeWord2 βa.2, ‖J v βa.2 w z‖ ^ 2)) 2 volume) := rfl

theorem outputCombination_monotone (π : ι → ℝ) (m K : ℕ) :
    Monotone (outputCombination π m K) := by
  intro N N' hN
  unfold outputCombination
  gcongr with β _ a _ v
  exact hN v (β, a)

theorem outputCombination_continuous (π : ι → ℝ) (m K : ℕ) :
    Continuous (outputCombination π m K) := by
  unfold outputCombination
  refine continuous_finsetSum _ fun β _ => continuous_finsetSum _ fun a _ => ?_
  refine (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp ?_
  refine ENNReal.continuous_rpow_const.comp ?_
  refine continuous_finsetSum _ fun v _ => ?_
  refine (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp ?_
  exact (ENNReal.continuous_pow 2).comp ((continuous_apply (β, a)).comp (continuous_apply v))

theorem output_word_norm_aestronglyMeasurable {a : ℕ} {E : Type*} [NormedAddCommGroup E]
    (s r : ℝ) (β : ℕ × ℕ) (J : DerivativeWord2 a → Vec 2 → E)
    (hJ : ∀ w, AEStronglyMeasurable (J w) volume) :
    AEStronglyMeasurable (fun z => outputWeight s r β a z *
      Real.sqrt (∑ w, ‖J w z‖ ^ 2)) volume := by
  have hsum : AEStronglyMeasurable (fun z => ∑ w, ‖J w z‖ ^ 2) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun w _ => ((hJ w).norm.pow 2)
  exact (outputWeight_continuous s r β a).aestronglyMeasurable.mul
    (Real.continuous_sqrt.comp_aestronglyMeasurable hsum)

/-- **Lower semicontinuity of the molecular output norm** under pointwise convergence of
measurable jets. -/
theorem jetOutputNorm_le_liminf (π : ι → ℝ) (m K : ℕ) (s r : ℝ)
    (J : ℕ → ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (Jlim : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (hJ : ∀ k v a w, AEStronglyMeasurable (J k v a w) volume)
    (hJlim : ∀ v a w, AEStronglyMeasurable (Jlim v a w) volume)
    (hlim : ∀ v a w z, Tendsto (fun k => J k v a w z) atTop (𝓝 (Jlim v a w z))) :
    jetOutputNorm π m K s r Jlim ≤ liminf (fun k => jetOutputNorm π m K s r (J k)) atTop := by
  let N : ℕ → ι → (ℕ × ℕ) × ℕ → ℝ≥0∞ := fun k v βa =>
    eLpNorm (fun z => outputWeight s r βa.1 βa.2 z *
      Real.sqrt (∑ w : DerivativeWord2 βa.2, ‖J k v βa.2 w z‖ ^ 2)) 2 volume
  let Nlim : ι → (ℕ × ℕ) × ℕ → ℝ≥0∞ := fun v βa =>
    eLpNorm (fun z => outputWeight s r βa.1 βa.2 z *
      Real.sqrt (∑ w : DerivativeWord2 βa.2, ‖Jlim v βa.2 w z‖ ^ 2)) 2 volume
  have hfatou : ∀ v βa, Nlim v βa ≤ liminf (fun k => N k v βa) atTop := by
    intro v βa
    refine Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun k => output_word_norm_aestronglyMeasurable s r βa.1 _ (hJ k v βa.2))
      _ (output_word_norm_aestronglyMeasurable s r βa.1 _ (hJlim v βa.2)) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    refine tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp ?_)
    refine tendsto_finsetSum _ fun w _ => ?_
    exact ((hlim v βa.2 w z).norm).pow 2
  rw [jetOutputNorm_eq_combination]
  simp only [jetOutputNorm_eq_combination]
  exact le_trans (outputCombination_monotone π m K fun v βa => hfatou v βa)
    (map_liminf_le_liminf _ (outputCombination_monotone π m K)
      (outputCombination_continuous π m K) N)

/-- Minkowski in the words. -/
theorem sqrt_sum_norm_add_le {W E : Type*} [Fintype W] [NormedAddCommGroup E] (x y : W → E) :
    Real.sqrt (∑ w, ‖x w + y w‖ ^ 2) ≤
      Real.sqrt (∑ w, ‖x w‖ ^ 2) + Real.sqrt (∑ w, ‖y w‖ ^ 2) := by
  have h := norm_add_le (WithLp.toLp 2 x : PiLp 2 (fun _ : W => E)) (WithLp.toLp 2 y)
  rw [← WithLp.toLp_add, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2] at h
  simpa using h

/-- **The triangle inequality of the molecular output norm.** -/
theorem jetOutputNorm_add_le (π : ι → ℝ) (m K : ℕ) (s r : ℝ)
    (J J' : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (hJ : ∀ v a w, AEStronglyMeasurable (J v a w) volume)
    (hJ' : ∀ v a w, AEStronglyMeasurable (J' v a w) volume) :
    jetOutputNorm π m K s r (fun v a w z => J v a w z + J' v a w z) ≤
      jetOutputNorm π m K s r J + jetOutputNorm π m K s r J' := by
  unfold jetOutputNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun β _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_add]
  gcongr
  refine ennreal_weighted_l2_add_le _ _ _ _ fun v => ?_
  set wt : Vec 2 → ℝ := fun z => (s * z 0) ^ β.1 * (s * z 1) ^ β.2 * r ^ a
  have hpt : ∀ z, ‖wt z * Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z + J' v a w z‖ ^ 2)‖ ≤
      ‖wt z * Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2) +
        wt z * Real.sqrt (∑ w : DerivativeWord2 a, ‖J' v a w z‖ ^ 2)‖ := by
    intro z
    rw [← mul_add, norm_mul (wt z), norm_mul (wt z)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (wt z))
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact sqrt_sum_norm_add_le _ _
  have hmeas : AEStronglyMeasurable (fun z => wt z *
      Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z + J' v a w z‖ ^ 2)) volume :=
    output_word_norm_aestronglyMeasurable s r β (fun w z => J v a w z + J' v a w z)
      (fun w => (hJ v a w).add (hJ' v a w))
  refine (eLpNorm_mono hmeas hpt).trans ?_
  exact eLpNorm_add_le (f := fun z => wt z * Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2))
    (g := fun z => wt z * Real.sqrt (∑ w : DerivativeWord2 a, ‖J' v a w z‖ ^ 2)) (by norm_num)

/-- The molecular output norm only sees the jets of order `≤ K`, up to null sets. -/
theorem jetOutputNorm_congr_ae (π : ι → ℝ) (m K : ℕ) (s r : ℝ)
    {J J' : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v}
    (hJ : ∀ v a w, a ≤ K → J v a w =ᵐ[volume] J' v a w) :
    jetOutputNorm π m K s r J = jetOutputNorm π m K s r J' := by
  unfold jetOutputNorm
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun a ha => ?_
  have haK : a ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
  congr 2
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 2
  refine eLpNorm_congr_ae ?_
  filter_upwards [ae_all_iff.2 fun w => hJ v a w haK] with z hz
  simp only [hz]
end

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization Filter AVRegularity.Sobolev
open scoped ENNReal Topology
namespace AVRegularity.CycleWords.Assembly

/-! # Band-limited calculus

`ampFun r A B z = ∫_{|θ| ≤ r} cos(θ·z) A θ + sin(θ·z) B θ`. Differentiating under the integral,
`∂_k ampFun r A B = ampFun r (θ_k B) (-θ_k A)`: the derivatives of a band-limited function are
band-limited with amplitudes multiplied by a coordinate of `θ` (at most `r` on the ball). Hence
`ampFun r A B` is smooth of every order and its ordered derivatives of order `a` are bounded by
`r^a (‖A‖_{L¹} + ‖B‖_{L¹})` (`ampFun_contDiff`, `norm_orderedDerivative_ampFun_le`). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The band-limited function of an amplitude pair on the ball `|θ| ≤ r`. -/
noncomputable def ampFun (r : ℝ) (A B : Vec 2 → E) (z : Vec 2) : E :=
  ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2},
    (Real.cos (vecDot θ z) • A θ + Real.sin (vecDot θ z) • B θ)

/-- The amplitudes of `∂_k`: `(θ_k B, -θ_k A)`. -/
def derivAmpA (k : Fin 2) (B : Vec 2 → E) : Vec 2 → E := fun θ => θ k • B θ

/-- The amplitudes of `∂_k`: `(θ_k B, -θ_k A)`. -/
def derivAmpB (k : Fin 2) (A : Vec 2 → E) : Vec 2 → E := fun θ => -(θ k • A θ)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
theorem abs_coord_le_of_mem_ampBall {r : ℝ} (hr : 0 ≤ r) {θ : Vec 2}
    (hθ : θ ∈ {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (k : Fin 2) : |θ k| ≤ r := by
  have hk : θ k * θ k ≤ vecDot θ θ :=
    Finset.single_le_sum (f := fun j => θ j * θ j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ k)
  have h := sq_le_sq.mp (by nlinarith [hθ.out] : θ k ^ 2 ≤ r ^ 2)
  rwa [abs_of_nonneg hr] at h

omit [CompleteSpace E] in
theorem integrableOn_coord_smul {r : ℝ} (hr : 0 ≤ r) {B : Vec 2 → E}
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (k : Fin 2) :
    IntegrableOn (fun θ => θ k • B θ) {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} := by
  refine Integrable.mono' (hB.norm.const_mul r)
    ((continuous_apply k).aestronglyMeasurable.smul hB.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (amplitudeBall_measurable r)] with θ hθ
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_coord_le_of_mem_ampBall hr hθ k) (norm_nonneg _)

omit [CompleteSpace E] in
theorem integrableOn_derivAmpA {r : ℝ} (hr : 0 ≤ r) {B : Vec 2 → E}
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (k : Fin 2) :
    IntegrableOn (derivAmpA k B) {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} :=
  integrableOn_coord_smul hr hB k

omit [CompleteSpace E] in
theorem integrableOn_derivAmpB {r : ℝ} (hr : 0 ≤ r) {A : Vec 2 → E}
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (k : Fin 2) :
    IntegrableOn (derivAmpB k A) {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} :=
  (integrableOn_coord_smul hr hA k).neg

omit [CompleteSpace E] in
/-- The integrand of `ampFun` is integrable on the ball. -/
theorem integrableOn_ampIntegrand {r : ℝ} {A B : Vec 2 → E}
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (z : Vec 2) :
    IntegrableOn (fun θ => Real.cos (vecDot θ z) • A θ + Real.sin (vecDot θ z) • B θ)
      {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} := by
  have hc : Continuous fun θ : Vec 2 => vecDot θ z := by unfold vecDot; fun_prop
  refine Integrable.mono' (hA.norm.add hB.norm)
    (((Real.continuous_cos.comp hc).aestronglyMeasurable.smul hA.aestronglyMeasurable).add
      ((Real.continuous_sin.comp hc).aestronglyMeasurable.smul hB.aestronglyMeasurable))
    (Eventually.of_forall fun θ => ?_)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

omit [CompleteSpace E] in
/-- The norm of a band-limited function is at most the `L¹` norms of its amplitudes. -/
theorem norm_ampFun_le {r : ℝ} {A B : Vec 2 → E}
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (z : Vec 2) :
    ‖ampFun r A B z‖ ≤ ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, (‖A θ‖ + ‖B θ‖) := by
  refine norm_integral_le_of_norm_le (hA.norm.add hB.norm) (Eventually.of_forall fun θ => ?_)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

/-- The continuous linear map `v ↦ (w ↦ w_k v)`. -/
noncomputable def coordSmulRight (k : Fin 2) : E →L[ℝ] (Vec 2 →L[ℝ] E) :=
  ContinuousLinearMap.smulRightL ℝ (Vec 2) E (ContinuousLinearMap.proj k)

omit [CompleteSpace E] in
theorem coordSmulRight_apply (k : Fin 2) (v : E) (w : Vec 2) :
    coordSmulRight k v w = w k • v := rfl

/-- The derivative in `z` of the integrand of `ampFun`. -/
noncomputable def ampIntegrandDeriv (A B : Vec 2 → E) (z θ : Vec 2) : Vec 2 →L[ℝ] E :=
  ∑ k : Fin 2, coordSmulRight k
    (Real.cos (vecDot θ z) • derivAmpA k B θ + Real.sin (vecDot θ z) • derivAmpB k A θ)

omit [CompleteSpace E] in
theorem hasFDerivAt_ampIntegrand (A B : Vec 2 → E) (θ z : Vec 2) :
    HasFDerivAt (fun z => Real.cos (vecDot θ z) • A θ + Real.sin (vecDot θ z) • B θ)
      (ampIntegrandDeriv A B z θ) z := by
  set ℓ : Vec 2 →L[ℝ] ℝ := ∑ k : Fin 2, θ k • ContinuousLinearMap.proj k with hℓ
  have hℓx : (fun x => vecDot θ x) = ℓ := by
    funext x
    simp [hℓ, vecDot, Fin.sum_univ_two]
  have hd : HasFDerivAt (fun x => vecDot θ x) ℓ z := by
    rw [hℓx]
    exact ℓ.hasFDerivAt
  have hc := ((Real.hasDerivAt_cos (vecDot θ z)).comp_hasFDerivAt z hd).smul_const (A θ)
  have hs := ((Real.hasDerivAt_sin (vecDot θ z)).comp_hasFDerivAt z hd).smul_const (B θ)
  refine (hc.add hs).congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp [ampIntegrandDeriv, coordSmulRight_apply, derivAmpA, derivAmpB, hℓ, Fin.sum_univ_two]
  module

omit [CompleteSpace E] in
theorem integrableOn_ampIntegrandDeriv {r : ℝ} (hr : 0 ≤ r) {A B : Vec 2 → E}
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (z : Vec 2) :
    IntegrableOn (fun θ => ampIntegrandDeriv A B z θ) {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} := by
  unfold ampIntegrandDeriv
  refine integrable_finsetSum (f := fun k θ => coordSmulRight (E := E) k
    (Real.cos (vecDot θ z) • derivAmpA k B θ + Real.sin (vecDot θ z) • derivAmpB k A θ))
    Finset.univ fun k _ => ?_
  exact (coordSmulRight (E := E) k).integrable_comp
    (integrableOn_ampIntegrand (integrableOn_derivAmpA hr hB k) (integrableOn_derivAmpB hr hA k) z)

omit [CompleteSpace E] in
theorem norm_coordSmulRight_le (k : Fin 2) (v : E) : ‖coordSmulRight k v‖ ≤ ‖v‖ := by
  show ‖(ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ).smulRight v‖ ≤ ‖v‖
  rw [ContinuousLinearMap.norm_smulRight_apply]
  have hp : ‖(ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      rw [one_mul, ContinuousLinearMap.proj_apply]
      exact norm_le_pi_norm w k
  exact mul_le_of_le_one_left (norm_nonneg _) hp

omit [CompleteSpace E] in
theorem norm_ampDerivTerm_le {r : ℝ} (hr : 0 ≤ r) {A B : Vec 2 → E} {θ : Vec 2}
    (hθ : θ ∈ {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (x : Vec 2) (k : Fin 2) :
    ‖Real.cos (vecDot θ x) • derivAmpA k B θ + Real.sin (vecDot θ x) • derivAmpB k A θ‖ ≤
      r * (‖A θ‖ + ‖B θ‖) := by
  have hθk := abs_coord_le_of_mem_ampBall hr hθ k
  refine (norm_add_le _ _).trans ?_
  simp only [derivAmpA, derivAmpB, norm_smul, norm_neg, Real.norm_eq_abs]
  have h1 : |Real.cos (vecDot θ x)| * (|θ k| * ‖B θ‖) ≤ r * ‖B θ‖ :=
    (mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)).trans
      (mul_le_mul_of_nonneg_right hθk (norm_nonneg _))
  have h2 : |Real.sin (vecDot θ x)| * (|θ k| * ‖A θ‖) ≤ r * ‖A θ‖ :=
    (mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one _)).trans
      (mul_le_mul_of_nonneg_right hθk (norm_nonneg _))
  rw [mul_add, add_comm (r * ‖A θ‖)]
  exact add_le_add h1 h2

omit [CompleteSpace E] in
theorem norm_ampIntegrandDeriv_le {r : ℝ} (hr : 0 ≤ r) {A B : Vec 2 → E} {θ : Vec 2}
    (hθ : θ ∈ {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (x : Vec 2) :
    ‖ampIntegrandDeriv A B x θ‖ ≤ 2 * (r * (‖A θ‖ + ‖B θ‖)) := by
  unfold ampIntegrandDeriv
  refine (norm_sum_le _ _).trans ?_
  rw [Fin.sum_univ_two, two_mul]
  exact add_le_add ((norm_coordSmulRight_le _ _).trans (norm_ampDerivTerm_le hr hθ x 0))
    ((norm_coordSmulRight_le _ _).trans (norm_ampDerivTerm_le hr hθ x 1))

theorem integral_ampIntegrandDeriv {r : ℝ} (hr : 0 ≤ r) {A B : Vec 2 → E}
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (z : Vec 2) :
    ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, ampIntegrandDeriv A B z θ =
      ∑ k : Fin 2, coordSmulRight k (ampFun r (derivAmpA k B) (derivAmpB k A) z) := by
  have hv := fun k : Fin 2 =>
    integrableOn_ampIntegrand (integrableOn_derivAmpA hr hB k) (integrableOn_derivAmpB hr hA k) z
  unfold ampIntegrandDeriv
  rw [integral_finsetSum _ fun k _ => (coordSmulRight (E := E) k).integrable_comp (hv k)]
  exact Finset.sum_congr rfl fun k _ => (coordSmulRight (E := E) k).integral_comp_comm (hv k)

/-- **Differentiation under the integral**: `∂_k ampFun r A B = ampFun r (θ_k B) (-θ_k A)`. -/
theorem hasFDerivAt_ampFun {r : ℝ} (hr : 0 ≤ r) {A B : Vec 2 → E}
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (z : Vec 2) :
    HasFDerivAt (ampFun r A B)
      (∑ k : Fin 2, coordSmulRight k (ampFun r (derivAmpA k B) (derivAmpB k A) z)) z := by
  rw [← integral_ampIntegrandDeriv hr hA hB z]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (bound := fun θ => 2 * (r * (‖A θ‖ + ‖B θ‖))) Filter.univ_mem
    (Eventually.of_forall fun x => (integrableOn_ampIntegrand hA hB x).aestronglyMeasurable)
    (integrableOn_ampIntegrand hA hB z)
    (integrableOn_ampIntegrandDeriv hr hA hB z).aestronglyMeasurable
    ((ae_restrict_mem (amplitudeBall_measurable r)).mono fun θ hθ x _ =>
      norm_ampIntegrandDeriv_le hr hθ x)
    (((hA.norm.add hB.norm).const_mul r).const_mul 2)
    (Eventually.of_forall fun θ x _ => hasFDerivAt_ampIntegrand A B θ x)

/-- **Smoothness** of band-limited functions. -/
theorem ampFun_contDiff {r : ℝ} (hr : 0 ≤ r) : ∀ (M : ℕ) {A B : Vec 2 → E},
    IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} →
    IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} → ContDiff ℝ M (ampFun r A B)
  | 0, A, B, hA, hB => by
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun z =>
      (hasFDerivAt_ampFun hr hA hB z).differentiableAt.continuousAt
  | M + 1, A, B, hA, hB => by
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv.2 ⟨fun z => (hasFDerivAt_ampFun hr hA hB z).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    have hf : fderiv ℝ (ampFun r A B) = fun z =>
        ∑ k : Fin 2, coordSmulRight k (ampFun r (derivAmpA k B) (derivAmpB k A) z) :=
      funext fun z => (hasFDerivAt_ampFun hr hA hB z).fderiv
    rw [hf]
    exact ContDiff.sum fun k _ => (coordSmulRight (E := E) k).contDiff.comp
      (ampFun_contDiff hr M (integrableOn_derivAmpA hr hB k) (integrableOn_derivAmpB hr hA k))

/-- Ordered derivatives of a band-limited function are band-limited, with amplitudes multiplied by
at most `r` per derivative. -/
theorem orderedDerivative_ampFun {r : ℝ} (hr : 0 ≤ r) : ∀ {a : ℕ} (wd : DerivativeWord2 a)
    {A B : Vec 2 → E}, IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} →
    IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} →
    ∃ A' B' : Vec 2 → E, IntegrableOn A' {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} ∧
      IntegrableOn B' {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} ∧
      orderedDerivative wd (ampFun r A B) = ampFun r A' B' ∧
      ∀ θ ∈ {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, ‖A' θ‖ + ‖B' θ‖ ≤ r ^ a * (‖A θ‖ + ‖B θ‖)
  | 0, wd, A, B, hA, hB => ⟨A, B, hA, hB, AVRegularity.orderedDerivative_zero _ wd,
      fun θ _ => by rw [pow_zero, one_mul]⟩
  | a + 1, wd, A, B, hA, hB => by
    obtain ⟨A₁, B₁, hA₁, hB₁, h₁, hb₁⟩ :=
      orderedDerivative_ampFun hr (fun i : Fin a => wd i.castSucc) hA hB
    refine ⟨derivAmpA (wd (Fin.last a)) B₁, derivAmpB (wd (Fin.last a)) A₁,
      integrableOn_derivAmpA hr hB₁ _, integrableOn_derivAmpB hr hA₁ _, ?_, ?_⟩
    · rw [AVRegularity.orderedDerivative_succ, h₁]
      funext z
      rw [(hasFDerivAt_ampFun hr hA₁ hB₁ z).fderiv]
      generalize wd (Fin.last a) = k
      fin_cases k <;> simp [coordSmulRight_apply, basisVec_apply, Fin.sum_univ_two]
    · intro θ hθ
      have hb := hb₁ θ hθ
      have hk := abs_coord_le_of_mem_ampBall hr hθ (wd (Fin.last a))
      simp only [derivAmpA, derivAmpB, norm_neg, norm_smul, Real.norm_eq_abs]
      calc |θ (wd (Fin.last a))| * ‖B₁ θ‖ + |θ (wd (Fin.last a))| * ‖A₁ θ‖ =
            |θ (wd (Fin.last a))| * (‖A₁ θ‖ + ‖B₁ θ‖) := by ring
        _ ≤ r * (r ^ a * (‖A θ‖ + ‖B θ‖)) := mul_le_mul hk hb (by positivity) hr
        _ = r ^ (a + 1) * (‖A θ‖ + ‖B θ‖) := by ring

/-- **Derivative bound** of band-limited functions. -/
theorem norm_orderedDerivative_ampFun_le {r : ℝ} (hr : 0 ≤ r) {A B : Vec 2 → E}
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) {a : ℕ} (wd : DerivativeWord2 a)
    (z : Vec 2) :
    ‖orderedDerivative wd (ampFun r A B) z‖ ≤
      r ^ a * ((∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, ‖A θ‖) +
        ∫ θ in {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}, ‖B θ‖) := by
  obtain ⟨A', B', hA', hB', h, hb⟩ := orderedDerivative_ampFun hr wd hA hB
  rw [h]
  refine (norm_ampFun_le hA' hB' z).trans ?_
  rw [← integral_add hA.norm hB.norm, ← integral_const_mul]
  exact setIntegral_mono_on (hA'.norm.add hB'.norm) ((hA.norm.add hB.norm).const_mul _)
    (amplitudeBall_measurable r) hb

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Transfer of weighted jet bounds from compact data

A retained map is determined by its values on smooth compactly supported data: a weighted jet bound
by a moment norm that holds on every such datum holds on every measurable datum of finite moment
norm (density, `CompactDensityStatement`; the `bounded` field; the derivative bound of
band-limited calculus; Fatou). -/

section
universe u v

section Transfer

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- **Transfer.** A weighted jet bound of the retained map on smooth compactly supported data holds
on every measurable datum of finite moment norm of an order at least `∑K_i`. -/
theorem retainedMap_jets_le_of_compact (hB0 : AmplitudePlancherelStatement.{v})
    (hA4 : CompactDensityStatement.{u, v})
    {K : ScalarConstants} {χlo : Vec 2 → ℝ} {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D}
    {η S ηg t₀ ϖ : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {X₀ : Vec 2}
    {R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x)}
    (hR : IsRetainedMap K χlo π letters η S ηg t₀ ϖ G v X₀ R)
    (hr : 0 < 2 * K.ξlo * Real.sqrt η) (hπ : ∀ x, 0 < π x) (p : ℝ) (M n : ℕ) (s rj C : ℝ)
    (hn : wordReserveN 0 (fun i => (letters i).slow) ≤ n)
    (hcompact : ∀ φ : ∀ x, Vec 2 → h x, (∀ x, ContDiff ℝ (⊤ : ℕ∞) (φ x) ∧ HasCompactSupport (φ x)) →
      weightedJetNorm π p M s rj (fun x _ wd z => orderedDerivative wd (R φ x) z) ≤
        ENNReal.ofReal C * momentNorm π n ϖ φ)
    (F : ∀ x, Vec 2 → h x) (hF : ∀ x, AEStronglyMeasurable (F x) volume)
    (hfin : momentNorm π n ϖ F < ⊤) :
    weightedJetNorm π p M s rj (fun x _ wd z => orderedDerivative wd (R F x) z) ≤
      ENNReal.ofReal C * momentNorm π n ϖ F := by
  obtain ⟨φs, hφs, hconv⟩ := hA4.2 F hF
  set n0 := wordReserveN 0 fun i => (letters i).slow
  have hfin0 : momentNorm π n0 ϖ F < ⊤ := (momentNorm_mono hn π ϖ F).trans_lt hfin
  have hφm : ∀ k x, AEStronglyMeasurable (φs k x) volume :=
    fun k x => (hφs k x).1.continuous.aestronglyMeasurable
  have hjets : ∀ (G' : ∀ x, Vec 2 → h x) x a (wd : DerivativeWord2 a),
      AEStronglyMeasurable (fun z => orderedDerivative wd (R G' x) z) volume := by
    intro G' x a wd
    have hcd := (hR.band G' x).1 a
    rw [orderedDerivative_eq_iteratedFDeriv wd hcd]
    exact ((continuous_eval_const _).comp
      (hcd.continuous_iteratedFDeriv le_rfl)).aestronglyMeasurable
  have hlsc := weightedJetNorm_le_liminf π p M s rj
    (fun k x _ wd z => orderedDerivative wd (R (φs k) x) z)
    (fun x _ wd z => orderedDerivative wd (R F x) z)
    (fun k x a wd => hjets (φs k) x a wd) (fun x a wd => hjets F x a wd)
    (fun x a wd z => retainedMap_orderedDerivative_tendsto hB0 hR hr hπ F φs hF hφm
      (hconv π n0 ϖ hfin0) x a wd z)
  have hmom := momentNorm_tendsto π n ϖ F φs hfin (hconv π n ϖ hfin)
  have hlim : Tendsto (fun k => ENNReal.ofReal C * momentNorm π n ϖ (φs k)) atTop
      (𝓝 (ENNReal.ofReal C * momentNorm π n ϖ F)) :=
    ENNReal.Tendsto.const_mul hmom (Or.inr ENNReal.ofReal_ne_top)
  refine hlsc.trans ?_
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf (Filter.Eventually.of_forall fun k => hcompact (φs k) (hφs k))

end Transfer
end

/-! # The discard on compact data from its two bands

`compactDiscard_of_parts : QuietHighStatement → MarksBandStatement → CompactDiscardStatement`.
The retained cutoff is `a·b` with `a = χ_lo(·/√η)` and the zone factor `b = zoneCutoff`, so the
endpoint minus its retained cutoff is the endpoint minus `b(D)` (the high plane frequencies, damped
across the terminal quiet stretch) plus `b(D) - (ab)(D)` (the marks band); the molecular output norm
is subadditive (`jetOutputNorm_add_le`), and the two factors add up to the discard factor. -/

section
universe u v

section Measurability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem foldl_fderiv_aestronglyMeasurable (l : List (Fin 2)) {g : Vec 2 → E}
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g) volume := by
  induction l using List.reverseRecOn with
  | nil => simpa using hg
  | append_singleton l i _ =>
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable

/-- An ordered derivative of a measurable function is measurable (every derivative of order
`≥ 1` is, without assumption: `measurable_fderiv_apply_const`). -/
theorem orderedDerivative_aestronglyMeasurable {a : ℕ} (wd : DerivativeWord2 a) {g : Vec 2 → E}
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (orderedDerivative wd g) volume :=
  foldl_fderiv_aestronglyMeasurable _ hg

end Measurability

section Cutoffs

theorem zoneCutoff_contDiff {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo) :
    ContDiff ℝ (⊤ : ℕ∞) (zoneCutoff K χlo) :=
  hχ.smooth.comp (contDiff_const_smul _)

theorem zoneCutoff_eq_zero {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (hξlo : 0 < K.ξlo) (θ : Vec 2) (hθ : Real.pi / 2 ≤ Real.sqrt (vecDot θ θ)) :
    zoneCutoff K χlo θ = 0 := by
  unfold zoneCutoff
  apply hχ.supp
  have hc : 0 ≤ 4 * K.ξlo / Real.pi := by positivity
  have hvd : vecDot ((4 * K.ξlo / Real.pi) • θ) ((4 * K.ξlo / Real.pi) • θ) =
      (4 * K.ξlo / Real.pi) ^ 2 * vecDot θ θ := by
    unfold vecDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hvd, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]
  calc 2 * K.ξlo = 4 * K.ξlo / Real.pi * (Real.pi / 2) := by field_simp; ring
    _ ≤ 4 * K.ξlo / Real.pi * Real.sqrt (vecDot θ θ) := mul_le_mul_of_nonneg_left hθ hc

theorem retainedCutoff_eq_zone (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ) (θ : Vec 2) :
    retainedCutoff K η χlo θ = χlo ((Real.sqrt η)⁻¹ • θ) * zoneCutoff K χlo θ := rfl

theorem retainedCutoff_contDiff {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo)
    (η : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (retainedCutoff K η χlo) :=
  (hχ.smooth.comp (contDiff_const_smul _)).mul (zoneCutoff_contDiff hχ)

end Cutoffs

section Assembly

/-- The two band factors add up to the discard factor. -/
theorem discard_parts_le {C₁ C₂ Θ P S B D c₁ c₂ : ℝ} {Q₁ Q₂ : ℕ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hΘ : 0 ≤ Θ) (hP : 1 ≤ P) (hS : 0 ≤ S) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    C₁ * Θ * P ^ Q₁ * (1 + S) ^ Q₁ * Real.exp (-c₁ * D) +
        C₂ * Θ * P ^ Q₂ * (1 + S) ^ Q₂ * Real.exp (-c₂ * S) ≤
      (C₁ + C₂) * Θ * P ^ (max Q₁ Q₂) * (1 + S) ^ (max Q₁ Q₂) *
        (Real.exp (-(min c₁ c₂) * S) + (1 + B) * Real.exp (-(min c₁ c₂) * D)) := by
  have hA₁ : 0 ≤ C₁ * Θ * P ^ Q₁ * (1 + S) ^ Q₁ := by
    have : 0 ≤ P := by linarith
    positivity
  have hA₂ : 0 ≤ C₂ * Θ * P ^ Q₂ * (1 + S) ^ Q₂ := by
    have : 0 ≤ P := by linarith
    positivity
  have h1 : C₁ * Θ * P ^ Q₁ * (1 + S) ^ Q₁ * Real.exp (-c₁ * D) ≤
      C₁ * Θ * P ^ Q₁ * (1 + S) ^ Q₁ * (Real.exp (-c₁ * S) + (1 + B) * Real.exp (-c₁ * D)) := by
    refine mul_le_mul_of_nonneg_left ?_ hA₁
    have := Real.exp_pos (-c₁ * S)
    have : Real.exp (-c₁ * D) ≤ (1 + B) * Real.exp (-c₁ * D) :=
      le_mul_of_one_le_left (Real.exp_pos _).le (by linarith)
    linarith
  have h2 : C₂ * Θ * P ^ Q₂ * (1 + S) ^ Q₂ * Real.exp (-c₂ * S) ≤
      C₂ * Θ * P ^ Q₂ * (1 + S) ^ Q₂ * (Real.exp (-c₂ * S) + (1 + B) * Real.exp (-c₂ * D)) := by
    refine mul_le_mul_of_nonneg_left ?_ hA₂
    have : 0 ≤ (1 + B) * Real.exp (-c₂ * D) := by positivity
    linarith
  have h1' := discardFactor_mono (C₂ := C₁) (Q₂ := max Q₁ Q₂) (c₂ := min c₁ c₂) hC₁ le_rfl hΘ hP
    hS hB hD (le_max_left _ _) (min_le_left _ _) (D := D) (c₁ := c₁) (Q₁ := Q₁)
  have h2' := discardFactor_mono (C₂ := C₂) (Q₂ := max Q₁ Q₂) (c₂ := min c₁ c₂) hC₂ le_rfl hΘ hP
    hS hB hD (le_max_right _ _) (min_le_right _ _) (D := D) (c₁ := c₂) (Q₁ := Q₂)
  have hsum : C₁ * Θ * P ^ (max Q₁ Q₂) * (1 + S) ^ (max Q₁ Q₂) *
        (Real.exp (-(min c₁ c₂) * S) + (1 + B) * Real.exp (-(min c₁ c₂) * D)) +
      C₂ * Θ * P ^ (max Q₁ Q₂) * (1 + S) ^ (max Q₁ Q₂) *
        (Real.exp (-(min c₁ c₂) * S) + (1 + B) * Real.exp (-(min c₁ c₂) * D)) =
      (C₁ + C₂) * Θ * P ^ (max Q₁ Q₂) * (1 + S) ^ (max Q₁ Q₂) *
        (Real.exp (-(min c₁ c₂) * S) + (1 + B) * Real.exp (-(min c₁ c₂) * D)) := by ring
  linarith

/-- **The discard on compact data from its two bands.** -/
theorem compactDiscard_of_parts (hQH : QuietHighStatement.{u, v})
    (hMB : MarksBandStatement.{u, v}) : CompactDiscardStatement.{u, v} := by
  intro K
  obtain ⟨g₁Q, hg₁Q, hQ⟩ := hQH K
  obtain ⟨g₁M, hg₁M, hM⟩ := hMB K
  refine ⟨min g₁Q g₁M, lt_min hg₁Q hg₁M, ?_⟩
  intro χlo hχ Nw D H Kf m Cout hCout d Ks pos
  obtain ⟨C₁, c₁, Q₁, hC₁, hc₁, hQs⟩ := hQ χlo hχ Nw D H Kf m Cout hCout d Ks pos
  obtain ⟨C₂, c₂, Q₂, hC₂, hc₂, hMs⟩ := hM χlo hχ Nw D H Kf m Cout hCout d Ks pos
  refine ⟨C₁ + C₂, min c₁ c₂, max Q₁ Q₂, by positivity, lt_min hc₁ hc₂, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg hB hJ hrstar
    hrstarC X₀ κ hκf hκ f u w hcd hch
  have h1 := hQs J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg (hB.mono (min_le_left _ _))
    hJ hrstar hrstarC X₀ κ hκf hκ f u w hcd hch
  have h2 := hMs J π letters hletters η S ηg rstar t₀ ϖ G v g reg pkg (hB.mono (min_le_right _ _))
    hJ hrstar hrstarC X₀ κ hκf hκ f u w hcd hch
  have hξlo : 0 < K.ξlo := pkg.consts_pos.2.1
  -- measurability of the jets
  have hU : ∀ x, MemLp (planeValue (u (Fin.last Nw) x (t₀ + S))) 2 volume :=
    fun x => planeValue_memLp _
  have hmb : ∀ x a (wd : DerivativeWord2 a), AEStronglyMeasurable (orderedDerivative wd
      (fourierCutoff (zoneCutoff K χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))))) volume :=
    fun x a wd => orderedDerivative_aestronglyMeasurable wd
      (fourierCutoff_memLp_of_memLp _ (Real.pi / 2) (zoneCutoff_eq_zero hχ hξlo)
        (zoneCutoff_contDiff hχ) (hU x)).aestronglyMeasurable
  have hmab : ∀ x a (wd : DerivativeWord2 a), AEStronglyMeasurable (orderedDerivative wd
      (fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))))) volume :=
    fun x a wd => orderedDerivative_aestronglyMeasurable wd
      (fourierCutoff_memLp_of_memLp _ (Real.pi / 2)
        (fun θ hθ => by rw [retainedCutoff_eq_zone, zoneCutoff_eq_zero hχ hξlo θ hθ, mul_zero])
        (retainedCutoff_contDiff hχ η) (hU x)).aestronglyMeasurable
  have hsplit : (fun x a (wd : DerivativeWord2 a) z =>
      planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
        orderedDerivative wd (fourierCutoff (retainedCutoff K η χlo)
          (planeValue (u (Fin.last Nw) x (t₀ + S)))) z) =
      fun x a wd z => (planeJetOrder (u (Fin.last Nw) x (t₀ + S)) a wd z -
          orderedDerivative wd (fourierCutoff (zoneCutoff K χlo)
            (planeValue (u (Fin.last Nw) x (t₀ + S)))) z) +
        (orderedDerivative wd (fourierCutoff (zoneCutoff K χlo)
            (planeValue (u (Fin.last Nw) x (t₀ + S)))) z -
          orderedDerivative wd (fourierCutoff (retainedCutoff K η χlo)
            (planeValue (u (Fin.last Nw) x (t₀ + S)))) z) := by
    funext x a wd z
    abel
  rw [hsplit]
  refine (jetOutputNorm_add_le π m Kf ϖ rstar _ _
    (fun x a wd => (planeJetOrder_aestronglyMeasurable _ a wd).sub (hmb x a wd))
    (fun x a wd => (hmb x a wd).sub (hmab x a wd))).trans ?_
  refine (add_le_add h1 h2).trans ?_
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ zero_le
  have hΘ := hB.wordTheta_nonneg
  have hS0 : 0 ≤ S := zero_le_one.trans hB.hS
  have hbuf : 0 ≤ reg.buffer := pkg.buffer_nonneg
  rw [← ENNReal.ofReal_add (by have := AVRegularity.CycleWords.Assembly.one_le_peFactor η; positivity)
    (by have := AVRegularity.CycleWords.Assembly.one_le_peFactor η; positivity)]
  exact ENNReal.ofReal_le_ofReal (discard_parts_le hC₁.le hC₂.le hΘ (AVRegularity.CycleWords.Assembly.one_le_peFactor η) hS0
    (Nat.cast_nonneg _) hbuf)

end Assembly
end

end AVRegularity.CycleWords.Assembly
end
