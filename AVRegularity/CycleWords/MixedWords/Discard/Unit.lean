-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.Discard.Pair
import AVRegularity.CycleWords.MixedWords.ConstituentTransposeStep

section
section
section
/-! # tools for the limit of compact chains

* `rff_jetOutputNorm_le_liminf_ae`: Fatou for the molecular output norm under almost everywhere
  convergence of the jets.
* `rff_eLpNorm_jet_le`: one jet in `L²` by the output norm (the term `β = 0`).
* `rff_ofReal_norm_le` and `rff_eLpNorm_jet_le_norm`: the `PlaneHk` norm against the `L²` norms of
  the jets.
* `rff_tendsto_integral_inner`: the pairing of the value with an `L²` test is continuous on
  `PlaneHk`.
* `rff_planeHk_eq_zero`: an element whose value pairs to zero with every smooth compactly
  supported test is zero.
* `rff_cauchySeq`, `rff_eq_of_pairing_tendsto`, `rff_limit_le`: a sequence whose jet differences
  are controlled is Cauchy; its limit is identified by the value pairings; the output norm of the
  limit is at most the limit of the bounds (an almost everywhere convergent subsequence, Fatou). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

open AVRegularity.CycleWords.Assembly

section Norms

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]

/-- **Fatou for the output norm**, almost everywhere. -/
theorem rff_jetOutputNorm_le_liminf_ae (π : ι → ℝ) (m K : ℕ) (s r : ℝ)
    (J : ℕ → ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (Jlim : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (hJ : ∀ k v a w, AEStronglyMeasurable (J k v a w) volume)
    (hJlim : ∀ v a w, AEStronglyMeasurable (Jlim v a w) volume)
    (hlim : ∀ v a w, ∀ᵐ z, Tendsto (fun k => J k v a w z) atTop (𝓝 (Jlim v a w z))) :
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
    filter_upwards [ae_all_iff.2 fun w => hlim v βa.2 w] with z hz
    refine tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp ?_)
    refine tendsto_finsetSum _ fun w _ => ?_
    exact ((hz w).norm).pow 2
  rw [jetOutputNorm_eq_combination]
  simp only [jetOutputNorm_eq_combination]
  exact le_trans (outputCombination_monotone π m K fun v βa => hfatou v βa)
    (map_liminf_le_liminf _ (outputCombination_monotone π m K)
      (outputCombination_continuous π m K) N)

/-- **One jet by the output norm**: the term `β = 0`, order `a`, component `x`. -/
theorem rff_eLpNorm_jet_le (π : ι → ℝ) (m K : ℕ) (s r : ℝ) (hr : 0 < r)
    (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v) (x : ι) (hπ : 0 < π x) {a : ℕ}
    (ha : a ≤ K) (wd : DerivativeWord2 a) (hJ : AEStronglyMeasurable (J x a wd) volume) :
    eLpNorm (J x a wd) 2 volume ≤
      ENNReal.ofReal (a.factorial * Real.sqrt (π x) / r ^ a) * jetOutputNorm π m K s r J := by
  set Y := eLpNorm (fun z => Real.sqrt (∑ w : DerivativeWord2 a, ‖J x a w z‖ ^ 2)) 2 volume
  have hXY : eLpNorm (J x a wd) 2 volume ≤ Y := by
    refine eLpNorm_mono_real hJ fun z => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun w => ‖J x a w z‖ ^ 2) (fun w _ => sq_nonneg _)
      (Finset.mem_univ wd)
  have hra : 0 < r ^ a := pow_pos hr a
  have hfa : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  have hsq : 0 < Real.sqrt (π x) := Real.sqrt_pos.2 hπ
  -- the term `β = 0`, order `a`
  have h00 : ((0 : ℕ), (0 : ℕ)) ∈ momentIndices m := by simp [momentIndices]
  have haK : a ∈ Finset.range (K + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le ha)
  have hN : eLpNorm (fun z => ((s * z 0) ^ (0 : ℕ) * (s * z 1) ^ (0 : ℕ) * r ^ a) *
      Real.sqrt (∑ w : DerivativeWord2 a, ‖J x a w z‖ ^ 2)) 2 volume =
      ENNReal.ofReal (r ^ a) * Y := by
    have he : (fun z : Vec 2 => ((s * z 0) ^ (0 : ℕ) * (s * z 1) ^ (0 : ℕ) * r ^ a) *
        Real.sqrt (∑ w : DerivativeWord2 a, ‖J x a w z‖ ^ 2)) =
        (r ^ a) • fun z => Real.sqrt (∑ w : DerivativeWord2 a, ‖J x a w z‖ ^ 2) := by
      funext z
      simp
    rw [he, eLpNorm_const_smul, Real.enorm_eq_ofReal hra.le]
  have hterm : ENNReal.ofReal ((((0 : ℕ).factorial * (0 : ℕ).factorial * a.factorial : ℕ) : ℝ)⁻¹)
      * (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((s * z 0) ^ (0 : ℕ) * (s * z 1) ^ (0 : ℕ) * r ^ a) *
          Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2)) 2 volume ^ 2) ^ (1 / 2 : ℝ) ≤
      jetOutputNorm π m K s r J := by
    unfold jetOutputNorm
    refine le_trans ?_ (Finset.single_le_sum (f := fun β : ℕ × ℕ => ∑ a ∈ Finset.range (K + 1),
      ENNReal.ofReal ((((β.1.factorial * β.2.factorial * a.factorial : ℕ)) : ℝ)⁻¹) *
        (∑ v, ENNReal.ofReal ((π v)⁻¹) *
          eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2 * r ^ a) *
            Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2)) 2 volume ^ 2) ^ (1 / 2 : ℝ))
      (fun _ _ => zero_le) h00)
    exact Finset.single_le_sum (f := fun a' => ENNReal.ofReal
      ((((0 : ℕ).factorial * (0 : ℕ).factorial * a'.factorial : ℕ) : ℝ)⁻¹) *
        (∑ v, ENNReal.ofReal ((π v)⁻¹) *
          eLpNorm (fun z => ((s * z 0) ^ (0 : ℕ) * (s * z 1) ^ (0 : ℕ) * r ^ a') *
            Real.sqrt (∑ w : DerivativeWord2 a', ‖J v a' w z‖ ^ 2)) 2 volume ^ 2) ^ (1 / 2 : ℝ))
      (fun _ _ => zero_le) haK
  have hone : ENNReal.ofReal ((π x)⁻¹) * (ENNReal.ofReal (r ^ a) * Y) ^ 2 ≤
      ∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((s * z 0) ^ (0 : ℕ) * (s * z 1) ^ (0 : ℕ) * r ^ a) *
          Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2)) 2 volume ^ 2 := by
    rw [← hN]
    exact Finset.single_le_sum (f := fun v => ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((s * z 0) ^ (0 : ℕ) * (s * z 1) ^ (0 : ℕ) * r ^ a) *
          Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2)) 2 volume ^ 2)
      (fun _ _ => zero_le) (Finset.mem_univ x)
  have hroot : (ENNReal.ofReal ((π x)⁻¹) * (ENNReal.ofReal (r ^ a) * Y) ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((Real.sqrt (π x))⁻¹ * r ^ a) * Y := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
    rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hπ.le) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_inv, ← mul_assoc]
  have hlow : ENNReal.ofReal ((a.factorial : ℝ)⁻¹ * ((Real.sqrt (π x))⁻¹ * r ^ a)) * Y ≤
      jetOutputNorm π m K s r J := by
    refine le_trans ?_ hterm
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hfa.le), mul_assoc, ← hroot]
    simp only [Nat.factorial_zero, one_mul]
    exact mul_le_mul_right (ENNReal.rpow_le_rpow hone (by norm_num)) _
  have hc : (a.factorial * Real.sqrt (π x) / r ^ a) *
      ((a.factorial : ℝ)⁻¹ * ((Real.sqrt (π x))⁻¹ * r ^ a)) = 1 := by
    field_simp
  calc eLpNorm (J x a wd) 2 volume ≤ Y := hXY
    _ = ENNReal.ofReal (a.factorial * Real.sqrt (π x) / r ^ a) *
          (ENNReal.ofReal ((a.factorial : ℝ)⁻¹ * ((Real.sqrt (π x))⁻¹ * r ^ a)) * Y) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hc, ENNReal.ofReal_one, one_mul]
    _ ≤ _ := mul_le_mul_right hlow _

end Norms

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A jet is the stored component of the carrier. -/
theorem rff_eLpNorm_jet_eq {K : ℕ} (U : PlaneHk Set.univ K E) (i : JetIndex2 K) :
    eLpNorm (planeJetOrder U i.1.val i.2) 2 volume =
      ‖(U : JetL2 (volume.restrict Set.univ) K E) i‖ₑ := by
  rw [planeJetOrder_eq_stored (Nat.lt_succ_iff.1 i.1.isLt), Lp.enorm_def]
  conv_rhs => arg 3; rw [Measure.restrict_univ]
  rfl

/-- The carrier norm is at most the sum of the `L²` norms of the jets. -/
theorem rff_ofReal_norm_le {K : ℕ} (U : PlaneHk Set.univ K E) :
    ENNReal.ofReal ‖U‖ ≤ ∑ i : JetIndex2 K, eLpNorm (planeJetOrder U i.1.val i.2) 2 volume := by
  simp only [rff_eLpNorm_jet_eq]
  have hU : ‖U‖ = ‖(U : JetL2 (volume.restrict Set.univ) K E)‖ := rfl
  have hle : ‖(U : JetL2 (volume.restrict Set.univ) K E)‖ ≤
      ∑ i, ‖(U : JetL2 (volume.restrict Set.univ) K E) i‖ := by
    rw [PiLp.norm_eq_of_L2]
    refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun i _ => norm_nonneg _, ?_⟩
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _
  rw [hU]
  calc ENNReal.ofReal ‖(U : JetL2 (volume.restrict Set.univ) K E)‖
        ≤ ENNReal.ofReal (∑ i, ‖(U : JetL2 (volume.restrict Set.univ) K E) i‖) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ∑ i, ‖(U : JetL2 (volume.restrict Set.univ) K E) i‖ₑ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _]
        simp only [ofReal_norm]

/-- One jet is at most the carrier norm. -/
theorem rff_eLpNorm_jet_le_norm {K a : ℕ} (ha : a ≤ K) (U : PlaneHk Set.univ K E)
    (wd : DerivativeWord2 a) :
    eLpNorm (planeJetOrder U a wd) 2 volume ≤ ENNReal.ofReal ‖U‖ := by
  have := rff_eLpNorm_jet_eq U ⟨⟨a, Nat.lt_succ_of_le ha⟩, wd⟩
  simp only at this
  rw [this, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le (U : JetL2 (volume.restrict Set.univ) K E) _)

/-- **The pairing of the value with an `L²` test is continuous on the carrier.** -/
theorem rff_tendsto_integral_inner {K : ℕ} {W : ℕ → PlaneHk Set.univ K E}
    {W' : PlaneHk Set.univ K E} (hW : Tendsto W atTop (𝓝 W')) {Φ : Vec 2 → E}
    (hΦ : MemLp Φ 2 volume) :
    Tendsto (fun k => ∫ z, inner ℝ (planeValue (W k) z) (Φ z)) atTop
      (𝓝 (∫ z, inner ℝ (planeValue W' z) (Φ z))) := by
  have hΦ' : MemLp Φ 2 (volume.restrict (Set.univ : Set (Vec 2))) := by
    rw [Measure.restrict_univ]
    exact hΦ
  let P : PlaneHk Set.univ K E → ℝ := fun U =>
    inner ℝ ((U : JetL2 (volume.restrict Set.univ) K E) (valueIndex2 K)) (hΦ'.toLp Φ)
  have hP : Continuous P :=
    ((PiLp.continuous_apply 2 _ (valueIndex2 K)).comp continuous_subtype_val).inner
      continuous_const
  have hPeq : ∀ U : PlaneHk Set.univ K E,
      P U = ∫ z, inner ℝ (planeValue U z) (Φ z) := by
    intro U
    simp only [P]
    rw [L2.inner_def, ← setIntegral_univ (f := fun z => inner ℝ (planeValue U z) (Φ z))]
    refine integral_congr_ae ?_
    filter_upwards [hΦ'.coeFn_toLp] with z hz
    rw [hz, planeValue_eq_stored]
  have := (hP.tendsto W').comp hW
  simp only [Function.comp_def, hPeq] at this
  exact this

variable [FiniteDimensional ℝ E]

/-- **An element whose value pairs to zero with every smooth compactly supported test is zero.** -/
theorem rff_planeHk_eq_zero {K : ℕ} (W : PlaneHk Set.univ K E)
    (hW : ∀ Φ : Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      ∫ z, inner ℝ (planeValue W z) (Φ z) = 0) : W = 0 := by
  have hloc : LocallyIntegrable (planeValue W) volume :=
    (planeJetOrder_memLp (Nat.zero_le K) W _).locallyIntegrable (by norm_num)
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc => by
    have hint : Integrable (fun z => g z • planeValue W z) volume :=
      hloc.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
    refine ext_inner_right ℝ fun e => ?_
    rw [inner_zero_left, real_inner_comm, ← integral_inner hint]
    have hΦ := hW (fun z => g z • e) (hg.smul contDiff_const) (hgc.smul_right)
    rw [← hΦ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm]
  refine planeHk_eq_of_planeValue_ae ?_
  have h0 : planeValue (0 : PlaneHk Set.univ K E) =ᵐ[volume] 0 := by
    rw [planeValue_eq_stored]
    have := (ae_restrict_iff' MeasurableSet.univ).1
      (Lp.coeFn_zero E 2 (volume.restrict (Set.univ : Set (Vec 2))))
    filter_upwards [this] with z hz
    exact hz (Set.mem_univ z)
  filter_upwards [hz, h0] with z hz h0z
  rw [hz, h0z]
  rfl

/-- **Identification of the limit by the value pairings.** -/
theorem rff_eq_of_pairing_tendsto {K : ℕ} {V : ℕ → PlaneHk Set.univ K E}
    {L T : PlaneHk Set.univ K E} (hVL : Tendsto V atTop (𝓝 L))
    (hpair : ∀ Φ : Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      Tendsto (fun k => ∫ z, inner ℝ (planeValue (V k - T) z) (Φ z)) atTop (𝓝 0)) :
    L = T := by
  have h0 := rff_planeHk_eq_zero (L - T) fun Φ hΦ hΦc => tendsto_nhds_unique
    (rff_tendsto_integral_inner (hVL.sub_const T)
      (hΦ.continuous.memLp_of_hasCompactSupport hΦc)) (hpair Φ hΦ hΦc)
  exact sub_eq_zero.1 h0

end Carrier

section Limit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- **A sequence whose jet differences are controlled is Cauchy.** -/
theorem rff_cauchySeq {K : ℕ} (V : ℕ → PlaneHk Set.univ K E) (M : JetIndex2 K → ℝ≥0∞)
    (hM : ∀ i, M i ≠ ⊤) (e : ℕ → ℝ≥0∞) (he : Tendsto e atTop (𝓝 0))
    (hV : ∀ k l (i : JetIndex2 K),
      eLpNorm (planeJetOrder (V k - V l) i.1.val i.2) 2 volume ≤ M i * (e k + e l)) :
    CauchySeq V := by
  set M' := ∑ i, M i with hM'def
  have hM' : M' ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => hM i
  have hd : ∀ k l, edist (V k) (V l) ≤ M' * e k + M' * e l := by
    intro k l
    rw [edist_dist, dist_eq_norm]
    refine (rff_ofReal_norm_le (V k - V l)).trans ?_
    refine (Finset.sum_le_sum fun i _ => hV k l i).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← hM'def, mul_add]
  have hb : Tendsto (fun k => M' * e k) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul he (Or.inr hM')
  rw [EMetric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hb).2 (ε / 2) (ENNReal.half_pos hε.ne'))
  refine ⟨N, fun n hn => ?_⟩
  calc edist (V n) (V N) ≤ M' * e n + M' * e N := hd n N
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (hN n hn) (hN N le_rfl)
    _ = ε := ENNReal.add_halves ε

end Limit

section Fatou

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **The output norm of a limit**: at most the limit of bounds for the approximants. -/
theorem rff_limit_le (π : ι → ℝ) (m Kf : ℕ) (s r : ℝ) (V : ℕ → ∀ x, PlaneHk Set.univ Kf (h x))
    (T : ∀ x, PlaneHk Set.univ Kf (h x)) (hVT : ∀ x, Tendsto (fun k => V k x) atTop (𝓝 (T x)))
    (B : ℕ → ℝ≥0∞) (B' : ℝ≥0∞) (hB : Tendsto B atTop (𝓝 B'))
    (hV : ∀ k, jetOutputNorm π m Kf s r (fun x a wd z => planeJetOrder (V k x) a wd z) ≤ B k) :
    jetOutputNorm π m Kf s r (fun x a wd z => planeJetOrder (T x) a wd z) ≤ B' := by
  classical
  -- one function controlling all the jets
  let Sf : ℕ → Vec 2 → ℝ := fun k z => ∑ p : ι × JetIndex2 Kf,
    ‖planeJetOrder (V k p.1) p.2.1.val p.2.2 z - planeJetOrder (T p.1) p.2.1.val p.2.2 z‖
  have hjet : ∀ x (i : JetIndex2 Kf), Tendsto (fun k => eLpNorm (fun z =>
      ‖planeJetOrder (V k x) i.1.val i.2 z - planeJetOrder (T x) i.1.val i.2 z‖) 2 volume)
      atTop (𝓝 0) := by
    intro x i
    have hn : Tendsto (fun k => ENNReal.ofReal ‖V k x - T x‖) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal ((tendsto_iff_norm_sub_tendsto_zero).1 (hVT x))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hn (fun k => zero_le)
      (fun k => ?_)
    rw [eLpNorm_norm (fun z => planeJetOrder (V k x) i.1.val i.2 z -
      planeJetOrder (T x) i.1.val i.2 z) ((planeJetOrder_aestronglyMeasurable (V k x) _ _).sub
        (planeJetOrder_aestronglyMeasurable (T x) _ _))]
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      (rff_eLpNorm_jet_le_norm (Nat.lt_succ_iff.1 i.1.isLt) (V k x - T x) i.2)
    exact (planeJetOrder_sub_ae (Nat.lt_succ_iff.1 i.1.isLt) (V k x) (T x) i.2).symm
  have hS : Tendsto (fun k => eLpNorm (Sf k - 0) 2 volume) atTop (𝓝 0) := by
    have hsum : Tendsto (fun k => ∑ p : ι × JetIndex2 Kf, eLpNorm (fun z =>
        ‖planeJetOrder (V k p.1) p.2.1.val p.2.2 z - planeJetOrder (T p.1) p.2.1.val p.2.2 z‖)
        2 volume) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (ι × JetIndex2 Kf))
        fun p _ => hjet p.1 p.2
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun k => zero_le)
      (fun k => ?_)
    rw [sub_zero]
    have he : Sf k = ∑ p : ι × JetIndex2 Kf, fun z =>
        ‖planeJetOrder (V k p.1) p.2.1.val p.2.2 z - planeJetOrder (T p.1) p.2.1.val p.2.2 z‖ := by
      funext z
      simp only [Sf, Finset.sum_apply]
    rw [he]
    exact eLpNorm_sum_le (by norm_num)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (f := Sf) (g := 0) (by norm_num) hS).exists_seq_tendsto_ae
  have hlim : ∀ x a (wd : DerivativeWord2 a), ∀ᵐ z, Tendsto
      (fun i => planeJetOrder (V (ns i) x) a wd z) atTop (𝓝 (planeJetOrder (T x) a wd z)) := by
    intro x a wd
    by_cases ha : a ≤ Kf
    · filter_upwards [hae] with z hz
      have hz' : Tendsto (fun i => Sf (ns i) z) atTop (𝓝 0) := by simpa using hz
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hz'
      exact Finset.single_le_sum (f := fun p : ι × JetIndex2 Kf =>
        ‖planeJetOrder (V (ns i) p.1) p.2.1.val p.2.2 z -
          planeJetOrder (T p.1) p.2.1.val p.2.2 z‖)
        (fun p _ => norm_nonneg _) (Finset.mem_univ (x, ⟨⟨a, Nat.lt_succ_of_le ha⟩, wd⟩))
    · refine Filter.Eventually.of_forall fun z => ?_
      have h0 : ∀ U : PlaneHk Set.univ Kf (h x), planeJetOrder U a wd z = 0 := fun U => by
        simp [planeJetOrder, ha]
      simp only [h0]
      exact tendsto_const_nhds
  have hfat := rff_jetOutputNorm_le_liminf_ae π m Kf s r
    (fun i x a wd z => planeJetOrder (V (ns i) x) a wd z)
    (fun x a wd z => planeJetOrder (T x) a wd z)
    (fun i x a wd => planeJetOrder_aestronglyMeasurable _ a wd)
    (fun x a wd => planeJetOrder_aestronglyMeasurable _ a wd) hlim
  calc _ ≤ _ := hfat
    _ ≤ liminf (fun i => B (ns i)) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall fun i => hV (ns i))
    _ = B' := (hB.comp hns.tendsto_atTop).liminf_eq

end Fatou

end AVRegularity.CycleWords.Discard
end
end

section
/-! # weak smoothing with a free time scale

`cellDriftWeakSmoothing` fixes the time scale `δ = 1 / ((J+1) M P²)`; the Galerkin smoothing it is
built from (`GalerkinSmoothing`) allows every `δ` with `M P² δ ≤ 1`. This gives the heat scaling
`δ^{-J/2}` after a time `J δ`, for every small `δ`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

/-- **Weak smoothing, free time scale.** -/
theorem weakSmoothing_free (J : ℕ) (R P : ℝ) (hR : 0 ≤ R) (hP : 1 ≤ P)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2) (hθ : Real.sqrt (vecDot θ θ) ≤ R)
    {a b : ℝ} (hab : a < b) (hJ : DriftJets v a b P J)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
        ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0))
    (δ : ℝ) (hδ : 0 < δ) (hprice : cellDriftWindowPrice J R * P ^ 2 * δ ≤ 1)
    (t : ℝ) (ht : t ∈ Icc a b) (hat : a + J * δ ≤ t) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧
      ‖W‖ ^ 2 ≤ (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J * ‖U a‖ ^ 2 := by
  have hS := cellDriftGalerkinSmoothing (cellDriftGalerkinWindow cellDriftGalerkinEnergy)
    cellDriftGalerkinContraction
  apply AVRegularity.CycleWords.cellActualWeak_native_of_finite_bound hab
    ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ hG V 0 hv.1 hb measurable_const
    (fun _ => by simp) (U a) U slice hU rfl J t ht
    ((Real.exp 1 * (2 * Real.exp 1) / δ) ^ J * ‖U a‖ ^ 2)
    (mul_nonneg (pow_nonneg (by have := Real.exp_pos 1; positivity) _) (sq_nonneg _))
  intro N y hy hyinit
  have he := hS J N R P hR hP G hG hv V hb θ hθ hab.le hJ y hy δ hδ hprice t hat ht.2
  have hi : ‖cellGalerkinValue N (y a)‖ ^ 2 ≤ ‖U a‖ ^ 2 := by
    rw [hyinit]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (cellGalerkinL2Initial_norm_le N (U a))
  exact he.trans (mul_le_mul_of_nonneg_left hi
    (pow_nonneg (by have := Real.exp_pos 1; positivity) _))

end AVRegularity.CycleWords.Discard
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # forward realizations

`FReal N n s G B` says that the functional `G` of a `C^s` periodic test is the transpose of a
real-linear map `H^N → H^n` of norm `≤ B`: `∫ (A X) φ = ∫ X · G φ`.  The class is closed under sums
and real multiples; `unit0` and `unit1` realize the unit terms
`κ D_{-θ}^{(p,q)}(c φ)` and `κ D_{-θ}^{(p,q)}(c D_{-θ,k} φ)` (the transposes of the test-form unit
terms `realizes_unit0/1`). -/

/-- `G`, a functional of a `C^s` periodic test, is the transpose of a map `H^N → H^n` of norm
`≤ B`. -/
def FReal (N n s : ℕ) (G : (Vec 2 → ℂ) → Vec 2 → ℂ) (B : ℝ) : Prop :=
  ∃ A : TorusHk N ℂ →L[ℝ] TorusHk n ℂ, (∀ X, ‖A X‖ ≤ B * ‖X‖) ∧
    ∀ φ : Vec 2 → ℂ, ContDiff ℝ (s : ℕ) φ → AVenhance.IsZ2Periodic φ →
      Continuous (G φ) ∧ ∀ X : TorusHk N ℂ,
        ∫ y in AVenhance.unitCube, (torusHkValueCLM (A X) : Vec 2 → ℂ) y * φ y =
          ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y * G φ y

theorem int_eq (Y : ComponentL2 (volume.restrict AVenhance.unitCube) ℂ) (φ : Vec 2 → ℂ)
    (hφ : Continuous φ) :
    ∫ y in AVenhance.unitCube, (Y : Vec 2 → ℂ) y * φ y = PrCLM φ hφ Y :=
  (PrCLM_apply φ hφ Y).symm

section Closure

variable {N n s : ℕ} {G G' : (Vec 2 → ℂ) → Vec 2 → ℂ} {B B' : ℝ}

theorem FReal.zero : FReal N n s (fun _ _ => 0) 0 :=
  ⟨0, fun X => by simp, fun φ h1 _ => ⟨continuous_const, fun X => by
    simp only [zero_apply, map_zero, mul_zero, integral_zero]
    rw [int_eq _ _ h1.continuous, map_zero]⟩⟩

theorem FReal.mono (h : FReal N n s G B) (hB : B ≤ B') : FReal N n s G B' := by
  obtain ⟨A, hn, hp⟩ := h
  exact ⟨A, fun X => (hn X).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _)), hp⟩

theorem FReal.congr (h : FReal N n s G B)
    (hG : ∀ φ : Vec 2 → ℂ, ContDiff ℝ (s : ℕ) φ → AVenhance.IsZ2Periodic φ → G φ = G' φ) :
    FReal N n s G' B := by
  obtain ⟨A, hn, hp⟩ := h
  refine ⟨A, hn, fun φ h1 h2 => ?_⟩
  rw [← hG φ h1 h2]
  exact hp φ h1 h2

theorem FReal.add (h : FReal N n s G B) (h' : FReal N n s G' B') :
    FReal N n s (fun f z => G f z + G' f z) (B + B') := by
  obtain ⟨A, hn, hp⟩ := h
  obtain ⟨A', hn', hp'⟩ := h'
  refine ⟨A + A', fun X => ?_, fun φ h1 h2 => ?_⟩
  · rw [add_apply]
    exact (norm_add_le _ _).trans (by nlinarith [hn X, hn' X])
  · obtain ⟨c1, e1⟩ := hp φ h1 h2
    obtain ⟨c2, e2⟩ := hp' φ h1 h2
    refine ⟨c1.add c2, fun X => ?_⟩
    have hφ := h1.continuous
    rw [add_apply, map_add, int_eq _ _ hφ, map_add, ← int_eq _ _ hφ,
      ← int_eq _ _ hφ, e1, e2]
    simp only [mul_add]
    exact (integral_add (pair_integrable _ c1 _) (pair_integrable _ c2 _)).symm

theorem FReal.smul (h : FReal N n s G B) (a : ℝ) :
    FReal N n s (fun f z => (a : ℂ) * G f z) (|a| * B) := by
  obtain ⟨A, hn, hp⟩ := h
  refine ⟨lrSmul a A, fun X => ?_, fun φ h1 h2 => ?_⟩
  · rw [lrSmul_apply, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hn X) (abs_nonneg _)
  · obtain ⟨c1, e1⟩ := hp φ h1 h2
    refine ⟨continuous_const.mul c1, fun X => ?_⟩
    have hφ := h1.continuous
    rw [lrSmul_apply, map_smul, int_eq _ _ hφ, map_smul, ← int_eq _ _ hφ, e1]
    simp only [Complex.real_smul]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)

theorem FReal.finset_sum {κ : Type*} (S : Finset κ) {G : κ → (Vec 2 → ℂ) → Vec 2 → ℂ}
    {B : κ → ℝ} (h : ∀ j ∈ S, FReal N n s (G j) (B j)) :
    FReal N n s (fun f z => ∑ j ∈ S, G j f z) (∑ j ∈ S, B j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (FReal.zero (N := N) (n := n) (s := s))
  | insert a S ha ih =>
    have := (h a (Finset.mem_insert_self a S)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using this

theorem FReal.list_sum {κ : Type*} (l : List κ) {G : κ → (Vec 2 → ℂ) → Vec 2 → ℂ}
    {B : κ → ℝ} (h : ∀ j ∈ l, FReal N n s (G j) (B j)) :
    FReal N n s (fun f z => (l.map fun j => G j f z).sum) (l.map B).sum := by
  induction l with
  | nil => simpa using (FReal.zero (N := N) (n := n) (s := s))
  | cons a l ih =>
    have := (h a List.mem_cons_self).add (ih fun j hj => h j (List.mem_cons_of_mem _ hj))
    simpa using this

end Closure

end AVRegularity.CycleWords.Discard
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # the forward unit terms

The transposes of `realizes_unit0` and `realizes_unit1`: for a real periodic coefficient `c`,
`φ ↦ κ D_{-θ}^{(p,q)}(c φ)` is realized by `X ↦ (-1)^{p+q} κ c · fwdPow X` and
`φ ↦ κ D_{-θ}^{(p,q)}(c D_{-θ,k} φ)` by `X ↦ (-1)^{p+q+1} κ (∂_k + iθ_k)(c · fwdPow X)`. -/

/-- **Forward unit term, no extra derivative**: `κ D_{-θ}^{(p,q)}(c φ)`. -/
theorem unit0 (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n N s p q : ℕ)
    (h1 : n + q + p ≤ N) (hs : p + q ≤ s) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ) :
    FReal N n s (fun f z => (κ : ℂ) * fibreCovPow (-θ) (p, q) (fun y => (c y : ℂ) * f y) z)
      (|κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice n| * P))) := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0 (Nat.zero_le _) 0)
  have hcn : ContDiff ℝ (n : ℕ∞) c := hc.of_le (by exact_mod_cast (by omega : n ≤ n + p + q))
  let M := tbMulCLM n hcn hp hP
  let W : TorusHk N ℂ →L[ℝ] TorusHk n ℂ := (fwdPow θ n q p).comp (truncateTorusHk h1)
  refine ⟨lrSmul (((-1 : ℝ) ^ (p + q)) * κ) (M.comp W), fun X => ?_, fun φ hφ hφp => ?_⟩
  · rw [lrSmul_apply, norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h3 := tbMulCLM_norm_le n hcn hp hP (W X)
    have h4 := fwdPow_norm θ ρ hθ n q p (truncateTorusHk h1 X)
    have h5 := truncateTorusHk_norm_le h1 X
    have hle : cellDriftNativePrice n * P ≤ |cellDriftNativePrice n| * P :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hP0
    rw [ContinuousLinearMap.comp_apply]
    calc _ ≤ cellDriftNativePrice n * P * ‖W X‖ := h3
      _ ≤ |cellDriftNativePrice n| * P * ((1 + ρ) ^ (p + q) * ‖X‖) := by
          have : ‖W X‖ ≤ (1 + ρ) ^ (p + q) * ‖X‖ :=
            h4.trans (mul_le_mul_of_nonneg_left h5 (by positivity))
          exact mul_le_mul hle this (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hφc := hφ.continuous
    have hcφ : ContDiff ℝ (p + q : ℕ) (fun y => (c y : ℂ) * φ y) :=
      contDiff_real_mul_complex (hc.of_le (by exact_mod_cast (by omega : p + q ≤ n + p + q)))
        (hφ.of_le (by exact_mod_cast hs))
    have hcφp : AVenhance.IsZ2Periodic (fun y => (c y : ℂ) * φ y) := by
      intro m z
      simp only
      rw [hp m z, hφp m z]
    have hcont : Continuous (fibreCovPow (-θ) (p, q) (fun y => (c y : ℂ) * φ y)) :=
      (contDiff_fibreCovPow (-θ) (p, q) 0 (by simpa using hcφ)).continuous
    refine ⟨continuous_const.mul hcont, fun X => ?_⟩
    have hibp := ibp_pow θ n q p (truncateTorusHk h1 X) _ hcφ hcφp
    rw [torusHkValueCLM_truncate] at hibp
    have hv := tbMulCLM_value_ae n hcn hp hP (W X)
    rw [lrSmul_apply, map_smul, int_eq _ _ hφc, map_smul, ← int_eq _ _ hφc]
    have e1 : ∫ y in AVenhance.unitCube,
        (torusHkValueCLM (M (W X)) : Vec 2 → ℂ) y * φ y =
        ∫ y in AVenhance.unitCube, (torusHkValueCLM (W X) : Vec 2 → ℂ) y * ((c y : ℂ) * φ y) := by
      refine integral_congr_ae ?_
      filter_upwards [hv] with y hy
      rw [hy]; ring
    have e2 : ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y *
        ((κ : ℂ) * fibreCovPow (-θ) (p, q) (fun y => (c y : ℂ) * φ y) y) =
        (κ : ℂ) * ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y *
          fibreCovPow (-θ) (p, q) (fun y => (c y : ℂ) * φ y) y := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [e2, hibp]
    simp only [ContinuousLinearMap.comp_apply, Complex.real_smul]
    rw [e1]
    push_cast
    have hWX : W X = fwdPow θ n q p (truncateTorusHk h1 X) := rfl
    rw [hWX]
    ring

theorem mul_pair (K : ℕ) {c : Vec 2 → ℝ} (hc : ContDiff ℝ (K : ℕ) c)
    (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP : ∀ l ≤ K, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P)
    (Z : TorusHk K ℂ) (ψ : Vec 2 → ℂ) :
    ∫ y in AVenhance.unitCube, (torusHkValueCLM (tbMulCLM K hc hp hP Z) : Vec 2 → ℂ) y * ψ y =
      ∫ y in AVenhance.unitCube, (torusHkValueCLM Z : Vec 2 → ℂ) y * ((c y : ℂ) * ψ y) := by
  refine integral_congr_ae ?_
  filter_upwards [tbMulCLM_value_ae K hc hp hP Z] with y hy
  rw [hy]; ring

/-- The operator of `unit1`. -/
def Unit1Op (θ : Vec 2) (n N p q : ℕ) (k : Fin 2) (h1 : n + 1 + q + p ≤ N) {c : Vec 2 → ℝ}
    (hcn : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ) :
    TorusHk N ℂ →L[ℝ] TorusHk n ℂ :=
  lrSmul (((-1 : ℝ) ^ (p + q + 1)) * κ) ((tbTwist n θ k).comp
    ((tbMulCLM (n + 1) hcn hp hP).comp ((fwdPow θ (n + 1) q p).comp (truncateTorusHk h1))))

theorem Unit1Op_norm (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n N p q : ℕ) (k : Fin 2)
    (h1 : n + 1 + q + p ≤ N) {c : Vec 2 → ℝ}
    (hcn : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ) (X : TorusHk N ℂ) :
    ‖Unit1Op θ n N p q k h1 hcn hp hP κ X‖ ≤
      |κ| * ((1 + ρ) ^ (p + q + 1) * (|cellDriftNativePrice (n + 1)| * P)) * ‖X‖ := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0 (Nat.zero_le _) 0)
  unfold Unit1Op
  rw [lrSmul_apply, norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  simp only [ContinuousLinearMap.comp_apply]
  set Y := fwdPow θ (n + 1) q p (truncateTorusHk h1 X) with hY
  have h3 := tbMulCLM_norm_le (n + 1) hcn hp hP Y
  have h4 := fwdPow_norm θ ρ hθ (n + 1) q p (truncateTorusHk h1 X)
  have h5 := truncateTorusHk_norm_le h1 X
  have h6 : ‖tbTwist n θ k (tbMulCLM (n + 1) hcn hp hP Y)‖ ≤
      (1 + ρ) * ‖tbMulCLM (n + 1) hcn hp hP Y‖ :=
    ((tbTwist n θ k).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((tbTwist_norm_le _ θ k).trans (by linarith [hθ k]))
        (norm_nonneg _))
  have hle : cellDriftNativePrice (n + 1) * P ≤ |cellDriftNativePrice (n + 1)| * P :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hP0
  have hW : ‖Y‖ ≤ (1 + ρ) ^ (p + q) * ‖X‖ :=
    h4.trans (mul_le_mul_of_nonneg_left h5 (by positivity))
  have hM : ‖tbMulCLM (n + 1) hcn hp hP Y‖ ≤
      |cellDriftNativePrice (n + 1)| * P * ((1 + ρ) ^ (p + q) * ‖X‖) :=
    h3.trans (mul_le_mul hle hW (norm_nonneg _) (by positivity))
  calc _ ≤ (1 + ρ) * ‖tbMulCLM (n + 1) hcn hp hP Y‖ := h6
    _ ≤ (1 + ρ) * (|cellDriftNativePrice (n + 1)| * P * ((1 + ρ) ^ (p + q) * ‖X‖)) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
    _ = _ := by ring

theorem Unit1Op_pair (θ : Vec 2) (n N s p q : ℕ) (k : Fin 2)
    (h1 : n + 1 + q + p ≤ N) (hs : p + q + 1 ≤ s) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + 1 + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ)
    (φ : Vec 2 → ℂ) (hφ : ContDiff ℝ (s : ℕ) φ) (hφp : AVenhance.IsZ2Periodic φ)
    (X : TorusHk N ℂ) :
    ∫ y in AVenhance.unitCube,
        (torusHkValueCLM (Unit1Op θ n N p q k h1
          (hc.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 1 + p + q))) hp hP κ X) :
          Vec 2 → ℂ) y * φ y =
      ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y *
        ((κ : ℂ) * fibreCovPow (-θ) (p, q)
          (fun y => (c y : ℂ) * fibreCovDeriv (-θ) k φ y) y) := by
  have hφc := hφ.continuous
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast (by omega : 1 ≤ s))
  have hDφ : ContDiff ℝ (p + q : ℕ) (fibreCovDeriv (-θ) k φ) :=
    contDiff_fibreCovDeriv (j := p + q) (hφ.of_le (by exact_mod_cast hs)) (-θ) k
  have hDp := isZ2Periodic_fibreCovDeriv hφp (-θ) k
  have hcφ : ContDiff ℝ (p + q : ℕ) (fun y => (c y : ℂ) * fibreCovDeriv (-θ) k φ y) :=
    contDiff_real_mul_complex (hc.of_le (by exact_mod_cast (by omega : p + q ≤ n + 1 + p + q)))
      hDφ
  have hcφp : AVenhance.IsZ2Periodic (fun y => (c y : ℂ) * fibreCovDeriv (-θ) k φ y) := by
    intro m z
    simp only
    rw [hp m z, hDp m z]
  have hibp := ibp_pow θ (n + 1) q p (truncateTorusHk h1 X) _ hcφ hcφp
  rw [torusHkValueCLM_truncate] at hibp
  set Y := fwdPow θ (n + 1) q p (truncateTorusHk h1 X) with hY
  set Z := tbMulCLM (n + 1) (hc.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 1 + p + q)))
    hp hP Y with hZ
  have hts := torusHk_integration_by_parts n θ k Z φ hφ1 hφp
  have e1 := mul_pair (n + 1) (hc.of_le (by exact_mod_cast
    (by omega : n + 1 ≤ n + 1 + p + q))) hp hP Y (fibreCovDeriv (-θ) k φ)
  have e2 : ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y *
      ((κ : ℂ) * fibreCovPow (-θ) (p, q)
        (fun y => (c y : ℂ) * fibreCovDeriv (-θ) k φ y) y) =
      (κ : ℂ) * ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y *
        fibreCovPow (-θ) (p, q) (fun y => (c y : ℂ) * fibreCovDeriv (-θ) k φ y) y := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  have hT : ∫ y in AVenhance.unitCube, (torusHkValueCLM (tbTwist n θ k Z) : Vec 2 → ℂ) y * φ y =
      -∫ y in AVenhance.unitCube, (torusHkValueCLM Y : Vec 2 → ℂ) y *
        ((c y : ℂ) * fibreCovDeriv (-θ) k φ y) := by
    rw [← e1, hts]; ring
  unfold Unit1Op
  rw [lrSmul_apply, map_smul, int_eq _ _ hφc, map_smul, ← int_eq _ _ hφc]
  simp only [ContinuousLinearMap.comp_apply, Complex.real_smul]
  rw [e2]
  change (((-1 : ℝ) ^ (p + q + 1) * κ : ℝ) : ℂ) * ∫ y in AVenhance.unitCube,
    (torusHkValueCLM (tbTwist n θ k Z) : Vec 2 → ℂ) y * φ y = _
  rw [hT]
  push_cast
  linear_combination (-(κ : ℂ)) * hibp

/-- **Forward unit term with one extra twisted derivative**: `κ D_{-θ}^{(p,q)}(c D_{-θ,k} φ)`. -/
theorem unit1 (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n N s p q : ℕ) (k : Fin 2)
    (h1 : n + 1 + q + p ≤ N) (hs : p + q + 1 ≤ s) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + 1 + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ) :
    FReal N n s (fun f z => (κ : ℂ) * fibreCovPow (-θ) (p, q)
        (fun y => (c y : ℂ) * fibreCovDeriv (-θ) k f y) z)
      (|κ| * ((1 + ρ) ^ (p + q + 1) * (|cellDriftNativePrice (n + 1)| * P))) := by
  refine ⟨Unit1Op θ n N p q k h1
    (hc.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 1 + p + q))) hp hP κ,
    Unit1Op_norm θ ρ hθ n N p q k h1 _ hp hP κ, fun φ hφ hφp => ?_⟩
  have hDφ : ContDiff ℝ (p + q : ℕ) (fibreCovDeriv (-θ) k φ) :=
    contDiff_fibreCovDeriv (j := p + q) (hφ.of_le (by exact_mod_cast hs)) (-θ) k
  have hcφ : ContDiff ℝ (p + q : ℕ) (fun y => (c y : ℂ) * fibreCovDeriv (-θ) k φ y) :=
    contDiff_real_mul_complex (hc.of_le (by exact_mod_cast (by omega : p + q ≤ n + 1 + p + q)))
      hDφ
  have hcont : Continuous (fibreCovPow (-θ) (p, q)
      (fun y => (c y : ℂ) * fibreCovDeriv (-θ) k φ y)) :=
    (contDiff_fibreCovPow (-θ) (p, q) 0 (by simpa using hcφ)).continuous
  exact ⟨continuous_const.mul hcont, fun X =>
    Unit1Op_pair θ n N s p q k h1 hs hc hp hP κ φ hφ hφp X⟩

end AVRegularity.CycleWords.Discard
end
end
