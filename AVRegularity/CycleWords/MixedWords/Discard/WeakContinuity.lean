-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.Discard.WeakContStepDuality
public import AVRegularity.CycleWords.MixedWords.Discard.WeakContStatements
import AVRegularity.CycleWords.MixedWords.Discard.WeakContFluxTerm
import AVRegularity.CycleJoint.WeightedGradientLiftComparison
import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition
import AVRegularity.CycleWords.Seam.B1PlainNeg
import AVRegularity.CycleWords.Seam.S3bRoughCore
import AVRegularity.Weighted.WordNativeSolutionPack
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleWords.Assembly
open AVRegularity.CycleWords.Seam
open scoped ENNReal
namespace AVRegularity.CycleWords.Discard

/-! # The level claim for every chain

`weakContLevelBound_of_flux : WeakContFluxStatement → WeakContLevelBoundStatement`: the level
induction of the adjoint word chain (`wordChain_level_succ_bound`, `wordChain_level_bound`)
re-run without the `L²(I; L²)` realization of the letter flux. The one-step duality is the
split-weight step `weakContStepDuality`; its hypotheses are two facts on the window of the letters,
restricted to `[a, t]`, and a bound uniform in time of the weighted norms of the
scalar reversed chains (`weakCont_reversed_weighted_sup`: the supremum form of
`reversedAdjoint_weighted_finite`, read through `weakCont_reversed_family_bound`). -/

universe u v

/-- The weighted factorial norms of the reversed adjoint chain are bounded uniformly in time
(the supremum form of `reversedAdjoint_weighted_finite`, by the same energy estimate). -/
theorem weakCont_reversed_weighted_sup (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    {η : ℝ} (hη : 0 < η) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (ϖ : ℝ) (hϖ : 0 ≤ ϖ) (m n : ℕ) {a t : ℝ} (hat : a ≤ t) (φ : PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-t) (-a)
      (fun τ z => -(v (-τ) z)) (fun _ => φ) (fun _ _ _ => 0) ψ ψw)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1 / (3 * Interior.negAdjointJetConstant Cvj m *
      (1 + (Real.sqrt η)⁻¹)))
    (hφ : weightedFactorialNormSq n ϖ 0 r m φ ≠ ⊤) :
    (⨆ τ ∈ Icc (-t) (-a), weightedFactorialNormSq n ϖ 0 r m (ψ 0 () τ)) ≠ ⊤ := by
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  set A := Interior.negAdjointJetConstant Cvj m with hAdef
  have hA : 1 ≤ A := Interior.one_le_negAdjointJetConstant Cvj m
  set strain := A / Real.sqrt η with hstraindef
  have hstrain0 : 0 ≤ strain := by positivity
  have hP : 1 ≤ 1 + (Real.sqrt η)⁻¹ := by
    have := inv_pos.mpr hsη
    linarith
  have hr3 : r ≤ 1 / 3 := by
    refine hr1.trans ?_
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hstrain : strain * r ^ 2 ≤ 1 / 8 := by
    set ρ := 1 / (3 * A * (1 + (Real.sqrt η)⁻¹)) with hρdef
    have hρ : 0 < ρ := by positivity
    have hsP : Real.sqrt η * (1 + (Real.sqrt η)⁻¹) = Real.sqrt η + 1 := by
      field_simp
    have hX : 1 ≤ A * (Real.sqrt η * (1 + (Real.sqrt η)⁻¹)) * (1 + (Real.sqrt η)⁻¹) := by
      rw [hsP]
      have h1 : 1 ≤ Real.sqrt η + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ A * (Real.sqrt η + 1) * (1 + (Real.sqrt η)⁻¹) := by gcongr
    have he : strain * ρ ^ 2 =
        1 / (9 * (A * (Real.sqrt η * (1 + (Real.sqrt η)⁻¹)) * (1 + (Real.sqrt η)⁻¹))) := by
      rw [hstraindef, hρdef]
      field_simp
      ring
    have hρ8 : strain * ρ ^ 2 ≤ 1 / 8 := by
      rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc strain * r ^ 2 ≤ strain * ρ ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hr1 2) hstrain0
      _ ≤ 1 / 8 := hρ8
  set vr : ℝ → Vec 2 → Vec 2 := fun τ z => -(v (-τ) z) with hvrdef
  have hvrD : IsCellDrift vr := cellDrift_timeReverse hv
  have hvrs : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (vr τ) := fun τ => (hvs (-τ)).neg
  set V := |Cvj 0| / Real.sqrt η with hVdef
  have hV : 0 ≤ V := by positivity
  have hbv : ∀ τ z, ‖vr τ z‖ ≤ V := fun τ x => by
    have h := reversedDrift_iteratedFDeriv_le hη v hvs Cvj hvj 0 τ x
    rw [norm_iteratedFDeriv_zero] at h
    rw [hVdef, le_div_iff₀ hsη, mul_comm]
    exact h.trans (le_abs_self _)
  have hjets : ∀ l, 1 ≤ l → l ≤ m → ∀ τ x,
      ‖coefficientDerivativeArray (driftCoefficient (vr τ)) l x‖ ≤ strain * (l.factorial : ℝ) :=
    fun l _ hlm τ x => reversedDrift_jets hη v hvs Cvj hvj m τ l hlm x
  obtain ⟨W, -⟩ := crudeChartWeights_exists (fun τ => G (-τ)) (cellMetric_timeReverse hG) vr V hV
    hbv (-t) (t - a + 1) ϖ (by linarith) hϖ n
  have hsol : IsPlaneChainFrom (h := fun _ : Unit => ℝ)
      (geometryScalarData 2 (fun τ _ => G (-τ))) (fun _ _ => m) (-t) (-a) vr
      (fun _ _ => φ) (fun _ _ => 0) (fun _ _ => ψ 0 ()) (fun _ _ => ψw 0 ()) := by
    unfold IsPlaneChain at hψ
    unfold IsPlaneChainFrom
    convert hψ using 2
    all_goals first
      | rfl
      | (rename_i q
         obtain ⟨j, x⟩ := q
         obtain rfl : j = 0 := Fin.fin_one_eq_zero j
         rfl)
  have hfin := constantMetric_scalar_component_energy_ne_top (E := ℝ) (-t) (-a) (by linarith) m m n
    le_rfl vr hvrD hvrs strain r hstrain0 hr (by linarith) hstrain hjets
    (fun τ => G (-τ)) (cellMetric_timeReverse hG) (-t) (t - a + 1) ϖ 0
    (fun k => 1 + crudeChartRate ϖ V k * (t - a + 1)) W le_rfl (by linarith) φ (fun _ => 0)
    (planeHk_zero_time_memLp _ _) (ψ 0 ()) (ψw 0 ()) hsol hφ (by simp)
  exact ne_top_of_le_ne_top hfin le_self_add


section Readout

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- One weighted jet of a carrier is controlled by its weighted factorial norm. -/
theorem weakCont_weighted_jet_lintegral_le {ϖ r : ℝ} (hr : 0 < r) {K : ℕ}
    (U : PlaneHk Set.univ K E) (n j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    ∫⁻ z, ENNReal.ofReal ((polynomialMomentRoot ϖ z ^ n * ‖planeJetOrder U j w z‖) ^ 2) ≤
      ENNReal.ofReal (((j.factorial : ℝ)) ^ 2 / r ^ (2 * j)) *
        weightedFactorialNormSq n ϖ 0 r K U := by
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hterm : ENNReal.ofReal (r ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - (0 : Vec 2) 0) ^ 2 +
        (z 1 - (0 : Vec 2) 1) ^ 2)) ^ n * ∑ w : DerivativeWord2 j,
          ‖planeJetOrder U j w z‖ ^ 2) ≤ weightedFactorialNormSq n ϖ 0 r K U := by
    unfold weightedFactorialNormSq
    exact Finset.single_le_sum (f := fun j => ENNReal.ofReal (r ^ (2 * j) /
      ((j.factorial : ℝ)) ^ 2) * ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - (0 : Vec 2) 0) ^ 2 +
        (z 1 - (0 : Vec 2) 1) ^ 2)) ^ n * ∑ w : DerivativeWord2 j,
          ‖planeJetOrder U j w z‖ ^ 2)) (fun _ _ => zero_le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hle : ∫⁻ z, ENNReal.ofReal ((polynomialMomentRoot ϖ z ^ n * ‖planeJetOrder U j w z‖) ^ 2) ≤
      ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - (0 : Vec 2) 0) ^ 2 +
        (z 1 - (0 : Vec 2) 1) ^ 2)) ^ n * ∑ w : DerivativeWord2 j,
          ‖planeJetOrder U j w z‖ ^ 2) := by
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    rw [mul_pow, polynomialMomentRoot_pow_sq]
    unfold Weighted.planeMomentPolynomial
    simp only [Pi.zero_apply, sub_zero]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
      (f := fun w => ‖planeJetOrder U j w z‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w))
      (by positivity)
  have hone : ((j.factorial : ℝ)) ^ 2 / r ^ (2 * j) * (r ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) =
      1 := by
    have hr' : r ^ (2 * j) ≠ 0 := (pow_pos hr _).ne'
    field_simp
  refine hle.trans ?_
  refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl hterm)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hone, ENNReal.ofReal_one, one_mul]

end Readout

/-- An extended real whose square is at most `ofReal y` is at most `ofReal (√y)`. -/
theorem weakCont_le_ofReal_sqrt {x : ℝ≥0∞} {y : ℝ} (hy : 0 ≤ y)
    (hx : x ^ 2 ≤ ENNReal.ofReal y) : x ≤ ENNReal.ofReal (Real.sqrt y) := by
  by_contra hcon
  push Not at hcon
  have h1 : ENNReal.ofReal (Real.sqrt y) ^ 2 < x ^ 2 := by
    rw [pow_two, pow_two]
    exact ENNReal.mul_lt_mul hcon hcon
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hy] at h1
  exact absurd hx (not_le.mpr h1)

/-- The weighted `L²` norm of a real function that is a jet of a carrier. -/
theorem weakCont_weighted_readout_le {ϖ r : ℝ} (hr : 0 < r) {K : ℕ}
    (U : PlaneHk Set.univ K ℝ) (n j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) (G : Vec 2 → ℝ)
    (hGm : AEStronglyMeasurable G volume) (hG : G =ᵐ[volume] planeJetOrder U j w)
    (Wb : ℝ≥0∞) (hWb : Wb ≠ ⊤) (hU : weightedFactorialNormSq n ϖ 0 r K U ≤ Wb) :
    eLpNorm (fun z => polynomialMomentRoot ϖ z ^ n * G z) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (((j.factorial : ℝ)) ^ 2 / r ^ (2 * j) * Wb.toReal)) := by
  have hfm : AEStronglyMeasurable (fun z => polynomialMomentRoot ϖ z ^ n * G z) volume :=
    ((polynomialMomentRoot_continuous ϖ).pow n).aestronglyMeasurable.mul hGm
  have hc0 : (0 : ℝ) ≤ ((j.factorial : ℝ)) ^ 2 / r ^ (2 * j) := by positivity
  refine weakCont_le_ofReal_sqrt (mul_nonneg hc0 ENNReal.toReal_nonneg) ?_
  rw [eLpNorm_two_sq_real _ hfm]
  have hcongr : ∫⁻ z, ENNReal.ofReal ((polynomialMomentRoot ϖ z ^ n * G z) ^ 2) =
      ∫⁻ z, ENNReal.ofReal ((polynomialMomentRoot ϖ z ^ n * ‖planeJetOrder U j w z‖) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hG] with z hz
    rw [hz, mul_pow, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hcongr]
  refine (weakCont_weighted_jet_lintegral_le hr U n j hj w).trans ?_
  rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_toReal hWb]
  exact mul_le_mul' le_rfl hU

/-- The value and the gradient of the `H¹` truncation of a carrier, with the weight. -/
theorem weakCont_reversed_readout_bounds {mm : ℕ} (hmm : 1 ≤ mm) (U : PlaneHk Set.univ mm ℝ)
    (n : ℕ) (ϖ r₀ : ℝ) (hr₀ : 0 < r₀) (Wb : ℝ≥0∞) (hWb : Wb ≠ ⊤)
    (hU : weightedFactorialNormSq n ϖ 0 r₀ mm U ≤ Wb) :
    eLpNorm (fun z => polynomialMomentRoot ϖ z ^ n *
        (planeHkValueOperator 1 (truncatePlaneHk hmm U) : Vec 2 → ℝ) z) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (((Nat.factorial 0 : ℝ)) ^ 2 / r₀ ^ (2 * 0) * Wb.toReal)) ∧
    ∀ k : Fin 2, eLpNorm (fun z => polynomialMomentRoot ϖ z ^ n *
        (planeH1GradientOperator (truncatePlaneHk hmm U) k : Vec 2 → ℝ) z) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (((Nat.factorial 1 : ℝ)) ^ 2 / r₀ ^ (2 * 1) * Wb.toReal)) := by
  refine ⟨?_, fun k => ?_⟩
  · refine weakCont_weighted_readout_le hr₀ U n 0 (Nat.zero_le _) Fin.elim0 _
      (Lp.aestronglyMeasurable _) ?_ Wb hWb hU
    have h1 := planeJetL2_value_ae (truncatePlaneHk hmm U)
    rw [planeJetOrder_truncate hmm (Nat.zero_le _) U] at h1
    exact h1
  · refine weakCont_weighted_readout_le hr₀ U n 1 hmm (fun _ => k) _
      (Lp.aestronglyMeasurable _) ?_ Wb hWb hU
    rw [planeH1Gradient_truncate_eq]
    filter_upwards [planeJetL2_ae U (truncateJetIndex hmm ⟨⟨1, by omega⟩, fun _ => k⟩)]
      with z hz
    rw [hz]
    simp only [planeJetOrder, hmm, dite_true]
    rfl

/-- **Uniform weighted bounds of a finite family of reversed chains**, in the form of the
hypothesis of `WeakContStepDualityStatement`. -/
theorem weakCont_reversed_family_bound {ι : Type*} [Fintype ι] {n : ι → Type*}
    [∀ x, Fintype (n x)] {mm : ℕ} (hmm : 1 ≤ mm) (a t : ℝ)
    (ψ : ∀ x, n x → ℝ → PlaneHk Set.univ mm ℝ) (q : ℕ) (ϖ r₀ : ℝ) (hr₀ : 0 < r₀)
    (hsup : ∀ x e, (⨆ τ ∈ Set.Icc (-t) (-a),
      weightedFactorialNormSq q ϖ 0 r₀ mm (ψ x e τ)) ≠ ⊤) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ r ∈ Set.Icc a t, ∀ x e,
      eLpNorm (fun z => polynomialMomentRoot ϖ z ^ q *
        (planeHkValueOperator 1 (truncatePlaneHk hmm (ψ x e (-r))) : Vec 2 → ℝ) z) 2 volume ≤
          ENNReal.ofReal Bd ∧
      ∀ k : Fin 2, eLpNorm (fun z => polynomialMomentRoot ϖ z ^ q *
        (planeH1GradientOperator (truncatePlaneHk hmm (ψ x e (-r))) k : Vec 2 → ℝ) z) 2 volume ≤
          ENNReal.ofReal Bd := by
  set bx : ∀ x, n x → ℝ := fun x e =>
    Real.sqrt (((Nat.factorial 0 : ℝ)) ^ 2 / r₀ ^ (2 * 0) *
      (⨆ τ ∈ Set.Icc (-t) (-a), weightedFactorialNormSq q ϖ 0 r₀ mm (ψ x e τ)).toReal) +
    Real.sqrt (((Nat.factorial 1 : ℝ)) ^ 2 / r₀ ^ (2 * 1) *
      (⨆ τ ∈ Set.Icc (-t) (-a), weightedFactorialNormSq q ϖ 0 r₀ mm (ψ x e τ)).toReal) with hbx
  have hbx0 : ∀ x e, 0 ≤ bx x e := fun x e => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsingle : ∀ x e, bx x e ≤ ∑ x, ∑ e, bx x e := by
    intro x e
    refine le_trans ?_ (Finset.single_le_sum (f := fun x => ∑ e, bx x e)
      (fun x _ => Finset.sum_nonneg fun e _ => hbx0 x e) (Finset.mem_univ x))
    exact Finset.single_le_sum (f := fun e => bx x e) (fun e _ => hbx0 x e) (Finset.mem_univ e)
  refine ⟨∑ x, ∑ e, bx x e, Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun e _ => hbx0 x e,
    ?_⟩
  intro r hr x e
  have hle : weightedFactorialNormSq q ϖ 0 r₀ mm (ψ x e (-r)) ≤
      ⨆ τ ∈ Set.Icc (-t) (-a), weightedFactorialNormSq q ϖ 0 r₀ mm (ψ x e τ) :=
    le_iSup₂ (f := fun τ (_ : τ ∈ Set.Icc (-t) (-a)) =>
      weightedFactorialNormSq q ϖ 0 r₀ mm (ψ x e τ)) (-r) ⟨neg_le_neg hr.2, neg_le_neg hr.1⟩
  obtain ⟨hv, hg⟩ := weakCont_reversed_readout_bounds hmm (ψ x e (-r)) q ϖ r₀ hr₀ _ (hsup x e) hle
  refine ⟨hv.trans (ENNReal.ofReal_le_ofReal ?_), fun k => (hg k).trans
    (ENNReal.ofReal_le_ofReal ?_)⟩
  · exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (hsingle x e)
  · exact (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans (hsingle x e)

variable {ι : Type u} [Fintype ι] {h : ι → Type v}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- **The step of the level claim for every chain** (no flux realization; the split-weight
step `weakContStepDuality` with the two facts of (17a) on the window of the letters). -/
theorem weakCont_level_succ_bound (hFlux : WeakContFluxStatement.{u, v}) (hD : 2 ≤ D) (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : ∀ i, IsCycleLetter π (letters i) (Set.Icc a b ×ˢ Set.univ) J H)
    (hmeas : ∀ i x y o, ∀ γ ∈ (letters i).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t)) (g : ℝ)
    (hg0 : 0 ≤ g) (hg : g ≤ 1 / 32) (hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    {η : ℝ} (hη : 0 < η) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (M : ℝ) (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (P : ℝ) (hP : 1 ≤ P) (Ca : ℕ → ℕ → ℝ)
    (hCa : ∀ k p, 0 ≤ Ca k p) (Qa : ℕ → ℕ)
    (hadj : ∀ (k p : ℕ) (s t : ℝ), a ≤ s → s ≤ t → t ≤ b →
      ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
        (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
        (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
        IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
          (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
        weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
          ENNReal.ofReal (Ca k p * P ^ Qa k * (1 + (t - s)) ^ Qa k) *
            weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
              (fun x a w' => planeJetOrder (f x) a w'))
    (X₀ : Vec 2) (κ : Fin (N + 1) → ι → ℕ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (U : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (Uw : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hsol : IsPlaneChain (wordChainData G letters X₀ (ζ * ϖ)) κ a b v f (fun _ _ _ => 0) U Uw)
    (jj : Fin N) (lowj : ℕ) (hlowj : 1 ≤ lowj) (Cj : ℕ → ℕ → ℝ) (hCj : ∀ n p, 0 ≤ Cj n p)
    (Qj : ℕ → ℕ) (Fj : ℕ → ℝ≥0∞)
    (ih : ∀ n : ℕ, lowj ≤ n → n ≤ J + 1 → ∀ (p : ℕ) (r : ℝ), r ∈ Set.Icc a b →
      ∀ T : ∀ x, PlaneHk Set.univ n (h x), (∀ x, IsRapidPlaneHk ϖ (T x)) →
        ENNReal.ofReal |∑ x, (π x)⁻¹ * inner ℝ
            (planeHkValueOperator (κ jj.castSucc x) (U jj.castSucc x r))
            (planeHkValueOperator n (T x))| ≤
          ENNReal.ofReal (Cj n p * P ^ Qj n * (1 + (r - a)) ^ Qj n) *
            weightedJetNorm π (-(p : ℝ)) n ϖ 1 (fun x i w z => planeJetOrder (T x) i w z) *
            Fj p)
    (n : ℕ) (hn : lowj ≤ n) (hnJ : n + (letters jj).order ≤ J + 1) (p : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (Φ : ∀ x, PlaneHk Set.univ (n + (letters jj).order) (h x))
    (hΦ : ∀ x, IsRapidPlaneHk ϖ (Φ x)) :
    ENNReal.ofReal |∑ x, (π x)⁻¹ * inner ℝ (planeHkValueOperator (κ jj.succ x) (U jj.succ x t))
        (planeHkValueOperator (n + (letters jj).order) (Φ x))| ≤
      ENNReal.ofReal (Cj n (p + (letters jj).slow) *
          letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
          ((letters jj).theta * (if (letters jj).positive then ζ else 1)) *
          (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) *
          P ^ (Qj n + Qa (n + (letters jj).order) + 1) *
          (1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order) + 1)) *
        weightedJetNorm π (-(p : ℝ)) (n + (letters jj).order) ϖ 1
          (fun x i w z => planeJetOrder (Φ x) i w z) *
        Fj (p + (letters jj).slow) := by
  have hd2 : 2 ≤ (letters jj).order := (hL jj).order_ge
  have hn1 : 1 ≤ n := hlowj.trans hn
  have hn1' : 1 ≤ n + (letters jj).order := by omega
  -- the reversed adjoint chains of the coordinates of the test
  set B : ∀ x, OrthonormalBasis (Fin (Module.finrank ℝ (h x))) ℝ (h x) :=
    fun x => stdOrthonormalBasis ℝ (h x)
  choose ψ ψw hψ using fun x (e : Fin (Module.finrank ℝ (h x))) =>
    exists_reversedAdjoint G hG g hg0 hg hGn v hv hvs hη Cvj hvj (n + (letters jj).order) ht.1
      (planeHkCoord (B x e) (Φ x))
  -- rapid decay of the assembled adjoint family
  set r₀ := 1 / (3 * Interior.negAdjointJetConstant Cvj (n + (letters jj).order) * (1 + (Real.sqrt η)⁻¹)) with hr₀def
  have hr₀ : 0 < r₀ := by
    have h1 := Interior.one_le_negAdjointJetConstant Cvj (n + (letters jj).order)
    have h2 : 0 < (Real.sqrt η)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hη)
    rw [hr₀def]
    positivity
  have hΨr : ∀ τ ∈ Set.Icc (-t) (-a), ∀ x,
      IsRapidPlaneHk ϖ (planeHkAssemble (B x) (fun e => ψ x e 0 () τ)) := fun τ hτ x =>
    rapid_assemble (B x) _ fun e => rapid_of_weightedFactorialNormSq hr₀ _ fun q =>
      reversedAdjoint_weighted_finite G hG v hv hvs hη Cvj hvj ϖ hϖ.le (n + (letters jj).order) q ht.1 _ (ψ x e)
        (ψw x e) (hψ x e) r₀ hr₀ le_rfl
        (weightedFactorialNormSq_ne_top_of_rapid _ (rapid_coord _ _ (hΦ x)) q r₀) τ hτ
  have hΨr' : ∀ r ∈ Set.Icc a t, ∀ x,
      IsRapidPlaneHk ϖ (planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))) := fun r hr =>
    hΨr (-r) ⟨neg_le_neg hr.2, neg_le_neg hr.1⟩
  -- the forward chain on `[a, t]`
  have hfrom : IsPlaneChainFrom (wordChainData G letters X₀ (ζ * ϖ)) κ a b v
      (wordLevelDatum κ f) (fun _ _ _ => 0) U Uw := hsol
  have hrest := CycleJointProofs.planeChainFrom_restart_subwindow _ κ a b a t le_rfl ht.1 ht.2
    v _ _ U Uw hfrom
  have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl ht.2
  -- the almost-every-time facts of the letter
  have hregAE := letterTermRegular_ae π hπ (letters jj) a b J H (hL jj) ϖ ζ hϖ hϖ1 hζ hζ1 X₀ n (letters jj).order
    hnJ
  have hbndAE := letterTranspose_weightedJetNorm_le_ae π hπ (letters jj) a b J H (hL jj) ϖ ζ hϖ
    hϖ1 hζ hζ1 X₀ (fun q : Fin (N + 1) × ι => κ q.1 q.2) (fun x => (jj.succ, x))
    (fun u => (jj.castSucc, u)) n (letters jj).order hnJ
  have hrapAE := letterTransposeHk_rapid_ae π hπ (letters jj) a b J H (hL jj) ϖ ζ hϖ hϖ1 hζ hζ1
    X₀ (fun q : Fin (N + 1) × ι => κ q.1 q.2) (fun x => (jj.succ, x))
    (fun u => (jj.castSucc, u)) n (letters jj).order hnJ
  have hregΨ : ∀ r ∈ Set.Icc a t, ∀ x (i : JetIndex2 (n + (letters jj).order)), MemLp (fun z =>
      polynomialMomentRoot ϖ z ^ (letters jj).slow *
        ‖(planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))).toFunction.jet i z‖) 2 volume := by
    intro r hr x i
    have h1 := hΨr' r hr x (letters jj).slow i.1.val i.2
    simpa only [planeJetOrder, Nat.le_of_lt_succ i.1.isLt, dite_true, Fin.eta, Sigma.eta] using h1
  have hreg : ∀ᵐ r ∂volume.restrict (Set.Icc a t), LetterTermRegular (letters jj)
      (if (letters jj).positive then 1 else 0) X₀ (ζ * ϖ) r n (letters jj).order
      (fun x => planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hregAE,
      ae_restrict_mem measurableSet_Icc] with r hr hrmem
    exact hr _ (hregΨ r hrmem)
  -- the one-step duality
  have hempty : ∀ x u (o : Finset.Icc 2 D), (letters jj).order < o.1 → (letters jj).edge x u o = [] :=
    fun x u o ho => (hL jj).edge_order x u o ho
  -- the two facts of (17a) on the window of the letters, restricted to `[a, t]`
  unfold WeakContFluxStatement at hFlux
  have hfl := fun x => hFlux π hπ letters a b J H jj x (hL jj)
    (fun u o k w X z => hmeas jj x u o _ (List.get_mem _ _) w X z) ϖ ζ hϖ hϖ1 hζ hζ1 X₀ κ
    (fun q => Uw q.1 q.2) (fun u => hfrom.2.1 (jj.castSucc, u))
  have hcut : ∀ x (M : ℕ), ∃ S : ℝ → PlaneFluxL2 (h x),
      MemLp S 2 (volume.restrict (Set.Icc a t)) ∧
      ∀ᵐ r ∂volume.restrict (Set.Icc a t), ∀ k, ∀ᵐ z ∂volume,
        z ∈ Metric.ball (0 : Vec 2) ((M : ℝ) + 1) → S r k z =
          wordChainPreviousFlux letters X₀ (ζ * ϖ) κ (fun p => Uw p.1 p.2 r) (jj.succ, x) r z k := by
    intro x M
    obtain ⟨S, hSl, hS⟩ := (hfl x).1 M
    exact ⟨S, hSl.mono_measure (Measure.restrict_mono hsub le_rfl),
      ae_restrict_of_ae_restrict_of_subset hsub hS⟩
  have hwt : ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ r ∂volume.restrict (Set.Icc a t), ∀ k : Fin 2,
      eLpNorm (fun z => (polynomialMomentRoot ϖ z ^ (letters jj).slow)⁻¹ •
          wordChainPreviousFlux letters X₀ (ζ * ϖ) κ (fun p => Uw p.1 p.2 r) (jj.succ, x) r z k)
          2 volume ≤
        ENNReal.ofReal (C * ∑ u, ‖Uw jj.castSucc u r‖) := by
    intro x
    obtain ⟨C, hC, hw⟩ := (hfl x).2
    exact ⟨C, hC, ae_restrict_of_ae_restrict_of_subset hsub hw⟩
  -- the reversed chains are rapidly decaying uniformly in time
  have hrap := weakCont_reversed_family_bound (show 1 ≤ n + (letters jj).order by omega) a t
    (fun x (e : Fin (Module.finrank ℝ (h x))) τ => ψ x e 0 () τ) (letters jj).slow ϖ r₀ hr₀
    (fun x e => weakCont_reversed_weighted_sup G hG v hv hvs hη Cvj hvj ϖ hϖ.le
      (n + (letters jj).order) (letters jj).slow ht.1 _ (ψ x e) (ψw x e) (hψ x e) r₀ hr₀ le_rfl
      (weightedFactorialNormSq_ne_top_of_rapid _ (rapid_coord _ _ (hΦ x)) (letters jj).slow r₀))
  have hdual := weakContStepDuality hD π hπ letters a t ht.1 G hG v hv M hb ϖ ζ X₀ κ
    (fun q => U q.1 q.2 a) (fun q => U q.1 q.2) (fun q => Uw q.1 q.2) hrest jj hcut hwt B n
    (letters jj).order (by omega) hempty Φ ψ ψw hψ hreg hrap
  have hUa : ∀ x, U jj.succ x a = 0 := fun x => by
    have h0 := hfrom.2.2.2.1 (jj.succ, x)
    simpa only [wordLevelDatum_succ] using h0
  simp only [hUa, ContinuousLinearMap.map_zero, inner_zero_left, mul_zero, Finset.sum_const_zero,
    zero_sub] at hdual
  rw [hdual, abs_neg]
  -- the constants
  have hθζ : 0 ≤ (letters jj).theta * (if (letters jj).positive then ζ else 1) :=
    mul_nonneg (hL jj).theta_nonneg (by split <;> positivity)
  have hLθ : 0 ≤ letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
      ((letters jj).theta * (if (letters jj).positive then ζ else 1)) :=
    mul_nonneg (letterNormConst_nonneg _ _ _ _ _) hθζ
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hsq : 0 ≤ Real.sqrt (↑(n + (letters jj).order) + 1) := Real.sqrt_nonneg _
  have hK0 : 0 ≤ Cj n (p + (letters jj).slow) *
      (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
        ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
      (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) *
      P ^ Qj n * P ^ Qa (n + (letters jj).order) := by
    have := hCj n (p + (letters jj).slow)
    have := hCa (n + (letters jj).order) p
    positivity
  have hsubI : Set.Ioc a t ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self.trans hsub
  refine (ofReal_abs_intervalIntegral_le ht.1 (Bd := ENNReal.ofReal
      (Cj n (p + (letters jj).slow) *
        (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
          ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
        (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) *
        P ^ Qj n * P ^ Qa (n + (letters jj).order) *
        (1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order)) ) *
      weightedJetNorm π (-(p : ℝ)) (n + (letters jj).order) ϖ 1
        (fun x i w z => planeJetOrder (Φ x) i w z) * Fj (p + (letters jj).slow)) ?_).trans ?_
  · -- the integrand, almost everywhere
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubI hregAE,
      ae_restrict_of_ae_restrict_of_subset hsubI hbndAE,
      ae_restrict_of_ae_restrict_of_subset hsubI hrapAE, ae_restrict_mem measurableSet_Ioc]
      with r hr1 hr2 hr3 hrI
    have hrab : r ∈ Set.Icc a b := hsubI hrI
    have hrat : r ∈ Set.Icc a t := Set.Ioc_subset_Icc_self hrI
    have hregr := hr1 _ (hregΨ r hrat)
    have hgr := letterTranspose_pairing_eq π (letters jj) (fun q : Fin (N + 1) × ι => κ q.1 q.2)
      (fun x => (jj.succ, x)) (fun u => (jj.castSucc, u))
      (if (letters jj).positive then 1 else 0) X₀ (ζ * ϖ) r n (letters jj).order
      (fun x => planeHkAssemble (B x) (fun e => ψ x e 0 () (-r))) hregr
      (fun u => U jj.castSucc u r)
    beta_reduce at hgr
    have hih := ih n hn ((Nat.le_add_right n (letters jj).order).trans hnJ)
      (p + (letters jj).slow) r hrab _ (hr3 _ hregr fun x => hΨr' r hrat x)
    have hLb := hr2 _ hregr (p : ℝ) (letters jj).slow le_rfl
    have hvb := reversedAdjoint_vector_bound π B G v ϖ P Ca Qa hadj (n + (letters jj).order) p
      ht.2 Φ ψ ψw hψ r hrat.1 hrat.2
    have hcast : (-(((p + (letters jj).slow : ℕ) : ℝ))) = -((p : ℝ) + ((letters jj).slow : ℝ)) := by
      push_cast
      ring
    rw [hcast] at hih
    have h1 := hgr ▸ hih
    rw [← Real.enorm_eq_ofReal_abs] at h1
    have hx0 : 0 ≤ Cj n (p + (letters jj).slow) * P ^ Qj n * (1 + (r - a)) ^ Qj n := by
      have := hCj n (p + (letters jj).slow)
      have : 0 ≤ 1 + (r - a) := by linarith [hrat.1]
      positivity
    have hy0 : 0 ≤ ((n + 1 : ℕ) : ℝ) * ((n + (letters jj).order).factorial : ℝ) *
        (letterTransposeConst n (letters jj).order J (letters jj).slow (letters jj).positive ζ *
          (letters jj).theta) :=
      mul_nonneg (by positivity) (mul_nonneg (letterTransposeConst_nonneg _ _ _ _ _ _ hζ)
        (hL jj).theta_nonneg)
    refine (ennreal_chain_le hx0 hy0 hsq h1 hLb hvb).trans ?_
    refine mul_le_mul_left (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _) _
    rw [letterNorm_eq]
    exact step_constants_le _ _ (hCj _ _) hLθ hsq (hCa _ _) hP0 hrat.1 hrat.2
  · -- the time integration
    have hta : 0 ≤ t - a := by linarith [ht.1]
    have hX : 0 ≤ Cj n (p + (letters jj).slow) *
        (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
          ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
        (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) *
        P ^ Qj n * P ^ Qa (n + (letters jj).order) *
        (1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order)) :=
      mul_nonneg hK0 (pow_nonneg (by linarith) _)
    rw [mul_right_comm, mul_right_comm (ENNReal.ofReal _) _ (ENNReal.ofReal (t - a)),
      ← ENNReal.ofReal_mul hX]
    refine mul_le_mul_left (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _) _
    have h1 : (t - a) ≤ 1 + (t - a) := by linarith
    have hPP : P ^ Qj n * P ^ Qa (n + (letters jj).order) ≤
        P ^ (Qj n + Qa (n + (letters jj).order) + 1) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hP (Nat.le_succ _)
    have hC1 : 0 ≤ Cj n (p + (letters jj).slow) *
        (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
          ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
        (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) := by
      have := hCj n (p + (letters jj).slow)
      have := hCa (n + (letters jj).order) p
      positivity
    calc Cj n (p + (letters jj).slow) *
          (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
            ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
          (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p) *
          P ^ Qj n * P ^ Qa (n + (letters jj).order) *
          (1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order)) * (t - a)
        = (Cj n (p + (letters jj).slow) *
            (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
              ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
            (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p)) *
          (P ^ Qj n * P ^ Qa (n + (letters jj).order)) *
          ((1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order)) * (t - a)) := by ring
      _ ≤ (Cj n (p + (letters jj).slow) *
            (letterNormConst n (letters jj).order J (letters jj).slow (letters jj).positive *
              ((letters jj).theta * (if (letters jj).positive then ζ else 1))) *
            (Real.sqrt (↑(n + (letters jj).order) + 1) * Ca (n + (letters jj).order) p)) *
          P ^ (Qj n + Qa (n + (letters jj).order) + 1) *
          (1 + (t - a)) ^ (Qj n + Qa (n + (letters jj).order) + 1) := by
          rw [pow_succ (1 + (t - a))]
          gcongr
      _ = _ := by ring


/-- **The level claim for every chain** (`wordChain_level_bound` without its flux hypothesis). -/
theorem weakCont_level_bound (hFlux : WeakContFluxStatement.{u, v}) (hD : 2 ≤ D) (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : ∀ i, IsCycleLetter π (letters i) (Set.Icc a b ×ˢ Set.univ) J H)
    (hmeas : ∀ i x y o, ∀ γ ∈ (letters i).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t)) (g : ℝ)
    (hg0 : 0 ≤ g) (hg : g ≤ 1 / 32) (hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    {η : ℝ} (hη : 0 < η) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (M : ℝ) (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (P : ℝ) (hP : 1 ≤ P) (Ca : ℕ → ℕ → ℝ)
    (hCa : ∀ k p, 0 ≤ Ca k p) (Qa : ℕ → ℕ)
    (hadj : ∀ (k p : ℕ) (s t : ℝ), a ≤ s → s ≤ t → t ≤ b →
      ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
        (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
        (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
        IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
          (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
        weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
          ENNReal.ofReal (Ca k p * P ^ Qa k * (1 + (t - s)) ^ Qa k) *
            weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
              (fun x a w' => planeJetOrder (f x) a w'))
    (X₀ : Vec 2) (κ : Fin (N + 1) → ι → ℕ) (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (U : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (Uw : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hsol : IsPlaneChain (wordChainData G letters X₀ (ζ * ϖ)) κ a b v f (fun _ _ _ => 0) U Uw) :
    ∀ (j : ℕ) (hj : j ≤ N) (m : ℕ), (∑ i ∈ Finset.range j, wordOrders letters i) + 1 ≤ m →
      m ≤ J + 1 → ∀ (p : ℕ) (t : ℝ), t ∈ Set.Icc a b →
      ∀ Φ : ∀ x, PlaneHk Set.univ m (h x), (∀ x, IsRapidPlaneHk ϖ (Φ x)) →
        ENNReal.ofReal |∑ x, (π x)⁻¹ * inner ℝ
            (planeHkValueOperator (κ ⟨j, Nat.lt_succ_of_le hj⟩ x)
              (U ⟨j, Nat.lt_succ_of_le hj⟩ x t))
            (planeHkValueOperator m (Φ x))| ≤
          ENNReal.ofReal (levelC Ca (wordOrders letters) (wordSlows letters)
              (wordLetterConsts letters J) j m p * levelTheta (wordAmplitudes letters ζ) j *
              P ^ levelQ Qa (wordOrders letters) j m *
              (1 + (t - a)) ^ levelQ Qa (wordOrders letters) j m) *
            weightedJetNorm π (-(p : ℝ)) m ϖ 1 (fun x i w z => planeJetOrder (Φ x) i w z) *
            weightedJetNorm π ((p + ∑ i ∈ Finset.range j, wordSlows letters i : ℕ) : ℝ) 0 ϖ 1
              (fun x i w z => planeJetOrder (f x) i w z) := by
  have hLc : ∀ j n, 0 ≤ wordLetterConsts letters J j n := fun j n =>
    letterNormConst_nonneg _ _ _ _ _
  have hθ : ∀ i, 0 ≤ wordAmplitudes letters ζ i := by
    intro i
    unfold wordAmplitudes wordAt
    split_ifs
    · exact mul_nonneg (hL _).theta_nonneg (by split <;> positivity)
    · exact zero_le_one
  intro j
  induction j with
  | zero =>
    intro hj m hm hmJ p t ht Φ _
    have h0 := wordChain_level_zero_bound hD π hπ letters a b G hG g hg0 hg hGn v hv hvs hη Cvj
      hvj M hb ϖ (ζ * ϖ) P Ca Qa hadj X₀ κ f U Uw hsol m (by simpa using hm) p t ht Φ
    refine h0.trans (le_of_eq ?_)
    simp only [levelC, levelTheta, levelQ, Finset.prod_range_zero, Finset.sum_range_zero,
      add_zero, mul_one]
  | succ j ih =>
    intro hj m hm hmJ p t ht Φ hΦ
    set jj : Fin N := ⟨j, hj⟩ with hjjdef
    have hord : wordOrders letters j = (letters jj).order := wordAt_of_lt _ _ hj
    have hslow : wordSlows letters j = (letters jj).slow := wordAt_of_lt _ _ hj
    have hpos : wordAt (fun i => (letters i).positive) false j = (letters jj).positive :=
      wordAt_of_lt _ _ hj
    have hamp : wordAmplitudes letters ζ j =
        (letters jj).theta * (if (letters jj).positive then ζ else 1) := wordAt_of_lt _ _ hj
    rw [Finset.sum_range_succ, hord] at hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + (letters jj).order := ⟨m - (letters jj).order, by omega⟩
    have hstep := weakCont_level_succ_bound hFlux hD π hπ letters a b J H hL hmeas G hG g hg0 hg hGn v hv
      hvs hη Cvj hvj M hb ϖ ζ hϖ hϖ1 hζ hζ1 P hP Ca hCa Qa hadj X₀ κ f U Uw hsol jj
      ((∑ i ∈ Finset.range j, wordOrders letters i) + 1) (Nat.succ_le_succ (Nat.zero_le _))
      (fun n p => levelC Ca (wordOrders letters) (wordSlows letters)
        (wordLetterConsts letters J) j n p * levelTheta (wordAmplitudes letters ζ) j)
      (fun n p => mul_nonneg (levelC_nonneg Ca hCa _ _ _ hLc j n p)
        (levelTheta_nonneg _ hθ j))
      (levelQ Qa (wordOrders letters) j)
      (fun p => weightedJetNorm π ((p + ∑ i ∈ Finset.range j, wordSlows letters i : ℕ) : ℝ) 0 ϖ 1
        (fun x i w z => planeJetOrder (f x) i w z))
      (fun n hn hnJ p r hr T hT => ih (Nat.le_of_succ_le hj) n hn hnJ p r hr T hT)
      n (by omega) hmJ p t ht Φ hΦ
    beta_reduce at hstep
    refine hstep.trans (le_of_eq ?_)
    have hw : p + (letters jj).slow + ∑ i ∈ Finset.range j, wordSlows letters i =
        p + ∑ i ∈ Finset.range (j + 1), wordSlows letters i := by
      rw [Finset.sum_range_succ, hslow]
      ring
    rw [hw]
    congr 2
    congr 1
    simp only [levelC, levelQ, levelTheta, Finset.prod_range_succ, hslow, hamp,
      wordLetterConsts, hord, hpos, Nat.add_sub_cancel]
    ring


/-- **(17c) from (17a)**: the level claim for every chain. -/
theorem weakContLevelBound_of_flux (hFlux : WeakContFluxStatement.{u, v}) :
    WeakContLevelBoundStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ D N hD π hπ letters a b J H hL hmeas G hG g hg0 hg hGn v hv hvs η hη Cvj
    hvj M hb ϖ ζ hϖ hϖ1 hζ hζ1 P hP Ca hCa Qa hadj X₀ κ f U Uw hsol j hj m hm hmJ p t ht Φ hΦ
  exact weakCont_level_bound hFlux hD π hπ letters a b J H hL hmeas G hG g hg0 hg hGn v hv hvs hη
    Cvj hvj M hb ϖ ζ hϖ hϖ1 hζ hζ1 P hP Ca hCa Qa hadj X₀ κ f U Uw hsol j hj m hm hmJ p t ht Φ hΦ

end AVRegularity.CycleWords.Discard
end

section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CycleJointProofs
open AVRegularity.CycleWords.Seam
open scoped ENNReal Topology
namespace AVRegularity.CycleWords.Discard

/-! # The letter flux of an arbitrary level family

`weakContFlux : WeakContFluxStatement`.

* On balls: the level curves are cut by a compact cutoff `χ_M` (a bounded operator on `H^{κ+1}`,
  `weakContCut`). The cut family has every weighted norm, so the existing realization
  `wordChainPrevious_l2_flux_exists` applies to it; on the ball where `χ_M = 1` the jets of the
  cut and of the original curves agree almost everywhere, hence so do the fluxes.
* The weight: at almost every time the Taylor factor of every constituent is at most
  `P ⟨ϖz⟩^{K}` (`analyticOriginalSource_flagged_taylor_fast_price` at jet order `0`), so
  `⟨ϖz⟩^{-K}|flux| ≤ C ∑ |jets|` pointwise, and the jets are in `L²` with norm at most that of
  the curve. No moment of the curves is used. -/

universe u v

section Cut

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The budget of the expanding cutoffs on `H^K`, uniform in the cutoff. -/
def weakContCutBudget (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : ℕ) :
    Fin (K + 1) → ℝ :=
  Classical.choose (exists_expandingPlaneCoefficient_budget (E := E) K)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem weakContCutBudget_bound (M K : ℕ) (l : Fin (K + 1)) (x : Vec 2) :
    ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) M) l.val x‖ ≤
      weakContCutBudget E K l :=
  (Classical.choose_spec (exists_expandingPlaneCoefficient_budget (E := E) K)).2.1 M l x

/-- The cut of a plane carrier by the `M`-th expanding cutoff, as a bounded operator. -/
def weakContCut (M K : ℕ) : PlaneHk Set.univ K E →L[ℝ] PlaneHk Set.univ K E :=
  productPlaneHkOperator (expandingPlaneCoefficient (E := E) M)
    ((expandingPlaneCoefficient_contDiff M).of_le (by simp)) (weakContCutBudget_bound M K)

theorem weakContCut_eq (M K : ℕ) (U : PlaneHk Set.univ K E) :
    weakContCut M K U =
      expandingCutoffPlaneHk U M (weakContCutBudget E K) (weakContCutBudget_bound M K) := by
  rw [weakContCut, productPlaneHkOperator_apply]
  rfl

theorem weakContCut_value_ae (M K : ℕ) (U : PlaneHk Set.univ K E) :
    planeValue (weakContCut M K U) =ᵐ[volume]
      fun x => expandingPlaneCutoff M x • planeValue U x := by
  rw [weakContCut_eq]
  exact expandingCutoffPlaneHk_value_ae U M _ _

/-- The `M`-th expanding cutoff is one on the ball of radius `M + 1`. -/
theorem expandingPlaneCutoff_eq_one_of_mem_ball (M : ℕ) {z : Vec 2}
    (hz : z ∈ Metric.ball (0 : Vec 2) ((M : ℝ) + 1)) : expandingPlaneCutoff M z = 1 := by
  unfold expandingPlaneCutoff
  apply ContDiffBump.one_of_mem_closedBall
  have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hz' : ‖z‖ < (M : ℝ) + 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  change ((M : ℝ) + 1)⁻¹ * ‖z‖ ≤ 1
  calc ((M : ℝ) + 1)⁻¹ * ‖z‖ ≤ ((M : ℝ) + 1)⁻¹ * ((M : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hz'.le (inv_nonneg.mpr hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- On the ball where the cutoff is one, the jets of the cut carrier are those of the carrier. -/
theorem weakContCut_jet_ae (M K : ℕ) (U : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    ∀ᵐ z ∂volume, z ∈ Metric.ball (0 : Vec 2) ((M : ℝ) + 1) →
      (weakContCut M K U).toFunction.jet a z = U.toFunction.jet a z := by
  have hval : ∀ᵐ x ∂volume, x ∉ (Metric.ball (0 : Vec 2) ((M : ℝ) + 1))ᶜ →
      planeValue (weakContCut M K U - U) x = 0 := by
    filter_upwards [planeValue_sub_ae (weakContCut M K U) U, weakContCut_value_ae M K U]
      with x h1 h2 hx
    have hx' : x ∈ Metric.ball (0 : Vec 2) ((M : ℝ) + 1) := not_not.mp hx
    rw [h1, h2, expandingPlaneCutoff_eq_one_of_mem_ball M hx', one_smul, sub_self]
  have hjet := planeRawJet_supported (weakContCut M K U - U) _
    Metric.isOpen_ball.isClosed_compl hval a
  have hsub := planeJetOrder_sub_ae (Nat.le_of_lt_succ a.1.isLt) (weakContCut M K U) U a.2
  filter_upwards [hjet, hsub] with z h1 h2 hz
  have h3 := h1 (not_not.mpr hz)
  simp only [planeJetOrder, Nat.le_of_lt_succ a.1.isLt, dite_true] at h2
  exact sub_eq_zero.mp (h2.symm.trans h3)

/-- The cut of a square integrable curve has every weighted gradient norm, integrably in time. -/
theorem weakContCut_weightedGrad_lintegral_ne_top (M Q n : ℕ) (ϖ ρ : ℝ) (hρ : 0 < ρ)
    {μ : Measure ℝ} (W : ℝ → PlaneHk Set.univ (Q + 1) E) (hW : MemLp W 2 μ) :
    (∫⁻ t, weightedGradFactorialNormSq n ϖ 0 ρ Q (weakContCut M (Q + 1) (W t)) ∂μ) ≠ ⊤ := by
  have hcomp : IsCompact (tsupport (expandingPlaneCutoff M)) :=
    expandingPlaneCutoff_hasCompactSupport M
  have hqc : Continuous (planeMomentPolynomial n ϖ (0 : Vec 2)) := by
    unfold planeMomentPolynomial
    fun_prop
  obtain ⟨Cq, hCq⟩ := hcomp.exists_bound_of_continuousOn hqc.continuousOn
  have hpt : ∀ t, weightedGradFactorialNormSq n ϖ 0 ρ Q (weakContCut M (Q + 1) (W t)) ≤
      ENNReal.ofReal ((((Q + 1 : ℕ) : ℝ) ^ 2 / ρ ^ 2)) * (ENNReal.ofReal (max Cq 0) *
        ENNReal.ofReal (factorialWeightMax ρ (Q + 1) *
          ‖weakContCut M (Q + 1) (W t)‖ ^ 2)) := by
    intro t
    have hsupp : ∀ᵐ x ∂volume, x ∉ tsupport (expandingPlaneCutoff M) →
        (weakContCut M (Q + 1) (W t)).toFunction.jet (valueIndex2 (Q + 1)) x = 0 := by
      have h := expandingCutoffPlaneHk_supported (W t) M (weakContCutBudget E (Q + 1))
        (weakContCutBudget_bound M (Q + 1))
      rw [← weakContCut_eq] at h
      filter_upwards [h] with x hx hout
      have h0 := hx hout
      simp only [planeValue, planeJetOrder, Nat.zero_le, dite_true] at h0
      exact h0
    refine (weightedGradFactorialNormSq_le_full_lift n ϖ 0 ρ hρ _).trans
      (mul_le_mul' le_rfl ?_)
    rw [weightedFactorialNormSq_stored_readout]
    refine (storedChartFactorialEnergy_value_supported_bound ρ _ _ (isClosed_tsupport _) hsupp
      (max Cq 0) (le_max_right _ _) (fun x hx => ?_)).trans
        (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (factorialNormSq_upper ρ _)))
    exact ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hCq x hx))).trans
      (le_max_left _ _)
  have hmem : MemLp (fun t => weakContCut M (Q + 1) (W t)) 2 μ :=
    (weakContCut M (Q + 1)).comp_memLp' hW
  have hint : Integrable (fun t => factorialWeightMax ρ (Q + 1) *
      ‖weakContCut M (Q + 1) (W t)‖ ^ 2) μ := hmem.norm.integrable_sq.const_mul _
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hint.lintegral_lt_top.ne)

omit [FiniteDimensional ℝ E] in
/-- The `L²` norm of a stored jet is at most the norm of the carrier. -/
theorem weakCont_jet_eLpNorm_le {K : ℕ} (U : PlaneHk Set.univ K E) (a' : JetIndex2 K) :
    eLpNorm (fun z => ‖U.toFunction.jet a' z‖) 2 (volume : Measure (Vec 2)) ≤
      ENNReal.ofReal ‖U‖ := by
  have hm := U.toFunction.memL2 a'
  obtain ⟨c, hc, hn⟩ : ∃ c : ℝ, c = ‖U.val a'‖ ∧
      eLpNorm (U.toFunction.jet a') 2 (volume.restrict Set.univ) = ENNReal.ofReal c := by
    refine ⟨_, rfl, ?_⟩
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    rfl
  generalize U.toFunction.jet a' = g at hm hn ⊢
  rw [Measure.restrict_univ] at hm hn
  rw [eLpNorm_norm g hm.aestronglyMeasurable, hn, hc]
  exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le U.val a')

end Cut

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- On the ball where the cutoff is one, the letter flux of the cut level is the letter flux. -/
theorem weakCont_cut_flux_eq (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (j : Fin N) (x : ι) (r : ℝ) (M : ℕ) (k : Fin 2) :
    ∀ᵐ z ∂volume, z ∈ Metric.ball (0 : Vec 2) ((M : ℝ) + 1) →
      wordChainPreviousFlux letters X0 δ κ (fun p => weakContCut M (κ p.1 p.2 + 1) (U p))
          (j.succ, x) r z k =
        wordChainPreviousFlux letters X0 δ κ U (j.succ, x) r z k := by
  have hjets : ∀ᵐ z ∂volume, ∀ u (a' : JetIndex2 (κ j.castSucc u + 1)),
      z ∈ Metric.ball (0 : Vec 2) ((M : ℝ) + 1) →
        (weakContCut M (κ j.castSucc u + 1) (U (j.castSucc, u))).toFunction.jet a' z =
          (U (j.castSucc, u)).toFunction.jet a' z :=
    ae_all_iff.mpr fun u => ae_all_iff.mpr fun a' => weakContCut_jet_ae M _ _ a'
  filter_upwards [hjets] with z hj hzb
  rw [wordChainPreviousFlux_succ, wordChainPreviousFlux_succ]
  unfold Weighted.letterAdmissibleFlux
  refine congrArg (fun y : PiLp 2 (fun _ : Fin 2 => h x) => y k) ?_
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun o _ => ?_
  congr 1
  exact congrArg _ (funext fun w => hj u _ hzb)

/-- **The letter flux on a ball** has an `L²(I; L²)` realization, for every family of level
curves in `L²(I; H^{κ+1})`. -/
theorem weakCont_flux_ball (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (letters : Fin N → CycleLetter ι h D) (a b : ℝ) (J H : ℕ) (j : Fin N) (x : ι)
    (hL : IsCycleLetter π (letters j) (Set.Icc a b ×ˢ Set.univ) J H)
    (κ : Fin (N + 1) → ι → ℕ) (X0 : Vec 2) (δ : ℝ)
    (hm : ∀ u o (k : Fin ((letters j).edge x u o).length), ∀ w X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff w t X z))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hUw : ∀ u, MemLp (Uw (j.castSucc, u)) 2 (volume.restrict (Set.Icc a b))) (M : ℕ) :
    ∃ S : ℝ → PlaneFluxL2 (h x), MemLp S 2 (volume.restrict (Set.Icc a b)) ∧
      ∀ᵐ r ∂volume.restrict (Set.Icc a b), ∀ k, ∀ᵐ z ∂volume,
        z ∈ Metric.ball (0 : Vec 2) ((M : ℝ) + 1) → (S r k : Vec 2 → h x) z =
          wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) (j.succ, x) r z k := by
  obtain ⟨S, hSl, hS⟩ := wordChainPrevious_l2_flux_exists π hπ letters a b J H j x hL κ X0 δ
    hm 1 1 one_pos one_pos (fun p r => weakContCut M (κ p.1 p.2 + 1) (Uw p r))
    (fun u => (weakContCut M (κ j.castSucc u + 1)).comp_memLp' (hUw u))
    (fun u => weakContCut_weightedGrad_lintegral_ne_top M (κ j.castSucc u) (letters j).slow 1 1
      one_pos _ (hUw u))
  refine ⟨S, hSl, ?_⟩
  filter_upwards [hS] with r hr k
  filter_upwards [hr k, weakCont_cut_flux_eq letters X0 δ κ (fun p => Uw p r) j x r M k]
    with z hz hcz hzb
  rw [hz]
  exact hcz hzb

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The letter flux at one point**, from a bound `P wz` of every Taylor factor: the norm of a
component of the flux is at most `N P wz` times the sum of the norms of all jets. -/
theorem weakCont_letterFlux_norm_le {σ : Type*} (L : CycleLetter ι h D) (κ : σ → ℕ) (a : σ)
    (b : ι → σ) (v : ι) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ u, PlaneHk Set.univ (κ (b u) + 1) (h u)) (s : ℝ) (z : Vec 2) (k : Fin 2)
    (P wz : ℝ) (hP : 0 ≤ P) (hwz : 0 ≤ wz)
    (hcoef : ∀ u (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length)
      (α : DerivativeWord2 (o.1 - 1)) (k' : Fin 2),
      ‖((L.edge v u o).get q).map‖ * |letterCoeff L lo X₀ δ s v u o q α k' z| ≤ P * wz) :
    ‖(letterAdmissibleFlux L κ a b v lo X₀ δ W s z) k‖ ≤
      (∑ u, ∑ o : admissibleOrders κ D a (b u),
        ∑ _q : Fin (L.edge v u (admissibleLetterOrder κ D a (b u) o)).length,
          ∑ _α : DerivativeWord2 (o.1 - 1), ∑ _k' : Fin 2, (1 : ℝ)) * (P * wz) *
        ∑ u, ∑ a' : JetIndex2 (κ (b u) + 1), ‖(W u).toFunction.jet a' z‖ := by
  set fk := (letterAdmissibleFlux L κ a b v lo X₀ δ W s z) k with hfk
  set Tz := ∑ u, ∑ a' : JetIndex2 (κ (b u) + 1), ‖(W u).toFunction.jet a' z‖ with hTz
  have hTz0 : 0 ≤ Tz := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hjetle : ∀ u (a' : JetIndex2 (κ (b u) + 1)), ‖(W u).toFunction.jet a' z‖ ≤ Tz := by
    intro u a'
    refine le_trans ?_ (Finset.single_le_sum (f := fun u => ∑ a' : JetIndex2 (κ (b u) + 1),
      ‖(W u).toFunction.jet a' z‖) (fun u _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ u))
    exact Finset.single_le_sum (f := fun a' : JetIndex2 (κ (b u) + 1) =>
      ‖(W u).toFunction.jet a' z‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ a')
  have hexp := letterAdmissibleFlux_inner_expand L κ a b v lo X₀ δ W s z (Pi.single k fk)
  have hL : ∑ k' : Fin 2, inner ℝ ((letterAdmissibleFlux L κ a b v lo X₀ δ W s z) k')
      ((Pi.single k fk : Fin 2 → h v) k') = ‖fk‖ ^ 2 := by
    rw [Finset.sum_eq_single k (fun k' _ hne => by
      rw [Pi.single_eq_of_ne hne, inner_zero_right]) (fun hk => absurd (Finset.mem_univ k) hk),
      Pi.single_eq_same, real_inner_self_eq_norm_sq]
  have hy : ∀ k' : Fin 2, ‖(Pi.single k fk : Fin 2 → h v) k'‖ ≤ ‖fk‖ := by
    intro k'
    by_cases hk : k' = k
    · rw [hk, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hk, norm_zero]
      exact norm_nonneg _
  have hsq : ‖fk‖ ^ 2 ≤ (∑ u, ∑ o : admissibleOrders κ D a (b u),
        ∑ _q : Fin (L.edge v u (admissibleLetterOrder κ D a (b u) o)).length,
          ∑ _α : DerivativeWord2 (o.1 - 1), ∑ _k' : Fin 2, (1 : ℝ)) * (P * wz * Tz * ‖fk‖) := by
    rw [← hL, hexp]
    simp only [Finset.sum_mul, one_mul]
    refine (le_abs_self _).trans ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun o _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k' _ => ?_)
    rw [abs_mul]
    have h1 := hcoef u (admissibleLetterOrder κ D a (b u) o) q α k'
    have h2 : |inner ℝ (((L.edge v u (admissibleLetterOrder κ D a (b u) o)).get q).map
        ((W u).toFunction.jet (admissibleLetterSourceIndex κ D a (b u) o α) z))
        ((Pi.single k fk : Fin 2 → h v) k')| ≤
        ‖((L.edge v u (admissibleLetterOrder κ D a (b u) o)).get q).map‖ * Tz * ‖fk‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      refine mul_le_mul ?_ (hy k') (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) hTz0)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hjetle u _) (norm_nonneg _))
    calc |letterCoeff L lo X₀ δ s v u (admissibleLetterOrder κ D a (b u) o) q α k' z| *
          |inner ℝ (((L.edge v u (admissibleLetterOrder κ D a (b u) o)).get q).map
            ((W u).toFunction.jet (admissibleLetterSourceIndex κ D a (b u) o α) z))
            ((Pi.single k fk : Fin 2 → h v) k')|
        ≤ |letterCoeff L lo X₀ δ s v u (admissibleLetterOrder κ D a (b u) o) q α k' z| *
            (‖((L.edge v u (admissibleLetterOrder κ D a (b u) o)).get q).map‖ * Tz * ‖fk‖) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = (‖((L.edge v u (admissibleLetterOrder κ D a (b u) o)).get q).map‖ *
            |letterCoeff L lo X₀ δ s v u (admissibleLetterOrder κ D a (b u) o) q α k' z|) *
            (Tz * ‖fk‖) := by ring
      _ ≤ (P * wz) * (Tz * ‖fk‖) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hTz0 (norm_nonneg _))
      _ = P * wz * Tz * ‖fk‖ := by ring
  set Nc := (∑ u, ∑ o : admissibleOrders κ D a (b u),
    ∑ _q : Fin (L.edge v u (admissibleLetterOrder κ D a (b u) o)).length,
      ∑ _α : DerivativeWord2 (o.1 - 1), ∑ _k' : Fin 2, (1 : ℝ)) with hNc
  have hNc0 : 0 ≤ Nc := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      zero_le_one
  by_cases hf0 : ‖fk‖ = 0
  · rw [hf0]
    exact mul_nonneg (mul_nonneg hNc0 (mul_nonneg hP hwz)) hTz0
  · have hfpos : 0 < ‖fk‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf0)
    have h3 : ‖fk‖ * ‖fk‖ ≤ (Nc * (P * wz) * Tz) * ‖fk‖ := by
      calc ‖fk‖ * ‖fk‖ = ‖fk‖ ^ 2 := (pow_two _).symm
        _ ≤ Nc * (P * wz * Tz * ‖fk‖) := hsq
        _ = (Nc * (P * wz) * Tz) * ‖fk‖ := by ring
    exact le_of_mul_le_mul_right h3 hfpos

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The weighted letter flux at one time** is in `L²` with norm at most `C ∑_u ‖w_u‖`. -/
theorem weakCont_letterFlux_weighted {σ : Type*} (L : CycleLetter ι h D) (κ : σ → ℕ) (a : σ)
    (b : ι → σ) (v : ι) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ u, PlaneHk Set.univ (κ (b u) + 1) (h u)) (s : ℝ) (k : Fin 2)
    (P : ℝ) (hP : 0 ≤ P) (wt : Vec 2 → ℝ) (hw1 : ∀ z, 0 < wt z)
    (hFm : AEStronglyMeasurable
      (fun z => (wt z)⁻¹ • (letterAdmissibleFlux L κ a b v lo X₀ δ W s z) k) volume)
    (hcoef : ∀ z u (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length)
      (α : DerivativeWord2 (o.1 - 1)) (k' : Fin 2),
      ‖((L.edge v u o).get q).map‖ * |letterCoeff L lo X₀ δ s v u o q α k' z| ≤ P * wt z) :
    eLpNorm (fun z => (wt z)⁻¹ • (letterAdmissibleFlux L κ a b v lo X₀ δ W s z) k) 2 volume ≤
      ENNReal.ofReal (((∑ u, ∑ o : admissibleOrders κ D a (b u),
        ∑ _q : Fin (L.edge v u (admissibleLetterOrder κ D a (b u) o)).length,
          ∑ _α : DerivativeWord2 (o.1 - 1), ∑ _k' : Fin 2, (1 : ℝ)) * P *
        ∑ u, (Fintype.card (JetIndex2 (κ (b u) + 1)) : ℝ)) * ∑ u, ‖W u‖) := by
  set Nc := (∑ u, ∑ o : admissibleOrders κ D a (b u),
    ∑ _q : Fin (L.edge v u (admissibleLetterOrder κ D a (b u) o)).length,
      ∑ _α : DerivativeWord2 (o.1 - 1), ∑ _k' : Fin 2, (1 : ℝ)) with hNc
  have hNc0 : 0 ≤ Nc := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      zero_le_one
  -- the pointwise bound
  have hpt : ∀ z, ‖(wt z)⁻¹ • (letterAdmissibleFlux L κ a b v lo X₀ δ W s z) k‖ ≤
      (Nc * P) * ∑ u, ∑ a' : JetIndex2 (κ (b u) + 1), ‖(W u).toFunction.jet a' z‖ := by
    intro z
    have h1 := weakCont_letterFlux_norm_le L κ a b v lo X₀ δ W s z k P (wt z) hP (hw1 z).le
      (hcoef z)
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hw1 z).le)]
    calc (wt z)⁻¹ * ‖(letterAdmissibleFlux L κ a b v lo X₀ δ W s z) k‖
        ≤ (wt z)⁻¹ * (Nc * (P * wt z) *
            ∑ u, ∑ a' : JetIndex2 (κ (b u) + 1), ‖(W u).toFunction.jet a' z‖) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (hw1 z).le)
      _ = ((wt z)⁻¹ * wt z) * ((Nc * P) *
            ∑ u, ∑ a' : JetIndex2 (κ (b u) + 1), ‖(W u).toFunction.jet a' z‖) := by ring
      _ = (Nc * P) * ∑ u, ∑ a' : JetIndex2 (κ (b u) + 1), ‖(W u).toFunction.jet a' z‖ := by
          rw [inv_mul_cancel₀ (hw1 z).ne', one_mul]
  -- the `L²` norm of the sum of the jets
  have hjet : ∀ u (a' : JetIndex2 (κ (b u) + 1)),
      eLpNorm (fun z => ‖(W u).toFunction.jet a' z‖) 2 volume ≤ ENNReal.ofReal ‖W u‖ :=
    fun u a' => weakCont_jet_eLpNorm_le (W u) a'
  have hsumfun : (fun z => ∑ u, ∑ a' : JetIndex2 (κ (b u) + 1), ‖(W u).toFunction.jet a' z‖) =
      ∑ u, ∑ a' : JetIndex2 (κ (b u) + 1), fun z => ‖(W u).toFunction.jet a' z‖ := by
    funext z
    simp only [Finset.sum_apply]
  have hT : eLpNorm (fun z => ∑ u, ∑ a' : JetIndex2 (κ (b u) + 1),
      ‖(W u).toFunction.jet a' z‖) 2 volume ≤
      ENNReal.ofReal ((∑ u, (Fintype.card (JetIndex2 (κ (b u) + 1)) : ℝ)) * ∑ u, ‖W u‖) := by
    rw [hsumfun]
    refine (eLpNorm_sum_le (by norm_num)).trans ?_
    have hstep : ∀ u ∈ (Finset.univ : Finset ι),
        eLpNorm (∑ a' : JetIndex2 (κ (b u) + 1), fun z => ‖(W u).toFunction.jet a' z‖) 2
          volume ≤ ENNReal.ofReal ((∑ u, (Fintype.card (JetIndex2 (κ (b u) + 1)) : ℝ)) * ‖W u‖) := by
      intro u _
      refine (eLpNorm_sum_le (by norm_num)).trans ?_
      refine (Finset.sum_le_sum fun a' _ => hjet u a').trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact Finset.single_le_sum (f := fun u => (Fintype.card (JetIndex2 (κ (b u) + 1)) : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ u)
    refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg fun u _ => mul_nonneg (Finset.sum_nonneg fun _ _ =>
      Nat.cast_nonneg _) (norm_nonneg _), Finset.mul_sum]
  have hmain := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (g := fun z => ∑ u, ∑ a' : JetIndex2 (κ (b u) + 1), ‖(W u).toFunction.jet a' z‖)
    (c := Nc * P) hFm (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun _ _ =>
        norm_nonneg _)]
      exact hpt z) 2
  refine hmain.trans ((mul_le_mul' le_rfl hT).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_mul (mul_nonneg hNc0 hP)]
  congr 1
  ring

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The weighted letter flux at one time, with a constant that does not depend on the time or
on the curves. -/
theorem weakCont_letterFlux_weighted_exists {σ : Type*} (L : CycleLetter ι h D) (κ : σ → ℕ)
    (a : σ) (b : ι → σ) (v : ι) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ) (P : ℝ) (hP : 0 ≤ P)
    (wt : Vec 2 → ℝ) (hw1 : ∀ z, 0 < wt z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ∀ u, PlaneHk Set.univ (κ (b u) + 1) (h u)) (s : ℝ) (k : Fin 2),
      AEStronglyMeasurable
        (fun z => (wt z)⁻¹ • (letterAdmissibleFlux L κ a b v lo X₀ δ W s z) k) volume →
      (∀ z u (o : Finset.Icc 2 D) (q : Fin (L.edge v u o).length)
        (α : DerivativeWord2 (o.1 - 1)) (k' : Fin 2),
        ‖((L.edge v u o).get q).map‖ * |letterCoeff L lo X₀ δ s v u o q α k' z| ≤ P * wt z) →
      eLpNorm (fun z => (wt z)⁻¹ • (letterAdmissibleFlux L κ a b v lo X₀ δ W s z) k) 2 volume ≤
        ENNReal.ofReal (C * ∑ u, ‖W u‖) := by
  refine ⟨_, ?_, fun W s k hFm hcoef =>
    weakCont_letterFlux_weighted L κ a b v lo X₀ δ W s k P hP wt hw1 hFm hcoef⟩
  exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      zero_le_one) hP) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

/-- **(17a)**: the letter flux of an arbitrary level family. -/
theorem weakContFlux : WeakContFluxStatement.{u, v} := by
  intro ι _ h _ _ _ _ _ _ D N π hπ letters a b J H j x hL hm ϖ ζ hϖ hϖ1 hζ hζ1 X₀ κ Uw hUw
  have hball := fun M : ℕ => weakCont_flux_ball π hπ letters a b J H j x hL κ X₀
    (ζ * ϖ) hm Uw hUw M
  refine ⟨hball, ?_⟩
  -- the price of every Taylor factor, at almost every time
  obtain ⟨hC0, hprice⟩ := analyticOriginalSource_flagged_taylor_fast_price (ι := ι) (h := h)
    (D := D) (P := Unit) (Ctx := fun _ => Unit) (letters j).positive (letters j).slow J
  have hall : ∀ᵐ t ∂volume, ∀ u
      (α' : OriginalSourceIndex (ChartedFamily.ofFiber (letters j).edge) x u),
      (∀ Y : Vec 2, (t, Y) ∈ Set.Icc a b ×ˢ (Set.univ : Set (Vec 2))) → ∀ φ k X j', j' ≤ J →
        ∀ z, ‖((ChartedFamily.ofFiber (letters j).edge).identity x u α'.1).map‖ *
          ‖iteratedFDeriv ℝ j' (fun y => taylorSlow (if (letters j).positive then 1 else 0)
            (letters j).slow (fun Y => (ChartedFamily.ofFiber (letters j).edge).flux () () x u
              α'.1 α'.2.1.1 α'.2.2.1 t Y (y + φ) k) X ((ζ * ϖ) • y)) z‖ ≤
        originalFlaggedTaylorFastJetPriceConstant (letters j).positive (letters j).slow J *
          analyticOriginalSourcePrice (ChartedFamily.ofFiber (letters j).edge)
            (fun _ _ => Set.Icc a b ×ˢ Set.univ) (letters j).slow J x u α' *
          (if (letters j).positive then ζ else 1) * polynomialMomentRoot ϖ z ^ (letters j).slow :=
    ae_all_iff.mpr fun u => ae_all_iff.mpr fun α' =>
      hprice (ChartedFamily.ofFiber (letters j).edge) π hπ
        (fun _ _ => Set.Icc a b ×ˢ Set.univ) (letters j).majorant hL.analytic x u α' () () ϖ ζ
        hϖ hϖ1 hζ hζ1
  have hflag : 0 ≤ (if (letters j).positive then ζ else 1) := by
    split_ifs
    · exact hζ
    · exact zero_le_one
  -- one constant for all constituents
  set Pall : ℝ := ∑ u, ∑ α' : OriginalSourceIndex (ChartedFamily.ofFiber (letters j).edge) x u,
    originalFlaggedTaylorFastJetPriceConstant (letters j).positive (letters j).slow J *
      analyticOriginalSourcePrice (ChartedFamily.ofFiber (letters j).edge)
        (fun _ _ => Set.Icc a b ×ˢ Set.univ) (letters j).slow J x u α' *
      (if (letters j).positive then ζ else 1) with hPall
  have hterm0 : ∀ u (α' : OriginalSourceIndex (ChartedFamily.ofFiber (letters j).edge) x u),
      0 ≤ originalFlaggedTaylorFastJetPriceConstant (letters j).positive (letters j).slow J *
        analyticOriginalSourcePrice (ChartedFamily.ofFiber (letters j).edge)
          (fun _ _ => Set.Icc a b ×ˢ Set.univ) (letters j).slow J x u α' *
        (if (letters j).positive then ζ else 1) := fun u α' =>
    mul_nonneg (mul_nonneg hC0 ENNReal.toReal_nonneg) hflag
  have hPall0 : 0 ≤ Pall := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun α' _ => hterm0 u α'
  have hsingle : ∀ u (α' : OriginalSourceIndex (ChartedFamily.ofFiber (letters j).edge) x u),
      originalFlaggedTaylorFastJetPriceConstant (letters j).positive (letters j).slow J *
        analyticOriginalSourcePrice (ChartedFamily.ofFiber (letters j).edge)
          (fun _ _ => Set.Icc a b ×ˢ Set.univ) (letters j).slow J x u α' *
        (if (letters j).positive then ζ else 1) ≤ Pall := by
    intro u α'
    refine le_trans ?_ (Finset.single_le_sum (f := fun u => ∑ α' : OriginalSourceIndex
      (ChartedFamily.ofFiber (letters j).edge) x u,
      originalFlaggedTaylorFastJetPriceConstant (letters j).positive (letters j).slow J *
        analyticOriginalSourcePrice (ChartedFamily.ofFiber (letters j).edge)
          (fun _ _ => Set.Icc a b ×ˢ Set.univ) (letters j).slow J x u α' *
        (if (letters j).positive then ζ else 1))
      (fun u _ => Finset.sum_nonneg fun α' _ => hterm0 u α') (Finset.mem_univ u))
    exact Finset.single_le_sum (f := fun α' : OriginalSourceIndex
      (ChartedFamily.ofFiber (letters j).edge) x u =>
      originalFlaggedTaylorFastJetPriceConstant (letters j).positive (letters j).slow J *
        analyticOriginalSourcePrice (ChartedFamily.ofFiber (letters j).edge)
          (fun _ _ => Set.Icc a b ×ˢ Set.univ) (letters j).slow J x u α' *
        (if (letters j).positive then ζ else 1)) (fun α' _ => hterm0 u α') (Finset.mem_univ α')
  have hw1 : ∀ z : Vec 2, 0 < polynomialMomentRoot ϖ z ^ (letters j).slow := fun z =>
    pow_pos (lt_of_lt_of_le one_pos (polynomialMomentRoot_one_le ϖ z)) _
  have hwinv : Continuous fun z : Vec 2 => (polynomialMomentRoot ϖ z ^ (letters j).slow)⁻¹ :=
    ((polynomialMomentRoot_continuous ϖ).pow _).inv₀ fun z => (hw1 z).ne'
  obtain ⟨C, hC, hbound⟩ := weakCont_letterFlux_weighted_exists (letters j)
    (fun p : Fin (N + 1) × ι => κ p.1 p.2) (j.succ, x) (fun u => (j.castSucc, u)) x
    (if (letters j).positive then 1 else 0) X₀ (ζ * ϖ) Pall hPall0
    (fun z => polynomialMomentRoot ϖ z ^ (letters j).slow) hw1
  refine ⟨C, hC, ?_⟩
  choose S hSl hS using hball
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Icc, ae_all_iff.mpr hS]
    with r hr hrmem hSr k
  -- measurability in space, from the realizations on balls
  have hFm0 : AEStronglyMeasurable (fun z =>
      wordChainPreviousFlux letters X₀ (ζ * ϖ) κ (fun p => Uw p r) (j.succ, x) r z k) volume :=
    weakCont_aestronglyMeasurable_of_balls _ (fun M z => (S M r k : Vec 2 → h x) z)
      (fun M => Lp.aestronglyMeasurable _) fun M => hSr M k
  have hfun : (fun z => (polynomialMomentRoot ϖ z ^ (letters j).slow)⁻¹ •
      wordChainPreviousFlux letters X₀ (ζ * ϖ) κ (fun p => Uw p r) (j.succ, x) r z k) =
      fun z => (polynomialMomentRoot ϖ z ^ (letters j).slow)⁻¹ •
        (letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
          (j.succ, x) (fun u => (j.castSucc, u)) x (if (letters j).positive then 1 else 0)
          X₀ (ζ * ϖ) (fun u => Uw (j.castSucc, u) r) r z) k := by
    funext z
    rw [wordChainPreviousFlux_succ]
  have hFm : AEStronglyMeasurable (fun z => (polynomialMomentRoot ϖ z ^ (letters j).slow)⁻¹ •
      (letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
        (j.succ, x) (fun u => (j.castSucc, u)) x (if (letters j).positive then 1 else 0)
        X₀ (ζ * ϖ) (fun u => Uw (j.castSucc, u) r) r z) k) volume := by
    rw [← hfun]
    exact hwinv.aestronglyMeasurable.smul hFm0
  rw [hfun]
  refine hbound (fun u => Uw (j.castSucc, u) r) r k hFm ?_
  intro z u o q α k'
  have hp := hr u (constituentSourceIndex (letters j) x u o q α k')
    (fun Y => ⟨hrmem, Set.mem_univ Y⟩) 0 k' X₀ 0 (Nat.zero_le J) z
  rw [constituent_taylor_eq, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right (hsingle u _)
    (pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _))

end AVRegularity.CycleWords.Discard
end

section
namespace AVRegularity.CycleWords.Discard

/-! # Weak continuity of the endpoint on rough data

`chainWeakContinuity : ChainWeakContinuityStatement`, for every
chain of a block whose datum has a finite moment norm: (17a) `weakContFlux`, (17b)
`weakContStepDuality` (inside `weakContLevelBound_of_flux`), (17c) `weakContLevelBound_of_flux`,
and the assembly `chainWeakContinuity_of_levelBound`. -/

universe u v

/-- **(17c)**: the level claim of the adjoint word chain for every chain. -/
theorem weakContLevelBound : WeakContLevelBoundStatement.{u, v} :=
  weakContLevelBound_of_flux weakContFlux

/-- **Weak continuity of the endpoint on rough data.** -/
theorem chainWeakContinuity : ChainWeakContinuityStatement.{u, v} :=
  chainWeakContinuity_of_levelBound weakContLevelBound

end AVRegularity.CycleWords.Discard
end
