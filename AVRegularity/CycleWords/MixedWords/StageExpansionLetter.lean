-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.LetterBlochClauses
import AVRegularity.CycleWords.MixedWords.WeightedPlainDecayKappa
public import AVRegularity.CycleWords.MixedWords.CompactChainExistence
public import AVRegularity.CycleWords.Assembly.InteriorScalarIngredients
import Mathlib.Data.Int.Star

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The stage sources as tested sources

The word fibre facts pair the forcing of a stage with a test slice `z` sesquilinearly:
`cellComplexSource θ S F z = ∫ S conj z - ∑_k ∫ F_k conj(D*_k z)`. For a real shift and a test with
a `C¹` representative `φ`, `conj(D*_k z) = D_{-θ,k}(conj φ)` a.e. (`cellDerivativeCLM_ae_of_smooth`,
`star_shifted_ae`), so the pairing is the bilinear tested source against `conj φ`
(`cellComplexSource_eq_integrals`). With the literal forcing of the amplitude identification this is
`b1wTestedSource`, the left side of the letter Bloch identity (`cellComplexSource_eq_testedSource`).
The actual fibre shift is the plane frequency:
`√η · θ/√η = θ` (`fibreShift_eq`). -/

universe u v

/-- The actual fibre shift is the plane frequency. -/
theorem fibreShift_eq {η : ℝ} (hη : 0 < η) (θ : Vec 2) :
    (fun k => (Real.sqrt η : ℂ) * planeFibreFrequency η θ k) = fun k => ((θ k : ℝ) : ℂ) := by
  funext k
  unfold planeFibreFrequency
  rw [← Complex.ofReal_mul, mul_div_cancel₀ _ (Real.sqrt_pos.mpr hη).ne']

/-- The derivative jet of a test with a `C¹` representative is its classical derivative. -/
theorem cellDerivativeCLM_ae_of_smooth (z : TorusHk 1 ℂ) (φ : Vec 2 → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hval : (torusHkValueCLM z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] φ)
    (k : Fin 2) :
    (cellDerivativeCLM k z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => fderiv ℝ φ x (basisVec k) := by
  have h := torusHigher_smooth_local_readout z φ (by exact_mod_cast hφ) hval
    ⟨⟨1, by decide⟩, fun _ => k⟩
  have hl : orderedDerivative (fun _ : Fin 1 => k) φ = fun x => fderiv ℝ φ x (basisVec k) := by
    simp [orderedDerivative, List.ofFn_succ]
  rw [hl] at h
  exact h

/-- The derivative of the conjugate. -/
theorem fderiv_star_apply {φ : Vec 2 → ℂ} {x : Vec 2} (hφ : DifferentiableAt ℝ φ x)
    (w : Vec 2) : fderiv ℝ (fun y => star (φ y)) x w = star (fderiv ℝ φ x w) := by
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := φ x)).comp x
    hφ.hasFDerivAt
  rw [show (fun y => star (φ y)) = Complex.conjCLE.toContinuousLinearMap ∘ φ from rfl,
    h.fderiv]
  rfl

/-- **The conjugate of the shifted derivative** of a test with a `C¹` representative, for a real
shift: `conj(D*_k z) = D_{-θ,k}(conj φ)` a.e. -/
theorem star_shifted_ae (θ : Vec 2) (z : TorusHk 1 ℂ) (φ : Vec 2 → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hval : (torusHkValueCLM z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] φ)
    (k : Fin 2) :
    (fun x => star (cellShiftedDerivativeCLM (fun i => star ((θ i : ℝ) : ℂ)) k z x))
      =ᵐ[volume.restrict AVenhance.unitCube]
      fibreCovDeriv (-θ) k (fun y => star (φ y)) := by
  have hd := cellDerivativeCLM_ae_of_smooth z φ hφ hval k
  have hs := cellScalarCLM_ae (Complex.I * star ((θ k : ℝ) : ℂ)) (torusHkValueCLM z)
  have ha := Lp.coeFn_add (cellDerivativeCLM k z)
    (cellScalarCLM (Complex.I * star ((θ k : ℝ) : ℂ)) (torusHkValueCLM z))
  filter_upwards [hd, hs, ha, hval] with x h1 h2 h3 h4
  change star ((cellDerivativeCLM k z +
    cellScalarCLM (Complex.I * star ((θ k : ℝ) : ℂ)) (torusHkValueCLM z)) x) = _
  rw [h3, Pi.add_apply, h1, h2, h4]
  unfold fibreCovDeriv
  rw [fderiv_star_apply ((hφ.differentiable one_ne_zero) x)]
  simp only [star_add, star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
    Pi.neg_apply, Complex.ofReal_neg]
  ring

/-- **The sesquilinear source pairing is the bilinear tested source against the conjugate.** -/
theorem cellComplexSource_eq_integrals (θ : Vec 2) (S : ComplexCellL2)
    (Fv : Fin 2 → ComplexCellL2) (z : TorusHk 1 ℂ) (φ : Vec 2 → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hval : (torusHkValueCLM z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] φ)
    (s : Vec 2 → ℂ) (fl : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hS : (S : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] s)
    (hF : ∀ k, (Fv k : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun x => fl x k) :
    cellComplexSource (fun k => ((θ k : ℝ) : ℂ)) S Fv z =
      (∫ x in AVenhance.unitCube, s x * star (φ x)) -
        ∑ k : Fin 2, ∫ x in AVenhance.unitCube,
          fl x k * fibreCovDeriv (-θ) k (fun y => star (φ y)) x := by
  unfold cellComplexSource cellComplexPair
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [hS, hval] with x h1 h2
    rw [h1, h2]
  · refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
    filter_upwards [hF k, star_shifted_ae θ z φ hφ hval k] with x h1 h2
    rw [h1]
    exact congrArg _ h2

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- **The stage source paired with a test is the tested source of the letter Bloch identity.** -/
theorem cellComplexSource_eq_testedSource {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ) (r : ℝ) (c : ℂ) (S : ComplexCellL2)
    (Fv : Fin 2 → ComplexCellL2)
    (hS : (S : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => c * amplitudeIdLiteralSource F θ j x e β r z)
    (hF : ∀ k, (Fv k : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => c * amplitudeIdLiteralFlux F θ j x e β r z k)
    (z : TorusHk 1 ℂ) (φ : Vec 2 → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hval : (torusHkValueCLM z : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] φ) :
    cellComplexSource (fun k => ((θ k : ℝ) : ℂ)) S Fv z =
      c * b1wTestedSource F θ j x e β r (fun y => star (φ y)) := by
  rw [cellComplexSource_eq_integrals θ S Fv z φ hφ hval _
    (fun z => c • amplitudeIdLiteralFlux F θ j x e β r z) hS (fun k => ?_)]
  · unfold b1wTestedSource amplitudeIdLiteralSource amplitudeIdLiteralFlux
    simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul,
      ← Finset.mul_sum, mul_sub]
  · filter_upwards [hF k] with z hz
    rw [hz, PiLp.smul_apply, smul_eq_mul]

end Frame

end AVRegularity.CycleWords.Assembly
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! Common full-jet and previous-flux moment integrability for the letter identity. -/

section
universe u v

/-- All finite factorial budgets give every integrable monomial of every stored jet. -/
theorem letterBloch_jet_integrable {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {k : ℕ} (U : PlaneHk Set.univ k E) (ϖ r : ℝ) (hϖ : 0 < ϖ) (hr : 0 < r)
    (he : ∀ n, weightedFactorialNormSq n ϖ 0 r k U ≠ ⊤)
    (β : ℕ × ℕ) (n : ℕ) (w : DerivativeWord2 n) :
    Integrable (fun y => momentWeight β y • planeJetOrder U n w y) := by
  by_cases hn : n ≤ k
  · apply amplitudeId_integrable_of_all_monomial_memLp
    intro γ
    apply amplitudeId_monomial_memLp_of_weighted _ (planeJetOrder_memLp hn U w).aestronglyMeasurable ϖ hϖ
    intro m
    rw [planeJetOrder_eq_stored hn]
    exact amplitudeId_stored_moment_finite U m ϖ r hr (he m) _
  · simp only [planeJetOrder, dite_eq_right hn, smul_zero]
    exact integrable_zero _ _ _

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- The whole word has simultaneous monomial moments for all weak jets and fluxes a.e. in time. -/
theorem letterBlochIntegrableAE
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) :
    LetterBlochIntegrableAE F := by
  classical
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  obtain ⟨r, hr, hb⟩ := amplitudeId_full_polynomial_budgets F
  obtain ⟨s, hs, hflux⟩ := amplitudeId_flux_moments F
  choose V hV hVe hVr using hflux
  have he : ∀ j x n, ∀ᵐ t ∂volume.restrict (Icc F.a F.b),
      weightedFactorialNormSq n F.ϖ 0 r (F.κ j x + 1) (F.w j x t) ≠ ⊤ := by
    intro j x n
    exact (ae_lt_top' (Weighted.weightedFactorialNormSq_time_aemeasurable n F.ϖ 0 r _ _
      (F.solution.2.1 (j, x))) (hb n j x).2).mono (fun _ ht => ht.ne)
  have hf : ∀ j x n, ∀ᵐ t ∂volume.restrict (Icc F.a F.b),
      weightedFactorialNormSq n F.ϖ 0 s (F.κ j x) (V j x t) ≠ ⊤ := by
    intro j x n
    exact (ae_lt_top' (Weighted.weightedFactorialNormSq_time_aemeasurable n F.ϖ 0 s _ _
      (hV j x)) (hVe j x n)).mono (fun _ ht => ht.ne)
  have hue : ∀ j x, ∀ᵐ t ∂volume.restrict (Icc F.a F.b),
      planeValue (F.u j x t) =ᵐ[volume] planeValue (F.w j x t) := by
    intro j x
    filter_upwards [F.solution.2.2.1 (j, x)] with t ht
    rw [← ht]
    rw [planeValue, planeValue]
    exact Filter.Eventually.of_forall (fun _ => rfl)
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun x => ae_all_iff.mpr (he j x))),
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun x => ae_all_iff.mpr (hf j x))),
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (hVr j)),
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (hue j)),
    ae_restrict_mem measurableSet_Icc] with t het hft hrt hut hmem
  refine ⟨hmem, ?_⟩
  intro j x
  have hw := letterBloch_jet_integrable (F.w j x t) F.ϖ r hϖ hr (het j x)
  refine ⟨hut j x, ?_, ?_, hw⟩
  · intro e β
    have hi : Integrable (fun y => momentWeight β y * inner ℝ e (planeValue (F.w j x t) y)) := by
      simpa only [planeValue, innerSL_apply_apply, inner_smul_right] using
        (innerSL ℝ e).integrable_comp (hw β 0 (fun i => i.elim0))
    apply hi.congr
    filter_upwards [hut j x] with y hy
    rw [hy]
  · intro e β k
    have hi := letterBloch_jet_integrable (V j x t) F.ϖ s hϖ hs (hft j x) β 0 (fun i => i.elim0)
    have hi' := ((innerSL ℝ e).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h x) k)).integrable_comp hi
    apply hi'.congr
    filter_upwards [hrt j x] with y hy
    change inner ℝ e ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h x) k)
      (momentWeight β y • planeValue (V j x t) y)) = _
    rw [map_smul, inner_smul_right, PiLp.proj_apply, hy]
end

/-! The letter identity on its actual word frame. -/

section
universe u v
variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- The same-level periodization algebra applied to the genuine frame. -/
theorem letterBlochClause1
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) :
    LetterBlochClause1 F := by
  intro θ r hr j x e β φ hφ hp
  have hφ1 : ContDiff ℝ (1 : ℕ) φ := hφ.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))
  exact clause1_core θ (F.G r) (F.v r) (F.piece.hvs r).continuous
    (F.piece.hv.2.2.1 r) β e (planeValue (F.u j x r))
    (fun y k => inner ℝ e (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ
      (fun q => F.w q.1 q.2 r) (j, x) r y k))
    ((hr.2 j x).2.1 e) ((hr.2 j x).2.2.1 e) hφ.continuous hp
    (fun k => (contDiff_fibreCovDeriv (j := 0) (by simpa using hφ1) (-θ) k).continuous)
    (fun k => isZ2Periodic_fibreCovDeriv hp (-θ) k)

/-- One slow derivative evaluated on fixed directions keeps every reserved fast derivative. -/
theorem letterBloch_slow_coefficient_contDiff
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin Nw) (x x' : ι) (o : Finset.Icc 2 D)
    (q : Fin ((F.letters j).edge x x' o).length) (α : DerivativeWord2 (o.1 - 1))
    (r : ℝ) (hr : r ∈ Icc F.a F.b) (s : ℕ) (hs : s ≤ (F.letters j).slow)
    (ω : DerivativeWord2 s) (k : Fin 2) :
    ContDiff ℝ (F.J : ℕ) (fun y => iteratedFDeriv ℝ s
      (fun X => (((F.letters j).edge x x' o).get q).coeff α r X y k) F.X₀
      (fun i => basisVec (ω i))) := by
  have hj := Weighted.letter_coefficient_joint_contDiff F.π (F.letters j) F.a F.b F.J F.H
    (F.piece.hlet j) x x' o q α r hr
  have hf := (contDiff_pi.mp hj k).of_le
    (show (F.J + s : WithTop ℕ∞) ≤ ((F.letters j).slow + F.J : ℕ) by exact_mod_cast (show F.J + s ≤ (F.letters j).slow + F.J by omega))
  have hh := Weighted.joint_partialIteratedFDeriv_left_contDiff F.J s _ hf
  have ha : ContDiff ℝ (F.J : ℕ) (fun y => iteratedFDeriv ℝ s
      (fun X => (((F.letters j).edge x x' o).get q).coeff α r X y k) F.X₀) :=
    hh.comp (contDiff_const.prodMk contDiff_id)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Vec 2) ℝ
    (fun i => basisVec (ω i))).contDiff.comp ha

/-- Fast periodicity is preserved by a derivative in the independent slow variable. -/
theorem letterBloch_slow_coefficient_periodic {d s : ℕ} {E E' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (γ : Constituent d E E') (α : DerivativeWord2 (d - 1)) (r : ℝ) (X₀ : Vec 2)
    (ω : DerivativeWord2 s) (k : Fin 2) :
    AVenhance.IsZ2Periodic (fun y => iteratedFDeriv ℝ s (fun X => γ.coeff α r X y k)
      X₀ (fun i => basisVec (ω i))) := by
  intro n y
  have he : (fun X => γ.coeff α r X (y + AVenhance.latticeShift n) k) =
      (fun X => γ.coeff α r X y k) := by
    funext X
    rw [γ.periodic α r X n y]
  change iteratedFDeriv ℝ s (fun X => γ.coeff α r X (y + AVenhance.latticeShift n) k) X₀ _ = _
  rw [he]
end

/-! The full weak letter Bloch identity, with finite test regularity. -/

section
universe u v

/-- A.e. equality of plane representatives preserves their literal Bloch sums a.e. on the cell. -/
theorem letterBloch_planeBlochC_congr (θ : Vec 2) {g g' : Vec 2 → ℝ}
    (he : g =ᵐ[volume] g') :
    planeBlochC θ g =ᵐ[volume.restrict AVenhance.unitCube] planeBlochC θ g' := by
  have hs : ∀ n : Fin 2 → ℤ, ∀ᵐ z ∂volume.restrict AVenhance.unitCube,
      g (z + AVenhance.latticeShift n) = g' (z + AVenhance.latticeShift n) :=
    fun n => ((measurePreserving_add_right volume (AVenhance.latticeShift n)).quasiMeasurePreserving.ae_eq_comp he).restrict
  filter_upwards [ae_all_iff.mpr hs] with z hz
  unfold planeBlochC
  exact tsum_congr (fun n => congrArg (fun a : ℝ =>
    Complex.exp (-(Complex.I * (vecDot θ (z + AVenhance.latticeShift n) : ℂ))) * (a : ℂ)) (hz n))

/-- Value a.e. equality suffices for the entire finite jet-to-value pairing. -/
theorem letterBloch_jetPair_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) {g g' : Vec 2 → E} (he : g =ᵐ[volume] g')
    (c : Vec 2 → ℝ) {n : ℕ} (α : DerivativeWord2 n) (ψ : Vec 2 → ℂ) :
    b1wJetPair θ β e g c α ψ = b1wJetPair θ β e g' c α ψ := by
  unfold b1wJetPair
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply integral_congr_ae
  filter_upwards [letterBloch_planeBlochC_congr θ (he.mono (fun y hy =>
    congrArg (fun v => momentWeight (β.1 - a.1, β.2 - a.2) y * inner ℝ e v) hy))] with z hz
  rw [b1wStageFun, b1wStageFun, hz]

private theorem letterBloch_pair_finset (θ : Vec 2) {ψ : Vec 2 → ℂ}
    (hc : Continuous ψ) (hp : AVenhance.IsZ2Periodic ψ) (m : Vec 2 → ℝ)
    {A : Type*} (s : Finset A) (f : A → Vec 2 → ℝ) (q : A → ℂ)
    (h : ∀ i ∈ s, Integrable (fun y => m y * f i y) ∧
      (∫ z in AVenhance.unitCube, planeBlochC θ (fun y => m y * f i y) z * ψ z) = q i) :
    Integrable (fun y => m y * ∑ i ∈ s, f i y) ∧
      (∫ z in AVenhance.unitCube, planeBlochC θ (fun y => m y * ∑ i ∈ s, f i y) z * ψ z) =
        ∑ i ∈ s, q i := by
  have hi := integrable_finsetSum s (fun i hi => (h i hi).1)
  refine ⟨by simpa only [Finset.mul_sum] using hi, ?_⟩
  simp_rw [Finset.mul_sum]
  rw [cell_pair_sum θ s (fun i hi => (h i hi).1) hc hp]
  exact Finset.sum_congr rfl (fun i hi => (h i hi).2)

private theorem letterBloch_pair_list (θ : Vec 2) {ψ : Vec 2 → ℂ}
    (hc : Continuous ψ) (hp : AVenhance.IsZ2Periodic ψ) (m : Vec 2 → ℝ)
    {A : Type*} (L : List A) (f : A → Vec 2 → ℝ) (q : A → ℂ)
    (h : ∀ i ∈ L, Integrable (fun y => m y * f i y) ∧
      (∫ z in AVenhance.unitCube, planeBlochC θ (fun y => m y * f i y) z * ψ z) = q i) :
    Integrable (fun y => m y * (L.map (fun i => f i y)).sum) ∧
      (∫ z in AVenhance.unitCube, planeBlochC θ (fun y => m y * (L.map (fun i => f i y)).sum) z * ψ z) =
        (L.map q).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero, planeBlochC, Complex.ofReal_zero,
      tsum_zero, zero_mul, integral_zero]; exact ⟨integrable_zero _ _ _, True.intro⟩
  | cons a L ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [List.map_cons, List.sum_cons, mul_add]
    exact ⟨ha.1.add ht.1, (cell_pair_add θ ha.1 ht.1 hc hp).trans (congrArg₂ (· + ·) ha.2 ht.2)⟩

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- Each Taylor term has its integrable plane representative and exact weak value pairing. -/
theorem letterBloch_taylor_term
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (horder : ∀ i, (F.letters i).order ≤ F.J) (θ : Vec 2) (r : ℝ) (hr : LetterBlochGood F r)
    (j : Fin Nw) (x x' : ι) (e : h x) (β : ℕ × ℕ) (k : Fin 2)
    (o : Finset.Icc 2 D) (ho : o.1 ∈ admissibleOrders
      (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (j.succ, x) (j.castSucc, x'))
    (γ : Constituent o.1 (h x') (h x)) (hγ : γ ∈ (F.letters j).edge x x' o)
    (α : DerivativeWord2 (o.1 - 1)) (s : ℕ) (hs : s ≤ (F.letters j).slow)
    (ω : DerivativeWord2 s) (ψ : Vec 2 → ℂ)
    (hψ : ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) ψ)
    (hψp : AVenhance.IsZ2Periodic ψ) :
    let c := fun y => iteratedFDeriv ℝ s (fun X => γ.coeff α r X y k) F.X₀ (fun i => basisVec (ω i))
    let B := (β.1 + (wordCount ω).1, β.2 + (wordCount ω).2)
    let A := (F.ϖ * F.ηg) ^ s / (s.factorial : ℝ)
    Integrable (fun y => momentWeight β y * (A * momentWeight (wordCount ω) y * c y *
      inner ℝ (ContinuousLinearMap.adjoint γ.map e) (planeJetOrder (F.w j.castSucc x' r) (o.1 - 1) α y))) ∧
    (∫ z in AVenhance.unitCube, planeBlochC θ (fun y => momentWeight β y *
      (A * momentWeight (wordCount ω) y * c y * inner ℝ (ContinuousLinearMap.adjoint γ.map e)
        (planeJetOrder (F.w j.castSucc x' r) (o.1 - 1) α y))) z * ψ z) =
      (A : ℂ) * b1wJetPair θ B (ContinuousLinearMap.adjoint γ.map e)
        (planeValue (F.u j.castSucc x' r)) c α ψ := by
  classical
  dsimp only
  have hod : o.1 ≤ (F.letters j).order := by
    by_contra hh
    have hempty := (F.piece.hlet j).edge_order x x' o (Nat.lt_of_not_ge hh)
    rw [hempty] at hγ
    exact List.not_mem_nil hγ
  have hnJ : o.1 - 1 ≤ F.J := (Nat.sub_le _ _).trans (hod.trans (horder j))
  have hnd : o.1 - 1 ≤ F.κ j.castSucc x' + 1 := by
    have h := (Finset.mem_filter.mp ho).2
    dsimp only at h
    omega
  have hmax : ((o.1 - 1 : ℕ) : WithTop ℕ∞) ≤
      Finset.univ.sup (fun l => ((F.letters l).order : WithTop ℕ∞)) :=
    (show ((o.1 - 1 : ℕ) : WithTop ℕ∞) ≤ ((F.letters j).order : WithTop ℕ∞) by
      exact_mod_cast (Nat.sub_le o.1 1).trans hod).trans
        (Finset.le_sup (f := fun l => ((F.letters l).order : WithTop ℕ∞)) (Finset.mem_univ j))
  obtain ⟨q, hq⟩ := List.mem_iff_get.mp hγ
  subst γ
  let c := fun y => iteratedFDeriv ℝ s
    (fun X => (((F.letters j).edge x x' o).get q).coeff α r X y k) F.X₀ (fun i => basisVec (ω i))
  let B := (β.1 + (wordCount ω).1, β.2 + (wordCount ω).2)
  let A := (F.ϖ * F.ηg) ^ s / (s.factorial : ℝ)
  let e' := ContinuousLinearMap.adjoint (((F.letters j).edge x x' o).get q).map e
  let W := F.w j.castSucc x' r
  have hc : ContDiff ℝ (o.1 - 1 : ℕ) c :=
    (letterBloch_slow_coefficient_contDiff F j x x' o q α r hr.1 s hs ω k).of_le (by exact_mod_cast hnJ)
  have hcp : AVenhance.IsZ2Periodic c := letterBloch_slow_coefficient_periodic _ α r F.X₀ ω k
  have hi : Integrable (fun y => momentWeight B y * inner ℝ e' (planeJetOrder W (o.1 - 1) α y)) := by
    simpa only [innerSL_apply_apply, inner_smul_right] using
      (innerSL ℝ e').integrable_comp ((hr.2 j.castSucc x').2.2.2 B (o.1 - 1) α)
  have hit := integrable_periodic_mul hc.continuous hcp hi
  have heq : (fun y => momentWeight β y * (A * momentWeight (wordCount ω) y * c y *
      inner ℝ e' (planeJetOrder W (o.1 - 1) α y))) =
      (fun y => A * (c y * (momentWeight B y * inner ℝ e' (planeJetOrder W (o.1 - 1) α y)))) := by
    funext y
    dsimp only [B, momentWeight]
    simp only [pow_add]
    ring
  change Integrable (fun y => momentWeight β y * (A * momentWeight (wordCount ω) y * c y *
    inner ℝ e' (planeJetOrder W (o.1 - 1) α y))) ∧ _
  rw [heq]
  refine ⟨hit.const_mul A, ?_⟩
  rw [cell_pair_const_mul θ A hψ.continuous hψp hit,
    cell_pair_periodic_mul θ hc.continuous hcp hi hψ.continuous hψp,
    weakJetToValue (h x') θ (F.κ j.castSucc x' + 1) (o.1 - 1) hnd α B W e'
      ((hr.2 j.castSucc x').2.2.2) c ψ hc hcp (hψ.of_le hmax) hψp]
  rw [letterBloch_jetPair_congr θ B e' ((hr.2 j.castSucc x').1.symm) c α ψ]

/-- The previous-letter flux identity, with only the actual maximum letter order of tests. -/
theorem letterBlochClause3
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) :
    LetterBlochClause3 F := by
  classical
  intro horder θ r hr j x e β k ψ hψ hψp
  have hc := hψ.continuous
  have hcert : Integrable (fun y => momentWeight β y * inner ℝ e
      (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ
        (fun q => F.w q.1 q.2 r) (j.succ, x) r y k)) ∧
      b1wFluxPair F θ j.succ x e β k r ψ = b1wLetterExpansion F θ j x e β k r ψ := by
    unfold b1wFluxPair b1wLetterExpansion
    simp_rw [letterFluxPointwise F j x e k r]
    apply letterBloch_pair_finset θ hc hψp
    intro x' _
    apply letterBloch_pair_finset θ hc hψp
    intro d hd
    have hdi := (Finset.mem_filter.mp hd).1
    simp only [dite_eq_left hdi]
    apply letterBloch_pair_list θ hc hψp
    intro γ hγ
    apply letterBloch_pair_finset θ hc hψp
    intro α _
    apply letterBloch_pair_finset θ hc hψp
    intro s hs
    apply letterBloch_pair_finset θ hc hψp
    intro ω _
    exact letterBloch_taylor_term F horder θ r hr j x x' e β k ⟨d, hdi⟩ hd γ hγ α s
      (Finset.mem_Icc.mp hs).2 ω ψ hψ hψp
  exact hcert.2

/-- The exact finite-regularity letter Bloch identity. -/
theorem letterBloch : LetterBlochStatement.{u, v} := by
  intro K g₁ ι _ h _ _ _ _ _ _ D Nw F θ horder
  exact letterBloch_frame F (letterBlochIntegrableAE F) (letterBlochClause1 F)
    (letterBlochClause2 F) (letterBlochClause3 F) θ horder
end

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # The sharp slow test: the crude bound proved

The crude `H^j` bound of `q - E·1` (`SharpSlowCrudeStatement`), from `sharpSlow_crude_curve` and the
proved `cellDriftRegularity`. -/

/-- The constant class has norm `≤ (‖1‖ + ‖I‖)|c|` in `TorusHk j ℂ`. -/
theorem sharpSlow_const_norm (j : ℕ) (c : ℂ) :
    ‖torusHigherConstant j c‖ ≤
      (‖torusHigherConstant j 1‖ + ‖torusHigherConstant j Complex.I‖) * ‖c‖ := by
  have hc : torusHigherConstant j c =
      c.re • torusHigherConstant j 1 + c.im • torusHigherConstant j Complex.I := by
    apply sharpSlow_value_injective
    rw [map_add, map_smul, map_smul, torusHigherConstant_value, torusHigherConstant_value,
      torusHigherConstant_value, ← map_smul, ← map_smul, ← map_add]
    congr 1
    apply Complex.ext <;> simp
  rw [hc]
  calc ‖c.re • torusHigherConstant j 1 + c.im • torusHigherConstant j Complex.I‖
      ≤ ‖c.re • torusHigherConstant j 1‖ + ‖c.im • torusHigherConstant j Complex.I‖ :=
        norm_add_le _ _
    _ = |c.re| * ‖torusHigherConstant j 1‖ + |c.im| * ‖torusHigherConstant j Complex.I‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖c‖ * ‖torusHigherConstant j 1‖ + ‖c‖ * ‖torusHigherConstant j Complex.I‖ := by
        gcongr
        · exact Complex.abs_re_le_norm c
        · exact Complex.abs_im_le_norm c
    _ = _ := by ring

/-- **The crude bound of the sharp slow test.** -/
theorem sharpSlowCrude : SharpSlowCrudeStatement := by
  intro K j ρ hρ0 hρ1
  obtain ⟨Cc, Q, hCc, hcr⟩ := sharpSlow_crude_curve (K := K) cellDriftRegularity j
    (ρ := max ρ 0) (le_max_right _ _) (fun l => |K.Cvj l|) (fun l => abs_nonneg _)
  set κ := ‖torusHigherConstant j 1‖ + ‖torusHigherConstant j Complex.I‖ with hκ
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨Cc + κ, Q, ?_⟩
  intro s r hr
  have hξ : fibreNorm s.ξ ≤ max ρ 0 := s.hξρ.trans (le_max_left _ _)
  have hvj : ∀ (l : ℕ) t z, ‖iteratedFDeriv ℝ l (fun z' => Real.sqrt s.η • s.v t z') z‖ ≤
      |K.Cvj l| := fun l t z => (s.hvj l t z).trans (le_abs_self _)
  obtain ⟨w, hw, hn⟩ := hcr s.η s.G s.v s.ξ s.H s.pkg.actual s.hη hξ s.hvs hvj s.V s.hb' s.hab
    s.u s.slice s.hu s.hu1 r hr
  refine ⟨w - torusHigherConstant j (star (s.E r)), ?_, ?_⟩
  · rw [map_sub, torusHigherConstant_value, hw]; rfl
  · have hpe : 1 ≤ peFactor s.η ^ Q := one_le_pow₀ (AVRegularity.CycleWords.Assembly.one_le_peFactor s.η)
    calc ‖w - torusHigherConstant j (star (s.E r))‖
        ≤ ‖w‖ + ‖torusHigherConstant j (star (s.E r))‖ := norm_sub_le _ _
      _ ≤ Cc * peFactor s.η ^ Q * ‖s.E r‖ + κ * ‖s.E r‖ :=
          add_le_add hn ((sharpSlow_const_norm j _).trans_eq (by rw [norm_star]))
      _ ≤ (Cc + κ) * peFactor s.η ^ Q * ‖s.E r‖ := by
          have h0 : 0 ≤ ‖s.E r‖ := norm_nonneg _
          nlinarith [mul_nonneg hκ0 h0, mul_nonneg (mul_nonneg hκ0 h0) (sub_nonneg.2 hpe)]

/-- **The sharp slow test from the three remaining open steps** (the quiet and window cases of the
one-step inequality, and the transversality defect). -/
theorem sharpSlowTest_of_cases (hQ : QuietHsDecayStatement) (hq : SharpSlowQuietStepStatement)
    (hw : SharpSlowWindowStepStatement) (hT : SharpSlowDefectStatement) :
    SharpSlowTestStatement :=
  sharpSlowTest_of_steps hQ sharpSlowCrude (sharpSlowStep_of_cases hq hw) hT

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # Only earlier stages appear in the stage expansion

`stageTransformEarlier`: the test transform `T_{i,i'}` vanishes unless `i'` is an earlier stage. -/

section
universe u v

section Order

variable {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {Nw m : ℕ} {Ks : Fin Nw → ℕ}

theorem stageExp_St_lt_of_deg_lt {i i' : B1WIndex ι h Nw m Ks} (hd : b1wDeg i' < b1wDeg i) :
    b1wSt i' < b1wSt i := by
  unfold b1wSt
  have := i'.1.isLt
  have h2 : (b1wDeg i' + 1) * (Nw + 1) ≤ b1wDeg i * (Nw + 1) := Nat.mul_le_mul_right _ hd
  nlinarith

theorem stageExp_St_lt_of_deg_le {i i' : B1WIndex ι h Nw m Ks} (hd : b1wDeg i' ≤ b1wDeg i)
    (hl : i'.1 < i.1) : b1wSt i' < b1wSt i := by
  rcases hd.lt_or_eq with hd | hd
  · exact stageExp_St_lt_of_deg_lt hd
  · unfold b1wSt
    rw [hd]
    have : i'.1.val < i.1.val := hl
    omega

theorem stageExp_prefix_succ {Nw : ℕ} (Ks : Fin Nw → ℕ) (l : Fin Nw) :
    b1wPrefix Ks l.succ = b1wPrefix Ks l.castSucc + Ks l := by
  unfold b1wPrefix
  have : ∀ l' : Fin Nw, (if l'.val < l.succ.val then Ks l' else 0) =
      (if l'.val < l.castSucc.val then Ks l' else 0) + (if l' = l then Ks l' else 0) := by
    intro l'
    simp only [Fin.val_succ, Fin.val_castSucc]
    by_cases h1 : l'.val < l.val
    · have : l' ≠ l := fun h => by simp [h] at h1
      simp [h1, this]
      omega
    · by_cases h2 : l' = l
      · subst h2; simp
      · have : ¬ l'.val < l.val + 1 := by
          have : l'.val ≠ l.val := fun h => h2 (Fin.ext h)
          omega
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl fun l' _ => this l', Finset.sum_add_distrib]
  simp

theorem stageExp_levelMoments_castSucc {Nw : ℕ} (m : ℕ) (Ks : Fin Nw → ℕ) (l : Fin Nw) :
    b1wLevelMoments m Ks l.castSucc = b1wLevelMoments m Ks l.succ + Ks l := by
  have h1 := b1wPrefix_add_levelMoments m Ks l.castSucc
  have h2 := b1wPrefix_add_levelMoments m Ks l.succ
  rw [stageExp_prefix_succ] at h2
  omega

end Order

section Transform

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw m : ℕ}
  {Ks : Fin Nw → ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- A letter part vanishes when the moment of `i'` exceeds `|β₀| + slow`. -/
theorem stageExp_letterPart_eq_zero
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (l : Fin Nw)
    (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (ψ : Vec 2 → ℂ)
    (i' : B1WIndex ι h Nw m Ks)
    (H : β₀.1 + β₀.2 + (F.letters l).slow < (b1wMom i').1 + (b1wMom i').2) (z : Vec 2) :
    b1wLetterPart F θ l x e β₀ k r ψ i' z = 0 := by
  unfold b1wLetterPart
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, ↓reduceDIte]
    refine List.sum_eq_zero fun a ha => ?_
    obtain ⟨γ, _, rfl⟩ := List.mem_map.1 ha
    refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun s hs =>
      Finset.sum_eq_zero fun ω _ => ?_
    have hs' := (Finset.mem_Icc.1 hs).2
    have hw := wordCount_sum ω
    rw [Finset.sum_eq_zero (fun a _ => ?_)]
    · simp
    · split_ifs with hc
      · exfalso
        rw [hc] at H
        simp only at H
        omega
      · rfl
  · simp only [hd, ↓reduceDIte]

theorem stageExp_ite_mul_zero {C : Prop} [Decidable C] (a b : ℂ) (h : C → a = 0) :
    (if C then a * b else 0) = 0 := by
  split_ifs with hc
  · rw [h hc, zero_mul]
  · rfl

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem stageExp_sameTransform_eq_zero (θ : Vec 2) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (vf : Vec 2 → Vec 2) (i i' : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ)
    (hn : ¬ b1wSt i' < b1wSt i) (z : Vec 2) : b1wSameTransform θ G vf i i' φ z = 0 := by
  unfold b1wSameTransform
  by_cases hl : i'.1 = i.1
  · simp only [hl, ↓reduceIte]
    have hd : ¬ b1wDeg i' < b1wDeg i := fun hd => hn (stageExp_St_lt_of_deg_lt hd)
    have hp : b1wPrefix Ks i'.1 = b1wPrefix Ks i.1 := by rw [hl]
    unfold b1wDeg at hd
    rw [hp] at hd
    change ¬ (b1wMom i').1 + (b1wMom i').2 + b1wPrefix Ks i.1 <
      (b1wMom i).1 + (b1wMom i).2 + b1wPrefix Ks i.1 at hd
    generalize b1wMom i = mi at *
    generalize b1wMom i' = mi' at *
    obtain ⟨p, q⟩ := mi
    obtain ⟨p', q'⟩ := mi'
    simp only at hd ⊢
    rw [stageExp_ite_mul_zero _ _ ?c1, stageExp_ite_mul_zero _ _ ?c2,
      stageExp_ite_mul_zero _ _ ?c3, stageExp_ite_mul_zero _ _ ?c4,
      stageExp_ite_mul_zero _ _ ?c5]
    · simp
    all_goals
      intro hc
      simp only [Prod.mk.injEq] at hc
      first
        | (have : p < 2 := by omega
           interval_cases p <;> simp
           done)
        | (have : q < 2 := by omega
           interval_cases q <;> simp
           done)
        | (have : p = 0 := by omega
           subst this; simp)
        | (have : q = 0 := by omega
           subst this; simp)
  · simp only [hl, ↓reduceIte]

/-- **Only earlier stages appear in the expansion.** -/
theorem stageTransformEarlier : StageTransformEarlierStatement.{u, v} := by
  intro K g₁ ι _ h _ _ _ _ _ _ D Nw F θ m Ks hslow i i' hn r φ
  funext z
  unfold b1wTestTransform
  rw [stageExp_sameTransform_eq_zero θ (F.G r) (F.v r) i i' φ hn z, zero_add]
  unfold b1wLetterTransform
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hc : i.1 = l.succ ∧ i'.1 = l.castSucc
  · simp only [hc, and_self, ↓reduceIte]
    have hdeg : ¬ b1wDeg i' ≤ b1wDeg i := fun hd =>
      hn (stageExp_St_lt_of_deg_le hd (by rw [hc.1, hc.2]; exact Fin.castSucc_lt_succ))
    unfold b1wDeg at hdeg
    have hp : b1wPrefix Ks i.1 = b1wPrefix Ks i'.1 + Ks l := by
      rw [hc.1, hc.2]; exact stageExp_prefix_succ Ks l
    rw [hp] at hdeg
    have hm : (b1wMom i).1 + (b1wMom i).2 + Ks l < (b1wMom i').1 + (b1wMom i').2 := by
      change ¬ (b1wMom i').1 + (b1wMom i').2 + b1wPrefix Ks i'.1 ≤
        (b1wMom i).1 + (b1wMom i).2 + (b1wPrefix Ks i'.1 + Ks l) at hdeg
      omega
    have hs := hslow l
    have h1 := stageExp_letterPart_eq_zero F θ l i.2.1 (b1wVec i) ((b1wMom i).1 - 1, (b1wMom i).2)
      0 r φ i' (by simp only; omega) z
    have h2 := stageExp_letterPart_eq_zero F θ l i.2.1 (b1wVec i) ((b1wMom i).1, (b1wMom i).2 - 1)
      1 r φ i' (by simp only; omega) z
    have h3 : ∀ k : Fin 2, b1wLetterPart F θ l i.2.1 (b1wVec i) (b1wMom i) k r
        (fibreCovDeriv (-θ) k φ) i' z = 0 := fun k =>
      stageExp_letterPart_eq_zero F θ l i.2.1 (b1wVec i) (b1wMom i) k r _ i' (by omega) z
    simp [h1, h2, h3]
  · simp only [hc, ↓reduceIte]

end Transform
end

/-! # The letter expansion over the stages of the previous level

`stageExp_letter_key`: the letter expansion `b1wLetterExpansion` equals the sum, over the stages
`(l, x', β', b')` of the previous level, of the cell pairings of their values with the letter
parts `b1wLetterPart`. -/

section
universe u v

section Regularity

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
  {K : ScalarConstants} {g₁ : ℝ}

/-- The `X`-jets of the coefficients of a letter are `C^J` in the fast variable and periodic. -/
theorem stageExp_coeff_jet
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (l : Fin Nw) (x x' : ι)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 D) (γ : Constituent d (h x') (h x))
    (hγ : γ ∈ (F.letters l).edge x x' ⟨d, hd⟩) (α : DerivativeWord2 (d - 1)) (k : Fin 2)
    (s : ℕ) (hs : s ≤ (F.letters l).slow) (ω : DerivativeWord2 s) (r : ℝ)
    (hr : r ∈ Icc F.a F.b) :
    ContDiff ℝ F.J (fun z => iteratedFDeriv ℝ s (fun X => γ.coeff α r X z k) F.X₀
        (fun n => basisVec (ω n))) ∧
      AVenhance.IsZ2Periodic (fun z => iteratedFDeriv ℝ s (fun X => γ.coeff α r X z k) F.X₀
        (fun n => basisVec (ω n))) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨q, rfl⟩ := List.mem_iff_get.1 hγ
    have hj := AVRegularity.Weighted.letter_coefficient_joint_contDiff F.π (F.letters l) F.a F.b
      F.J F.H (F.piece.hlet l) x x' ⟨d, hd⟩ q α r hr
    have hk : ContDiff ℝ (F.J + s : ℕ) (fun p : Vec 2 × Vec 2 =>
        ((F.letters l).edge x x' ⟨d, hd⟩).get q |>.coeff α r p.1 p.2 k) :=
      (contDiff_pi.mp hj k).of_le (by exact_mod_cast (show F.J + s ≤ (F.letters l).slow + F.J by omega))
    have hh := AVRegularity.Weighted.joint_partialIteratedFDeriv_left_contDiff F.J s _ hk
    have hc : ContDiff ℝ F.J (fun z : Vec 2 =>
        iteratedFDeriv ℝ s (fun X => (((F.letters l).edge x x' ⟨d, hd⟩).get q).coeff α r X z k)
          F.X₀) := hh.comp (contDiff_const.prodMk contDiff_id)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Vec 2) ℝ
      (fun n => basisVec (ω n))).contDiff.comp hc
  · intro n z
    have : ∀ X, γ.coeff α r X (z + AVenhance.latticeShift n) = γ.coeff α r X z :=
      fun X => γ.periodic α r X n z
    simp only [this]

/-- The letter coefficient test is a continuous periodic function. -/
theorem stageExp_atom_test
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (hord : ∀ l, (F.letters l).order ≤ F.J) (θ : Vec 2) (l : Fin Nw) (x x' : ι)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 D) (γ : Constituent d (h x') (h x))
    (hγ : γ ∈ (F.letters l).edge x x' ⟨d, hd⟩) (α : DerivativeWord2 (d - 1)) (k : Fin 2)
    (s : ℕ) (hs : s ≤ (F.letters l).slow) (ω : DerivativeWord2 s) (r : ℝ)
    (hr : r ∈ Icc F.a F.b) (ψ : Vec 2 → ℂ)
    (hψ : ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) ψ)
    (hψp : AVenhance.IsZ2Periodic ψ) (b : ℕ × ℕ) (hb : b.1 + b.2 ≤ d - 1) :
    fibreCovPow (-θ) b (fun z' => ((iteratedFDeriv ℝ s (fun X => γ.coeff α r X z' k) F.X₀
        (fun n => basisVec (ω n)) : ℝ) : ℂ) * ψ z') ∈ stageTests := by
  have hdo : d ≤ (F.letters l).order := by
    by_contra hlt
    have := (F.piece.hlet l).edge_order x x' ⟨d, hd⟩ (not_le.1 hlt)
    rw [this] at hγ
    simp at hγ
  have hdJ : d ≤ F.J := hdo.trans (hord l)
  obtain ⟨hc, hcp⟩ := stageExp_coeff_jet F l x x' d hd γ hγ α k s hs ω r hr
  have hφ : ContDiff ℝ (0 + b.1 + b.2 : ℕ) (fun z' => ((iteratedFDeriv ℝ s
      (fun X => γ.coeff α r X z' k) F.X₀ (fun n => basisVec (ω n)) : ℝ) : ℂ) * ψ z') := by
    refine (Complex.ofRealCLM.contDiff.comp (hc.of_le ?_)).mul (hψ.of_le ?_)
    · exact_mod_cast (show 0 + b.1 + b.2 ≤ F.J by omega)
    · exact (Nat.cast_le.2 (show 0 + b.1 + b.2 ≤ (F.letters l).order by omega)).trans
        (Finset.le_sup (f := fun l => (((F.letters l).order : ℕ) : WithTop ℕ∞))
          (Finset.mem_univ l))
  refine ⟨(contDiff_fibreCovPow (-θ) b 0 hφ).continuous, isZ2Periodic_fibreCovPow (-θ) b ?_⟩
  intro n z
  simp only [hcp n z, hψp n z]

/-- Moments of the values are integrable against any vector. -/
theorem stageExp_integrable_moment
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (hM : AmplitudeIdMoments F)
    (j : Fin (Nw + 1)) (x : ι) (r : ℝ) (hr : r ∈ Icc F.a F.b) (β : ℕ × ℕ) (e : h x) :
    Integrable (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x r) y)) := by
  have hI := hM j x r hr (β.1 + β.2) β (by
    simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega)
  have := (innerSL ℝ e).integrable_comp hI
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [momentWeight]

/-- The summands of `b1wLetterPart` at the stage with component `x'`, moment `β'` and vector
index `b'`. -/
def stageLetterR
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (_l : Fin Nw)
    (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (ψ : Vec 2 → ℂ) (x' : ι)
    (β' : ℕ × ℕ) (b' : Fin (Module.finrank ℝ (h x'))) : LetterArgs (h := h) D x x' (Vec 2 → ℂ) :=
  fun d _ γ α s ω z =>
    ((((F.ϖ * F.ηg) ^ s / (s.factorial : ℝ)) : ℝ) : ℂ) *
      ((-1 : ℂ) ^ (d - 1) * ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
          Finset.range ((wordCount α).2 + 1),
        if β' = (β₀.1 + (wordCount ω).1 - a.1, β₀.2 + (wordCount ω).2 - a.2) then
          ((((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
              (β₀.1 + (wordCount ω).1).descFactorial a.1 *
              (β₀.2 + (wordCount ω).2).descFactorial a.2 : ℕ) : ℂ) *
            (inner ℝ (ContinuousLinearMap.adjoint γ.map e) (stdOrthonormalBasis ℝ (h x') b') : ℂ) *
            fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
              (fun z' => ((iteratedFDeriv ℝ s (fun X => γ.coeff α r X z' k) F.X₀
                (fun n => basisVec (ω n)) : ℝ) : ℂ) * ψ z') z)
        else 0)

/-- The summands of `b1wLetterExpansion` for the component `x'`. -/
def stageLetterL
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (l : Fin Nw)
    (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (ψ : Vec 2 → ℂ) (x' : ι) :
    LetterArgs (h := h) D x x' ℂ :=
  fun _ _ γ α s ω =>
    ((((F.ϖ * F.ηg) ^ s / (s.factorial : ℝ)) : ℝ) : ℂ) *
      b1wJetPair θ (β₀.1 + (wordCount ω).1, β₀.2 + (wordCount ω).2)
        (ContinuousLinearMap.adjoint γ.map e) (planeValue (F.u l.castSucc x' r))
        (fun y => iteratedFDeriv ℝ s (fun X => γ.coeff α r X y k) F.X₀
          (fun i => basisVec (ω i))) α ψ

theorem b1wLetterExpansion_eq
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (l : Fin Nw)
    (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (ψ : Vec 2 → ℂ) :
    b1wLetterExpansion F θ l x e β₀ k r ψ =
      ∑ x' : ι, letterBig F l x x' (stageLetterL F θ l x e β₀ k r ψ x') := rfl

/-- **The letter expansion over the stages of the previous level.** -/
theorem stageExp_letter_key {m : ℕ} {Ks : Fin Nw → ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (hslow : ∀ l, (F.letters l).slow = Ks l) (hord : ∀ l, (F.letters l).order ≤ F.J)
    (hM : AmplitudeIdMoments F) (θ : Vec 2) (l : Fin Nw) (x : ι) (e : h x) (β₀ : ℕ × ℕ)
    (hβ₀ : β₀.1 + β₀.2 ≤ b1wLevelMoments m Ks l.succ) (k : Fin 2) (r : ℝ)
    (hr : r ∈ Icc F.a F.b) (ψ : Vec 2 → ℂ)
    (hψ : ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) ψ)
    (hψp : AVenhance.IsZ2Periodic ψ) :
    b1wLetterExpansion F θ l x e β₀ k r ψ =
      ∑ x' : ι, ∑ β' : {β' // β' ∈ momentIndices (b1wLevelMoments m Ks l.castSucc)},
        ∑ b' : Fin (Module.finrank ℝ (h x')),
          stagePair θ (fun y => momentWeight β'.1 y *
            inner ℝ (stdOrthonormalBasis ℝ (h x') b') (planeValue (F.u l.castSucc x' r) y))
            (b1wLetterPart F θ l x e β₀ k r ψ (⟨l.castSucc, x', β', b'⟩ : B1WIndex ι h Nw m Ks)) := by
  rw [b1wLetterExpansion_eq]
  refine Finset.sum_congr rfl fun x' _ => ?_
  have hG : ∀ (β' : ℕ × ℕ) (b : h x'), Integrable (fun y => momentWeight β' y *
      inner ℝ b (planeValue (F.u l.castSucc x' r) y)) :=
    fun β' b => stageExp_integrable_moment F hM _ _ r hr β' b
  have hR : ∀ (β' : {β' // β' ∈ momentIndices (b1wLevelMoments m Ks l.castSucc)})
      (b' : Fin (Module.finrank ℝ (h x'))),
      ∀ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
        (l.succ, x) (l.castSucc, x'), ∀ hd : d ∈ Finset.Icc 2 D,
      ∀ γ ∈ (F.letters l).edge x x' ⟨d, hd⟩, ∀ α : DerivativeWord2 (d - 1),
      ∀ s ∈ Finset.Icc (if (F.letters l).positive then 1 else 0) (F.letters l).slow,
      ∀ ω : DerivativeWord2 s,
        (fun z => stageLetterR F θ l x e β₀ k r ψ x' β'.1 b' d hd γ α s ω z) ∈ stageTests := by
    intro β' b' d _ hd γ hγ α s hs ω
    refine stageTests_const_mul_mem _ (stageTests_const_mul_mem _ (stageTests_sum_mem _ _
      fun a ha => stageTests_ite_mem _ ?_))
    refine stageExp_atom_test F hord θ l x x' d hd γ hγ α k s (Finset.mem_Icc.1 hs).2 ω r hr ψ hψ
      hψp _ ?_
    simp only [Finset.mem_product, Finset.mem_range] at ha
    have := wordCount_sum α
    omega
  have step1 : ∀ (β' : {β' // β' ∈ momentIndices (b1wLevelMoments m Ks l.castSucc)})
      (b' : Fin (Module.finrank ℝ (h x'))),
      stagePair θ (fun y => momentWeight β'.1 y *
            inner ℝ (stdOrthonormalBasis ℝ (h x') b') (planeValue (F.u l.castSucc x' r) y))
          (b1wLetterPart F θ l x e β₀ k r ψ (⟨l.castSucc, x', β', b'⟩ : B1WIndex ι h Nw m Ks)) =
        letterBig F l x x' (fun d hd γ α s ω => stagePair θ (fun y => momentWeight β'.1 y *
            inner ℝ (stdOrthonormalBasis ℝ (h x') b') (planeValue (F.u l.castSucc x' r) y))
          (stageLetterR F θ l x e β₀ k r ψ x' β'.1 b' d hd γ α s ω)) := fun β' b' =>
    (letterBig_pair F l x x' θ (hG _ _) (stageLetterR F θ l x e β₀ k r ψ x' β'.1 b')
      (hR β' b')).2
  rw [Finset.sum_congr rfl fun β' _ => Finset.sum_congr rfl fun b' _ => step1 β' b']
  have key : letterBig F l x x' (stageLetterL F θ l x e β₀ k r ψ x') =
      letterBig F l x x' (fun d hd γ α s ω =>
        ∑ β' : {β' // β' ∈ momentIndices (b1wLevelMoments m Ks l.castSucc)},
          ∑ b' : Fin (Module.finrank ℝ (h x')), stagePair θ (fun y => momentWeight β'.1 y *
            inner ℝ (stdOrthonormalBasis ℝ (h x') b') (planeValue (F.u l.castSucc x' r) y))
          (stageLetterR F θ l x e β₀ k r ψ x' β'.1 b' d hd γ α s ω)) := by
    refine letterBig_congr F l x x' _ _ fun d hdm hd γ hγ α s hs ω => ?_
    have hs' := (Finset.mem_Icc.1 hs).2
    have hw := wordCount_sum ω
    have hN := stageExp_levelMoments_castSucc m Ks l
    have hsl := hslow l
    exact (stageExp_atom θ (b1wLevelMoments m Ks l.castSucc)
      (β₀.1 + (wordCount ω).1, β₀.2 + (wordCount ω).2) (by simp only; omega)
      (ContinuousLinearMap.adjoint γ.map e) (planeValue (F.u l.castSucc x' r)) hG α
      (fun y => iteratedFDeriv ℝ s (fun X => γ.coeff α r X y k) F.X₀
          (fun i => basisVec (ω i))) ψ
      (fun b hb => stageExp_atom_test F hord θ l x x' d hd γ hγ α k s hs' ω r hr ψ hψ hψp b hb)
      _).symm
  rw [key, letterBig_finset_sum]
  refine Finset.sum_congr rfl fun β' _ => ?_
  exact letterBig_finset_sum F l x x' _ _

/-- Every letter part is a continuous periodic test. -/
theorem stageExp_letterPart_mem {m : ℕ} {Ks : Fin Nw → ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (hord : ∀ l, (F.letters l).order ≤ F.J) (θ : Vec 2) (l : Fin Nw) (x : ι) (e : h x)
    (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (hr : r ∈ Icc F.a F.b) (ψ : Vec 2 → ℂ)
    (hψ : ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) ψ)
    (hψp : AVenhance.IsZ2Periodic ψ) (i' : B1WIndex ι h Nw m Ks) :
    b1wLetterPart F θ l x e β₀ k r ψ i' ∈ stageTests := by
  have := (letterBig_pair F l x i'.2.1 θ (G := fun _ => (0 : ℝ)) (integrable_zero _ _ _)
    (stageLetterR F θ l x e β₀ k r ψ i'.2.1 i'.2.2.1.1 i'.2.2.2) (by
      intro d _ hd γ hγ α s hs ω
      refine stageTests_const_mul_mem _ (stageTests_const_mul_mem _ (stageTests_sum_mem _ _
        fun a ha => stageTests_ite_mem _ ?_))
      refine stageExp_atom_test F hord θ l x i'.2.1 d hd γ hγ α k s (Finset.mem_Icc.1 hs).2 ω r hr
        ψ hψ hψp _ ?_
      simp only [Finset.mem_product, Finset.mem_range] at ha
      have := wordCount_sum α
      omega)).1
  exact this

end Regularity
end

end AVRegularity.CycleWords.Assembly
end
