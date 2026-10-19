-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Infra.Torus.FourierCalculus
public import AVRegularity.CycleComparison.Residual.TimeIntegration

@[expose] public section

section
open MeasureTheory Homogenization AVenhance.Infra.Torus
namespace AVRegularity

/-! Differentiation of a Fourier coefficient with respect to a slow parameter, by differentiation
under the integral sign over the bounded cell. -/

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_smoothFourierCoeff_apply (Λ : F →L[ℝ] ℂ) (n : Fin 2 → ℤ)
    (h : Vec 2 → Vec 2 → F)
    (hdiff : ∀ y, Differentiable ℝ (fun X => h X y))
    (hc : Continuous fun p : Vec 2 × Vec 2 => h p.1 p.2)
    (hc' : ∀ i : Fin 2,
      Continuous fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => h X p.2) p.1 (basisVec i))
    (X e : Vec 2) :
    fderiv ℝ (fun X => smoothFourierCoeff (fun y => Λ (h X y)) n) X e =
      smoothFourierCoeff (fun y => Λ (fderiv ℝ (fun X' => h X' y) X e)) n := by
  have hc'' : ∀ e, Continuous fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => h X p.2) p.1 e := by
    intro e
    have he : e = ∑ i, e i • basisVec i := by
      ext j; simp [basisVec, Pi.single_apply, Finset.sum_apply]
    have : (fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X => h X p.2) p.1 e) =
        fun p => ∑ i, e i • fderiv ℝ (fun X => h X p.2) p.1 (basisVec i) := by
      funext p
      conv_lhs => rw [he]
      simp
    rw [this]
    exact continuous_finsetSum _ fun i _ => continuous_const.smul (hc' i)
  have hκ : Continuous (torusCharacter n) := (torusCharacter_contDiff n).continuous
  let F' : Vec 2 → Vec 2 → (Vec 2 →L[ℝ] ℂ) := fun X' y =>
    torusCharacter n y • (Λ.comp (fderiv ℝ (fun X'' => h X'' y) X'))
  have hF'c : Continuous (fun p : Vec 2 × Vec 2 => F' p.1 p.2) := by
    refine continuous_clm_apply.2 fun e' => ?_
    have : Continuous (fun p : Vec 2 × Vec 2 =>
        torusCharacter n p.2 * Λ (fderiv ℝ (fun X => h X p.2) p.1 e')) :=
      (hκ.comp continuous_snd).mul (Λ.continuous.comp (hc'' e'))
    exact this
  have hF'y : Continuous (fun y => F' X y) := by
    have : Continuous ((fun p : Vec 2 × Vec 2 => F' p.1 p.2) ∘ fun y : Vec 2 => (X, y)) :=
      hF'c.comp (Continuous.prodMk continuous_const continuous_id)
    exact this
  have hcell := Calculus.isCompact_closedUnitCell 2
  obtain ⟨C, hC⟩ := ((isCompact_closedBall X 1).prod hcell).exists_bound_of_continuousOn
    hF'c.continuousOn
  have hdd : HasFDerivAt (fun x => ∫ a in unitCell 2, torusCharacter n a * Λ (h x a))
      (∫ a in unitCell 2, F' X a) X := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball X 1)
      (bound := fun _ => C) (Metric.ball_mem_nhds X one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun x => Continuous.aestronglyMeasurable ?_
      exact hκ.mul (Λ.continuous.comp (hc.comp (Continuous.prodMk continuous_const continuous_id)))
    · exact Calculus.continuous_integrableOn_unitCell
        (hκ.mul (Λ.continuous.comp (hc.comp (Continuous.prodMk continuous_const continuous_id))))
    · exact hF'y.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (measurableSet_unitCell 2)] with a ha x hx
      exact hC (x, a) ⟨Metric.ball_subset_closedBall hx,
        Calculus.unitCell_subset_closedUnitCell 2 ha⟩
    · exact Calculus.continuous_integrableOn_unitCell continuous_const
    · refine Filter.Eventually.of_forall fun a x _ => ?_
      have h1 := Λ.hasFDerivAt.comp x (hdiff a x).hasFDerivAt
      exact h1.const_mul (torusCharacter n a)
  have hint : Integrable (fun a => F' X a) (volume.restrict (unitCell 2)) :=
    Calculus.continuous_integrableOn_unitCell hF'y
  have hdd' : HasFDerivAt (fun X => smoothFourierCoeff (fun y => Λ (h X y)) n)
      (∫ a in unitCell 2, F' X a) X := hdd
  rw [hdd'.fderiv, ContinuousLinearMap.integral_apply hint e]
  rfl
end

/-! The `L²` bound for a field whose cell Fourier coefficients are `2πi n_k p(n)`, with divergence
`g`: pointwise multiplier estimate and Parseval. -/

theorem sq_norm_le_of_multiplier (n : Fin 2 → ℤ) (p a₀ a₁ g : ℂ)
    (h₀ : a₀ = (2 * Real.pi * Complex.I * (n 0 : ℂ)) * p)
    (h₁ : a₁ = (2 * Real.pi * Complex.I * (n 1 : ℂ)) * p)
    (hg : g = (2 * Real.pi * Complex.I * (n 0 : ℂ)) * a₀ +
      (2 * Real.pi * Complex.I * (n 1 : ℂ)) * a₁) :
    ‖a₀‖ ^ 2 + ‖a₁‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ * ‖g‖ ^ 2 := by
  have hn0 : (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 = 0 → n = 0 := by
    intro h
    have e0 : (n 0 : ℝ) = 0 := by nlinarith [sq_nonneg (n 0 : ℝ), sq_nonneg (n 1 : ℝ)]
    have e1 : (n 1 : ℝ) = 0 := by nlinarith [sq_nonneg (n 0 : ℝ), sq_nonneg (n 1 : ℝ)]
    ext i; fin_cases i <;> simp_all
  by_cases hn : n = 0
  · subst hn
    simp [h₀, h₁, hg]
  · have hN : 1 ≤ (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 := by
      have := FourierCalculus.intFrequencySq_ge_one (n := 1) hn
      simpa [Fin.sum_univ_two] using this
    have hgp : g = (((-(4 * Real.pi ^ 2 * ((n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2)) : ℝ)) : ℂ) * p := by
      rw [hg, h₀, h₁]
      push_cast
      ring_nf
      simp [Complex.I_sq]
      ring
    have ha₀ := FourierCalculus.normSq_fourierMultiplier (n 0) p
    have ha₁ := FourierCalculus.normSq_fourierMultiplier (n 1) p
    have hgn : ‖g‖ ^ 2 = (4 * Real.pi ^ 2 * ((n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2)) ^ 2 * ‖p‖ ^ 2 := by
      rw [hgp, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_sq]
    rw [h₀, h₁, ha₀, ha₁, hgn]
    have hP : 0 < 4 * Real.pi ^ 2 := by positivity
    generalize 4 * Real.pi ^ 2 = P at hP ⊢
    generalize (n 0 : ℝ) ^ 2 = a at hN ⊢
    generalize (n 1 : ℝ) ^ 2 = b at hN ⊢
    have hq : 0 ≤ ‖p‖ ^ 2 := sq_nonneg _
    generalize ‖p‖ ^ 2 = q at hq ⊢
    have e : P⁻¹ * ((P * (a + b)) ^ 2 * q) = P * (a + b) ^ 2 * q := by
      field_simp
    rw [e]
    have := mul_nonneg (mul_nonneg hP.le hq)
      (mul_nonneg (by linarith : 0 ≤ a + b) (by linarith : 0 ≤ a + b - 1))
    nlinarith


theorem cell_sq_integral_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (W : Fin 2 → Vec 2 → E) (G : Vec 2 → E)
    (hW : ∀ k, Continuous (W k)) (hG : Continuous G)
    (hrel : ∀ (Λ : E →L[ℝ] ℂ) (n : Fin 2 → ℤ), ∃ p : ℂ,
      (∀ k, smoothFourierCoeff (fun y => Λ (W k y)) n =
        (2 * Real.pi * Complex.I * (n k : ℂ)) * p) ∧
      smoothFourierCoeff (fun y => Λ (G y)) n =
        (2 * Real.pi * Complex.I * (n 0 : ℂ)) * smoothFourierCoeff (fun y => Λ (W 0 y)) n +
        (2 * Real.pi * Complex.I * (n 1 : ℂ)) * smoothFourierCoeff (fun y => Λ (W 1 y)) n) :
    ∫ y in unitCell 2, ∑ k, ‖W k y‖ ^ 2 ≤
      (4 * Real.pi ^ 2)⁻¹ * ∫ y in unitCell 2, ‖G y‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ E
  let L : Fin (Module.finrank ℝ E) → E →L[ℝ] ℂ := fun i =>
    Complex.ofRealCLM.comp (innerSL ℝ (b i))
  have hLsum : ∀ w : E, ‖w‖ ^ 2 = ∑ i, ‖L i w‖ ^ 2 := by
    intro w
    rw [← b.sum_sq_norm_inner_right w]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [L]
  have hc : ∀ (u : Vec 2 → E) (i : Fin (Module.finrank ℝ E)), Continuous u →
      Continuous (fun y => L i (u y)) := fun u i hu => (L i).continuous.comp hu
  have hint : ∀ (u : Vec 2 → E) (i : Fin (Module.finrank ℝ E)), Continuous u →
      IntegrableOn (fun y => ‖L i (u y)‖ ^ 2) (unitCell 2) := fun u i hu =>
    Calculus.continuous_integrableOn_unitCell ((hc u i hu).norm.pow 2)
  have hS : HasSum (fun n : Fin 2 → ℤ => ∑ i, ∑ k : Fin 2,
      ‖smoothFourierCoeff (fun y => L i (W k y)) n‖ ^ 2)
      (∑ i, ∑ k : Fin 2, ∫ y in unitCell 2, ‖L i (W k y)‖ ^ 2) :=
    hasSum_sum fun i _ => hasSum_sum fun k _ =>
      hasSum_sq_smoothFourierCoeff (hc (W k) i (hW k))
  have hT : HasSum (fun n : Fin 2 → ℤ => (4 * Real.pi ^ 2)⁻¹ *
      ∑ i, ‖smoothFourierCoeff (fun y => L i (G y)) n‖ ^ 2)
      ((4 * Real.pi ^ 2)⁻¹ * ∑ i, ∫ y in unitCell 2, ‖L i (G y)‖ ^ 2) :=
    (hasSum_sum fun i _ => hasSum_sq_smoothFourierCoeff (hc G i hG)).mul_left _
  have hle : ∀ n : Fin 2 → ℤ, ∑ i, ∑ k : Fin 2,
      ‖smoothFourierCoeff (fun y => L i (W k y)) n‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ *
      ∑ i, ‖smoothFourierCoeff (fun y => L i (G y)) n‖ ^ 2 := by
    intro n
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨p, hp, hg⟩ := hrel (L i) n
    rw [Fin.sum_univ_two]
    exact sq_norm_le_of_multiplier n p _ _ _ (hp 0) (hp 1) (by rw [hg, hp 0, hp 1])
  have hmain := hasSum_le hle hS hT
  have hL : ∫ y in unitCell 2, ∑ k, ‖W k y‖ ^ 2 =
      ∑ i, ∑ k : Fin 2, ∫ y in unitCell 2, ‖L i (W k y)‖ ^ 2 := by
    simp_rw [hLsum (W _ _)]
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _
      (fun i _ => hint (W k) i (hW k))), Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ (fun i _ => hint (W k) i (hW k))]
  have hR : ∫ y in unitCell 2, ‖G y‖ ^ 2 = ∑ i, ∫ y in unitCell 2, ‖L i (G y)‖ ^ 2 := by
    simp_rw [hLsum (G _)]
    rw [integral_finsetSum _ (fun i _ => hint G i hG)]
  rw [hL, hR]
  exact hmain

end AVRegularity
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! Ordered derivative words and iterated Fréchet derivatives: `orderedDerivative β g` is the
iterated derivative evaluated on the reversed word, and it commutes with continuous linear maps,
sums and differences of `C^j` functions. -/

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedDerivative_zero (g : Vec 2 → F) (β : DerivativeWord2 0) :
    orderedDerivative β g = g := by
  simp [orderedDerivative]

theorem orderedDerivative_succ {j : ℕ} (β : DerivativeWord2 (j + 1)) (g : Vec 2 → F) :
    orderedDerivative β g = fun x =>
      fderiv ℝ (orderedDerivative (fun i : Fin j => β i.castSucc) g) x
        (basisVec (β (Fin.last j))) := by
  unfold orderedDerivative
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
  rfl

theorem orderedDerivative_const_zero {j : ℕ} (β : DerivativeWord2 j) :
    orderedDerivative β (fun _ : Vec 2 => (0 : F)) = fun _ => 0 := by
  induction j with
  | zero => exact orderedDerivative_zero _ β
  | succ j ih =>
    rw [orderedDerivative_succ, ih]
    funext x
    simp

/-- The ordered derivative is the iterated Fréchet derivative evaluated on the reversed word. -/
theorem orderedDerivative_eq_iteratedFDeriv {j : ℕ} (β : DerivativeWord2 j) {g : Vec 2 → F}
    (hg : ContDiff ℝ (j : ℕ∞) g) :
    orderedDerivative β g = fun x =>
      iteratedFDeriv ℝ j g x (fun i => basisVec (β (Fin.rev i))) := by
  induction j with
  | zero =>
    rw [orderedDerivative_zero]
    funext x
    simp [iteratedFDeriv_zero_apply]
  | succ j ih =>
    have hg' : ContDiff ℝ (j : ℕ∞) g := hg.of_le (by exact_mod_cast Nat.le_succ j)
    rw [orderedDerivative_succ, ih _ hg']
    funext x
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j g) x :=
      (hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)) x
    rw [iteratedFDeriv_succ_apply_left]
    have hH := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec 2) F
      (fun i => basisVec (β ((Fin.rev i).castSucc)))).hasFDerivAt.comp x hd.hasFDerivAt
    have e1 : fderiv ℝ (fun x => iteratedFDeriv ℝ j g x
        (fun i => basisVec (β ((Fin.rev i).castSucc)))) x =
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec 2) F
          (fun i => basisVec (β ((Fin.rev i).castSucc)))) ∘SL
          fderiv ℝ (iteratedFDeriv ℝ j g) x := hH.fderiv
    rw [e1]
    simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply]
    have hr : ∀ i : Fin j, (Fin.rev i).castSucc = Fin.rev i.succ := by
      intro i; ext; simp [Fin.val_rev]
    simp only [hr, Fin.rev_zero]
    rfl

theorem orderedDerivative_clm_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {j : ℕ} (β : DerivativeWord2 j) {g : Vec 2 → F}
    (hg : ContDiff ℝ (j : ℕ∞) g) :
    orderedDerivative β (fun x => L (g x)) = fun x => L (orderedDerivative β g x) := by
  have hLg : ContDiff ℝ (j : ℕ∞) (fun x => L (g x)) := L.contDiff.comp hg
  rw [orderedDerivative_eq_iteratedFDeriv β hLg, orderedDerivative_eq_iteratedFDeriv β hg]
  funext x
  have := L.iteratedFDeriv_comp_left (hg.contDiffAt (x := x)) (i := j) le_rfl
  have h2 := congrArg (fun T => T (fun i => basisVec (β (Fin.rev i)))) this
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h2
  exact h2

theorem orderedDerivative_add {j : ℕ} (β : DerivativeWord2 j) {g h : Vec 2 → F}
    (hg : ContDiff ℝ (j : ℕ∞) g) (hh : ContDiff ℝ (j : ℕ∞) h) :
    orderedDerivative β (fun x => g x + h x) =
      fun x => orderedDerivative β g x + orderedDerivative β h x := by
  rw [orderedDerivative_eq_iteratedFDeriv β (hg.add hh), orderedDerivative_eq_iteratedFDeriv β hg,
    orderedDerivative_eq_iteratedFDeriv β hh]
  funext x
  have := iteratedFDeriv_add_apply (hg.contDiffAt (x := x)) (hh.contDiffAt (x := x))
  have h2 := congrArg (fun T => T (fun i => basisVec (β (Fin.rev i)))) this
  simp only [add_apply] at h2
  exact h2

theorem orderedDerivative_sub {j : ℕ} (β : DerivativeWord2 j) {g h : Vec 2 → F}
    (hg : ContDiff ℝ (j : ℕ∞) g) (hh : ContDiff ℝ (j : ℕ∞) h) :
    orderedDerivative β (fun x => g x - h x) =
      fun x => orderedDerivative β g x - orderedDerivative β h x := by
  rw [orderedDerivative_eq_iteratedFDeriv β (hg.sub hh), orderedDerivative_eq_iteratedFDeriv β hg,
    orderedDerivative_eq_iteratedFDeriv β hh]
  funext x
  have := iteratedFDeriv_sub_apply (hg.contDiffAt (x := x)) (hh.contDiffAt (x := x))
  have h2 := congrArg (fun T => T (fun i => basisVec (β (Fin.rev i)))) this
  simp only [sub_apply] at h2
  exact h2
end

/-! Algebra of `IsSlowSmooth`: monotonicity, continuous linear images, sums, slow partial
derivatives, and the implication from `IsBoxSmooth`. -/

section
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem IsSlowSmooth.mono {m m' : ℕ} {f : Vec 2 → Vec 2 → F} (h : m' ≤ m)
    (hf : IsSlowSmooth m f) : IsSlowSmooth m' f :=
  ⟨fun y => (hf.1 y).of_le (by exact_mod_cast h), fun a ha => hf.2 a (ha.trans h)⟩

theorem IsSlowSmooth.contDiff {m : ℕ} {f : Vec 2 → Vec 2 → F} (hf : IsSlowSmooth m f)
    (y : Vec 2) : ContDiff ℝ (m : ℕ∞) (fun X => f X y) := hf.1 y

/-- Continuous linear images of slow smooth fields are slow smooth. -/
theorem IsSlowSmooth.clm_comp {m : ℕ} {f : Vec 2 → Vec 2 → F} (hf : IsSlowSmooth m f)
    (L : F →L[ℝ] G) : IsSlowSmooth m (fun X y => L (f X y)) := by
  refine ⟨fun y => L.contDiff.comp (hf.1 y), fun a ha => ?_⟩
  have h : (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ a (fun X => L (f X p.2)) p.1) =
      fun p => (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => Vec 2) F G L)
        (iteratedFDeriv ℝ a (fun X => f X p.2) p.1) := by
    funext p
    exact L.iteratedFDeriv_comp_left ((hf.1 p.2).contDiffAt (x := p.1))
      (i := a) (by exact_mod_cast ha)
  rw [h]
  exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => Vec 2) F G L).continuous.comp (hf.2 a ha)

theorem IsSlowSmooth.zero {m : ℕ} : IsSlowSmooth m (fun (_ _ : Vec 2) => (0 : F)) := by
  refine ⟨fun y => contDiff_const, fun a ha => ?_⟩
  have : (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ a (fun _ : Vec 2 => (0 : F)) p.1) =
      fun _ => 0 := by
    funext p
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · ext; simp
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      rfl
  simpa [this] using continuous_const

theorem IsSlowSmooth.add {m : ℕ} {f g : Vec 2 → Vec 2 → F} (hf : IsSlowSmooth m f)
    (hg : IsSlowSmooth m g) : IsSlowSmooth m (fun X y => f X y + g X y) := by
  refine ⟨fun y => (hf.1 y).add (hg.1 y), fun a ha => ?_⟩
  have h : (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ a (fun X => f X p.2 + g X p.2) p.1) =
      fun p => iteratedFDeriv ℝ a (fun X => f X p.2) p.1 +
        iteratedFDeriv ℝ a (fun X => g X p.2) p.1 := by
    funext p
    exact iteratedFDeriv_add_apply ((hf.1 p.2).contDiffAt (x := p.1) |>.of_le
      (by exact_mod_cast ha)) ((hg.1 p.2).contDiffAt (x := p.1) |>.of_le (by exact_mod_cast ha))
  rw [h]
  exact (hf.2 a ha).add (hg.2 a ha)

theorem IsSlowSmooth.const_smul {m : ℕ} {f : Vec 2 → Vec 2 → F} (hf : IsSlowSmooth m f)
    (c : ℝ) : IsSlowSmooth m (fun X y => c • f X y) :=
  hf.clm_comp (c • ContinuousLinearMap.id ℝ F)

theorem IsSlowSmooth.neg {m : ℕ} {f : Vec 2 → Vec 2 → F} (hf : IsSlowSmooth m f) :
    IsSlowSmooth m (fun X y => -f X y) :=
  hf.clm_comp (-ContinuousLinearMap.id ℝ F)

theorem IsSlowSmooth.sub {m : ℕ} {f g : Vec 2 → Vec 2 → F} (hf : IsSlowSmooth m f)
    (hg : IsSlowSmooth m g) : IsSlowSmooth m (fun X y => f X y - g X y) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem IsSlowSmooth.sum {ι : Type*} (s : Finset ι) {m : ℕ} {f : ι → Vec 2 → Vec 2 → F}
    (hf : ∀ i ∈ s, IsSlowSmooth m (f i)) : IsSlowSmooth m (fun X y => ∑ i ∈ s, f i X y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsSlowSmooth.zero (m := m) (F := F))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The component of a slow smooth vector field is slow smooth. -/
theorem IsSlowSmooth.component {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    {V : Vec 2 → Vec 2 → ι → F} (hV : IsSlowSmooth m V) (k : ι) :
    IsSlowSmooth m (fun X y => V X y k) :=
  hV.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) k)

theorem IsSlowSmooth.continuous_orderedDerivative {m j : ℕ} {g : Vec 2 → Vec 2 → F}
    (hg : IsSlowSmooth m g) (hj : j ≤ m) (β : DerivativeWord2 j) :
    Continuous (fun p : Vec 2 × Vec 2 => orderedDerivative β (fun X' => g X' p.2) p.1) := by
  have h : (fun p : Vec 2 × Vec 2 => orderedDerivative β (fun X' => g X' p.2) p.1) =
      fun p => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec 2) F
        (fun i => basisVec (β (Fin.rev i)))) (iteratedFDeriv ℝ j (fun X => g X p.2) p.1) := by
    funext p
    rw [orderedDerivative_eq_iteratedFDeriv β ((hg.1 p.2).of_le (by exact_mod_cast hj))]
    rfl
  rw [h]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec 2) F
    (fun i => basisVec (β (Fin.rev i)))).continuous.comp (hg.2 j hj)

theorem IsSlowSmooth.slowPartial {m : ℕ} {f : Vec 2 → Vec 2 → F} (hf : IsSlowSmooth (m + 1) f)
    (k : Fin 2) : IsSlowSmooth m (AVRegularity.slowPartial k f) := by
  have hd : ∀ y, ContDiff ℝ (m : ℕ∞) (fun X => fderiv ℝ (fun X' => f X' y) X) :=
    fun y => (hf.1 y).fderiv_right (by exact_mod_cast le_rfl)
  refine ⟨fun y => (hd y).clm_apply contDiff_const, fun a ha => ?_⟩
  have h : (fun p : Vec 2 × Vec 2 =>
      iteratedFDeriv ℝ a (fun X => AVRegularity.slowPartial k f X p.2) p.1) =
      fun p => (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => Vec 2) (Vec 2 →L[ℝ] F) F
          (ContinuousLinearMap.apply ℝ F (basisVec k)))
        ((continuousMultilinearCurryRightEquiv' ℝ a (Vec 2) F)
          (iteratedFDeriv ℝ (a + 1) (fun X => f X p.2) p.1)) := by
    funext p
    have e1 := (ContinuousLinearMap.apply ℝ F (basisVec k)).iteratedFDeriv_comp_left
      ((hd p.2).contDiffAt (x := p.1)) (i := a) (by exact_mod_cast ha)
    have e2 : iteratedFDeriv ℝ (a + 1) (fun X => f X p.2) p.1 =
        (continuousMultilinearCurryRightEquiv' ℝ a (Vec 2) F).symm
          (iteratedFDeriv ℝ a (fun y => fderiv ℝ (fun X => f X p.2) y) p.1) :=
      iteratedFDeriv_succ_eq_comp_right
    rw [e2, LinearIsometryEquiv.apply_symm_apply]
    exact e1
  rw [h]
  exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => Vec 2) (Vec 2 →L[ℝ] F) F
      (ContinuousLinearMap.apply ℝ F (basisVec k))).continuous.comp
    ((continuousMultilinearCurryRightEquiv' ℝ a (Vec 2) F).continuous.comp
      (hf.2 (a + 1) (by omega)))

theorem IsBoxSmooth.isSlowSmooth {sX sZ : ℕ} {f : Vec 2 → Vec 2 → F}
    (hf : IsBoxSmooth sX sZ f) : IsSlowSmooth sX f := by
  let e0 := (continuousMultilinearCurryFin0 ℝ (Vec 2) F).toContinuousLinearEquiv
  have hfun : ∀ y, (fun X => f X y) =
      fun X => e0 (iteratedFDeriv ℝ 0 (f X) y) := by
    intro y; funext X
    simp [e0, iteratedFDeriv_zero_eq_comp]
  refine ⟨fun y => ?_, fun a ha => ?_⟩
  · rw [hfun y]
    exact e0.contDiff.comp (hf.2.1 0 (Nat.zero_le _) y)
  · have h : (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ a (fun X => f X p.2) p.1) =
        fun p => (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => Vec 2) (Vec 2 [×0]→L[ℝ] F) F (e0 : (Vec 2 [×0]→L[ℝ] F) →L[ℝ] F))
          (iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ 0 (f X') p.2) p.1) := by
      funext p
      have e1 := (e0 : _ →L[ℝ] F).iteratedFDeriv_comp_left
        ((hf.2.1 0 (Nat.zero_le _) p.2).contDiffAt (x := p.1)) (i := a) (by exact_mod_cast ha)
      rw [hfun p.2]
      exact e1
    rw [h]
    exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin a => Vec 2) (Vec 2 [×0]→L[ℝ] F) F (e0 : (Vec 2 [×0]→L[ℝ] F) →L[ℝ] F)).continuous.comp
      (hf.2.2 a 0 ha (Nat.zero_le _))
end

end AVRegularity
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Torus
namespace AVRegularity

/-! Slow ordered derivatives commute with the cell Fourier coefficient. -/

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedDerivative_smoothFourierCoeff {m : ℕ} {u : Vec 2 → Vec 2 → F}
    (hu : IsSlowSmooth m u) (Λ : F →L[ℝ] ℂ) (n : Fin 2 → ℤ) :
    ∀ (j : ℕ), j ≤ m → ∀ β : DerivativeWord2 j,
      orderedDerivative β (fun X => smoothFourierCoeff (fun y => Λ (u X y)) n) =
        fun X => smoothFourierCoeff
          (fun y => Λ (orderedDerivative β (fun X' => u X' y) X)) n := by
  intro j
  induction j with
  | zero =>
    intro _ β
    simp only [orderedDerivative_zero]
  | succ j ih =>
    intro hj β
    have hj' : j ≤ m := Nat.le_of_succ_le hj
    set β0 : DerivativeWord2 j := fun i => β i.castSucc with hβ0
    rw [orderedDerivative_succ, ih hj' β0]
    funext X
    simp only [orderedDerivative_succ]
    refine fderiv_smoothFourierCoeff_apply Λ n
      (fun X y => orderedDerivative β0 (fun X' => u X' y) X) ?_ ?_ ?_ X _
    · intro y
      rw [orderedDerivative_eq_iteratedFDeriv β0 ((hu.1 y).of_le (by exact_mod_cast hj'))]
      have hd := ((hu.1 y).differentiable_iteratedFDeriv
        (m := j) (by exact_mod_cast Nat.lt_of_succ_le hj))
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec 2) F
        (fun i => basisVec (β0 (Fin.rev i)))).differentiable.comp hd
    · exact hu.continuous_orderedDerivative hj' β0
    · intro i
      have := hu.continuous_orderedDerivative hj (Fin.snoc (α := fun _ => Fin 2) β0 i)
      refine this.congr fun p => ?_
      rw [orderedDerivative_succ]
      simp [hβ0]

theorem smoothFourierCoeff_orderedDerivative_eq_zero {m : ℕ} {u : Vec 2 → Vec 2 → F}
    (hu : IsSlowSmooth m u) (Λ : F →L[ℝ] ℂ) (n : Fin 2 → ℤ)
    (h0 : ∀ X, smoothFourierCoeff (fun y => Λ (u X y)) n = 0)
    (β : DerivativeWord2 m) (X : Vec 2) :
    smoothFourierCoeff (fun y => Λ (orderedDerivative β (fun X' => u X' y) X)) n = 0 := by
  have h := congrFun (orderedDerivative_smoothFourierCoeff hu Λ n m le_rfl β) X
  have h0' : (fun X => smoothFourierCoeff (fun y => Λ (u X y)) n) = fun _ => 0 :=
    funext h0
  rw [h0', orderedDerivative_const_zero] at h
  exact h.symm
end

/-! Linear relations between cell Fourier coefficients persist under slow ordered derivatives. -/

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsSlowSmooth.continuous_uncurry {m : ℕ} {f : Vec 2 → Vec 2 → F} (hf : IsSlowSmooth m f) :
    Continuous (fun p : Vec 2 × Vec 2 => f p.1 p.2) := by
  have := hf.continuous_orderedDerivative (Nat.zero_le m) (Fin.elim0 : DerivativeWord2 0)
  simpa [orderedDerivative_zero] using this

theorem IsSlowSmooth.continuous_fast {m : ℕ} {f : Vec 2 → Vec 2 → F} (hf : IsSlowSmooth m f)
    (X : Vec 2) : Continuous (f X) :=
  hf.continuous_uncurry.comp (Continuous.prodMk continuous_const continuous_id)

theorem smoothFourierCoeff_sub {a b : Vec 2 → ℂ} (ha : Continuous a) (hb : Continuous b)
    (n : Fin 2 → ℤ) :
    smoothFourierCoeff (fun y => a y - b y) n = smoothFourierCoeff a n - smoothFourierCoeff b n := by
  have hκ : Continuous (torusCharacter n) := (torusCharacter_contDiff n).continuous
  simp only [smoothFourierCoeff, mul_sub]
  exact integral_sub (Calculus.continuous_integrableOn_unitCell (hκ.mul ha))
    (Calculus.continuous_integrableOn_unitCell (hκ.mul hb))

theorem smoothFourierCoeff_add {a b : Vec 2 → ℂ} (ha : Continuous a) (hb : Continuous b)
    (n : Fin 2 → ℤ) :
    smoothFourierCoeff (fun y => a y + b y) n = smoothFourierCoeff a n + smoothFourierCoeff b n := by
  have hκ : Continuous (torusCharacter n) := (torusCharacter_contDiff n).continuous
  simp only [smoothFourierCoeff, mul_add]
  exact integral_add (Calculus.continuous_integrableOn_unitCell (hκ.mul ha))
    (Calculus.continuous_integrableOn_unitCell (hκ.mul hb))

theorem smoothFourierCoeff_const_mul (c : ℂ) (a : Vec 2 → ℂ) (n : Fin 2 → ℤ) :
    smoothFourierCoeff (fun y => c * a y) n = c * smoothFourierCoeff a n := by
  simp only [smoothFourierCoeff]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-- If `a = c₁ b + c₂ d` coefficientwise at every slow point, then the same holds for the
ordered slow derivatives of order `m`. -/
theorem smoothFourierCoeff_orderedDerivative_lincomb {m : ℕ} {a b d : Vec 2 → Vec 2 → F}
    (ha : IsSlowSmooth m a) (hb : IsSlowSmooth m b) (hd : IsSlowSmooth m d)
    (Λ : F →L[ℝ] ℂ) (n : Fin 2 → ℤ) (c₁ c₂ : ℂ)
    (h0 : ∀ X, smoothFourierCoeff (fun y => Λ (a X y)) n =
      c₁ * smoothFourierCoeff (fun y => Λ (b X y)) n +
        c₂ * smoothFourierCoeff (fun y => Λ (d X y)) n)
    (β : DerivativeWord2 m) (X : Vec 2) :
    smoothFourierCoeff (fun y => Λ (orderedDerivative β (fun X' => a X' y) X)) n =
      c₁ * smoothFourierCoeff (fun y => Λ (orderedDerivative β (fun X' => b X' y) X)) n +
        c₂ * smoothFourierCoeff (fun y => Λ (orderedDerivative β (fun X' => d X' y) X)) n := by
  let Λ₁ : F →L[ℝ] ℂ := c₁ • Λ
  let Λ₂ : F →L[ℝ] ℂ := c₂ • Λ
  let u : Vec 2 → Vec 2 → ℂ := fun X y => Λ (a X y) - Λ₁ (b X y) - Λ₂ (d X y)
  have hu : IsSlowSmooth m u :=
    ((ha.clm_comp Λ).sub (hb.clm_comp Λ₁)).sub (hd.clm_comp Λ₂)
  have hcont : ∀ X, Continuous (fun y => Λ (a X y)) ∧ Continuous (fun y => Λ₁ (b X y)) ∧
      Continuous (fun y => Λ₂ (d X y)) := fun X =>
    ⟨Λ.continuous.comp (ha.continuous_fast X), Λ₁.continuous.comp (hb.continuous_fast X),
      Λ₂.continuous.comp (hd.continuous_fast X)⟩
  have hzero : ∀ X, smoothFourierCoeff
      (fun y => (ContinuousLinearMap.id ℝ ℂ) (u X y)) n = 0 := by
    intro X
    obtain ⟨h1, h2, h3⟩ := hcont X
    simp only [u, ContinuousLinearMap.id_apply]
    rw [smoothFourierCoeff_sub (a := fun y => Λ (a X y) - Λ₁ (b X y))
      (b := fun y => Λ₂ (d X y)) (h1.sub h2) h3 n,
      smoothFourierCoeff_sub (a := fun y => Λ (a X y)) (b := fun y => Λ₁ (b X y)) h1 h2 n]
    simp only [Λ₁, Λ₂, smul_apply, smul_eq_mul]
    rw [smoothFourierCoeff_const_mul c₁ (fun y => Λ (b X y)) n,
      smoothFourierCoeff_const_mul c₂ (fun y => Λ (d X y)) n, h0 X]
    ring
  have key := smoothFourierCoeff_orderedDerivative_eq_zero hu (ContinuousLinearMap.id ℝ ℂ) n
    hzero β X
  have hy : ∀ y, orderedDerivative β (fun X' => u X' y) X =
      Λ (orderedDerivative β (fun X' => a X' y) X) -
        Λ₁ (orderedDerivative β (fun X' => b X' y) X) -
        Λ₂ (orderedDerivative β (fun X' => d X' y) X) := by
    intro y
    have cm : ∀ {G : Vec 2 → Vec 2 → F} (hG : IsSlowSmooth m G) (L : F →L[ℝ] ℂ),
        ContDiff ℝ (m : ℕ∞) (fun X' => L (G X' y)) := fun hG L => L.contDiff.comp (hG.1 y)
    have e1 := orderedDerivative_sub β ((cm ha Λ).sub (cm hb Λ₁)) (cm hd Λ₂)
    have e2 := orderedDerivative_sub β (cm ha Λ) (cm hb Λ₁)
    have e3 := orderedDerivative_clm_comp Λ β (ha.1 y)
    have e4 := orderedDerivative_clm_comp Λ₁ β (hb.1 y)
    have e5 := orderedDerivative_clm_comp Λ₂ β (hd.1 y)
    have := congrFun e1 X
    simp only [u]
    rw [this]
    rw [congrFun e2 X, congrFun e3 X, congrFun e4 X, congrFun e5 X]
  simp only [ContinuousLinearMap.id_apply, hy] at key
  have c1' : Continuous (fun y => Λ (orderedDerivative β (fun X' => a X' y) X)) :=
    Λ.continuous.comp ((ha.continuous_orderedDerivative le_rfl β).comp
      (Continuous.prodMk continuous_const continuous_id))
  have c2 : Continuous (fun y => Λ₁ (orderedDerivative β (fun X' => b X' y) X)) :=
    Λ₁.continuous.comp ((hb.continuous_orderedDerivative le_rfl β).comp
      (Continuous.prodMk continuous_const continuous_id))
  have c3 : Continuous (fun y => Λ₂ (orderedDerivative β (fun X' => d X' y) X)) :=
    Λ₂.continuous.comp ((hd.continuous_orderedDerivative le_rfl β).comp
      (Continuous.prodMk continuous_const continuous_id))
  rw [smoothFourierCoeff_sub (a := fun y => Λ (orderedDerivative β (fun X' => a X' y) X) -
      Λ₁ (orderedDerivative β (fun X' => b X' y) X))
    (b := fun y => Λ₂ (orderedDerivative β (fun X' => d X' y) X)) (c1'.sub c2) c3 n,
    smoothFourierCoeff_sub c1' c2 n] at key
  simp only [Λ₁, Λ₂, smul_apply, smul_eq_mul] at key
  rw [smoothFourierCoeff_const_mul c₁ (fun y => Λ (orderedDerivative β (fun X' => b X' y) X)) n,
    smoothFourierCoeff_const_mul c₂ (fun y => Λ (orderedDerivative β (fun X' => d X' y) X)) n]
    at key
  linear_combination key
end

/-! Fast (fibrewise) Fourier identities for the cell antidivergence at a fixed slow point. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Fourier coefficient of a coordinate derivative of a smooth periodic `E`-valued function. -/
theorem smoothFourierCoeff_fderiv_apply (Λ : E →L[ℝ] ℂ) {g : Vec 2 → E}
    (hg : ContDiff ℝ 1 g) (hper : AVenhance.IsZ2Periodic g) (k : Fin 2) (n : Fin 2 → ℤ) :
    smoothFourierCoeff (fun y => Λ (fderiv ℝ g y (basisVec k))) n =
      (2 * Real.pi * Complex.I * (n k : ℂ)) * smoothFourierCoeff (fun y => Λ (g y)) n := by
  have hq : ContDiff ℝ 1 (fun y => Λ (g y)) := Λ.contDiff.comp hg
  have hqper : IsZdPeriodic (fun y => Λ (g y)) := by
    apply (isZdPeriodic_iff_frozen _).2
    intro n' z
    simp [hper n' z]
  have hder : coordDeriv k (fun y => Λ (g y)) = fun y => Λ (fderiv ℝ g y (basisVec k)) := by
    funext y
    simp only [coordDeriv]
    have := (Λ.hasFDerivAt.comp y (hg.differentiable (by norm_num) y).hasFDerivAt).fderiv
    rw [show (fun y => Λ (g y)) = Λ ∘ g from rfl, this]
    simp
  rw [← hder]
  exact smoothFourierCoeff_coordDeriv k hq hqper n

/-- Divergence identity on coefficients. -/
theorem smoothFourierCoeff_div (Λ : E →L[ℝ] ℂ) {V : Vec 2 → Fin 2 → E} {f : Vec 2 → E}
    (hV : ∀ k, ContDiff ℝ 1 (fun y => V y k)) (hper : ∀ k, AVenhance.IsZ2Periodic (fun y => V y k))
    (hdiv : ∀ y, ∑ k : Fin 2, fderiv ℝ (fun z => V z k) y (basisVec k) = f y) (n : Fin 2 → ℤ) :
    smoothFourierCoeff (fun y => Λ (f y)) n =
      (2 * Real.pi * Complex.I * (n 0 : ℂ)) * smoothFourierCoeff (fun y => Λ (V y 0)) n +
      (2 * Real.pi * Complex.I * (n 1 : ℂ)) * smoothFourierCoeff (fun y => Λ (V y 1)) n := by
  have hcont : ∀ k, Continuous (fun y => Λ (fderiv ℝ (fun z => V z k) y (basisVec k))) :=
    fun k => Λ.continuous.comp (((hV k).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hf : (fun y => Λ (f y)) = fun y =>
      Λ (fderiv ℝ (fun z => V z 0) y (basisVec 0)) + Λ (fderiv ℝ (fun z => V z 1) y (basisVec 1)) := by
    funext y
    rw [← hdiv y]
    simp [Fin.sum_univ_two]
  rw [hf, smoothFourierCoeff_add (hcont 0) (hcont 1) n,
    smoothFourierCoeff_fderiv_apply Λ (hV 0) (hper 0) 0 n,
    smoothFourierCoeff_fderiv_apply Λ (hV 1) (hper 1) 1 n]
end

/-! The fibrewise `L²` bound for the cell antidivergence together with slow derivatives. -/

section
/-- Lebesgue integral over the open unit square of a continuous nonnegative function. -/
theorem lintegral_unitCube_ofReal {u : Vec 2 → ℝ} (hu : Continuous u) (h0 : ∀ y, 0 ≤ u y) :
    ∫⁻ y in AVenhance.unitCube, ENNReal.ofReal (u y) =
      ENNReal.ofReal (∫ y in unitCell 2, u y) := by
  rw [← setLIntegral_congr unitCell_ae_eq_unitCube]
  exact (ofReal_integral_eq_lintegral_ofReal
    (Calculus.continuous_integrableOn_unitCell hu) (Filter.Eventually.of_forall h0)).symm

theorem enorm_sq_eq_ofReal {E : Type*} [NormedAddCommGroup E] (w : E) :
    ‖w‖ₑ ^ 2 = ENNReal.ofReal (‖w‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellAntidivergence_orderedDerivative_sq_le {sX sZ : ℕ} (hZ : 1 ≤ sZ)
    {f : Vec 2 → Vec 2 → E} {V : Vec 2 → Vec 2 → Fin 2 → E}
    (hV : IsCellAntidivergence sX sZ f V) {m : ℕ} (hm : m ≤ sX) (hf : IsSlowSmooth m f)
    (β : DerivativeWord2 m) (X : Vec 2) :
    ∫⁻ y in AVenhance.unitCube, ∑ k : Fin 2,
        ‖orderedDerivative β (fun X' => V X' y k) X‖ₑ ^ 2
      ≤ ENNReal.ofReal ((4 * Real.pi ^ 2)⁻¹) *
        ∫⁻ y in AVenhance.unitCube, ‖orderedDerivative β (fun X' => f X' y) X‖ₑ ^ 2 := by
  obtain ⟨hVbox, hVper, φ, hφbox, hφper, -, hVφ, hdiv⟩ := hV
  have hVs : IsSlowSmooth m V := (hVbox.isSlowSmooth).mono hm
  have hφs : IsSlowSmooth m φ := (hφbox.isSlowSmooth).mono hm
  have hVk : ∀ k, IsSlowSmooth m (fun X y => V X y k) := fun k => hVs.component k
  have hφC1 : ∀ X, ContDiff ℝ 1 (φ X) := fun X =>
    (hφbox.1 X).of_le (by exact_mod_cast Nat.le_add_left 1 sZ)
  have hVkC1 : ∀ X k, ContDiff ℝ 1 (fun y => V X y k) := fun X k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k).contDiff.comp
      ((hVbox.1 X).of_le (by exact_mod_cast hZ))
  have hVkper : ∀ X k, AVenhance.IsZ2Periodic (fun y => V X y k) := fun X k n z =>
    congrFun (hVper X n z) k
  have hrel : ∀ (Λ : E →L[ℝ] ℂ) (n : Fin 2 → ℤ), ∃ p : ℂ,
      (∀ k, smoothFourierCoeff
        (fun y => Λ (orderedDerivative β (fun X' => V X' y k) X)) n =
        (2 * Real.pi * Complex.I * (n k : ℂ)) * p) ∧
      smoothFourierCoeff (fun y => Λ (orderedDerivative β (fun X' => f X' y) X)) n =
        (2 * Real.pi * Complex.I * (n 0 : ℂ)) * smoothFourierCoeff
          (fun y => Λ (orderedDerivative β (fun X' => V X' y 0) X)) n +
        (2 * Real.pi * Complex.I * (n 1 : ℂ)) * smoothFourierCoeff
          (fun y => Λ (orderedDerivative β (fun X' => V X' y 1) X)) n := by
    intro Λ n
    refine ⟨smoothFourierCoeff (fun y => Λ (orderedDerivative β (fun X' => φ X' y) X)) n,
      fun k => ?_, ?_⟩
    · have := smoothFourierCoeff_orderedDerivative_lincomb (hVk k) hφs hφs Λ n
        (2 * Real.pi * Complex.I * (n k : ℂ)) 0 (fun X' => by
          have e : (fun y => Λ (V X' y k)) = fun y => Λ (fderiv ℝ (φ X') y (basisVec k)) := by
            funext y; rw [hVφ X' y k]
          rw [e, smoothFourierCoeff_fderiv_apply Λ (hφC1 X') (hφper X') k n]
          ring) β X
      simpa using this
    · exact smoothFourierCoeff_orderedDerivative_lincomb hf (hVk 0) (hVk 1) Λ n
        (2 * Real.pi * Complex.I * (n 0 : ℂ)) (2 * Real.pi * Complex.I * (n 1 : ℂ))
        (fun X' => smoothFourierCoeff_div Λ (hVkC1 X') (hVkper X') (hdiv X') n) β X
  have hcont : ∀ (g : Vec 2 → Vec 2 → E), IsSlowSmooth m g →
      Continuous (fun y => orderedDerivative β (fun X' => g X' y) X) := fun g hg =>
    (hg.continuous_orderedDerivative le_rfl β).comp
      (Continuous.prodMk continuous_const continuous_id)
  have key := cell_sq_integral_le
    (fun k y => orderedDerivative β (fun X' => V X' y k) X)
    (fun y => orderedDerivative β (fun X' => f X' y) X)
    (fun k => hcont _ (hVk k)) (hcont _ hf) hrel
  have hLc : Continuous (fun y => ∑ k : Fin 2,
      ‖orderedDerivative β (fun X' => V X' y k) X‖ ^ 2) :=
    continuous_finsetSum _ fun k _ => (hcont _ (hVk k)).norm.pow 2
  have hRc : Continuous (fun y => ‖orderedDerivative β (fun X' => f X' y) X‖ ^ 2) :=
    (hcont _ hf).norm.pow 2
  have eL : ∀ y, ∑ k : Fin 2, ‖orderedDerivative β (fun X' => V X' y k) X‖ₑ ^ 2 =
      ENNReal.ofReal (∑ k : Fin 2, ‖orderedDerivative β (fun X' => V X' y k) X‖ ^ 2) := by
    intro y
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
    exact Finset.sum_congr rfl fun k _ => enorm_sq_eq_ofReal _
  simp_rw [eL, enorm_sq_eq_ofReal]
  rw [lintegral_unitCube_ofReal hLc (fun y => Finset.sum_nonneg fun k _ => sq_nonneg _),
    lintegral_unitCube_ofReal hRc (fun y => sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal key
end

end AVRegularity
end
