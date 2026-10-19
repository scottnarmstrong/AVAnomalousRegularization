-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.StrongUniqueness
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Average-time energy control for the Fourier proof of continuous Hilbert traces. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- An absolutely continuous Hilbert curve is controlled uniformly by its average energy
and the absolute integral of its energy derivative. -/
theorem StrongTimeRegularity.norm_sq_le_average {a b : ℝ} (hab : a ≤ b)
    {u du : ℝ → H} (h : StrongTimeRegularity a b u du) :
    ∀ t ∈ Icc a b,
      (b - a) * ‖u t‖ ^ 2 ≤ (∫ s in a..b, ‖u s‖ ^ 2) +
        (b - a) * ∫ s in a..b, ‖2 * inner ℝ (u s) (du s)‖ := by
  let p := fun s => 2 * inner ℝ (u s) (du s)
  let K := ∫ s in a..b, ‖p s‖
  have hp : IntervalIntegrable p volume a b := h.energy_integrable
  have hn := hp.norm
  have hcont : ContinuousOn (fun s => ‖u s‖ ^ 2) (Icc a b) := by
    simpa only [uIcc_of_le hab] using h.norm_sq_ac.continuousOn
  intro t ht
  have hbnd : ∀ s ∈ Icc a b, ‖u t‖ ^ 2 ≤ ‖u s‖ ^ 2 + K := by
    intro s hs
    have hsub : uIcc s t ⊆ uIcc a b := by
      rw [uIcc_of_le hab]
      exact uIcc_subset_Icc hs ht
    have he := (h.mono hsub).energy_increment
    have habs : |‖u t‖ ^ 2 - ‖u s‖ ^ 2| ≤ K := by
      rw [he, ← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      have hi := uIoc_subset_uIoc_of_uIcc_subset_uIcc hsub
      have hmono := setIntegral_mono_set hn.def'
        (Filter.Eventually.of_forall (fun r => norm_nonneg (p r))) hi.eventuallySubset
      simpa only [K, p, intervalIntegral.integral_of_le hab, uIoc_of_le hab] using hmono
    exact (sub_le_iff_le_add.mp ((le_abs_self _).trans habs)).trans_eq (add_comm K _)
  have hint : IntervalIntegrable (fun s => ‖u s‖ ^ 2) volume a b := hcont.intervalIntegrable_of_Icc hab
  have hm := intervalIntegral.integral_mono_on hab (continuous_const.intervalIntegrable a b)
    (hint.add (continuous_const.intervalIntegrable a b)) (fun s hs => hbnd s ⟨hs.1, hs.2⟩)
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hint
    (continuous_const.intervalIntegrable a b), intervalIntegral.integral_const] at hm
  simpa only [smul_eq_mul, mul_comm, K, p] using hm
end

/-! Strong-time variational energy and uniqueness on a Hilbert pair V → H.
The V-valued slice represents the H-trace almost everywhere, with no condition at an
endpoint. These are conditional results: they prove neither existence nor the Lions–Magenes
lemma. -/

section
variable {V H : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Strong-time weak equation. Spatial regularity resides in `slice` and is tied to
the continuous trace only almost everywhere. `B` is the generator form, with its sign. -/
structure StrongVariationalSolution (a b : ℝ) (J : V →ₗ[ℝ] H)
    (B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (q : ℝ → V →ₗ[ℝ] ℝ)
    (u du : ℝ → H) (slice : ℝ → V) : Prop where
  time : StrongTimeRegularity a b u du
  agrees : ∀ᵐ t ∂volume.restrict (uIcc a b), u t = J (slice t)
  equation : ∀ᵐ t ∂volume.restrict (uIcc a b), ∀ z : V,
    inner ℝ (du t) (J z) = B t (slice t) z + q t z

/-- Test the weak equation with the almost-everywhere spatial slice and derive energy. -/
theorem StrongVariationalSolution.energy_increment {a b : ℝ} {J : V →ₗ[ℝ] H}
    {B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {q : ℝ → V →ₗ[ℝ] ℝ}
    {u du : ℝ → H} {slice : ℝ → V}
    (h : StrongVariationalSolution a b J B q u du slice) :
    ‖u b‖ ^ 2 - ‖u a‖ ^ 2 =
      ∫ t in a..b, 2 * (B t (slice t) (slice t) + q t (slice t)) := by
  rw [h.time.energy_increment]
  apply intervalIntegral.integral_congr_ae_restrict
  have ha := h.agrees.filter_mono
    (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  have he := h.equation.filter_mono
    (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  filter_upwards [ha, he] with t hat het
  rw [real_inner_comm, hat, het]

/-- The variational differential equation implies its integrated fixed-test identity. -/
theorem StrongVariationalSolution.test_increment {a b : ℝ} {J : V →ₗ[ℝ] H}
    {B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {q : ℝ → V →ₗ[ℝ] ℝ}
    {u du : ℝ → H} {slice : ℝ → V}
    (h : StrongVariationalSolution a b J B q u du slice) (z : V) :
    inner ℝ (u b) (J z) - inner ℝ (u a) (J z) =
      ∫ t in a..b, B t (slice t) z + q t z := by
  rw [h.time.pairing_increment (J z)]
  apply intervalIntegral.integral_congr_ae_restrict
  have he := h.equation.filter_mono
    (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  filter_upwards [he] with t het
  exact het z

/-- Common forcing cancels in the difference equation. -/
theorem StrongVariationalSolution.sub {a b : ℝ} {J : V →ₗ[ℝ] H}
    {B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {q : ℝ → V →ₗ[ℝ] ℝ}
    {u du v dv : ℝ → H} {slice other : ℝ → V}
    (hu : StrongVariationalSolution a b J B q u du slice)
    (hv : StrongVariationalSolution a b J B q v dv other) :
    StrongVariationalSolution a b J B (fun _ => 0)
      (fun t => u t - v t) (fun t => du t - dv t)
      (fun t => slice t - other t) := by
  refine ⟨hu.time.sub hv.time, ?_, ?_⟩
  · filter_upwards [hu.agrees, hv.agrees] with t hut hvt
    rw [hut, hvt, map_sub]
  · filter_upwards [hu.equation, hv.equation] with t hut hvt
    intro z
    simp only [inner_sub_left, hut z, hvt z, map_sub, LinearMap.sub_apply,
      LinearMap.zero_apply]
    ring
end

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Abstract-real polynomial bounds for the forced word operator. -/

theorem word_forced_cov_budget_le (R f C q S δ : ℝ)
    (hR : 0 < R) (hf : 0 ≤ f) (hC : 0 ≤ C) (hq : 0 ≤ q) (hS : 1 ≤ S) (hδ : δ ≤ S)
    (hfbound : f ≤ C * (1 + Real.sqrt S * q)) :
    224 + 16 * (δ + 1) * (q / R) ^ 2 * f ^ 2 + 4 * q ^ 2 * δ * f ^ 2 ≤
      (15 + C * Real.sqrt (32 / R ^ 2 + 4) * (Real.sqrt S * q) * (1 + Real.sqrt S * q)) ^ 2 := by
  have h := word_homogeneous_cov_budget_le R f q S δ hR hf hq hS hδ
  have hx : 0 ≤ Real.sqrt S * q := mul_nonneg (Real.sqrt_nonneg _) hq
  have hy : 0 ≤ f * Real.sqrt (32 / R ^ 2 + 4) * (Real.sqrt S * q) := by positivity
  have hfirst : 224 + 16 * (δ + 1) * (q / R) ^ 2 * f ^ 2 + 4 * q ^ 2 * δ * f ^ 2 ≤
      (15 + f * Real.sqrt (32 / R ^ 2 + 4) * (Real.sqrt S * q)) ^ 2 := by nlinarith
  apply hfirst.trans
  apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
  have hf' := mul_le_mul_of_nonneg_right hfbound
    (mul_nonneg (Real.sqrt_nonneg (32 / R ^ 2 + 4)) hx)
  nlinarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Metric
namespace AVRegularity.CycleEvolution

/-! Uniform Banach-domain bounds for every iterated complex Fréchet derivative. -/

def analyticBallDerivativeConstant : ℕ → ℝ
  | 0 => 1
  | n + 1 => 4 * (2 : ℝ) ^ n * analyticBallDerivativeConstant n

theorem analyticBallDerivativeConstant_pos (n : ℕ) :
    0 < analyticBallDerivativeConstant n := by
  induction n with
  | zero => norm_num [analyticBallDerivativeConstant]
  | succ n ih => exact mul_pos (mul_pos (by norm_num) (by positivity)) ih

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem analytic_ball_iterated_derivative_le {f : V → E} (n : ℕ) {x : V} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (ball x R))
    (hb : ∀ y ∈ ball x R, ‖f y‖ ≤ M) :
    ‖iteratedFDeriv ℂ n f x‖ ≤ analyticBallDerivativeConstant n * M / R ^ n := by
  induction n generalizing x R M with
  | zero => simpa only [norm_iteratedFDeriv_zero, analyticBallDerivativeConstant,
      pow_zero, div_one, one_mul] using hb x (mem_ball_self hR)
  | succ n ih =>
    have hhalf : 0 < R / 2 := half_pos hR
    have hinner y (hy : y ∈ ball x (R / 2)) : ball y (R / 2) ⊆ ball x R := by
      intro z hz
      rw [mem_ball] at hy hz ⊢
      have ht := dist_triangle z y x
      linarith
    have hn y (hy : y ∈ ball x (R / 2)) :
        ‖iteratedFDeriv ℂ n f y‖ ≤ (2 : ℝ) ^ n * analyticBallDerivativeConstant n * M / R ^ n := by
      have hi := ih hhalf (hf.mono (hinner y hy)) (fun z hz => hb z (hinner y hy hz))
      apply hi.trans_eq
      rw [div_pow]
      field_simp
    have hs := analytic_ball_iterated_derivative_step hhalf
      (hf.mono (by intro y hy; exact ball_subset_ball (by linarith) hy)) n hn
    apply hs.trans_eq
    simp only [analyticBallDerivativeConstant, pow_succ]
    field_simp
    ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Pair-indexed versions of the finite Pascal identities. -/

/-- A pair-indexed convolution is the corresponding rectangular iterated sum. -/
theorem binomialConvolution_pair_rectangle {M : Type*} [AddCommMonoid M]
    (u : ℕ × ℕ → ℕ × ℕ → M) (n m : ℕ) :
    (∑ β ∈ Finset.Iic (n, m), (n.choose β.1 * m.choose β.2) •
      u β (n - β.1, m - β.2)) =
    ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (n + 1),
      (n.choose i * m.choose j) • u (i, j) (n - i, m - j) := by
  have hn : Finset.Iic n = Finset.range (n + 1) := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  have hm : Finset.Iic m = Finset.range (m + 1) := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  rw [← Finset.Iic_product_Iic, hn, hm, Finset.sum_product, Finset.sum_comm]

/-- Pair-indexed Pascal identity in the first coordinate. -/
theorem binomialConvolution_pair_first {M : Type*} [AddCommMonoid M]
    (u : ℕ × ℕ → ℕ × ℕ → M) (n m : ℕ) :
    (∑ β ∈ Finset.Iic (n, m), (n.choose β.1 * m.choose β.2) •
      u (β.1 + 1, β.2) (n - β.1, m - β.2)) +
    (∑ β ∈ Finset.Iic (n, m), (n.choose β.1 * m.choose β.2) •
      u β (n - β.1 + 1, m - β.2)) =
    ∑ β ∈ Finset.Iic (n + 1, m), ((n + 1).choose β.1 * m.choose β.2) •
      u β (n + 1 - β.1, m - β.2) := by
  rw [binomialConvolution_pair_rectangle
      (fun β γ => u (β.1 + 1, β.2) γ),
    binomialConvolution_pair_rectangle (fun β γ => u β (γ.1 + 1, γ.2)),
    binomialConvolution_pair_rectangle u]
  exact binomialConvolution_rectangle_first (fun i j k l => u (i, j) (k, l)) n m

/-- Pair-indexed Pascal identity in the second coordinate. -/
theorem binomialConvolution_pair_second {M : Type*} [AddCommMonoid M]
    (u : ℕ × ℕ → ℕ × ℕ → M) (n m : ℕ) :
    (∑ β ∈ Finset.Iic (n, m), (n.choose β.1 * m.choose β.2) •
      u (β.1, β.2 + 1) (n - β.1, m - β.2)) +
    (∑ β ∈ Finset.Iic (n, m), (n.choose β.1 * m.choose β.2) •
      u β (n - β.1, m - β.2 + 1)) =
    ∑ β ∈ Finset.Iic (n, m + 1), (n.choose β.1 * (m + 1).choose β.2) •
      u β (n - β.1, m + 1 - β.2) := by
  rw [binomialConvolution_pair_rectangle
      (fun β γ => u (β.1, β.2 + 1) γ),
    binomialConvolution_pair_rectangle (fun β γ => u β (γ.1, γ.2 + 1)),
    binomialConvolution_pair_rectangle u]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range (m + 1)),
    Finset.sum_comm (s := Finset.range (m + 2))]
  exact binomialConvolution_rectangle_second (fun i j k l => u (i, j) (k, l)) n m

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! A compatible energy carrier is determined by its continuous Hilbert trace when the spatial embedding is injective. -/

variable {X V H : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem compatibleTraceLpTrace_injective (μ : Measure X) [IsFiniteMeasure μ]
    (ι : V →L[ℂ] H) (hι : Function.Injective ι) :
    Function.Injective (compatibleTraceLpTraceCLM μ ι) := by
  intro u v htrace
  have ht : u.val.1 = v.val.1 := htrace
  have hs : u.val.2 = v.val.2 := by
    apply Lp.ext
    filter_upwards [compatibleTraceLp_agrees μ ι u, compatibleTraceLp_agrees μ ι v] with x hu hv
    apply hι
    exact hu.symm.trans ((congrArg (fun z : C(X, H) => z x) ht).trans hv)
  apply Subtype.ext
  exact Prod.ext ht hs

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Actual mixed complex derivatives indexed by the two-coordinate multiindex. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def complexFrequencyCanonicalJet (f : (Fin 2 → ℂ) → E) (p : ℕ × ℕ) : (Fin 2 → ℂ) → E :=
  complexFrequencyWordJet f (p.1 + p.2) (complexFrequencyCanonicalWord p)

omit [CompleteSpace E] in
theorem complexFrequencyCanonicalJet_zero (f : (Fin 2 → ℂ) → E) (ξ : Fin 2 → ℂ) :
    complexFrequencyCanonicalJet f (0, 0) ξ = f ξ := iteratedFDeriv_zero_apply _

omit [CompleteSpace E] in
theorem complexFrequencyCanonicalJet_left (f : (Fin 2 → ℂ) → E) (a b : ℕ) (ξ : Fin 2 → ℂ) :
    complexFrequencyCanonicalJet f (a + 1, b) ξ =
      complexFrequencyWordJet f (a + b + 1)
        (Fin.cons (Pi.single 0 1) (complexFrequencyCanonicalWord (a, b))) ξ := by
  unfold complexFrequencyCanonicalJet
  rw [complexFrequencyCanonicalWord_left]
  exact complexFrequencyWordJet_cast f (Nat.add_right_comm a 1 b) _ ξ

omit [CompleteSpace E] in
theorem complexFrequencyCanonicalJet_right (f : (Fin 2 → ℂ) → E) (a b : ℕ) (ξ : Fin 2 → ℂ) :
    complexFrequencyCanonicalJet f (a, b + 1) ξ =
      complexFrequencyWordJet f (a + b + 1)
        (Fin.snoc (complexFrequencyCanonicalWord (a, b)) (Pi.single 1 1)) ξ := by
  unfold complexFrequencyCanonicalJet
  rw [complexFrequencyCanonicalWord_right]
  rfl

theorem complexFrequencyCanonicalJet_analyticAt (f : (Fin 2 → ℂ) → E)
    (U : Set (Fin 2 → ℂ)) (hf : AnalyticOnNhd ℂ f U) (p : ℕ × ℕ)
    (ξ : Fin 2 → ℂ) (hξ : ξ ∈ U) :
    AnalyticAt ℂ (complexFrequencyCanonicalJet f p) ξ :=
  complexFrequencyWordJet_analyticAt f U hf (p.1 + p.2) (complexFrequencyCanonicalWord p) ξ hξ

theorem complexFrequencyCanonicalJet_derivatives (f : (Fin 2 → ℂ) → E)
    (U : Set (Fin 2 → ℂ)) (hf : AnalyticOnNhd ℂ f U) (p : ℕ × ℕ)
    (ξ : Fin 2 → ℂ) (hξ : ξ ∈ U) :
    ∃ L : (Fin 2 → ℂ) →L[ℂ] E,
      HasFDerivAt (complexFrequencyCanonicalJet f p) L ξ ∧
      L (Pi.single 0 1) = complexFrequencyCanonicalJet f (p.1 + 1, p.2) ξ ∧
      L (Pi.single 1 1) = complexFrequencyCanonicalJet f (p.1, p.2 + 1) ξ := by
  refine ⟨(fderiv ℂ (iteratedFDeriv ℂ (p.1 + p.2) f) ξ).flipMultilinear
    (complexFrequencyCanonicalWord p),
    complexFrequencyWordJet_hasFDerivAt f U hf _ _ ξ hξ, ?_, ?_⟩
  · exact (complexFrequencyWordJet_derivative_cons f _ _ (Pi.single 0 1) ξ).trans
      (complexFrequencyCanonicalJet_left f p.1 p.2 ξ).symm
  · exact (complexFrequencyWordJet_derivative_cons f _ _ (Pi.single 1 1) ξ).trans
      ((complexFrequencyWordJet_cons_eq_snoc f _ _ (Pi.single 1 1) ξ (hf ξ hξ)).trans
        (complexFrequencyCanonicalJet_right f p.1 p.2 ξ).symm)
end

/-! Complex strong time regularity assembled from the two actual real components. -/

theorem complexStrongTime_of_components {a b : ℝ} {u du : ℝ → ℂ}
    (hr : StrongTimeRegularity a b (fun t => (u t).re) (fun t => (du t).re))
    (hi : StrongTimeRegularity a b (fun t => (u t).im) (fun t => (du t).im)) :
    StrongTimeRegularity a b u du := by
  let L : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp Complex.ofRealCLM
  have ha := (hr.map Complex.ofRealCLM).add (hi.map L)
  have hval : (fun t => Complex.ofRealCLM (u t).re + L (u t).im) = u := by
    funext t
    change ((u t).re : ℂ) + Complex.I * ((u t).im : ℂ) = u t
    simpa only [mul_comm] using Complex.re_add_im (u t)
  have hder : (fun t => Complex.ofRealCLM (du t).re + L (du t).im) = du := by
    funext t
    change ((du t).re : ℂ) + Complex.I * ((du t).im : ℂ) = du t
    simpa only [mul_comm] using Complex.re_add_im (du t)
  rw [hval, hder] at ha
  exact ha

/-! Homogeneous fibre monomials as coefficients of a fixed multilinear degree. -/

def fibreMonomialDegreeCoefficient (n : ℕ) (α : ℕ × ℕ) (hα : α.1 + α.2 = n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin 2 → ℂ) ℂ :=
  (fibreMonomialMultilinear α).domDomCongr (finCongr hα)

theorem fibreMonomialDegreeCoefficient_norm_le (n : ℕ) (α : ℕ × ℕ) (hα : α.1 + α.2 = n) :
    ‖fibreMonomialDegreeCoefficient n α hα‖ ≤ 1 := by
  have he : ‖fibreMonomialDegreeCoefficient n α hα‖ = ‖fibreMonomialMultilinear α‖ :=
    (ContinuousMultilinearMap.domDomCongrₗᵢ ℂ (Fin 2 → ℂ) ℂ (finCongr hα)).norm_map _
  rw [he]
  exact fibreMonomialMultilinear_norm_le α

theorem fibreMonomialDegreeCoefficient_diag (n : ℕ) (α : ℕ × ℕ) (hα : α.1 + α.2 = n)
    (ξ : Fin 2 → ℂ) : fibreMonomialDegreeCoefficient n α hα (fun _ => ξ) = fibreMonomial ξ α := by
  unfold fibreMonomialDegreeCoefficient
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  exact fibreMonomialMultilinear_diag α ξ

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Topology
namespace AVRegularity.CycleEvolution

/-! Exponential decay from a scalar a.e. differential energy inequality. -/

/-- Integrating a homogeneous dissipative inequality gives the exact exponential decay factor. -/
theorem StrongTimeRegularity.scalar_decay {a b : ℝ} (hab : a ≤ b) {E P : ℝ → ℝ}
    (h : StrongTimeRegularity a b E P) (c : ℝ)
    (hg : ∀ᵐ t ∂volume.restrict (Icc a b), P t + c * E t ≤ 0) :
    ∀ t ∈ Icc a b, E t ≤ Real.exp (-c * (t - a)) * E a := by
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have husub : uIcc a t ⊆ uIcc a b := by
    simpa only [uIcc_of_le ht.1, uIcc_of_le hab] using hsub
  have he := (h.mono husub).scalar_weighted_increment c
  have hi : (∫ s in a..t, Real.exp (c * (s - a)) * (P s + c * E s)) ≤ 0 := by
    rw [intervalIntegral.integral_of_le ht.1]
    apply integral_nonpos_of_ae
    have hr := hg.filter_mono (ae_mono (Measure.restrict_mono
      (show Ioc a t ⊆ Icc a b from Ioc_subset_Icc_self.trans hsub) le_rfl))
    filter_upwards [hr] with s hs
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hs
  have hdiv : E t ≤ E a / Real.exp (c * (t - a)) := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    rw [mul_comm]
    linarith
  rw [show -c * (t - a) = -(c * (t - a)) by ring, Real.exp_neg, mul_comm]
  exact (show E t ≤ E a * (Real.exp (c * (t - a)))⁻¹ by simpa only [div_eq_mul_inv] using hdiv)

end AVRegularity.CycleEvolution
end
end
