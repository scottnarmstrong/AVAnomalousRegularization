-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
public import AVRegularity.CycleWords.MixedWords.RetainedLinear
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

@[expose] public section

section
open MeasureTheory Homogenization Filter AVRegularity.Sobolev
open scoped ENNReal Topology
namespace AVRegularity.CycleWords.Assembly

/-! # Band-limited functions: derivatives, coordinate weights, Plancherel

For amplitudes `(A, B)` of class `C^m` vanishing outside `|θ| ≤ r` (`IsBandAmp`):
* a derivative `∂_{z_k}` multiplies the amplitudes by `θ_k` and rotates the pair by
  `J(A, B) = (B, -A)` (`orderedDerivative_ampFun_eq`);
* a coordinate weight `z_k` differentiates the amplitudes in `θ_k` and rotates the pair
  (integration by parts, `coordPow_smul_ampFun`);
* without parity, `‖ampFun r A B‖₂ ≤ 2π (‖A‖₂² + ‖B‖₂²)^{1/2}` (`eLpNorm_ampFun_le`). -/

section Rotation

variable {E : Type*} [NormedAddCommGroup E]

/-- The rotation `(A, B) ↦ (B, -A)` of amplitude pairs, iterated `j` times. -/
def jRot : ℕ → (Vec 2 → E) × (Vec 2 → E) → (Vec 2 → E) × (Vec 2 → E)
  | 0, p => p
  | j + 1, p => ((jRot j p).2, -(jRot j p).1)

theorem jRot_succ (j : ℕ) (p : (Vec 2 → E) × (Vec 2 → E)) :
    jRot (j + 1) p = jRot 1 (jRot j p) := rfl

theorem jRot_add (i j : ℕ) (p : (Vec 2 → E) × (Vec 2 → E)) :
    jRot (i + j) p = jRot i (jRot j p) := by
  induction i with
  | zero => simp [jRot]
  | succ i ih =>
    rw [Nat.add_right_comm, jRot_succ, ih, jRot_succ i]

theorem jRot_norm_sq (j : ℕ) (p : (Vec 2 → E) × (Vec 2 → E)) (θ : Vec 2) :
    ‖(jRot j p).1 θ‖ ^ 2 + ‖(jRot j p).2 θ‖ ^ 2 = ‖p.1 θ‖ ^ 2 + ‖p.2 θ‖ ^ 2 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [jRot, Pi.neg_apply, norm_neg]
    rw [add_comm, ih]

/-- An odd operation on amplitudes commutes with the rotation. -/
theorem jRot_comm (T : (Vec 2 → E) → (Vec 2 → E)) (hT : ∀ X, T (-X) = -T X) (j : ℕ)
    (p : (Vec 2 → E) × (Vec 2 → E)) :
    jRot j (T p.1, T p.2) = (T (jRot j p).1, T (jRot j p).2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [jRot, ih, hT]

/-- A property preserved by negation is preserved by the rotation. -/
theorem jRot_mem (P : (Vec 2 → E) → Prop) (hneg : ∀ X, P X → P (-X)) (j : ℕ)
    {p : (Vec 2 → E) × (Vec 2 → E)} (h1 : P p.1) (h2 : P p.2) :
    P (jRot j p).1 ∧ P (jRot j p).2 := by
  induction j with
  | zero => exact ⟨h1, h2⟩
  | succ j ih => exact ⟨ih.2, hneg _ ih.1⟩

end Rotation

section Amplitudes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An amplitude of class `C^m` vanishing outside the ball `|θ| ≤ r`. -/
def IsBandAmp (r : ℝ) (m : ℕ) (X : Vec 2 → E) : Prop :=
  ContDiff ℝ m X ∧ ∀ θ : Vec 2, r ^ 2 < vecDot θ θ → X θ = 0

/-- The directional derivative `∂_{θ_i}` of an amplitude. -/
noncomputable def dirDeriv (i : Fin 2) (X : Vec 2 → E) : Vec 2 → E :=
  fun θ => fderiv ℝ X θ (basisVec i)

theorem dirDeriv_neg (i : Fin 2) (X : Vec 2 → E) : dirDeriv i (-X) = -dirDeriv i X := by
  funext θ
  show fderiv ℝ (-X) θ (basisVec i) = -(fderiv ℝ X θ (basisVec i))
  rw [fderiv_neg]
  rfl

theorem iterate_dirDeriv_neg (i : Fin 2) (j : ℕ) (X : Vec 2 → E) :
    (dirDeriv i)^[j] (-X) = -(dirDeriv i)^[j] X := by
  induction j generalizing X with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dirDeriv_neg, ih]

theorem IsBandAmp.neg {r : ℝ} {m : ℕ} {X : Vec 2 → E} (hX : IsBandAmp r m X) :
    IsBandAmp r m (-X) :=
  ⟨hX.1.neg, fun θ hθ => by rw [Pi.neg_apply, hX.2 θ hθ, neg_zero]⟩

theorem IsBandAmp.of_le {r : ℝ} {m m' : ℕ} {X : Vec 2 → E} (hX : IsBandAmp r m X)
    (h : m' ≤ m) : IsBandAmp r m' X :=
  ⟨hX.1.of_le (by exact_mod_cast h), hX.2⟩

theorem isCompact_ampBall (r : ℝ) : IsCompact {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le (by unfold vecDot; fun_prop)
    continuous_const) ((Metric.isBounded_closedBall (x := (0 : Vec 2)) (r := |r|)).subset ?_)
  intro θ hθ
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (abs_nonneg r)]
  intro i
  have hi : θ i * θ i ≤ vecDot θ θ :=
    Finset.single_le_sum (f := fun j => θ j * θ j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  exact sq_le_sq.mp (by nlinarith [hθ.out])

theorem IsBandAmp.hasCompactSupport {r : ℝ} {m : ℕ} {X : Vec 2 → E} (hX : IsBandAmp r m X) :
    HasCompactSupport X :=
  HasCompactSupport.intro (isCompact_ampBall r) fun θ hθ => hX.2 θ (lt_of_not_ge hθ)

theorem IsBandAmp.integrable {r : ℝ} {m : ℕ} {X : Vec 2 → E} (hX : IsBandAmp r m X) :
    Integrable X :=
  hX.1.continuous.integrable_of_hasCompactSupport hX.hasCompactSupport

theorem IsBandAmp.integrableOn {r : ℝ} {m : ℕ} {X : Vec 2 → E} (hX : IsBandAmp r m X) :
    IntegrableOn X {θ : Vec 2 | vecDot θ θ ≤ r ^ 2} :=
  hX.integrable.integrableOn

theorem IsBandAmp.dir {r : ℝ} {m : ℕ} {X : Vec 2 → E} (hX : IsBandAmp r (m + 1) X)
    (i : Fin 2) : IsBandAmp r m (dirDeriv i X) := by
  refine ⟨?_, fun θ hθ => ?_⟩
  · have h := hX.1.fderiv_right (m := m) (by push_cast; exact le_rfl)
    exact h.clm_apply contDiff_const
  · have hopen : IsOpen {θ : Vec 2 | r ^ 2 < vecDot θ θ} :=
      isOpen_lt continuous_const (by unfold vecDot; fun_prop)
    have hev : X =ᶠ[𝓝 θ] fun _ => 0 :=
      eventually_of_mem (hopen.mem_nhds hθ) fun y hy => hX.2 y hy
    simp only [AVRegularity.CycleWords.Assembly.dirDeriv, hev.fderiv_eq]
    simp

theorem IsBandAmp.iterate_dirDeriv {r : ℝ} {m : ℕ} {X : Vec 2 → E} (i : Fin 2) :
    ∀ {j : ℕ}, IsBandAmp r (m + j) X → IsBandAmp r m ((dirDeriv i)^[j] X)
  | 0, hX => hX
  | j + 1, hX => by
    rw [Function.iterate_succ_apply']
    exact (IsBandAmp.iterate_dirDeriv (m := m + 1) i (j := j)
      (by rwa [show m + (j + 1) = m + 1 + j by omega] at hX)).dir i

/-- The monomial `θ^w = ∏_l θ_{w_l}` of a derivative word. -/
def wordMonomial {a : ℕ} (w : DerivativeWord2 a) (θ : Vec 2) : ℝ := ∏ l : Fin a, θ (w l)

theorem wordMonomial_contDiff {a : ℕ} (w : DerivativeWord2 a) :
    ContDiff ℝ (⊤ : ℕ∞) (wordMonomial w) := by
  unfold wordMonomial
  exact contDiff_prod fun l _ => contDiff_apply ℝ ℝ (w l)

theorem IsBandAmp.monomial_smul {r : ℝ} {m : ℕ} {X : Vec 2 → E} (hX : IsBandAmp r m X)
    {a : ℕ} (w : DerivativeWord2 a) : IsBandAmp r m (fun θ => wordMonomial w θ • X θ) :=
  ⟨((wordMonomial_contDiff w).of_le (by exact_mod_cast le_top)).smul hX.1,
    fun θ hθ => by
      show wordMonomial w θ • X θ = 0
      rw [hX.2 θ hθ, smul_zero]⟩

end Amplitudes

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem fderiv_ampFun_basisVec {r : ℝ} (hr : 0 ≤ r) {A B : Vec 2 → E}
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) (z : Vec 2) (k : Fin 2) :
    fderiv ℝ (ampFun r A B) z (basisVec k) = ampFun r (derivAmpA k B) (derivAmpB k A) z := by
  rw [(hasFDerivAt_ampFun hr hA hB z).fderiv]
  fin_cases k <;> simp [coordSmulRight_apply, basisVec_apply, Fin.sum_univ_two]

omit [CompleteSpace E] in
theorem jRot_succ_smul (k : Fin 2) (j : ℕ) (X Y : Vec 2 → E) :
    jRot (j + 1) (fun θ => θ k • X θ, fun θ => θ k • Y θ) =
      (derivAmpA k (jRot j (X, Y)).2, derivAmpB k (jRot j (X, Y)).1) := by
  have h := jRot_comm (fun X : Vec 2 → E => fun θ => θ k • X θ)
    (fun X => by funext θ; simp) j (X, Y)
  simp only at h
  rw [jRot_succ, h]
  rfl

theorem wordMonomial_succ {a : ℕ} (w : DerivativeWord2 (a + 1)) (θ : Vec 2) :
    wordMonomial w θ = θ (w (Fin.last a)) * wordMonomial (fun i : Fin a => w i.castSucc) θ := by
  simp only [wordMonomial, Fin.prod_univ_castSucc]
  ring

/-- **Derivatives of band-limited functions**: `D^w ampFun r A B` has the amplitudes
`J^a(θ^w A, θ^w B)`. -/
theorem orderedDerivative_ampFun_eq {r : ℝ} (hr : 0 ≤ r) : ∀ {a : ℕ} (w : DerivativeWord2 a)
    {A B : Vec 2 → E}, IsBandAmp r 0 A → IsBandAmp r 0 B →
    orderedDerivative w (ampFun r A B) =
      ampFun r (jRot a (fun θ => wordMonomial w θ • A θ, fun θ => wordMonomial w θ • B θ)).1
        (jRot a (fun θ => wordMonomial w θ • A θ, fun θ => wordMonomial w θ • B θ)).2
  | 0, w, A, B, _, _ => by
    rw [AVRegularity.orderedDerivative_zero]
    simp [jRot, wordMonomial]
  | a + 1, w, A, B, hA, hB => by
    have hmem := jRot_mem (fun X : Vec 2 → E => IsBandAmp r 0 X) (fun X hX => hX.neg) a
      (p := (fun θ => wordMonomial (fun i : Fin a => w i.castSucc) θ • A θ,
        fun θ => wordMonomial (fun i : Fin a => w i.castSucc) θ • B θ))
      (hA.monomial_smul _) (hB.monomial_smul _)
    rw [AVRegularity.orderedDerivative_succ,
      orderedDerivative_ampFun_eq hr (fun i : Fin a => w i.castSucc) hA hB]
    funext z
    rw [fderiv_ampFun_basisVec hr hmem.1.integrableOn hmem.2.integrableOn]
    have hPw : (fun θ => wordMonomial w θ • A θ, fun θ => wordMonomial w θ • B θ) =
        (fun θ => θ (w (Fin.last a)) • (wordMonomial (fun i : Fin a => w i.castSucc) θ • A θ),
          fun θ => θ (w (Fin.last a)) •
            (wordMonomial (fun i : Fin a => w i.castSucc) θ • B θ)) := by
      simp only [wordMonomial_succ, smul_smul]
    rw [hPw, jRot_succ_smul]

omit [CompleteSpace E] in
/-- Integrability of a bounded continuous multiple of an integrable function. -/
theorem integrable_bdd_smul {φ : Vec 2 → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hC : ∀ θ, |φ θ| ≤ C) {X : Vec 2 → E} (hX : Integrable X) :
    Integrable fun θ => φ θ • X θ :=
  Integrable.mono' (hX.norm.const_mul C) (hφ.aestronglyMeasurable.smul hX.aestronglyMeasurable)
    (Eventually.of_forall fun θ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC θ) (norm_nonneg _))

theorem hasFDerivAt_phase_comp {ψ ψ' : ℝ → ℝ} (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (z θ : Vec 2) :
    HasFDerivAt (fun θ => ψ (vecDot θ z)) (ψ' (vecDot θ z) • phaseCLM z) θ := by
  have h : (fun θ : Vec 2 => ψ (vecDot θ z)) = ψ ∘ phaseCLM z :=
    funext fun θ => by simp [phaseCLM_apply]
  rw [h]
  have := (hψ (phaseCLM z θ)).comp_hasFDerivAt θ (phaseCLM z).hasFDerivAt
  rwa [phaseCLM_apply] at this

theorem phaseCLM_basisVec (z : Vec 2) (k : Fin 2) : phaseCLM z (basisVec k) = z k := by
  rw [phaseCLM_apply]
  fin_cases k <;> simp [vecDot, basisVec_apply]

theorem fderiv_sin_phase (z θ : Vec 2) (k : Fin 2) :
    fderiv ℝ (fun θ => Real.sin (vecDot θ z)) θ (basisVec k) = Real.cos (vecDot θ z) * z k := by
  rw [(hasFDerivAt_phase_comp Real.hasDerivAt_sin z θ).fderiv]
  simp [phaseCLM_basisVec]

theorem fderiv_cos_phase (z θ : Vec 2) (k : Fin 2) :
    fderiv ℝ (fun θ => Real.cos (vecDot θ z)) θ (basisVec k) = -Real.sin (vecDot θ z) * z k := by
  rw [(hasFDerivAt_phase_comp Real.hasDerivAt_cos z θ).fderiv]
  simp [phaseCLM_basisVec]

omit [CompleteSpace E] in
theorem IsBandAmp.vanish_dir {r : ℝ} {X : Vec 2 → E} (hX : IsBandAmp r 1 X) (k : Fin 2) :
    ∀ θ : Vec 2, r ^ 2 < vecDot θ θ → dirDeriv k X θ = 0 :=
  (hX.dir (m := 0) k).2

omit [CompleteSpace E] in
theorem ampFun_eq_integral_of_vanish {r : ℝ} {A B : Vec 2 → E}
    (hzero : ∀ θ : Vec 2, r ^ 2 < vecDot θ θ → A θ = 0 ∧ B θ = 0) (z : Vec 2) :
    ampFun r A B z = ∫ θ, (Real.cos (vecDot θ z) • A θ + Real.sin (vecDot θ z) • B θ) := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun θ hθ => ?_
  obtain ⟨hA0, hB0⟩ := hzero θ (lt_of_not_ge hθ)
  rw [hA0, hB0, smul_zero, smul_zero, add_zero]

omit [CompleteSpace E] in
/-- **A coordinate weight differentiates the amplitudes** (integration by parts):
`z_k ampFun r A B = ampFun r (∂_k B) (-∂_k A)`. -/
theorem coord_smul_ampFun {r : ℝ} {A B : Vec 2 → E} (hA : IsBandAmp r 1 A)
    (hB : IsBandAmp r 1 B) (k : Fin 2) (z : Vec 2) :
    z k • ampFun r A B z = ampFun r (dirDeriv k B) (-dirDeriv k A) z := by
  have hzero : ∀ θ : Vec 2, r ^ 2 < vecDot θ θ → A θ = 0 ∧ B θ = 0 := fun θ h =>
    ⟨hA.2 θ h, hB.2 θ h⟩
  have hzero' : ∀ θ : Vec 2, r ^ 2 < vecDot θ θ →
      dirDeriv k B θ = 0 ∧ (-dirDeriv k A) θ = 0 := fun θ h =>
    ⟨hB.vanish_dir k θ h, by rw [Pi.neg_apply, hA.vanish_dir k θ h, neg_zero]⟩
  have hc : Continuous fun θ : Vec 2 => vecDot θ z := by unfold vecDot; fun_prop
  have hAi := hA.integrable
  have hBi := hB.integrable
  have hdA := (hA.dir (m := 0) k).integrable
  have hdB := (hB.dir (m := 0) k).integrable
  have hAd : Differentiable ℝ A := hA.1.differentiable (by norm_num)
  have hBd : Differentiable ℝ B := hB.1.differentiable (by norm_num)
  have hsd : Differentiable ℝ fun θ : Vec 2 => Real.sin (vecDot θ z) := fun θ =>
    (hasFDerivAt_phase_comp Real.hasDerivAt_sin z θ).differentiableAt
  have hcd : Differentiable ℝ fun θ : Vec 2 => Real.cos (vecDot θ z) := fun θ =>
    (hasFDerivAt_phase_comp Real.hasDerivAt_cos z θ).differentiableAt
  have hbd : ∀ θ, |Real.cos (vecDot θ z) * z k| ≤ |z k| := fun θ => by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
  have hbd' : ∀ θ, |-Real.sin (vecDot θ z) * z k| ≤ |z k| := fun θ => by
    rw [abs_mul, abs_neg]; exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)
  -- integration by parts against `A` and `B`
  have ibpA := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := fun θ : Vec 2 => Real.sin (vecDot θ z)) (g := A) (v := basisVec k)
    (by simp_rw [fderiv_sin_phase]; exact integrable_bdd_smul (by fun_prop) hbd hAi)
    (integrable_bdd_smul (Real.continuous_sin.comp hc)
      (fun θ => Real.abs_sin_le_one _) hdA)
    (integrable_bdd_smul (Real.continuous_sin.comp hc) (fun θ => Real.abs_sin_le_one _) hAi)
    (fun θ _ => hsd θ) (fun θ _ => hAd θ)
  have ibpB := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := fun θ : Vec 2 => Real.cos (vecDot θ z)) (g := B) (v := basisVec k)
    (by simp_rw [fderiv_cos_phase]; exact integrable_bdd_smul (by fun_prop) hbd' hBi)
    (integrable_bdd_smul (Real.continuous_cos.comp hc)
      (fun θ => Real.abs_cos_le_one _) hdB)
    (integrable_bdd_smul (Real.continuous_cos.comp hc) (fun θ => Real.abs_cos_le_one _) hBi)
    (fun θ _ => hcd θ) (fun θ _ => hBd θ)
  simp_rw [fderiv_sin_phase, fderiv_cos_phase] at ibpA ibpB
  rw [ampFun_eq_integral_of_vanish hzero, ampFun_eq_integral_of_vanish hzero', ← integral_smul]
  have e1 : (fun θ => z k • (Real.cos (vecDot θ z) • A θ + Real.sin (vecDot θ z) • B θ)) =
      fun θ => (Real.cos (vecDot θ z) * z k) • A θ -
        (-Real.sin (vecDot θ z) * z k) • B θ := by
    funext θ
    rw [smul_add, smul_smul, smul_smul, neg_mul, neg_smul, sub_neg_eq_add, mul_comm (z k),
      mul_comm (z k)]
  have e2 : (fun θ => Real.cos (vecDot θ z) • dirDeriv k B θ +
      Real.sin (vecDot θ z) • (-dirDeriv k A) θ) =
      fun θ => Real.cos (vecDot θ z) • dirDeriv k B θ -
        Real.sin (vecDot θ z) • dirDeriv k A θ := by
    funext θ
    rw [Pi.neg_apply, smul_neg, ← sub_eq_add_neg]
  have i1 : Integrable fun θ => (Real.cos (vecDot θ z) * z k) • A θ :=
    integrable_bdd_smul ((Real.continuous_cos.comp hc).mul continuous_const) hbd hAi
  have i2 : Integrable fun θ => (-Real.sin (vecDot θ z) * z k) • B θ :=
    integrable_bdd_smul ((Real.continuous_sin.comp hc).neg.mul continuous_const) hbd' hBi
  have i3 : Integrable fun θ => Real.cos (vecDot θ z) • dirDeriv k B θ :=
    integrable_bdd_smul (Real.continuous_cos.comp hc) (fun θ => Real.abs_cos_le_one _) hdB
  have i4 : Integrable fun θ => Real.sin (vecDot θ z) • dirDeriv k A θ :=
    integrable_bdd_smul (Real.continuous_sin.comp hc) (fun θ => Real.abs_sin_le_one _) hdA
  rw [e1, e2, integral_sub i1 i2, integral_sub i3 i4]
  have hA' : ∫ θ, Real.sin (vecDot θ z) • dirDeriv k A θ =
      -∫ θ, (Real.cos (vecDot θ z) * z k) • A θ := ibpA
  have hB' : ∫ θ, Real.cos (vecDot θ z) • dirDeriv k B θ =
      -∫ θ, (-Real.sin (vecDot θ z) * z k) • B θ := ibpB
  rw [hA', hB']
  abel

omit [CompleteSpace E] in
/-- **Powers of a coordinate weight**: `z_i^j ampFun r A B = ampFun (J^j (∂_i^j A, ∂_i^j B))`. -/
theorem coordPow_smul_ampFun {r : ℝ} (i : Fin 2) : ∀ (j : ℕ) {A B : Vec 2 → E},
    IsBandAmp r j A → IsBandAmp r j B → ∀ z : Vec 2,
    (z i) ^ j • ampFun r A B z =
      ampFun r (jRot j ((dirDeriv i)^[j] A, (dirDeriv i)^[j] B)).1
        (jRot j ((dirDeriv i)^[j] A, (dirDeriv i)^[j] B)).2 z
  | 0, A, B, _, _, z => by simp [jRot]
  | j + 1, A, B, hA, hB, z => by
    have hA' : IsBandAmp r (1 + j) A := by rwa [Nat.add_comm]
    have hB' : IsBandAmp r (1 + j) B := by rwa [Nat.add_comm]
    have hmem := jRot_mem (fun X : Vec 2 → E => IsBandAmp r 1 X) (fun X hX => hX.neg) j
      (p := ((dirDeriv i)^[j] A, (dirDeriv i)^[j] B)) (hA'.iterate_dirDeriv i)
      (hB'.iterate_dirDeriv i)
    rw [pow_succ', mul_smul, coordPow_smul_ampFun i j (hA.of_le (Nat.le_succ j))
      (hB.of_le (Nat.le_succ j)) z, coord_smul_ampFun hmem.1 hmem.2 i z,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h := jRot_comm (dirDeriv i) (dirDeriv_neg i) j ((dirDeriv i)^[j] A, (dirDeriv i)^[j] B)
    simp only at h
    rw [jRot_succ, h]
    rfl

/-- **Coordinate weights on derivatives**: `z_i^j D^w ampFun r A B` is band-limited with
amplitudes `J^{j+a}(∂_i^j(θ^w A), ∂_i^j(θ^w B))`. -/
theorem coordPow_orderedDerivative_ampFun {r : ℝ} (hr : 0 ≤ r) {m : ℕ} {A B : Vec 2 → E}
    (hA : IsBandAmp r m A) (hB : IsBandAmp r m B) (i : Fin 2) {j : ℕ} (hj : j ≤ m) {a : ℕ}
    (w : DerivativeWord2 a) (z : Vec 2) :
    (z i) ^ j • orderedDerivative w (ampFun r A B) z =
      ampFun r (jRot (j + a) ((dirDeriv i)^[j] (fun θ => wordMonomial w θ • A θ),
          (dirDeriv i)^[j] (fun θ => wordMonomial w θ • B θ))).1
        (jRot (j + a) ((dirDeriv i)^[j] (fun θ => wordMonomial w θ • A θ),
          (dirDeriv i)^[j] (fun θ => wordMonomial w θ • B θ))).2 z := by
  have hmem := jRot_mem (fun X : Vec 2 → E => IsBandAmp r j X) (fun X hX => hX.neg) a
    (p := (fun θ => wordMonomial w θ • A θ, fun θ => wordMonomial w θ • B θ))
    ((hA.of_le hj).monomial_smul w) ((hB.of_le hj).monomial_smul w)
  rw [orderedDerivative_ampFun_eq hr w (hA.of_le (Nat.zero_le m)) (hB.of_le (Nat.zero_le m)),
    coordPow_smul_ampFun i j hmem.1 hmem.2 z]
  have h := jRot_comm ((dirDeriv i)^[j]) (iterate_dirDeriv_neg i j) a
    (fun θ => wordMonomial w θ • A θ, fun θ => wordMonomial w θ • B θ)
  simp only at h
  rw [← h, ← jRot_add]

end Derivatives

section Plancherel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Symmetrizing an amplitude does not increase its `L²` norm. -/
theorem eLpNorm_half_add_neg_le {X : Vec 2 → E} (hX : Integrable X) (c : ℝ) (hc : |c| = 1) :
    eLpNorm (fun θ => (1 / 2 : ℝ) • (X θ + c • X (-θ))) 2 volume ≤ eLpNorm X 2 volume := by
  have hneg : eLpNorm (fun θ => c • X (-θ)) 2 volume = eLpNorm X 2 volume := by
    rw [show (fun θ => c • X (-θ)) = c • (X ∘ Neg.neg) from rfl, eLpNorm_const_smul,
      eLpNorm_comp_measurePreserving hX.aestronglyMeasurable
        (Measure.measurePreserving_neg volume), Real.enorm_eq_ofReal_abs, hc,
      ENNReal.ofReal_one, one_mul]
  have hhalf : ‖(1 / 2 : ℝ)‖ₑ * (eLpNorm X 2 volume + eLpNorm X 2 volume) =
      eLpNorm X 2 volume := by
    rw [Real.enorm_eq_ofReal (by norm_num), ← two_mul, ← mul_assoc,
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [show (fun θ => (1 / 2 : ℝ) • (X θ + c • X (-θ))) =
    (1 / 2 : ℝ) • fun θ => X θ + c • X (-θ) from rfl, eLpNorm_const_smul]
  calc ‖(1 / 2 : ℝ)‖ₑ * eLpNorm (fun θ => X θ + c • X (-θ)) 2 volume
      ≤ ‖(1 / 2 : ℝ)‖ₑ * (eLpNorm X 2 volume + eLpNorm (fun θ => c • X (-θ)) 2 volume) := by
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ = eLpNorm X 2 volume := by rw [hneg, hhalf]

/-- **Plancherel bound without parity**: `‖ampFun r A B‖₂ ≤ 2π (‖A‖₂² + ‖B‖₂²)^{1/2}`. -/
theorem eLpNorm_ampFun_le {r : ℝ} (hr : 0 ≤ r) {A B : Vec 2 → E}
    (hzero : ∀ θ : Vec 2, r ^ 2 < vecDot θ θ → A θ = 0 ∧ B θ = 0)
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) :
    eLpNorm (ampFun r A B) 2 volume ≤
      ENNReal.ofReal (2 * Real.pi) * (eLpNorm A 2 volume ^ 2 + eLpNorm B 2 volume ^ 2) ^
        (1 / 2 : ℝ) := by
  have hsym := IsRetainedAmplitude.symmetrize (g := ampFun r A B) (r := r)
    ⟨hzero, hA, hB, fun z => rfl⟩
  obtain ⟨hz', hAe, hBo, hrep⟩ := hsym
  have hgeq : ampFun r A B = ampFun r (fun θ => (1 / 2 : ℝ) • (A θ + A (-θ)))
      (fun θ => (1 / 2 : ℝ) • (B θ - B (-θ))) := funext hrep
  have hpar : ∀ θ, (fun θ => (1 / 2 : ℝ) • (A θ + A (-θ))) (-θ) =
      (fun θ => (1 / 2 : ℝ) • (A θ + A (-θ))) θ ∧
      (fun θ => (1 / 2 : ℝ) • (B θ - B (-θ))) (-θ) =
        -(fun θ => (1 / 2 : ℝ) • (B θ - B (-θ))) θ := fun θ => by
    simp only [neg_neg]
    constructor
    · rw [add_comm]
    · rw [← smul_neg, neg_sub]
  have hsq := eLpNorm_ampFun_sq hr hz' hAe hBo hpar
  have hAi := integrable_of_amplitude (fun θ h => (hzero θ h).1) hA
  have hBi := integrable_of_amplitude (fun θ h => (hzero θ h).2) hB
  have hAle : eLpNorm (fun θ => (1 / 2 : ℝ) • (A θ + A (-θ))) 2 volume ≤ eLpNorm A 2 volume := by
    have h := eLpNorm_half_add_neg_le hAi 1 (by norm_num)
    simpa only [one_smul] using h
  have hBle : eLpNorm (fun θ => (1 / 2 : ℝ) • (B θ - B (-θ))) 2 volume ≤ eLpNorm B 2 volume := by
    have h := eLpNorm_half_add_neg_le hBi (-1) (by norm_num)
    simpa only [neg_one_smul, ← sub_eq_add_neg] using h
  calc eLpNorm (ampFun r A B) 2 volume
      = (eLpNorm (ampFun r A B) 2 volume ^ 2) ^ (1 / 2 : ℝ) := (sq_rpow_half _).symm
    _ = ENNReal.ofReal (2 * Real.pi) *
          (eLpNorm (fun θ => (1 / 2 : ℝ) • (A θ + A (-θ))) 2 volume ^ 2 +
            eLpNorm (fun θ => (1 / 2 : ℝ) • (B θ - B (-θ))) 2 volume ^ 2) ^ (1 / 2 : ℝ) := by
        rw [hgeq, hsq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half]
    _ ≤ _ := by gcongr

end Plancherel

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # A linear band-limited map from an amplitude assignment

From a cosine and a sine amplitude assignment on compact data, the band-limited functions of the
limit amplitudes form a linear map on the measurable fields of finite moment norm into the band
(`ampLim_band`, `ampFun_ampLim_add_smul`); `LinearMap.exists_extend` extends it to all fields. The
extension is a.e. invariant, equals the band-limited function of the amplitudes on compact data,
and a moment bound on compact data transfers to every measurable field by Fatou
(`exists_band_extension`). -/

section
universe v

section Extend

variable {ι : Type*} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {π : ι → ℝ} {n : ℕ} {s : ℝ} {Cx : ι → ℝ} {ampC ampS : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x}

/-- The band-limited function of the limit amplitudes is in the band. -/
theorem ampLim_band (hB0 : AmplitudePlancherelStatement.{v}) {r : ℝ} (hr : 0 < r)
    (hC : IsAmpAssignment π n s Cx ampC) (hS : IsAmpAssignment π n s Cx ampS)
    {F : ∀ x, Vec 2 → h x} (hd : IsCompactDense F) (hF : F ∈ finiteMomentSubmodule π n s)
    (x : ι) :
    (∀ M : ℕ, ContDiff ℝ M (ampFun r (ampLim π n s ampC F x) (ampLim π n s ampS F x))) ∧
      HasFourierSupportIn (ampFun r (ampLim π n s ampC F x) (ampLim π n s ampS F x)) r := by
  have hret := isRetainedAmplitude_ampFun
    (integrableOn_ampBall_of_memLp (ampLim_memLp hC hd hF x) r)
    (integrableOn_ampBall_of_memLp (ampLim_memLp hS hd hF x) r)
  exact ⟨(hB0 r _ _ _ hr hret).1, ⟨_, _, hret⟩⟩

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- Linearity of the band-limited functions of the limit amplitudes. -/
theorem ampFun_ampLim_add_smul {r : ℝ} (hC : IsAmpAssignment π n s Cx ampC)
    (hS : IsAmpAssignment π n s Cx ampS)
    (hdens : ∀ F : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (F x) volume) → IsCompactDense F)
    {F G : ∀ x, Vec 2 → h x} (hF : F ∈ finiteMomentSubmodule π n s)
    (hG : G ∈ finiteMomentSubmodule π n s) (a b : ℝ) :
    (fun x => ampFun r (ampLim π n s ampC (fun y z => a • F y z + b • G y z) x)
      (ampLim π n s ampS (fun y z => a • F y z + b • G y z) x)) =
      fun x z => a • ampFun r (ampLim π n s ampC F x) (ampLim π n s ampS F x) z +
        b • ampFun r (ampLim π n s ampC G x) (ampLim π n s ampS G x) z := by
  have hFG : (fun y z => a • F y z + b • G y z) ∈ finiteMomentSubmodule π n s :=
    (finiteMomentSubmodule π n s).add_mem ((finiteMomentSubmodule π n s).smul_mem a hF)
      ((finiteMomentSubmodule π n s).smul_mem b hG)
  funext x
  rw [ampFun_congr_ae (ampLim_add_smul_ae hC (hdens F hF.1) (hdens G hG.1) hF hG a b
      (hdens _ hFG.1) x)
    (ampLim_add_smul_ae hS (hdens F hF.1) (hdens G hG.1) hF hG a b (hdens _ hFG.1) x)]
  exact ampFun_add_smul
    (integrableOn_ampBall_of_memLp (ampLim_memLp hC (hdens F hF.1) hF x) r)
    (integrableOn_ampBall_of_memLp (ampLim_memLp hS (hdens F hF.1) hF x) r)
    (integrableOn_ampBall_of_memLp (ampLim_memLp hC (hdens G hG.1) hG x) r)
    (integrableOn_ampBall_of_memLp (ampLim_memLp hS (hdens G hG.1) hG x) r) a b

theorem ampFun_zero_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℝ) :
    ampFun r (fun _ : Vec 2 => (0 : E)) (fun _ => 0) = fun _ => 0 := by
  funext z
  simp [ampFun]

/-- **The extension.** -/
theorem exists_band_extension (hB0 : AmplitudePlancherelStatement.{v}) {r : ℝ} (hr : 0 < r)
    (hC : IsAmpAssignment π n s Cx ampC)
    (hS : IsAmpAssignment π n s Cx ampS)
    (hdens : ∀ F : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (F x) volume) →
      IsCompactDense F) :
    ∃ R : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x),
      (∀ g x, (∀ M : ℕ, ContDiff ℝ M (R g x)) ∧ HasFourierSupportIn (R g x) r) ∧
      (∀ g g' : ∀ x, Vec 2 → h x, (∀ x, g x =ᵐ[volume] g' x) → R g = R g') ∧
      (∀ φ, IsCompactFamily φ → R φ = fun x => ampFun r (ampC φ x) (ampS φ x)) ∧
      ∀ C : ℝ, 0 < C → (∀ φ, IsCompactFamily φ →
        momentNorm π 0 1 (fun x => ampFun r (ampC φ x) (ampS φ x)) ≤
          ENNReal.ofReal C * momentNorm π n s φ) →
        ∀ g : ∀ x, Vec 2 → h x, (∀ x, AEStronglyMeasurable (g x) volume) →
          momentNorm π 0 1 (R g) ≤ ENNReal.ofReal C * momentNorm π n s g := by
  set W := finiteMomentSubmodule (h := h) π n s with hW
  set Band := bandSubmodule (h := h) r with hBand
  let R0 : W →ₗ[ℝ] Band :=
    { toFun := fun F => ⟨fun x => ampFun r (ampLim π n s ampC F x) (ampLim π n s ampS F x),
        fun x => ampLim_band hB0 hr hC hS (hdens F F.2.1) F.2 x⟩
      map_add' := fun F G => by
        apply Subtype.ext
        have hfun : ((F + G : W) : ∀ x, Vec 2 → h x) =
            fun y z => (1 : ℝ) • (F : ∀ x, Vec 2 → h x) y z +
              (1 : ℝ) • (G : ∀ x, Vec 2 → h x) y z := by
          funext y z
          simp
        show (fun x => ampFun r (ampLim π n s ampC ((F + G : W) : ∀ x, Vec 2 → h x) x)
          (ampLim π n s ampS ((F + G : W) : ∀ x, Vec 2 → h x) x)) = _
        rw [hfun, ampFun_ampLim_add_smul hC hS hdens F.2 G.2 1 1]
        funext x z
        simp
      map_smul' := fun c F => by
        apply Subtype.ext
        have hfun : ((c • F : W) : ∀ x, Vec 2 → h x) =
            fun y z => c • (F : ∀ x, Vec 2 → h x) y z + (0 : ℝ) • (F : ∀ x, Vec 2 → h x) y z := by
          funext y z
          simp
        show (fun x => ampFun r (ampLim π n s ampC ((c • F : W) : ∀ x, Vec 2 → h x) x)
          (ampLim π n s ampS ((c • F : W) : ∀ x, Vec 2 → h x) x)) = _
        rw [hfun, ampFun_ampLim_add_smul hC hS hdens F.2 F.2 c 0]
        funext x z
        simp }
  obtain ⟨E, hE⟩ := LinearMap.exists_extend R0
  set R := Band.subtype ∘ₗ E with hR
  have hRW : ∀ F (hF : F ∈ W),
      R F = fun x => ampFun r (ampLim π n s ampC F x) (ampLim π n s ampS F x) := fun F hF => by
    have := LinearMap.congr_fun hE ⟨F, hF⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    simp only [hR, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [this]
    rfl
  have hcomp : ∀ φ, IsCompactFamily φ → R φ = fun x => ampFun r (ampC φ x) (ampS φ x) := by
    intro φ hφ
    have hφW : φ ∈ W := ⟨hφ.aestronglyMeasurable, momentNorm_lt_top_of_compact π n s hφ⟩
    rw [hRW φ hφW]
    funext x
    exact ampFun_congr_ae (ampLim_compact_ae hC hφ (hdens φ hφ.aestronglyMeasurable) x)
      (ampLim_compact_ae hS hφ (hdens φ hφ.aestronglyMeasurable) x)
  have hmeas : ∀ G x, AEStronglyMeasurable (R G x) volume := fun G x =>
    (((E G).2 x).1 0).continuous.aestronglyMeasurable
  refine ⟨R, fun g x => (E g).2 x, fun g g' hgg' => ?_, hcomp, fun C hC0 hcb g hg => ?_⟩
  · -- a.e. invariance
    set N : ∀ x, Vec 2 → h x := fun y z => g y z - g' y z with hN
    have hN0 : ∀ x, N x =ᵐ[volume] 0 := fun x => (hgg' x).mono fun z hz => by simp [hN, hz]
    have hNW : N ∈ W := ⟨fun y => aestronglyMeasurable_zero.congr (hN0 y).symm, by
      rw [momentNorm_eq_zero_of_ae π n s hN0]
      exact ENNReal.zero_lt_top⟩
    have hsub : R g - R g' = R N := by
      rw [← map_sub]
      rfl
    have hzero : R N = 0 := by
      rw [hRW N hNW]
      funext x
      rw [ampFun_congr_ae (ampLim_null_ae hC hN0 (hdens N hNW.1) x)
        (ampLim_null_ae hS hN0 (hdens N hNW.1) x)]
      exact ampFun_zero_zero r
    exact sub_eq_zero.1 (hsub.trans hzero)
  · -- the bound, by Fatou along compact approximations
    by_cases hfin : momentNorm π n s g = ⊤
    · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 hC0).ne']
      exact le_top
    have hgW : g ∈ W := ⟨hg, lt_top_iff_ne_top.2 hfin⟩
    obtain ⟨φs, hφs, hconv⟩ := hdens g hg
    have hconv' := hconv π n s (lt_top_iff_ne_top.2 hfin)
    have hlim : ∀ x z, Tendsto (fun k => R (φs k) x z) atTop (𝓝 (R g x z)) := by
      intro x z
      have hk : (fun k => R (φs k) x z) = fun k => ampFun r (ampC (φs k) x) (ampS (φs k) x) z :=
        funext fun k => by rw [hcomp (φs k) (hφs k)]
      rw [hk, hRW g hgW]
      exact tendsto_ampFun (fun k => hC.mem _ (hφs k) x) (fun k => hS.mem _ (hφs k) x)
        (ampLim_memLp hC (hdens g hg) hgW x) (ampLim_memLp hS (hdens g hg) hgW x)
        (tendsto_ampLim_of_approx hC (hdens g hg) hgW hφs hconv' x)
        (tendsto_ampLim_of_approx hS (hdens g hg) hgW hφs hconv' x) z
    have hF := momentNorm_zero_le_liminf π (G := fun k => R (φs k)) (G₀ := R g)
      (fun k x => hmeas _ x) (fun x => hmeas g x) hlim
    refine hF.trans ?_
    have hbd : ∀ k, momentNorm π 0 1 (R (φs k)) ≤
        ENNReal.ofReal C * momentNorm π n s (φs k) := fun k => by
      rw [hcomp (φs k) (hφs k)]
      exact hcb (φs k) (hφs k)
    have htend := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C)
      (momentNorm_tendsto π n s g φs (lt_top_iff_ne_top.2 hfin) hconv')
      (Or.inr ENNReal.ofReal_ne_top)
    rw [← htend.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hbd)

end Extend
end

/-! # The amplitude assignment of a word block

A smooth compactly supported family lifts to the base slots (A4) and starts a chain (A3); the
explicit amplitudes of its endpoint form an amplitude assignment (`exists_blockAmplitudes`): linear
by the chain combination (A1) and B1 at the datum `0`, bounded in `L²` by Plancherel (B0) and the
order-`0` moment bound of the retained cutoff (B1 and B2). Their band-limited function is the
retained cutoff of the endpoint of every chain from the same datum, at any descending slots. -/

section
universe u v

section Block

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- A compact datum is a.e. a smooth compactly supported family. -/
theorem IsCompactDatum.exists_family {κ0 : ι → ℕ} {f : ∀ x, PlaneHk Set.univ (κ0 x) (h x)}
    (hf : IsCompactDatum f) : ∃ φ : ∀ x, Vec 2 → h x, IsCompactFamily φ ∧
      ∀ x, planeValue (f x) =ᵐ[volume] φ x :=
  ⟨fun x => (hf x).choose, fun x => ⟨(hf x).choose_spec.1, (hf x).choose_spec.2.1⟩,
    fun x => (hf x).choose_spec.2.2⟩

/-- **The amplitudes of compact data through chosen chains**: linear in the datum and equal to the
explicit amplitudes of every chain from the same datum, at any descending slots. -/
theorem exists_linearAmplitudes (hA1 : ChainCombinationStatement.{u, v})
    (hA4 : CompactDensityStatement.{u, v}) (K : ScalarConstants) (η : ℝ) (χlo : Vec 2 → ℝ)
    (hD : 2 ≤ D) (letters : Fin Nw → CycleLetter ι h D) (S ηg t₀ ϖ : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (X₀ : Vec 2)
    (hbase : IsWordSlots letters (wordBaseSlots letters))
    (hexist : ∀ f : ∀ x, PlaneHk Set.univ (wordBaseSlots letters 0 x) (h x), IsCompactDatum f →
      ∃ (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (wordBaseSlots letters j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (wordBaseSlots letters j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (wordBaseSlots letters) t₀ (t₀ + S) v
          f (fun _ _ _ => 0) u w)
    (hint : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        IsCompactDatum f → ∀ x, Integrable (planeValue (u (Fin.last Nw) x (t₀ + S))) volume)
    (hB1z : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        (∀ x, planeValue (f x) =ᵐ[volume] 0) →
        ∀ x, retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) = 0 ∧
          retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) = 0) :
    ∃ ampC ampS : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x,
      (∀ φ ψ, IsCompactFamily φ → IsCompactFamily ψ → ∀ a b : ℝ,
        ampC (fun x z => a • φ x z + b • ψ x z) = (fun x θ => a • ampC φ x θ + b • ampC ψ x θ) ∧
        ampS (fun x z => a • φ x z + b • ψ x z) = (fun x θ => a • ampS φ x θ + b • ampS ψ x θ)) ∧
      ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ φ : ∀ x, Vec 2 → h x, IsCompactFamily φ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        (∀ x, planeValue (f x) =ᵐ[volume] φ x) →
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        ampC φ =
          (fun x => retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S)))) ∧
        ampS φ =
          (fun x => retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S)))) := by
  classical
  have hlift0 : ∀ φ : ∀ x, Vec 2 → h x, IsCompactFamily φ →
      ∃ f : ∀ x, PlaneHk Set.univ (wordBaseSlots letters 0 x) (h x),
        ∀ x, planeValue (f x) =ᵐ[volume] φ x := fun φ hφ =>
    ⟨fun x => (hA4.1 _ (φ x) (hφ x).1 (hφ x).2).choose,
      fun x => (hA4.1 _ (φ x) (hφ x).1 (hφ x).2).choose_spec⟩
  choose lift hlift using hlift0
  have hcd : ∀ φ (hφ : IsCompactFamily φ), IsCompactDatum (lift φ hφ) := fun φ hφ x =>
    ⟨φ x, (hφ x).1, (hφ x).2, hlift φ hφ x⟩
  have hch0 := fun φ (hφ : IsCompactFamily φ) => hexist (lift φ hφ) (hcd φ hφ)
  choose uc wc hch using hch0
  set ampC : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x := fun φ =>
    if hφ : IsCompactFamily φ then fun x =>
      retainedCosAmplitude K η χlo (planeValue (uc φ hφ (Fin.last Nw) x (t₀ + S))) else 0
    with hampC
  set ampS : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x := fun φ =>
    if hφ : IsCompactFamily φ then fun x =>
      retainedSinAmplitude K η χlo (planeValue (uc φ hφ (Fin.last Nw) x (t₀ + S))) else 0
    with hampS
  have hCe : ∀ φ (hφ : IsCompactFamily φ), ampC φ = fun x =>
      retainedCosAmplitude K η χlo (planeValue (uc φ hφ (Fin.last Nw) x (t₀ + S))) :=
    fun φ hφ => by simp only [hampC, hφ, ↓reduceDIte]
  have hSe : ∀ φ (hφ : IsCompactFamily φ), ampS φ = fun x =>
      retainedSinAmplitude K η χlo (planeValue (uc φ hφ (Fin.last Nw) x (t₀ + S))) :=
    fun φ hφ => by simp only [hampS, hφ, ↓reduceDIte]
  refine ⟨ampC, ampS, fun φ ψ hφ hψ a b => ?_, fun κ hκ φ hφ f u w hfφ hc => ?_⟩
  · have hl := fun x => retainedAmplitudes_linear hA1 hD K η χlo letters G v X₀ (ϖ * ηg) t₀
      (t₀ + S) hint hB1z hbase hbase hbase (hch φ hφ) (hcd φ hφ) (hch ψ hψ) (hcd ψ hψ)
      (hch _ (hφ.add_smul hψ a b)) (hcd _ (hφ.add_smul hψ a b)) a b (fun y => by
        filter_upwards [hlift _ (hφ.add_smul hψ a b) y, hlift φ hφ y, hlift ψ hψ y]
          with z h3 h1 h2
        rw [h3, h1, h2]) x
    rw [hCe _ (hφ.add_smul hψ a b), hCe φ hφ, hCe ψ hψ, hSe _ (hφ.add_smul hψ a b), hSe φ hφ,
      hSe ψ hψ]
    exact ⟨funext fun x => funext fun θ => congrFun (hl x).1 θ,
      funext fun x => funext fun θ => congrFun (hl x).2 θ⟩
  · have hfcd : IsCompactDatum f := fun x => ⟨φ x, (hφ x).1, (hφ x).2, hfφ x⟩
    have hl := fun x => retainedAmplitudes_linear hA1 hD K η χlo letters G v X₀ (ϖ * ηg) t₀
      (t₀ + S) hint hB1z hbase hbase hκ (hch φ hφ) (hcd φ hφ) (hch φ hφ) (hcd φ hφ) hc hfcd 1 0
      (fun y => by
        filter_upwards [hfφ y, hlift φ hφ y] with z h3 h1
        rw [h3, h1]
        simp) x
    rw [hCe φ hφ, hSe φ hφ]
    refine ⟨funext fun x => ?_, funext fun x => ?_⟩
    · rw [(hl x).1]
      simp
    · rw [(hl x).2]
      simp

/-- **The amplitude assignment of a block.** -/
theorem exists_blockAmplitudes (hA1 : ChainCombinationStatement.{u, v})
    (hA4 : CompactDensityStatement.{u, v}) (hB0 : AmplitudePlancherelStatement.{v})
    {K : ScalarConstants} {χlo : Vec 2 → ℝ} (hχ : IsLowCutoff K χlo) (hD : 2 ≤ D)
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (letters : Fin Nw → CycleLetter ι h D)
    (η S ηg t₀ ϖ : ℝ) (hr : 0 < 2 * K.ξlo * Real.sqrt η) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (X₀ : Vec 2) (n₀ : ℕ) (C0 : ℝ)
    (hbase : IsWordSlots letters (wordBaseSlots letters))
    (hexist : ∀ f : ∀ x, PlaneHk Set.univ (wordBaseSlots letters 0 x) (h x), IsCompactDatum f →
      ∃ (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (wordBaseSlots letters j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (wordBaseSlots letters j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (wordBaseSlots letters) t₀ (t₀ + S) v
          f (fun _ _ _ => 0) u w)
    (hB1i : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ φ : ∀ x, Vec 2 → h x, IsCompactFamily φ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        (∀ x, planeValue (f x) =ᵐ[volume] φ x) →
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        (∀ x, Integrable (planeValue (u (Fin.last Nw) x (t₀ + S))) volume) ∧
        (∀ x, IsRetainedAmplitude
          (fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))))
          (2 * K.ξlo * Real.sqrt η)
          (retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))
          (retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))))) ∧
        momentNorm π 0 1 (fun x =>
            fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S)))) ≤
          ENNReal.ofReal C0 * momentNorm π n₀ ϖ φ)
    (hB1z : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        (∀ x, planeValue (f x) =ᵐ[volume] 0) →
        ∀ x, retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) = 0 ∧
          retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) = 0) :
    ∃ ampC ampS : (∀ x, Vec 2 → h x) → ∀ x, Vec 2 → h x,
      IsAmpAssignment π n₀ ϖ (fun x => (2 * Real.pi)⁻¹ * Real.sqrt (π x) * C0) ampC ∧
      IsAmpAssignment π n₀ ϖ (fun x => (2 * Real.pi)⁻¹ * Real.sqrt (π x) * C0) ampS ∧
      (∀ φ, IsCompactFamily φ → momentNorm π 0 1
        (fun x => ampFun (2 * K.ξlo * Real.sqrt η) (ampC φ x) (ampS φ x)) ≤
          ENNReal.ofReal C0 * momentNorm π n₀ ϖ φ) ∧
      ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ φ : ∀ x, Vec 2 → h x, IsCompactFamily φ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        (∀ x, planeValue (f x) =ᵐ[volume] φ x) →
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        (fun x => ampFun (2 * K.ξlo * Real.sqrt η) (ampC φ x) (ampS φ x)) = fun x =>
          fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))) := by
  have hint : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        IsCompactDatum f → ∀ x, Integrable (planeValue (u (Fin.last Nw) x (t₀ + S))) volume := by
    intro κ hκ f u w hc hf
    obtain ⟨φ, hφ, hfφ⟩ := hf.exists_family
    exact (hB1i κ hκ φ hφ f u w hfφ hc).1
  obtain ⟨ampC, ampS, hlin, hid⟩ := exists_linearAmplitudes hA1 hA4 K η χlo hD letters S ηg t₀ ϖ
    G v X₀ hbase hexist hint hB1z
  -- a chain for every compact datum
  have hchain : ∀ φ : ∀ x, Vec 2 → h x, IsCompactFamily φ →
      ∃ (f : ∀ x, PlaneHk Set.univ (wordBaseSlots letters 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (wordBaseSlots letters j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (wordBaseSlots letters j x + 1) (h x)),
        (∀ x, planeValue (f x) =ᵐ[volume] φ x) ∧
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) (wordBaseSlots letters) t₀ (t₀ + S) v
          f (fun _ _ _ => 0) u w := by
    intro φ hφ
    have hl := fun x => hA4.1 (wordBaseSlots letters 0 x) (φ x) (hφ x).1 (hφ x).2
    choose f hf using hl
    obtain ⟨u, w, hc⟩ := hexist f fun x => ⟨φ x, (hφ x).1, (hφ x).2, hf x⟩
    exact ⟨f, u, w, hf, hc⟩
  -- the `L²` bounds, by Plancherel and the order-`0` moment bound
  have hbd : ∀ φ, IsCompactFamily φ → ∀ x,
      eLpNorm (ampC φ x) 2 volume ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (π x) * C0) *
            momentNorm π n₀ ϖ φ ∧
        eLpNorm (ampS φ x) 2 volume ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (π x) * C0) *
            momentNorm π n₀ ϖ φ := by
    intro φ hφ x
    obtain ⟨f, u, w, hfφ, hc⟩ := hchain φ hφ
    obtain ⟨-, hret, hmom⟩ := hB1i _ hbase φ hφ f u w hfφ hc
    obtain ⟨hC, hS⟩ := hid _ hbase φ hφ f u w hfφ hc
    rw [hC, hS]
    have hsym : ∀ θ, retainedCosAmplitude K η χlo
        (planeValue (u (Fin.last Nw) x (t₀ + S))) (-θ) =
          retainedCosAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) θ ∧
        retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) (-θ) =
          -retainedSinAmplitude K η χlo (planeValue (u (Fin.last Nw) x (t₀ + S))) θ :=
      fun θ => ⟨retainedCosAmplitude_neg hχ η _ θ, retainedSinAmplitude_neg hχ η _ θ⟩
    obtain ⟨hA, hB⟩ := eLpNorm_amplitude_le hB0 hr (hret x) hsym
    have hg := (eLpNorm_le_momentNorm_zero π _ x (hπ x)).trans
      (mul_le_mul' le_rfl hmom)
    have hconst : ENNReal.ofReal (2 * Real.pi)⁻¹ * (ENNReal.ofReal (Real.sqrt (π x)) *
        (ENNReal.ofReal C0 * momentNorm π n₀ ϖ φ)) =
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (π x) * C0) * momentNorm π n₀ ϖ φ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      ring
    exact ⟨hA.trans ((mul_le_mul' le_rfl hg).trans (le_of_eq hconst)),
      hB.trans ((mul_le_mul' le_rfl hg).trans (le_of_eq hconst))⟩
  -- the identification with the retained cutoff
  have hident : ∀ κ : Fin (Nw + 1) → ι → ℕ, IsWordSlots letters κ →
      ∀ φ : ∀ x, Vec 2 → h x, IsCompactFamily φ →
      ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
        (u : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
        (w : ∀ (j : Fin (Nw + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
        (∀ x, planeValue (f x) =ᵐ[volume] φ x) →
        IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ t₀ (t₀ + S) v f (fun _ _ _ => 0) u w →
        (fun x => ampFun (2 * K.ξlo * Real.sqrt η) (ampC φ x) (ampS φ x)) = fun x =>
          fourierCutoff (retainedCutoff K η χlo) (planeValue (u (Fin.last Nw) x (t₀ + S))) := by
    intro κ hκ φ hφ f u w hfφ hc
    obtain ⟨-, hret, -⟩ := hB1i κ hκ φ hφ f u w hfφ hc
    obtain ⟨hC, hS⟩ := hid κ hκ φ hφ f u w hfφ hc
    rw [hC, hS]
    funext x z
    exact ((hret x).2.2.2 z).symm
  refine ⟨ampC, ampS, ⟨fun φ ψ hφ hψ a b => (hlin φ ψ hφ hψ a b).1, fun φ hφ x => ?_,
    fun φ hφ x => (hbd φ hφ x).1⟩, ⟨fun φ ψ hφ hψ a b => (hlin φ ψ hφ hψ a b).2,
    fun φ hφ x => ?_, fun φ hφ x => (hbd φ hφ x).2⟩, fun φ hφ => ?_, hident⟩
  · exact lt_of_le_of_lt (hbd φ hφ x).1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (momentNorm_lt_top_of_compact π n₀ ϖ hφ))
  · exact lt_of_le_of_lt (hbd φ hφ x).2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (momentNorm_lt_top_of_compact π n₀ ϖ hφ))
  · obtain ⟨f, u, w, hfφ, hc⟩ := hchain φ hφ
    rw [hident _ hbase φ hφ f u w hfφ hc]
    exact (hB1i _ hbase φ hφ f u w hfφ hc).2.2

end Block
end

end AVRegularity.CycleWords.Assembly
end
