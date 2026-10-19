-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.CleanupChain.Main
import AVRegularity.CycleComparison.Lift.TransverseModeFactor

/-! **The scalar cleanup chain is measurable in a parameter.** Let the scalar data `(f₀ t, F₀ t)`
depend on a parameter `t` of a measurable space, satisfy the hypotheses of the chain at every `t`,
and be measurable in `t` at every fixed `(X, z)`. Then:
- the normalized Fourier coefficients `t ↦ dataL2 s (G t) X` are strongly measurable into
  `ℓ²(ℤ²; ℂ)`: each coordinate is a cell integral of a Carathéodory integrand, and the finitely
  supported truncations converge in norm;
- the potential coefficients `t ↦ Pchain (f₀ t) (F₀ t) j X` are strongly measurable, by induction
  on `j`: a slow directional derivative is the limit of the difference quotients;
- the chain fields `t ↦ Vchain (f₀ t) (F₀ t) j X z k` are measurable, because the fast gradient
  of the potential at `z` is a continuous linear function of the coefficients (`gradCLM`);
- the chain sources `t ↦ cleanupSource (Vchain (f₀ t) (F₀ t)) n X z` are measurable. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVenhance.Infra.Torus Filter
open scoped ENNReal

namespace AVRegularity.CleanupChain

/-! ### Limits of difference quotients -/

theorem tendsto_norm_natCast_atTop : Tendsto (fun n : ℕ => ‖(n : ℝ)‖) atTop atTop := by
  have e : (fun n : ℕ => ‖(n : ℝ)‖) = fun n : ℕ => (n : ℝ) :=
    funext fun n => Real.norm_natCast n
  rw [e]
  exact tendsto_natCast_atTop_atTop

/-- A directional derivative in the second variable of a family that is strongly measurable in
a parameter is strongly measurable in the parameter: it is the limit of the difference
quotients. No measurable structure on the values is used. -/
theorem stronglyMeasurable_fderiv_apply {T : Type*} [MeasurableSpace T] {D G : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {R : T → D → G} (hR : ∀ X, StronglyMeasurable fun t => R t X) {X : D}
    (hd : ∀ t, DifferentiableAt ℝ (R t) X) (v : D) :
    StronglyMeasurable fun t => fderiv ℝ (R t) X v := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter ℕ)
    (f := fun (n : ℕ) (t : T) => (n : ℝ) • (R t (X + (n : ℝ)⁻¹ • v) - R t X))
  · intro n
    exact ((hR (X + (n : ℝ)⁻¹ • v)).sub (hR X)).const_smul (n : ℝ)
  · refine tendsto_pi_nhds.mpr fun t => ?_
    exact (hd t).hasFDerivAt.lim v tendsto_norm_natCast_atTop

/-! ### Coefficient sequences -/

/-- A map into `ℓ²(ℤ²; ℂ)` with measurable coordinates is strongly measurable: the finitely
supported truncations converge in norm. -/
theorem stronglyMeasurable_freqL2 {T : Type*} [MeasurableSpace T] {a : T → FreqL2}
    (h : ∀ k, Measurable fun t => a t k) : StronglyMeasurable a := by
  have hm : ∀ k : Fin 2 → ℤ, StronglyMeasurable
      (fun t => lp.single (E := fun _ : Fin 2 → ℤ => ℂ) 2 k (a t k)) := fun k =>
    (lp.isometry_single (E := fun _ : Fin 2 → ℤ => ℂ) (p := 2)
      k).continuous.comp_stronglyMeasurable (h k).stronglyMeasurable
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset (Fin 2 → ℤ)))
    (f := fun s t => ∑ k ∈ s, lp.single (E := fun _ : Fin 2 → ℤ => ℂ) 2 k (a t k))
  · intro s
    exact Finset.stronglyMeasurable_fun_sum s
      (f := fun k t => lp.single (E := fun _ : Fin 2 → ℤ => ℂ) 2 k (a t k)) (fun k _ => hm k)
  · refine tendsto_pi_nhds.mpr fun t => ?_
    have hh := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (a t)
    exact hh

/-- A cell integral of a family of continuous functions that is measurable in a parameter is
measurable in the parameter (Carathéodory integrand). -/
theorem measurable_setIntegral_param {T : Type*} [MeasurableSpace T] (S : Set (Vec 2))
    (g : T → Vec 2 → ℂ) (hc : ∀ t, Continuous (g t)) (hm : ∀ z, Measurable fun t => g t z) :
    Measurable fun t => ∫ z in S, g t z := by
  have hs : Measurable (fun p : Vec 2 × T => g p.2 p.1) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  have hj : Measurable (Function.uncurry g) := hs.comp measurable_swap
  exact (hj.stronglyMeasurable.integral_prod_right (ν := volume.restrict S)).measurable

/-- A Fourier coefficient of a family of continuous functions that is measurable in a parameter
is measurable in the parameter. -/
theorem measurable_smoothFourierCoeff_param {T : Type*} [MeasurableSpace T]
    {w : T → Vec 2 → ℂ} (hc : ∀ t, Continuous (w t)) (hm : ∀ z, Measurable fun t => w t z)
    (k : Fin 2 → ℤ) : Measurable fun t => smoothFourierCoeff (w t) k :=
  measurable_setIntegral_param (unitCell 2) (fun t z => torusCharacter k z * w t z)
    (fun t => (torusCharacter_contDiff k).continuous.mul (hc t))
    (fun z => (hm z).const_mul (torusCharacter k z))

/-- The `H^s` data map of data that are measurable in a parameter is strongly measurable in the
parameter. -/
theorem stronglyMeasurable_dataL2 {T : Type*} [MeasurableSpace T] {s : ℕ}
    {G : T → Vec 2 → Vec 2 → ℂ} (hG : ∀ t X, ContDiff ℝ (s : ℕ∞) (G t X))
    (hper : ∀ t X, AVenhance.IsZ2Periodic (G t X)) (hm : ∀ X z, Measurable fun t => G t X z)
    (X : Vec 2) : StronglyMeasurable fun t => dataL2 s (G t) X := by
  refine stronglyMeasurable_freqL2 fun k => ?_
  have e : (fun t => dataL2 s (G t) X k) =
      fun t => (omegaW s k : ℂ) * smoothFourierCoeff (G t X) k :=
    funext fun t => dataL2_apply (hG t) (hper t) X k
  show Measurable fun t => dataL2 s (G t) X k
  rw [e]
  exact (measurable_smoothFourierCoeff_param (w := fun t => G t X)
    (fun t => (hG t X).continuous) (hm X) k).const_mul (omegaW s k : ℂ)

/-! ### Slow differentiability at a fixed parameter -/

/-- The normalized coefficients of `V_j` are differentiable in the slow variable below the top
slow order. -/
theorem Rmap_differentiableAt {q N : ℕ} {f₀ : Vec 2 → Vec 2 → ℂ}
    {F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ} (hF : IsBoxSmooth N (q + 1) F₀) {j : ℕ} (hj : j + 1 ≤ N)
    (hinv : ChainInv q N f₀ F₀ j) (i : Fin 2) (X : Vec 2) :
    DifferentiableAt ℝ (Rmap (q + 1) F₀ j (Pchain (q + 1) f₀ F₀ j) i) X := by
  obtain ⟨hP, -, -, -, -⟩ := hinv
  obtain ⟨n, hn⟩ : ∃ n, N - j = n + 1 := ⟨N - j - 1, by omega⟩
  rw [hn] at hP
  have hR : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (Rmap (q + 1) F₀ j (Pchain (q + 1) f₀ F₀ j) i) :=
    (Qmap_contDiff hF (by omega) j i).add ((mulCLM (q + 1) i).contDiff.comp hP)
  exact hR.differentiable (natCast_succ_ne_zero n) X

/-- The chain field `V_j` is differentiable in the slow variable below the top slow order. -/
theorem Vchain_slow_differentiable {q N : ℕ} {f₀ : Vec 2 → Vec 2 → ℂ}
    {F₀ : Vec 2 → Vec 2 → Fin 2 → ℂ} (hF : IsBoxSmooth N (q + 1) F₀) {j : ℕ} (hj : j + 1 ≤ N)
    (hinv : ChainInv q N f₀ F₀ j) (z : Vec 2) (k : Fin 2) :
    Differentiable ℝ (fun X => Vchain (q + 1) f₀ F₀ j X z k) := by
  obtain ⟨n, hn⟩ : ∃ n, N - j = n + 1 := ⟨N - j - 1, by omega⟩
  have hbox := Vchain_isBoxSmooth hF hinv
  rw [hn] at hbox
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) k).contDiff.comp
    (hbox.contDiff_slow z)).differentiable (natCast_succ_ne_zero n)

/-! ### The fast gradient as a continuous linear map of the coefficients -/

/-- `∂_{zᵢ}` of the potential at `z`, as a continuous linear map of the coefficients. -/
def gradCLM (q : ℕ) (z : Vec 2) (i : Fin 2) : FreqL2 →L[ℝ] ℂ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Vec 2) ℂ (fun _ => basisVec i)).comp
    (jetCLM (alphaW (q + 1)) (summable_alphaW (q + 1)) 1 (Nat.le_add_left 1 q) z)

theorem gradPot_eq_gradCLM (q : ℕ) (P : Vec 2 → FreqL2) (X z : Vec 2) (i : Fin 2) :
    gradPot (q + 1) P X z i = gradCLM q z i (P X) := by
  have h := iteratedFDeriv_synth (summable_alphaW (q + 1)) (P X) (Nat.le_add_left 1 q) z
  have h1 : iteratedFDeriv ℝ 1 (synth (alphaW (q + 1)) (P X)) z (fun _ => basisVec i) =
      fderiv ℝ (synth (alphaW (q + 1)) (P X)) z (basisVec i) :=
    iteratedFDeriv_one_apply (fun _ => basisVec i)
  show fderiv ℝ (synth (alphaW (q + 1)) (P X)) z (basisVec i) =
    jetCLM (alphaW (q + 1)) (summable_alphaW (q + 1)) 1 (Nat.le_add_left 1 q) z (P X)
      (fun _ => basisVec i)
  rw [← h1, h]

/-! ### The chain with a parameter -/

section Param

variable {T : Type*} [MeasurableSpace T] {q N : ℕ} {f₀ : T → Vec 2 → Vec 2 → ℂ}
  {F₀ : T → Vec 2 → Vec 2 → Fin 2 → ℂ}

/-- The normalized coefficients of the added flux are strongly measurable in the parameter. -/
theorem stronglyMeasurable_Qmap (hF : ∀ t, IsBoxSmooth N (q + 1) (F₀ t))
    (hFp : ∀ t X, AVenhance.IsZ2Periodic (F₀ t X))
    (hFmeas : ∀ X z k, Measurable fun t => F₀ t X z k) (j : ℕ) (i : Fin 2) (X : Vec 2) :
    StronglyMeasurable fun t => Qmap (q + 1) (F₀ t) j i X := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have e : (fun t => Qmap (q + 1) (F₀ t) 0 i X) =
        fun t => dataL2 (q + 1) (fun X z => F₀ t X z i) X :=
      funext fun t => congrFun (Qmap_zero (q + 1) (F₀ t) i) X
    rw [e]
    exact stronglyMeasurable_dataL2 (G := fun t X z => F₀ t X z i)
      (fun t => (component_isBoxSmooth (hF t) i).1)
      (fun t X n z => congrFun (hFp t X n z) i) (fun X z => hFmeas X z i) X
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have e : (fun t => Qmap (q + 1) (F₀ t) (j' + 1) i X) = fun _ => (0 : FreqL2) :=
      funext fun t => congrFun (Qmap_succ (q + 1) (F₀ t) j' i) X
    rw [e]
    exact stronglyMeasurable_const

/-- **The potential coefficients of the chain are strongly measurable in the parameter**, as
maps into `ℓ²(ℤ²; ℂ)`, at every step `j ≤ N` and every slow point. -/
theorem stronglyMeasurable_Pchain (hq : 1 ≤ q) (hf : ∀ t, IsBoxSmooth N (q + 1) (f₀ t))
    (hfp : ∀ t X, AVenhance.IsZ2Periodic (f₀ t X)) (hfm : ∀ t X, fieldCellMean (f₀ t X) = 0)
    (hF : ∀ t, IsBoxSmooth N (q + 1) (F₀ t)) (hFp : ∀ t X, AVenhance.IsZ2Periodic (F₀ t X))
    (hFm : ∀ t X (k : Fin 2), fieldCellMean (fun z => F₀ t X z k) = 0)
    (hfmeas : ∀ X z, Measurable fun t => f₀ t X z)
    (hFmeas : ∀ X z k, Measurable fun t => F₀ t X z k) :
    ∀ j, j ≤ N → ∀ X, StronglyMeasurable fun t => Pchain (q + 1) (f₀ t) (F₀ t) j X := by
  intro j
  induction j with
  | zero =>
    intro _ X
    show StronglyMeasurable fun t => -dataL2 (q + 1) (f₀ t) X
    exact (stronglyMeasurable_dataL2 (G := f₀) (fun t => (hf t).1) hfp hfmeas X).neg
  | succ j ih =>
    intro hj X
    have hinv : ∀ t, ChainInv q N (f₀ t) (F₀ t) j := fun t =>
      chainInv_all hq (hf t) (hfp t) (hfm t) (hF t) (hFp t) (hFm t) j (by omega)
    have hRm : ∀ (i : Fin 2) (X' : Vec 2), StronglyMeasurable fun t =>
        Rmap (q + 1) (F₀ t) j (Pchain (q + 1) (f₀ t) (F₀ t) j) i X' := by
      intro i X'
      show StronglyMeasurable fun t => Qmap (q + 1) (F₀ t) j i X' +
        mulCLM (q + 1) i (Pchain (q + 1) (f₀ t) (F₀ t) j X')
      exact (stronglyMeasurable_Qmap hF hFp hFmeas j i X').add
        ((mulCLM (q + 1) i).continuous.comp_stronglyMeasurable (ih (by omega) X'))
    show StronglyMeasurable fun t => ∑ i : Fin 2,
      fderiv ℝ (Rmap (q + 1) (F₀ t) j (Pchain (q + 1) (f₀ t) (F₀ t) j) i) X (basisVec i)
    exact Finset.stronglyMeasurable_fun_sum Finset.univ
      (f := fun (i : Fin 2) (t : T) =>
        fderiv ℝ (Rmap (q + 1) (F₀ t) j (Pchain (q + 1) (f₀ t) (F₀ t) j) i) X (basisVec i))
      fun i _ => stronglyMeasurable_fderiv_apply
        (R := fun t => Rmap (q + 1) (F₀ t) j (Pchain (q + 1) (f₀ t) (F₀ t) j) i) (hRm i)
        (fun t => Rmap_differentiableAt (hF t) hj (hinv t) i X) (basisVec i)

/-- **The scalar chain is measurable in the parameter**, at every step `j ≤ N` and every point
`(X, z)`. -/
theorem measurable_Vchain_param (hq : 1 ≤ q) (hf : ∀ t, IsBoxSmooth N (q + 1) (f₀ t))
    (hfp : ∀ t X, AVenhance.IsZ2Periodic (f₀ t X)) (hfm : ∀ t X, fieldCellMean (f₀ t X) = 0)
    (hF : ∀ t, IsBoxSmooth N (q + 1) (F₀ t)) (hFp : ∀ t X, AVenhance.IsZ2Periodic (F₀ t X))
    (hFm : ∀ t X (k : Fin 2), fieldCellMean (fun z => F₀ t X z k) = 0)
    (hfmeas : ∀ X z, Measurable fun t => f₀ t X z)
    (hFmeas : ∀ X z k, Measurable fun t => F₀ t X z k) :
    ∀ j, j ≤ N → ∀ X z k, Measurable fun t => Vchain (q + 1) (f₀ t) (F₀ t) j X z k := by
  intro j hj X z k
  have hP := stronglyMeasurable_Pchain hq hf hfp hfm hF hFp hFm hfmeas hFmeas j hj X
  have hg : Measurable fun t => gradPot (q + 1) (Pchain (q + 1) (f₀ t) (F₀ t) j) X z k := by
    have e : (fun t => gradPot (q + 1) (Pchain (q + 1) (f₀ t) (F₀ t) j) X z k) =
        fun t => gradCLM q z k (Pchain (q + 1) (f₀ t) (F₀ t) j X) :=
      funext fun t => gradPot_eq_gradCLM q (Pchain (q + 1) (f₀ t) (F₀ t) j) X z k
    rw [e]
    exact ((gradCLM q z k).continuous.comp_stronglyMeasurable hP).measurable
  have hE : Measurable fun t => Evec (F₀ t) j X z k := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have e : (fun t => Evec (F₀ t) 0 X z k) = fun t => F₀ t X z k :=
        funext fun t => congrFun (congrFun (congrFun (Evec_zero (F₀ t)) X) z) k
      rw [e]
      exact hFmeas X z k
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have e : (fun t => Evec (F₀ t) (j' + 1) X z k) = fun _ => (0 : ℂ) :=
        funext fun t => congrFun (congrFun (congrFun (Evec_succ (F₀ t) j') X) z) k
      rw [e]
      exact measurable_const
  show Measurable fun t => Evec (F₀ t) j X z k +
    gradPot (q + 1) (Pchain (q + 1) (f₀ t) (F₀ t) j) X z k
  exact hE.add hg

/-- **The sources of the scalar chain are measurable in the parameter**: the source
`cleanupSource V n = -div_X V_{n-1}` for `1 ≤ n ≤ N`, at every point `(X, z)`. -/
theorem measurable_cleanupSource_Vchain_param (hq : 1 ≤ q)
    (hf : ∀ t, IsBoxSmooth N (q + 1) (f₀ t))
    (hfp : ∀ t X, AVenhance.IsZ2Periodic (f₀ t X)) (hfm : ∀ t X, fieldCellMean (f₀ t X) = 0)
    (hF : ∀ t, IsBoxSmooth N (q + 1) (F₀ t)) (hFp : ∀ t X, AVenhance.IsZ2Periodic (F₀ t X))
    (hFm : ∀ t X (k : Fin 2), fieldCellMean (fun z => F₀ t X z k) = 0)
    (hfmeas : ∀ X z, Measurable fun t => f₀ t X z)
    (hFmeas : ∀ X z k, Measurable fun t => F₀ t X z k) {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N)
    (X z : Vec 2) :
    Measurable fun t => cleanupSource (Vchain (q + 1) (f₀ t) (F₀ t)) n X z := by
  have hk : ∀ k : Fin 2, Measurable fun t =>
      fderiv ℝ (fun X' => Vchain (q + 1) (f₀ t) (F₀ t) (n - 1) X' z k) X (basisVec k) :=
    fun k => AVRegularity.CycleComparison.Lift.fderiv_apply_parameter_measurable
      (fun t X' => Vchain (q + 1) (f₀ t) (F₀ t) (n - 1) X' z k)
      (fun X' => measurable_Vchain_param hq hf hfp hfm hF hFp hFm hfmeas hFmeas (n - 1)
        (by omega) X' z k)
      (fun t => Vchain_slow_differentiable (hF t) (by omega)
        (chainInv_all hq (hf t) (hfp t) (hfm t) (hF t) (hFp t) (hFm t) (n - 1) (by omega)) z k)
      X (basisVec k)
  show Measurable fun t => -∑ k : Fin 2,
    fderiv ℝ (fun X' => Vchain (q + 1) (f₀ t) (F₀ t) (n - 1) X' z k) X (basisVec k)
  exact (Finset.measurable_sum Finset.univ
    (f := fun (k : Fin 2) (t : T) =>
      fderiv ℝ (fun X' => Vchain (q + 1) (f₀ t) (F₀ t) (n - 1) X' z k) X (basisVec k))
    fun k _ => hk k).neg

end Param

end AVRegularity.CleanupChain
