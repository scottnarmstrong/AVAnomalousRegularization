-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.StageForced
import AVRegularity.CycleJoint.Assembly.PatchBridges
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Flux
public import AVRegularity.Construction.Residual.Presentation.Cascade.CtxFloors

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **K4.1, step 3: from the strong energy bound to the forms.**

Let `û` have order `K + 1` with gradient representative `ŵ` of order `K + 2`
(`truncate ŵ = û` a.e. in time), `û` strongly measurable in time, and
`strongEnergy ρ B π û ŵ ≤ ofReal C`. Then `û` is in `L²` in time with values in `TorusHk (K + 1)`,
the order `K` gradient energy of `û` is integrable, and `√(B ∫ |∇û|²_{ρ,K;π}) ≤ C`. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem energy_forms {K : ℕ} (ρ B : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (hρ : 0 < ρ)
    (hB : 0 < B) (tp tf : ℝ) (û : ∀ i, ℝ → TorusHk (K + 1) (E i))
    (ŵ : ∀ i, ℝ → TorusHk (K + 1 + 1) (E i))
    (htr : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      truncateTorusHk (Nat.le_succ (K + 1)) (ŵ i t) = û i t)
    (hmeas : ∀ i, AEStronglyMeasurable (û i) (volume.restrict (Set.Icc tp tf)))
    (C : ℝ) (hC : 0 ≤ C) (hE : strongEnergy ρ B π tp tf û ŵ ≤ ENNReal.ofReal C) :
    (∀ i, MemLp (û i) 2 (volume.restrict (Set.Icc tp tf))) ∧
    Integrable (fun s => massGradNormSq (E := E) (K := fun _ => K) ρ π (fun i => (û i s).val))
      (volume.restrict (Set.Icc tp tf)) ∧
    Real.sqrt (B * ∫ s in Set.Icc tp tf,
      massGradNormSq (E := E) (K := fun _ => K) ρ π (fun i => (û i s).val)) ≤ C := by
  classical
  set A : ι → ℝ≥0∞ := fun i => ⨆ t ∈ Set.Icc tp tf,
    ENNReal.ofReal (factorialNormSq ρ (û i t).val) with hA
  set L : ι → ℝ≥0∞ := fun i => ∫⁻ s in Set.Icc tp tf,
    ENNReal.ofReal (gradFactorialNormSq ρ (ŵ i s).val) with hL
  set T : ℝ≥0∞ := ∑ i, ENNReal.ofReal (π i)⁻¹ * (A i + ENNReal.ofReal B * L i) with hT
  have hTle : T ≤ ENNReal.ofReal (C ^ 2) := by
    have h1 := ENNReal.rpow_le_rpow hE (show (0 : ℝ) ≤ 2 by norm_num)
    have h2 : T ^ ((1 / 2 : ℝ) * 2) ≤ ENNReal.ofReal C ^ (2 : ℝ) := by
      rw [ENNReal.rpow_mul]; exact h1
    rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2
    rw [ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)] at h2
    simpa using h2
  have hTtop : T < ⊤ := lt_of_le_of_lt hTle ENNReal.ofReal_lt_top
  have hterm : ∀ i, ENNReal.ofReal (π i)⁻¹ * (A i + ENNReal.ofReal B * L i) < ⊤ := fun i =>
    lt_of_le_of_lt (Finset.single_le_sum (f := fun i => ENNReal.ofReal (π i)⁻¹ *
      (A i + ENNReal.ofReal B * L i)) (fun _ _ => zero_le) (Finset.mem_univ i)) hTtop
  have hpos : ∀ i, ENNReal.ofReal (π i)⁻¹ ≠ 0 := fun i =>
    (ENNReal.ofReal_pos.2 (inv_pos.2 (hπ i))).ne'
  have hsum_top : ∀ i, A i + ENNReal.ofReal B * L i < ⊤ := by
    intro i
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    have := hterm i
    rw [hcon, ENNReal.mul_top (hpos i)] at this
    exact lt_irrefl _ this
  have hAtop : ∀ i, A i < ⊤ := fun i => lt_of_le_of_lt le_self_add (hsum_top i)
  have hBpos : ENNReal.ofReal B ≠ 0 := (ENNReal.ofReal_pos.2 hB).ne'
  have hLtop : ∀ i, L i < ⊤ := by
    intro i
    have h := lt_of_le_of_lt le_add_self (hsum_top i)
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.mul_top hBpos] at h
    exact lt_irrefl _ h
  have hmem : ∀ i, MemLp (û i) 2 (volume.restrict (Set.Icc tp tf)) := by
    intro i
    set M := (A i).toReal
    have hbd : ∀ t ∈ Set.Icc tp tf, factorialNormSq ρ (û i t).val ≤ M := by
      intro t ht
      have h1 : ENNReal.ofReal (factorialNormSq ρ (û i t).val) ≤ A i :=
        le_iSup₂ (f := fun t (_ : t ∈ Set.Icc tp tf) =>
          ENNReal.ofReal (factorialNormSq ρ (û i t).val)) t ht
      exact (ENNReal.ofReal_le_iff_le_toReal (hAtop i).ne).1 h1
    have hmin := factorialWeightMin_pos ρ hρ (K := K + 1)
    refine MemLp.of_bound (hmeas i) (M / factorialWeightMin ρ (K + 1) + 1) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hl := factorialNormSq_lower ρ (û i t).val
    have h3 : ‖û i t‖ ^ 2 ≤ M / factorialWeightMin ρ (K + 1) := by
      rw [le_div_iff₀ hmin]
      calc ‖û i t‖ ^ 2 * factorialWeightMin ρ (K + 1)
          = factorialWeightMin ρ (K + 1) * ‖û i t‖ ^ 2 := by ring
        _ ≤ factorialNormSq ρ (û i t).val := hl
        _ ≤ M := hbd t ht
    nlinarith [norm_nonneg (û i t), sq_nonneg (‖û i t‖ - 1)]
  have hint_i : ∀ i, Integrable (fun s => gradFactorialNormSq ρ (û i s).val)
      (volume.restrict (Set.Icc tp tf)) := fun i =>
    CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hmem i)
  have hint : Integrable (fun s => massGradNormSq (E := E) (K := fun _ => K) ρ π
      (fun i => (û i s).val)) (volume.restrict (Set.Icc tp tf)) := by
    unfold massGradNormSq
    exact integrable_finsetSum _ fun i _ => (hint_i i).const_mul _
  refine ⟨hmem, hint, ?_⟩
  have hnn : 0 ≤ ∫ s in Set.Icc tp tf,
      massGradNormSq (E := E) (K := fun _ => K) ρ π (fun i => (û i s).val) :=
    integral_nonneg fun s => Finset.sum_nonneg fun i _ =>
      mul_nonneg (inv_nonneg.2 (hπ i).le) (CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _)
  have hcomp : ∀ i, ENNReal.ofReal (∫ s in Set.Icc tp tf, gradFactorialNormSq ρ (û i s).val) ≤
      L i := by
    intro i
    rw [ofReal_integral_eq_lintegral_ofReal (hint_i i)
      (Filter.Eventually.of_forall fun s => CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _)]
    apply lintegral_mono_ae
    filter_upwards [htr i] with s hs
    apply ENNReal.ofReal_le_ofReal
    rw [← hs]
    exact CycleComparison.Error.gradFactorialNormSq_truncateTorusHk_le (Nat.le_succ K) ρ (ŵ i s)
  have hmain : ENNReal.ofReal (B * ∫ s in Set.Icc tp tf,
      massGradNormSq (E := E) (K := fun _ => K) ρ π (fun i => (û i s).val)) ≤ T := by
    have hrw : B * ∫ s in Set.Icc tp tf,
        massGradNormSq (E := E) (K := fun _ => K) ρ π (fun i => (û i s).val) =
        ∑ i, B * ((π i)⁻¹ * ∫ s in Set.Icc tp tf, gradFactorialNormSq ρ (û i s).val) := by
      unfold massGradNormSq
      rw [integral_finsetSum _ fun i _ => (hint_i i).const_mul _, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul]
    rw [hrw, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hB.le (mul_nonneg
      (inv_nonneg.2 (hπ i).le) (integral_nonneg fun s =>
        CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _)))]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [ENNReal.ofReal_mul hB.le, ENNReal.ofReal_mul (inv_nonneg.2 (hπ i).le)]
    calc ENNReal.ofReal B * (ENNReal.ofReal (π i)⁻¹ *
          ENNReal.ofReal (∫ s in Set.Icc tp tf, gradFactorialNormSq ρ (û i s).val))
        ≤ ENNReal.ofReal B * (ENNReal.ofReal (π i)⁻¹ * L i) := by gcongr; exact hcomp i
      _ = ENNReal.ofReal (π i)⁻¹ * (ENNReal.ofReal B * L i) := by ring
      _ ≤ ENNReal.ofReal (π i)⁻¹ * (A i + ENNReal.ofReal B * L i) := by gcongr; exact le_add_self
  have h3 := hmain.trans hTle
  have h4 := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg C)).1 h3
  exact Real.sqrt_le_iff.2 ⟨hC, h4⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The residual norm and the forcing words of the forced energy**.

At order `0` the forced energy asks the word bounds `hFw`, `hgw` for the forcing
`(-R, -q)` of the error equation; they follow from the residual norm of `(R, q)`
(`residualNorm`) by `‖-z‖ = ‖z‖` and the identification of the order-`0` jet.

For `R = 0` and `q = 0` one has `X = 0`. -/

section
section Jets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The order-`0` jet of an order-`0` element is its value jet. -/
theorem jetOrder_zero (W : TorusHk 0 E) (β : DerivativeWord2 0) :
    torusJetOrder W 0 β = W.toFunction.jet (valueIndex2 0) := by
  funext x
  have hβ : β = Fin.elim0 := Subsingleton.elim _ _
  subst hβ
  simp only [torusJetOrder]
  rfl

omit [FiniteDimensional ℝ E] in
/-- The order-`0` jet of the negation, almost everywhere. -/
theorem jetOrder_zero_neg (W : TorusHk 0 E) (β : DerivativeWord2 0) :
    torusJetOrder ((-1 : ℝ) • W) 0 β =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => -(W.toFunction.jet (valueIndex2 0) x) := by
  rw [jetOrder_zero]
  filter_upwards [KernelEnergy.torusJet_smul_ae (-1 : ℝ) W (valueIndex2 0)] with x hx
  rw [hx, neg_one_smul]

end Jets

section Words

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **The flux words of the forcing `-R`** from the residual norm of `R`. -/
theorem flux_words (ν r X : ℝ) (hν : 0 < ν) (hX : 0 ≤ X) (π : ι → ℝ) (I : Set ℝ)
    (Rr : ∀ v, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h v)))
    (hres : ENNReal.ofReal (Real.sqrt ν)⁻¹ *
      (∫⁻ t in I, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ∑ k : Fin 2, ‖((Rr v t).toFunction.jet (valueIndex2 0) x) k‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal X) :
    ∀ j : Fin (0 + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in I, ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube, ∑ r' : Fin 2,
        ‖r ^ j.val • (torusJetOrder ((-1 : ℝ) • Rr v t) j.val β x) r'‖ₑ ^ 2 ≤
        ENNReal.ofReal (ν * X ^ 2) := by
  intro j β
  obtain rfl := Fin.fin_one_eq_zero j
  refine le_trans (le_of_eq ?_) (AVRegularity.EntryTerminal.ForcedEnergy.lintegral_le_of_inv_sqrt_mul_rpow_le hν hX hres)
  refine lintegral_congr fun t => Finset.sum_congr rfl fun v _ => ?_
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [jetOrder_zero_neg (Rr v t) β] with x hx
  refine Finset.sum_congr rfl fun r' _ => ?_
  erw [hx]
  simp [enorm_neg]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The value words of the forcing `-q`** from the residual norm of `q`. -/
theorem value_words (r X : ℝ) (π : ι → ℝ) (I : Set ℝ)
    (qr : ∀ v, ℝ → TorusHk 0 (h v))
    (hres : ∫⁻ t in I, (∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖(qr v t).toFunction.jet (valueIndex2 0) x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal X) :
    ∀ j : Fin (0 + 1), ∀ β : DerivativeWord2 j.val,
      ∫⁻ t in I, (∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ x in AVenhance.unitCube,
        ‖r ^ j.val • torusJetOrder ((-1 : ℝ) • qr v t) j.val β x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal X := by
  intro j β
  obtain rfl := Fin.fin_one_eq_zero j
  refine le_trans (le_of_eq ?_) hres
  refine lintegral_congr fun t => ?_
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [jetOrder_zero_neg (qr v t) β] with x hx
  erw [hx]
  simp [enorm_neg]

end Words
end

/-! **The error norm of the comparison at order zero is at most twice the strong energy**.

`obsErrorNorm_le`: `obsErrorNorm ν π 0 t₀ t₁ e ew ≤ 2 · strongEnergy ρ ν π t₀ t₁ e ew` for
every radius `ρ` (the factorial weights of order `0` do not see the radius) and positive masses.

For `e = 0`, `ew = 0`, or an empty index both sides vanish. -/

section
section Weights

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {μ : Measure (Vec 2)}

/-- The factorial norm of order `0` does not see the radius. -/
theorem factorialNormSq_zero (r ρ : ℝ) (D : JetL2 μ 0 E) :
    factorialNormSq r D = factorialNormSq ρ D := by
  simp [factorialNormSq, factorialWeight]

/-- The gradient norm of order `0` does not see the radius. -/
theorem gradFactorialNormSq_zero (r ρ : ℝ) (D : JetL2 μ (0 + 1) E) :
    gradFactorialNormSq r D = gradFactorialNormSq ρ D := by
  simp [gradFactorialNormSq, factorialWeight]

end Weights

section Obs

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The sup term of the error norm is at most the strong energy bound (pointwise in time). -/
theorem obs_sup_le (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (t₀ t₁ : ℝ)
    (e : ∀ v, ℝ → TorusHk 0 (h v)) (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) :
    ENNReal.ofReal (massNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.zero_le _) (e v t)).val)) ≤
      ∑ v, ENNReal.ofReal (π v)⁻¹ *
        ⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (e v t).val) := by
  unfold massNormSq
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (inv_nonneg.2 (hπ i).le)
    (factorialNormSq_nonneg _ _))]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le)]
  refine mul_le_mul_right ?_ _
  rw [CycleJointProofs.Assembly.truncateTorusHk_self, factorialNormSq_zero 1 ρ]
  exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc t₀ t₁) =>
    ENNReal.ofReal (factorialNormSq ρ (e v t).val)) t ht

/-- The gradient integral of the error norm, in terms of the integrals of the components. -/
theorem obs_grad_le (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (t₀ t₁ : ℝ)
    (ew : ∀ v, ℝ → TorusHk (0 + 1) (h v))
    (hw : ∀ i, AEMeasurable (fun t => ENNReal.ofReal (gradFactorialNormSq ρ (ew i t).val))
      (volume.restrict (Set.Icc t₀ t₁))) :
    ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (massGradNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (ew v s)).val)) ≤
      ∑ v, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (gradFactorialNormSq ρ (ew v s).val) := by
  have hpt : ∀ s, ENNReal.ofReal (massGradNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (ew v s)).val)) =
      ∑ v, ENNReal.ofReal (π v)⁻¹ * ENNReal.ofReal (gradFactorialNormSq ρ (ew v s).val) := by
    intro s
    unfold massGradNormSq
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (inv_nonneg.2 (hπ i).le)
      (CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ v).le),
      CycleJointProofs.Assembly.truncateTorusHk_self, gradFactorialNormSq_zero 1 ρ]
  simp_rw [hpt]
  rw [lintegral_finsetSum' _ (fun v _ => (hw v).const_mul _)]
  refine le_of_eq (Finset.sum_congr rfl fun v _ => ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **The error norm at order zero is at most twice the strong energy.** -/
theorem obsErrorNorm_le (ν ρ : ℝ) (hν : 0 ≤ ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (t₀ t₁ : ℝ) (e : ∀ v, ℝ → TorusHk 0 (h v)) (ew : ∀ v, ℝ → TorusHk (0 + 1) (h v))
    (hw : ∀ i, AEMeasurable (fun t => ENNReal.ofReal (gradFactorialNormSq ρ (ew i t).val))
      (volume.restrict (Set.Icc t₀ t₁))) :
    obsErrorNorm ν π (fun _ => 0) t₀ t₁ e ew ≤ 2 * strongEnergy ρ ν π t₀ t₁ e ew := by
  set S : ι → ℝ≥0∞ := fun v => ⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (factorialNormSq ρ (e v t).val)
    with hS
  set I : ι → ℝ≥0∞ := fun v => ∫⁻ s in Set.Icc t₀ t₁,
    ENNReal.ofReal (gradFactorialNormSq ρ (ew v s).val) with hI
  have hSE : strongEnergy ρ ν π t₀ t₁ e ew =
      (∑ v, ENNReal.ofReal (π v)⁻¹ * (S v + ENNReal.ofReal ν * I v)) ^ (1 / 2 : ℝ) := rfl
  rw [hSE, two_mul]
  refine add_le_add ?_ ?_
  · refine iSup₂_le fun t ht => ?_
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg
      (AVRegularity.CoupledEnergy.Variational.massNormSq_nonneg _ π hπ _) (by norm_num)]
    refine ENNReal.rpow_le_rpow ((obs_sup_le ρ π hπ t₀ t₁ e t ht).trans ?_) (by norm_num)
    exact Finset.sum_le_sum fun v _ => mul_le_mul_right le_self_add _
  · have hg := obs_grad_le ρ π hπ t₀ t₁ ew hw
    have h1 : ENNReal.ofReal (Real.sqrt ν) = ENNReal.ofReal ν ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hν (by norm_num)]
    rw [h1, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ENNReal.ofReal ν * ∫⁻ s in Set.Icc t₀ t₁,
          ENNReal.ofReal (massGradNormSq (E := h) (K := fun _ => 0) 1 π
            (fun v => (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (ew v s)).val))
        ≤ ENNReal.ofReal ν * ∑ v, ENNReal.ofReal (π v)⁻¹ * I v := mul_le_mul_right hg _
      _ = ∑ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal ν * I v) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ _ := Finset.sum_le_sum fun v _ => mul_le_mul_right le_add_self _

end Obs
end

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.ForcedEnergy
open scoped ENNReal
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **Two bridges of the producer of the comparison clauses** (cascade side of the bill
residual).

The residual presentation of the reconstruction is stated for the trajectory `uK` of the
reconstruction and for the negated residual pair; `ComparisonClauses` asks it for the given
lifted field `û` and for the forcing of `û` itself.

* `kernelWeakSolution_congr_u`, `regSolution_congr_u`: the solution predicate depends on
  the trajectory `u` only through its values on the window `[t₀, t₁]` (for `t₀ ≤ t₁`).
* `residualNorm_of_wordsClause`: the residual clause at the order `0`
  (`ResidualWordsClause 0 … R₁ R₂ q X`, the norm of the scaled jets of the negated pair
  `(−R₁ − R₂, −q)`) gives the residual norm of the value jets of the pair `(R₁ + R₂, q)`, which
  is the forcing of `û`: `residualNorm … ≤ ofReal X`; and the measurability in time of the two
  members (`measurable_of_wordsClause`).

For `R₂ = 0` there is no fine tail, and for `I = ∅` the sums are empty. -/

section Solution

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)]

/-- **The kernel weak solution depends on the trajectory only through its values on the
window.** -/
theorem kernelWeakSolution_congr_u {ν t₀ t₁ : ℝ} {v : ℝ → Vec 2 → Vec 2} {k D : ℕ}
    {B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α}
    {S : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube))}
    {f : ∀ i, TorusHk k (h i)} {F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))}
    {g : ∀ i, ℝ → TorusHk k (h i)} {u : ∀ i, ℝ → TorusHk k (h i)}
    {w : ∀ i, ℝ → TorusHk (k + 1) (h i)}
    {y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α)}
    (hsol : IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u w y) (ht : t₀ ≤ t₁)
    (u' : ∀ i, ℝ → TorusHk k (h i)) (hu : ∀ i, ∀ t ∈ Set.Icc t₀ t₁, u' i t = u i t) :
    IsKernelWeakSolutionTorus ν t₀ t₁ v k D B C S f F g u' w y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hsol
  refine ⟨fun i => (h1 i).congr (hu i), h2, fun i => ?_, fun i => ?_, h5, h6,
    fun i t ht' φ => ?_⟩
  · filter_upwards [h3 i, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [hu i s hmem]
    exact hs
  · rw [hu i t₀ ⟨le_rfl, ht⟩]
    exact h4 i
  · rw [hu i t ht']
    exact h7 i t ht' φ

end Solution

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **A regular solution of a stage depends on the trajectory only through its values on the
window.** -/
theorem regSolution_congr_u {G : GenStage D hr Dm b j₀} {P : ProvParams}
    {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {ν : ℝ}
    {bv : ℝ → Vec 2 → Vec 2} {k : ℕ} {t₀ t₁ : ℝ}
    {f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root)}
    {F : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    {g U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root)}
    {W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root)}
    {Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)}
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f F g U W Y) (ht : t₀ ≤ t₁)
    (U' : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (hU : ∀ v, ∀ t ∈ Set.Icc t₀ t₁, U' v t = U v t) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f F g U' W Y := by
  unfold GenStage.IsRegSolution at hsol ⊢
  exact kernelWeakSolution_congr_u hsol ht U' hU

/-- The same with the initial datum replaced by an equal one. -/
theorem regSolution_congr_init {G : GenStage D hr Dm b j₀} {P : ProvParams}
    {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀} {ν : ℝ}
    {bv : ℝ → Vec 2 → Vec 2} {k : ℕ} {t₀ t₁ : ℝ}
    {f : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root)}
    {F : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))}
    {g U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root)}
    {W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root)}
    {Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)}
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f F g U W Y) (ht : t₀ ≤ t₁)
    (U' : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (hU : ∀ v, ∀ t ∈ Set.Icc t₀ t₁, U' v t = U v t)
    (f' : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root)) (hf : f' = f) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k t₀ t₁ f' F g U' W Y := by
  subst hf
  exact regSolution_congr_u hsol ht U' hU

section Residual

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The residual norm depends on its two members only through their cell integrals. -/
theorem residualNorm_congr (ν : ℝ) (π : ι → ℝ) (I : Set ℝ)
    {R R' : ℝ → Vec 2 → Fin 2 → ∀ i, h i} {q q' : ℝ → Vec 2 → ∀ i, h i}
    (hR : ∀ t v, ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖R t x k v‖ₑ ^ 2 =
      ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖R' t x k v‖ₑ ^ 2)
    (hq : ∀ t v, ∫⁻ x in AVenhance.unitCube, ‖q t x v‖ₑ ^ 2 =
      ∫⁻ x in AVenhance.unitCube, ‖q' t x v‖ₑ ^ 2) :
    residualNorm ν π I R q = residualNorm ν π I R' q' := by
  unfold residualNorm
  simp only [hR, hq]

/-- The word of order `0`. -/
abbrev Word0 : DerivativeWord2 0 := Fin.elim0

/-- **The residual clause at the order `0` in the form of the comparison clauses**: the residual
norm of the value jets of the pair `(R₁ + R₂, q)`. -/
theorem residualNorm_of_wordsClause (ν r : ℝ) (π : ι → ℝ) (I : Set ℝ)
    (R₁ R₂ : ∀ v, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h v)))
    (q : ∀ v, ℝ → TorusHk 0 (h v)) (X : ℝ)
    (hcl : ResidualWordsClause 0 ν r π I R₁ R₂ q X) :
    residualNorm ν π I
        (fun t x k v => ((R₁ v t + R₂ v t).toFunction.jet (valueIndex2 0) x) k)
        (fun t x v => (q v t).toFunction.jet (valueIndex2 0) x) ≤ ENNReal.ofReal X := by
  refine le_of_eq_of_le (residualNorm_congr ν π I ?_ ?_) (hcl.2.2 0 le_rfl Word0)
  · intro t v
    have hL := lintegral_scaled_word_flux (k := 0) 1 (R₁ v t + R₂ v t) (0 : Fin 1) Word0
    have hRr := lintegral_scaled_word_flux (k := 0) r (-(R₁ v t) - R₂ v t) (0 : Fin 1) Word0
    have e1 : ∀ x, ∑ k : Fin 2,
        ‖((R₁ v t + R₂ v t).toFunction.jet (valueIndex2 0) x) k‖ₑ ^ 2 =
        ∑ k : Fin 2, ‖(1 : ℝ) ^ ((0 : Fin 1) : ℕ) •
          (torusJetOrder (R₁ v t + R₂ v t) ((0 : Fin 1) : ℕ) Word0 x) k‖ₑ ^ 2 := by
      intro x
      rw [torusJetOrder_fin (R₁ v t + R₂ v t) (0 : Fin 1) Word0 x]
      simp only [Fin.val_zero, pow_zero, one_smul]
      rfl
    have e3 : ‖(-(R₁ v t) - R₂ v t).val ⟨(0 : Fin 1), Word0⟩‖ =
        ‖(R₁ v t + R₂ v t).val ⟨(0 : Fin 1), Word0⟩‖ := by
      rw [← neg_add']
      exact norm_neg _
    rw [lintegral_congr e1, hL]
    exact (hRr.trans (by simp only [Fin.val_zero, mul_zero, pow_zero, e3])).symm
  · intro t v
    have hL := lintegral_scaled_word_value (k := 0) 1 (q v t) (0 : Fin 1) Word0
    have hRr := lintegral_scaled_word_value (k := 0) r (-(q v t)) (0 : Fin 1) Word0
    have e1 : ∀ x, ‖(q v t).toFunction.jet (valueIndex2 0) x‖ₑ ^ 2 =
        ‖(1 : ℝ) ^ ((0 : Fin 1) : ℕ) •
          torusJetOrder (q v t) ((0 : Fin 1) : ℕ) Word0 x‖ₑ ^ 2 := by
      intro x
      rw [torusJetOrder_fin (q v t) (0 : Fin 1) Word0 x]
      simp only [Fin.val_zero, pow_zero, one_smul]
      rfl
    have e3 : ‖(-(q v t)).val ⟨(0 : Fin 1), Word0⟩‖ =
        ‖(q v t).val ⟨(0 : Fin 1), Word0⟩‖ := norm_neg _
    rw [lintegral_congr e1, hL]
    exact (hRr.trans (by simp only [Fin.val_zero, mul_zero, pow_zero, e3])).symm

/-- The two members of the forcing of `û` are measurable in time. -/
theorem measurable_of_wordsClause (ν r : ℝ) (π : ι → ℝ) (I : Set ℝ)
    (R₁ R₂ : ∀ v, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h v)))
    (q : ∀ v, ℝ → TorusHk 0 (h v)) (X : ℝ)
    (hcl : ResidualWordsClause 0 ν r π I R₁ R₂ q X) :
    (∀ v, AEStronglyMeasurable (fun t => R₁ v t + R₂ v t) (volume.restrict I)) ∧
      ∀ v, AEStronglyMeasurable (q v) (volume.restrict I) := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · refine (hcl.1 v).neg.congr (Filter.Eventually.of_forall fun t => ?_)
    show -(-(R₁ v t) - R₂ v t) = R₁ v t + R₂ v t
    abel
  · exact (hcl.2.1 v).neg.congr (Filter.Eventually.of_forall fun t => neg_neg _)

end Residual

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The data of the bill residual as one context** (cascade side of the bill residual).

`BillCtx` bundles the binders of the data statements of the preservation step, from the scale
data `D` to the retained solution `Y` (the text of `SuccessorBillResidualDataStatement`,
`Construction/Preservation/Assembly/SuccessorBillStatements.lean`, without the level threshold
`m_* ≤ m` and without the quiet margin, which only some statements take). A data statement of the
library is applied to a context by `c.D c.hα …` once, in its adapter; the cascade pieces are
stated at the frame `c.frame …` of a lifted field.

* `BillCtx.Gr`: the retained family `G'.retained m H J`.
* `BillCtx.frame`: the frame of a lifted field of the context with classical representatives of
  the readout and of the retained solution.
* `successorBillResidualData_of_ctx`: the data statement of the bill residual from its form over
  contexts.

An empty component family is a context (no field asks a component), and `Ain = 0` and
negative `C_Q`, `C_pr` are allowed, as in the data statement. -/

/-- The data of a cascade passage after the choices of the prefix (with the pointwise
molecular envelope `hpw` of the seed). -/
structure BillCtx (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ)
    (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] where
  D : OCData
  hα : D.α = α
  hq : D.q = q
  hΛ : D.Λ = Λ
  hζ : D.ζ = ζ
  hseq : IsOCStreamSeq α q Λ ζ D.Φ
  M : ℕ
  hband : IsOCBandChain α q Λ ζ M D.κ
  hterm : D.term = M
  Mnat : ℕ
  hMnat : M ≤ Mnat
  law : BirthLaw
  hlaw : IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law
  seedK : ℕ → KernelSpec
  freshK : ℕ → KernelSpec
  hfresh : ∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')
  seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀
  n : ℕ
  tS : ℝ
  tf : ℝ
  hseed : IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
    hφ₀ Mnat kS seed n tS tf Ce τe r₀ D₀
  hpw : IsSeedPointwiseMolecular law kS seed tS tf
  m : ℕ
  hmn : m ≤ n
  hnM : n < M
  tA : ℝ
  s₀ : ℝ
  htA : tS ≤ tA
  hs₀ : tA + 3 * ocTau α q Λ m ≤ s₀
  htf : s₀ + 4 * ocTauPP α q Λ m ≤ tf
  hT₀ : tf - s₀ ≤ T₀
  G : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀
  G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀
  hcascade : IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
    (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G
  hlevel : G.level = m
  hinv : IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
    hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
    (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G
  hactual : IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
    (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G'
  tp : ℝ
  Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
    (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))
  hprep : IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
    φ₀ hφ₀ G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg
  f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)
  Ain : ℝ
  hf : weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain
  Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root)
  Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root)
  Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root)
  Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ →
    TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)
  htrace : IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0
  hsol : (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
    seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
    (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk

namespace BillCtx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
    CQ Cpr Q T₀ hr)

/-- The retained family of the context. -/
abbrev Gr : GenStage c.D hr (succSchedD D₀ N p (H + 1)) bw j₀ := c.G'.retained c.m H J

/-- **The frame of a lifted field of the context**, with classical representatives of the readout
and of the retained solution (the instance of `Frame` at the cascade menu,
`CovarianceTransportDataStatement`). -/
def frame (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
    (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
    (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
      (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
    (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
      (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
      (fun x => aZ t x v) Naux)
    (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux) :
    Frame c.D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
  { G := c.G, G' := c.G', Gr := c.G'.retained c.m H J,
    Mn := succMenu c.Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s),
    P := succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p,
    seedK := c.seedK, freshK := c.freshK, φ₀ := φ₀, m := c.m, H := H, J := J, N := N,
    p := p, depth := succSchedR r₀ J H, Naux := Naux, sX := sX, sZ := sZ,
    η₀ := succEta0 α q s, tp := c.tp, tf := c.tf, Y := c.Y, CcT := CcT, PZ := PZ,
    aRep := aRep, aZ := aZ, aY := aY, û := û,
    lift := (isMenuLiftedField_cascade (succMenu c.Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s))
      rfl rfl c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
      (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û).2 hlift,
    readout := hZ, retained := hY }

end BillCtx

/-- **The data statement of the bill residual from its form over contexts**: above the level
`m_*`, under the quiet margin of the preparation endpoint, the comparison clauses of the context
with the bill `C·A_in·𝔅` for the residual and `C·A_in·(𝔅 + E^Q)` for the error. -/
theorem successorBillResidualData_of_ctx {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {bw Ce τe : ℝ} {kS : InvConsts}
    {r₀ D₀ H J N p nk Lc Lf Acl Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ} {kI : InvConsts}
    {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ C cg : ℝ} {mStar : ℕ}
    (h : ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI
        Cw j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
      Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
      ComparisonClauses c.law (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK
        c.freshK φ₀ hφ₀ c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.s₀ c.tp c.tf
        (C * c.Ain * succBill c.D c.G c.m kI.c₀ kI.cr cg σ₀ (succEta0 α q s) p N Lc Lf Acl J H
          c.tp c.tf (succTheta1 α q s σ₀ (succDstar D₀ N p H))
          (succTheta2 α q s σ₀ (succDstar D₀ N p H)))
        (C * c.Ain * (succBill c.D c.G c.m kI.c₀ kI.cr cg σ₀ (succEta0 α q s) p N Lc Lf Acl J H
          c.tp c.tf (succTheta1 α q s σ₀ (succDstar D₀ N p H))
          (succTheta2 α q s σ₀ (succDstar D₀ N p H)) + c.D.eps (c.m - 1) ^ Q)) c.f c.Y) :
    SuccessorBillResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Lc Lf Acl
      Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C cg mStar := by
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed hpw m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep hquietMargin f Ain hAin Y0 Y Yw Yk htrace hsol
  exact h
    { D := D, hα := hDα, hq := hDq, hΛ := hDΛ, hζ := hDζ, hseq := hseq, M := M, hband := hband,
      hterm := hterm, Mnat := Mnat, hMnat := hMnat, law := law, hlaw := hlaw, seedK := seedK,
      freshK := freshK, hfresh := hfresh, seed := seed, n := n, tS := tS, tf := tf,
      hseed := hseed, hpw := hpw, m := m, hmn := hn, hnM := hnM, tA := tA, s₀ := s₀, htA := htA,
      hs₀ := hs₀,
      htf := htf, hT₀ := hT₀, G := G, G' := G', hcascade := hcascade, hlevel := hlevel,
      hinv := hG, hactual := hactual, tp := tp, Preg := Preg, hprep := hprep, f := f, Ain := Ain,
      hf := hAin, Y0 := Y0, Y := Y, Yw := Yw, Yk := Yk, htrace := htrace, hsol := hsol }
    hm hquietMargin

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **Elementary facts of a context of the bill** (cascade side of the bill residual).

The facts that every piece at a frame asks as hypotheses and that a context `c : BillCtx …` has
by its fields alone: the level is below the terminal level (`m ≤ n < M = D.term`, strictly: a
cascade frame is never terminal), the band chain in the letters of `D`, positive diffusivities
and masses, the cutoff weights of the natural stage, and the order of the times
`t_A ≤ t_A + 3τ_m ≤ s₀ ≤ t_p ≤ s₀ + 4τ''_m ≤ t_f`, `t_f − t_p ≤ T₀`.

Not a fact: `t_p < t_f`. The window of a context can be a point (`t_p = s₀ + 4τ''_m = t_f`).

For an empty component family the mass statement is vacuous; `m = n` is allowed. -/

namespace BillCtx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
    CQ Cpr Q T₀ hr)

/-- The level of a context is at most the terminal level of the band chain. -/
theorem m_le_M : c.m ≤ c.M := le_trans c.hmn c.hnM.le

/-- The level of a context is strictly below the terminal level: a cascade frame is not
terminal. -/
theorem m_lt_term : c.m < c.D.term := by
  rw [c.hterm]
  exact lt_of_le_of_lt c.hmn c.hnM

theorem m_le_term : c.m ≤ c.D.term := c.m_lt_term.le

/-- The band chain in the letters of the data. -/
theorem bandD : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
  rw [c.hα, c.hq, c.hΛ, c.hζ, c.hterm]
  exact c.hband

theorem lambda_ge (hΛ : 128 ≤ Λ) : 128 ≤ c.D.Λ := by
  rw [c.hΛ]
  exact hΛ

theorem q_gt (hq : 1 < q) : 1 < c.D.q := by
  rw [c.hq]
  exact hq

/-- The diffusivity of the level. -/
theorem kappa_pos (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) : 0 < c.D.κ c.m :=
  CycleReference.bandChain_pos hΛ hζ c.hband c.m_le_M

/-- The diffusivity of the parent level. -/
theorem kappa_pred_pos (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) : 0 < c.D.κ (c.m - 1) :=
  CycleReference.bandChain_pos hΛ hζ c.hband (le_trans (Nat.sub_le _ _) c.m_le_M)

/-- The cell diffusivity of the incoming stage is the diffusivity of the level. -/
theorem kap_eq : c.D.kap c.G.level = c.D.κ c.m := by
  unfold OCData.kap
  rw [c.hlevel, min_eq_left c.m_le_term]

/-- The masses of the incoming stage are positive. -/
theorem mass_pos (hq : 1 < q) (hΛ : 128 ≤ Λ) (v : CompIn c.G.comps) : 0 < c.G.mass c.law v := by
  unfold GenStage.mass
  exact Construction.Preservation.Buffer.birth_compMass_pos (c.q_gt hq) (c.lambda_ge hΛ) c.law v.1

/-- The weights of the incoming stage are the cutoffs of the level. -/
theorem weight_eq (p : OddSlot) (t : ℝ) :
    c.G.fam.weight p t = ocCutoff c.D.α c.D.q c.D.Λ c.m p.1 t := by
  refine (c.hinv.1.2.1 p t).trans ?_
  rw [c.hlevel]

theorem s₀_le_tp : c.s₀ ≤ c.tp := c.hprep.2.1

/-- The entrance of the window: three renewal times after the start of the invariant. -/
theorem entrance : c.tA + 3 * ocTau α q Λ c.m ≤ c.tp := le_trans c.hs₀ c.s₀_le_tp

theorem tA_le_tp (hΛ : 1 ≤ Λ) : c.tA ≤ c.tp := by
  have h := c.entrance
  have hτ : 0 < ocTau α q Λ c.m := Construction.Stream.ocTau_pos hΛ
  linarith

theorem tp_le_tf : c.tp ≤ c.tf := by
  have h1 : c.tp ≤ c.s₀ + 4 * ocTauPP c.D.α c.D.q c.D.Λ c.G.level := c.hprep.2.2.1
  rw [c.hα, c.hq, c.hΛ, c.hlevel] at h1
  exact le_trans h1 c.htf

/-- The length of the window is at most `T₀`. -/
theorem window_le : c.tf - c.tp ≤ T₀ := by
  have h1 := c.hT₀
  have h2 := c.s₀_le_tp
  linarith

end BillCtx

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The pointwise molecular envelope of the incoming stage: the statement** (cascade side of
the bill residual).

At a context of the bill the incoming stage `G` is the seed (first passage) or a step of the
cascade. The reconstruction reads the edge coefficients of `G` at every time of the window, so it
needs the pointwise molecular envelope of `G` itself (`IsSeedPointwiseMolecular law k G a t_f`),
which `IsStageInvariant` does not give. From the supplied premise on the seed:

* `PwAt`: for every context of level `≥ m_*`, if the seed has the pointwise envelope
  `IsSeedPointwiseMolecular law kS seed tS tf`, then there are constants `kW` with the radius of
  `kI` (`kW.c₀ = kI.c₀`), the orders `K_res ≤ kW.Ks`, `K_res ≤ kW.Jm` and a start `a ≤ t_A` with
  `IsSeedPointwiseMolecular law kW G a tf`.
* `SeedPointwiseStatement`: that, in the common prefix form (the constant is the level
  `m_*`, chosen before the type data `hr` and the context).

The seed itself is the case `kW = kS`, `a = tS`, and a step is the case `kW = kI`, `a = tA`;
for an empty component family the envelope is vacuous. -/

/-- **The pointwise molecular envelope of the incoming stage at every context of level
`≥ m_*`**, from the supplied pointwise envelope of the seed. -/
def PwAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Kres mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    IsSeedPointwiseMolecular c.law kS c.seed c.tS c.tf →
    ∃ kW : InvConsts, kW.c₀ = kI.c₀ ∧ Kres ≤ kW.Ks ∧ Kres ≤ kW.Jm ∧
      ∃ a : ℝ, a ≤ c.tA ∧ IsSeedPointwiseMolecular c.law kW c.G a c.tf

/-- **The pointwise envelope in the common prefix form**; the constant is the level `m_*`. -/
def SeedPointwiseStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  SuccPrefix α s q (X := ℕ)
    (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout Kres npad sX sZ
        σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
      PwAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
        j₀ CQ Cpr Q T₀ Kres x)

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
