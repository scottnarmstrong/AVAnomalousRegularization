-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentParameterNormContinuity

@[expose] public noncomputable section

section
open Homogenization Set
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! Finite first and second real derivatives give uniform Taylor control. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independent_parameter_taylor_remainder (f : P → E) (hf : ContDiff ℝ 2 f)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ Y, ‖fderiv ℝ (fderiv ℝ f) Y‖ ≤ C)
    (X Y : P) :
    ‖f Y - f X - fderiv ℝ f X (Y - X)‖ ≤ C * ‖Y - X‖ ^ 2 := by
  let L := fderiv ℝ f X
  let g : P → E := fun Z => f Z - L Z
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgap (Z : P) : ‖fderiv ℝ f Z - L‖ ≤ C * ‖Z - X‖ :=
    independent_parameter_lipschitz _ hdf C hD X Z
  have hg (Z : P) : DifferentiableAt ℝ g Z :=
    ((hf.differentiable (by norm_num)) Z).sub L.differentiableAt
  have hder (Z : P) : fderiv ℝ g Z = fderiv ℝ f Z - L := by
    exact ((hf.differentiable (by norm_num)) Z).hasFDerivAt.sub L.hasFDerivAt |>.fderiv
  have hbound (Z : P) (hZ : Z ∈ Metric.closedBall X ‖Y - X‖) :
      ‖fderiv ℝ g Z‖ ≤ C * ‖Y - X‖ := by
    rw [hder]
    exact (hgap Z).trans (mul_le_mul_of_nonneg_left
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hZ) hC)
  have hx : X ∈ Metric.closedBall X ‖Y - X‖ := Metric.mem_closedBall_self (norm_nonneg _)
  have hy : Y ∈ Metric.closedBall X ‖Y - X‖ := by simp [Metric.mem_closedBall, dist_eq_norm]
  have hm := (convex_closedBall X ‖Y - X‖).norm_image_sub_le_of_norm_fderiv_le
    (fun Z _ => hg Z) hbound hx hy
  have he : g Y - g X = f Y - f X - L (Y - X) := by
    simp only [g, map_sub]
    abel
  rw [he] at hm
  simpa only [pow_two, mul_assoc] using hm

theorem independent_parameter_quotient_bound (f : P → E) (hf : ContDiff ℝ 2 f)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ Y, ‖fderiv ℝ (fderiv ℝ f) Y‖ ≤ C)
    (Y v : P) (h : ℝ) (hh : h ≠ 0) :
    ‖h⁻¹ • (f (Y + h • v) - f Y) - fderiv ℝ f Y v‖ ≤
      C * |h| * ‖v‖ ^ 2 := by
  have ht := independent_parameter_taylor_remainder f hf C hC hD Y (Y + h • v)
  have he : h⁻¹ • (f (Y + h • v) - f Y) - fderiv ℝ f Y v =
      h⁻¹ • (f (Y + h • v) - f Y - fderiv ℝ f Y (h • v)) := by
    simp only [map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hh, one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_inv]
  have hs : ‖Y + h • v - Y‖ = |h| * ‖v‖ := by
    simp [norm_smul, Real.norm_eq_abs]
  rw [hs] at ht
  calc
    |h|⁻¹ * ‖f (Y + h • v) - f Y - fderiv ℝ f Y (h • v)‖ ≤
        |h|⁻¹ * (C * (|h| * ‖v‖) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (by simpa using ht) (inv_nonneg.mpr (abs_nonneg h))
    _ = C * |h| * ‖v‖ ^ 2 := by
      have ha : |h| ≠ 0 := abs_ne_zero.mpr hh
      field_simp

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Finite recurrence sums retain their genuine forcing amplitude. -/

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem IndependentParameterSourceReserve.finsetSum_uniform_budget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ℕ) (f : ι → ℝ → Vec 2 → P → E)
    (Q : ∀ i ∈ s, IndependentParameterSourceReserve H (f i)) (θ B : ℝ)
    (hQ : ∀ i hi r, r ≤ H → (Q i hi).budget r ≤ θ * B) (r : ℕ) (hr : r ≤ H) :
    (IndependentParameterSourceReserve.finsetSum s H f Q).budget r ≤ (s.card : ℝ) * (θ * B) := by
  rw [IndependentParameterSourceReserve.finsetSum_budget]
  apply (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hQ i.val i.property r hr)).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
end

/-! Constituent lists retain multiplicity and the sum of their individual forcing reserves. -/

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def IndependentParameterSourceReserve.listSum {ι : Type*} (l : List ι) (H : ℕ)
    (f : ι → ℝ → Vec 2 → P → E)
    (Q : ∀ i ∈ l, IndependentParameterSourceReserve H (f i)) :
    IndependentParameterSourceReserve H (fun t z Y => (l.map (fun i => f i t z Y)).sum) := by
  induction l with
  | nil => exact IndependentParameterSourceReserve.zero H
  | cons i l ih =>
      have he : (fun t z Y => ((i :: l).map (fun i => f i t z Y)).sum) =
          fun t z Y => f i t z Y + (l.map (fun i => f i t z Y)).sum := by
        funext t z Y
        simp only [List.map_cons, List.sum_cons]
      exact ((Q i (List.mem_cons_self ..)).add
        (ih (fun j hj => Q j (List.mem_cons_of_mem i hj)))).congrSource he.symm

theorem IndependentParameterSourceReserve.listSum_uniform_budget {ι : Type*} (l : List ι) (H : ℕ)
    (f : ι → ℝ → Vec 2 → P → E)
    (Q : ∀ i ∈ l, IndependentParameterSourceReserve H (f i)) (θ B : ℝ)
    (hQ : ∀ i hi r, r ≤ H → (Q i hi).budget r ≤ θ * B) (r : ℕ) (hr : r ≤ H) :
    (IndependentParameterSourceReserve.listSum l H f Q).budget r ≤ (l.length : ℝ) * (θ * B) := by
  induction l with
  | nil =>
      simp only [IndependentParameterSourceReserve.listSum, IndependentParameterSourceReserve.zero, List.length_nil,
        Nat.cast_zero, zero_mul, le_refl]
  | cons i l ih =>
      unfold IndependentParameterSourceReserve.listSum
      rw [IndependentParameterSourceReserve.congrSource_budget]
      change (Q i (List.mem_cons_self ..)).budget r +
        (IndependentParameterSourceReserve.listSum l H f (fun j hj => Q j (List.mem_cons_of_mem i hj))).budget r ≤ _
      have ht := ih (fun j hj => Q j (List.mem_cons_of_mem i hj))
        (fun j hj => hQ j (List.mem_cons_of_mem i hj))
      apply (add_le_add (hQ i (List.mem_cons_self ..) r hr) ht).trans_eq
      rw [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
end

/-! One finite product constant bounds every retained source derivative without enlarging stored amplitudes. -/

section
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E F V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [SecondCountableTopology E] [SecondCountableTopology V] in
theorem IndependentParameterSourceReserve.bilinear_uniform_budget {H : ℕ}
    {f : ℝ → Vec 2 → P → E} {g : ℝ → Vec 2 → P → F}
    (Q : IndependentParameterSourceReserve H f) (R : IndependentParameterSourceReserve H g)
    (T : E →L[ℝ] F →L[ℝ] V) (θ φ B C : ℝ)
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hQ : ∀ i ≤ H, Q.budget i ≤ θ * B) (hR : ∀ i ≤ H, R.budget i ≤ φ * C)
    (r : ℕ) (hr : r ≤ H) :
    (Q.bilinear R T).budget r ≤ (θ * φ) * (‖T‖ * 2 ^ H * B * C) := by
  apply (Q.bilinear_budget_le R T θ φ B C hθ hB hQ hR r hr).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hθ hφ)
  have hp : (2 : ℝ) ^ r ≤ 2 ^ H := pow_le_pow_right₀ (by norm_num) hr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (norm_nonneg T)) hB) hC
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.EntryWeakProofs

/-! The carrier cutoff and time clamp give a genuine global molecular metric. -/

variable {P : Type*}

def cutoffParameterMetric (χ : P → ℝ) (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) (Y : P) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) + χ Y • (G t Y - 1)

theorem cutoffParameterMetric_eq_convex (χ : P → ℝ) (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) (Y : P) : cutoffParameterMetric χ G t Y = χ Y • G t Y + (1 - χ Y) • 1 := by
  ext i j
  simp only [cutoffParameterMetric, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem cutoffParameterMetric_isSymm (χ : P → ℝ) (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) (Y : P) (hG : (G t Y).IsSymm) : (cutoffParameterMetric χ G t Y).IsSymm := by
  rw [cutoffParameterMetric_eq_convex]
  exact (hG.smul (χ Y)).add (Matrix.isSymm_one.smul (1 - χ Y))

theorem cutoffParameterMetric_clamped_isCellMetric
    (χ : P → ℝ) (hχ : ∀ Y, χ Y ∈ Icc 0 1) (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (a b : ℝ) (hab : a ≤ b)
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j))
    (hsy : ∀ t ∈ Icc a b, ∀ Y, (G t Y).IsSymm)
    (he : ∀ t ∈ Icc a b, ∀ Y, ∀ ξ : Vec 2,
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t Y i j * ξ i * ξ j ∧
      (∑ i, ∑ j, G t Y i j * ξ i * ξ j) ≤ (5 / 4) * ∑ i, ξ i ^ 2) (Y : P) :
    IsCellMetric (fun t _ => clampedParameterMetric (cutoffParameterMetric χ G) a b t Y) := by
  apply clampedParameterMetric_isCellMetric (cutoffParameterMetric χ G) a b hab
  · intro X i j
    change Measurable (fun t => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
      χ X * (G t X i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    exact measurable_const.add (measurable_const.mul ((hm X i j).sub measurable_const))
  · intro t ht X
    exact cutoffParameterMetric_isSymm χ G t X (hsy t ht X)
  · intro t ht X ξ
    rw [cutoffParameterMetric_eq_convex]
    obtain ⟨hl, hu⟩ := he t ht X ξ
    exact convex_metric_ellipticity (G t X) (χ X) (hχ X).1 (hχ X).2 ξ hl hu

theorem cutoffParameterMetric_clamped_elliptic
    (χ : P → ℝ) (hχ : ∀ Y, χ Y ∈ Icc 0 1) (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (a b : ℝ) (hab : a ≤ b)
    (he : ∀ t ∈ Icc a b, ∀ Y, ∀ ξ : Vec 2,
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t Y i j * ξ i * ξ j ∧
      (∑ i, ∑ j, G t Y i j * ξ i * ξ j) ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (t : ℝ) (Y : P) (ξ : Vec 2) :
    (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, clampedParameterMetric (cutoffParameterMetric χ G) a b t Y i j * ξ i * ξ j ∧
    (∑ i, ∑ j, clampedParameterMetric (cutoffParameterMetric χ G) a b t Y i j * ξ i * ξ j) ≤ (5 / 4) * ∑ i, ξ i ^ 2 := by
  dsimp only [clampedParameterMetric]
  rw [cutoffParameterMetric_eq_convex]
  obtain ⟨hl, hu⟩ := he _ (metric_clamp_mem a b hab t) Y ξ
  exact convex_metric_ellipticity (G (max a (min b t)) Y) (χ Y) (hχ Y).1 (hχ Y).2 ξ hl hu

end AVRegularity.EntryWeakProofs
end

section
open Set
namespace AVRegularity.EntryWeakProofs

/-! Constant reference entries of norm at most one have a single global cutoff price. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def independentCutoffUnitBudget (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 + ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)‖ *
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * (B (n - i) + 1)

theorem independentCutoffUnitBudget_nonneg (A B : ℕ → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) (n : ℕ) :
    0 ≤ independentCutoffUnitBudget E A B n := by
  apply add_nonneg zero_le_one
  exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (add_nonneg (hB _) zero_le_one))

theorem independentCutoffExtension_jet_bound_one (χ : P → ℝ) (f : P → E) (e : E) (he : ‖e‖ ≤ 1)
    (H n : ℕ) (hχ : ContDiff ℝ (H : ℕ∞) χ) (hf : ContDiff ℝ (H : ℕ∞) f) (hn : n ≤ H)
    (U : Set P) (hs : tsupport χ ⊆ U) (A B : ℕ → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hbχ : ∀ i ≤ H, ∀ Y, ‖iteratedFDeriv ℝ i χ Y‖ ≤ A i)
    (hbf : ∀ i ≤ H, ∀ Y ∈ U, ‖iteratedFDeriv ℝ i f Y‖ ≤ B i) (X : P) :
    ‖iteratedFDeriv ℝ n (independentCutoffExtension χ f e) X‖ ≤ independentCutoffUnitBudget E A B n := by
  apply (independentCutoffExtension_jet_bound χ f e H n hχ hf hn U hs A B hA hB hbχ hbf X).trans
  apply add_le_add he
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) he) (mul_nonneg (Nat.cast_nonneg _) (hA i))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Literal native coordinates pack a slow point and its independent stored family parameters. -/

def independentIntrinsicParameterPacking (d : ℕ) (X : Vec 2) (P : Vec d) : Vec (2 + d) := Fin.addCases X P

theorem independentIntrinsicParameterPacking_slow (d : ℕ) (X : Vec 2) (P : Vec d) :
    independentIntrinsicSlowProjection d (independentIntrinsicParameterPacking d X P) = X := by
  funext i
  simp only [independentIntrinsicSlowProjection, independentIntrinsicParameterPacking,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Fin.addCases_left]

theorem independentIntrinsicParameterPacking_stored (d : ℕ) (X : Vec 2) (P : Vec d) :
    independentStoredParameterProjection d (independentIntrinsicParameterPacking d X P) = P := by
  funext i
  simp only [independentStoredParameterProjection, independentIntrinsicParameterPacking,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Fin.addCases_right]

/-! The full parameter carrier gives an open native slice containing its selected slow point. -/

def independentIntrinsicSliceCarrier (d : ℕ) (U : Set (Vec (2 + d))) (Y : Vec (2 + d)) : Set (Vec 2) :=
  (fun X => independentIntrinsicSlowEmbedding d X + independentIntrinsicSliceOffset d Y) ⁻¹' U

theorem independentIntrinsicSliceCarrier_isOpen (d : ℕ) (U : Set (Vec (2 + d)))
    (hU : IsOpen U) (Y : Vec (2 + d)) : IsOpen (independentIntrinsicSliceCarrier d U Y) :=
  hU.preimage ((independentIntrinsicSlowEmbedding d).continuous.add continuous_const)

theorem independentIntrinsicSliceCarrier_base (d : ℕ) (U : Set (Vec (2 + d)))
    (Y : Vec (2 + d)) (hY : Y ∈ U) :
    independentIntrinsicSlowProjection d Y ∈ independentIntrinsicSliceCarrier d U Y := by
  change independentIntrinsicSlowEmbedding d (independentIntrinsicSlowProjection d Y) +
    independentIntrinsicSliceOffset d Y ∈ U
  rw [independentIntrinsicSliceOffset_base]
  exact hY

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Changing each affine direction retains the small operator difference in every multilinear order. -/

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem independent_multilinear_composition_difference_bound (n : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (L₁ L₀ : V →L[ℝ] E) (K δ : ℝ) (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hL₁ : ‖L₁‖ ≤ K) (hL₀ : ‖L₀‖ ≤ K) (hLd : ‖L₁ - L₀‖ ≤ δ) :
    ‖A.compContinuousLinearMap (fun _ => L₁) - A.compContinuousLinearMap (fun _ => L₀)‖ ≤
      ‖A‖ * n * δ * K ^ n := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro w
  have hpoint i : ‖L₁ (w i) - L₀ (w i)‖ ≤ δ * ‖w i‖ := by
    change ‖(L₁ - L₀) (w i)‖ ≤ _
    exact ((L₁ - L₀).le_opNorm (w i)).trans (mul_le_mul_of_nonneg_right hLd (norm_nonneg _))
  have hnorm j : max ‖L₁ (w j)‖ ‖L₀ (w j)‖ ≤ K * ‖w j‖ :=
    max_le ((L₁.le_opNorm (w j)).trans (mul_le_mul_of_nonneg_right hL₁ (norm_nonneg _)))
      ((L₀.le_opNorm (w j)).trans (mul_le_mul_of_nonneg_right hL₀ (norm_nonneg _)))
  have hprod (i : Fin n) :
      (∏ j : Fin n, if j = i then ‖L₁ (w i) - L₀ (w i)‖ else max ‖L₁ (w j)‖ ‖L₀ (w j)‖) ≤
        δ * K ^ n * ∏ j, ‖w j‖ := by
    calc
      _ ≤ ∏ j : Fin n, (if j = i then δ else 1) * (K * ‖w j‖) := by
        apply Finset.prod_le_prod₀
        · intro j _
          split
          · exact norm_nonneg _
          · exact (norm_nonneg _).trans (le_max_left _ _)
        · intro j _
          by_cases hj : j = i
          · subst j
            simp only [ite_true]
            exact (hpoint i).trans (by
              exact mul_le_mul_of_nonneg_left
                (le_mul_of_one_le_left (norm_nonneg _) hK) hδ)
          · simp only [ite_false, hj, one_mul]
            exact hnorm j
      _ = δ * K ^ n * ∏ j, ‖w j‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_mul_distrib]
        simp only [Finset.mem_univ, ite_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
  change ‖A (fun i => L₁ (w i)) - A (fun i => L₀ (w i))‖ ≤ _
  exact (A.norm_image_sub_le' _ _).trans ((mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => hprod i)) (norm_nonneg A)).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A bounded genuine first derivative controls every nonzero parameter quotient. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independent_parameter_first_quotient_bound (f : P → E) (hf : ContDiff ℝ 1 f)
    (C : ℝ) (hb : ∀ Y, ‖fderiv ℝ f Y‖ ≤ C)
    (Y v : P) (h : ℝ) (hh : h ≠ 0) :
    ‖h⁻¹ • (f (Y + h • v) - f Y)‖ ≤ C * ‖v‖ := by
  have hm := independent_parameter_lipschitz f hf C hb Y (Y + h • v)
  have he : ‖Y + h • v - Y‖ = |h| * ‖v‖ := by
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  rw [he] at hm
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    |h|⁻¹ * ‖f (Y + h • v) - f Y‖ ≤ |h|⁻¹ * (C * (|h| * ‖v‖)) :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (abs_nonneg h))
    _ = C * ‖v‖ := by
      have ha : |h| ≠ 0 := abs_ne_zero.mpr hh
      field_simp

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Jet differences require a bound only along the actual interpolation segment. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independent_parameter_segment_lipschitz (f : P → E) (hf : ContDiff ℝ 1 f)
    (C : ℝ) (X Y : P)
    (hb : ∀ Z ∈ segment ℝ X Y, ‖fderiv ℝ f Z‖ ≤ C) :
    ‖f Y - f X‖ ≤ C * ‖Y - X‖ :=
  (convex_segment (𝕜 := ℝ) X Y).norm_image_sub_le_of_norm_fderiv_le
    (fun Z _ => hf.differentiable (by norm_num) Z) hb
    (left_mem_segment ℝ X Y) (right_mem_segment ℝ X Y)

theorem independent_parameter_segment_jet_difference_bound (f : P → E) (n : ℕ)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (C : ℝ) (X Y : P)
    (hb : ∀ Z ∈ segment ℝ X Y, ‖iteratedFDeriv ℝ (n + 1) f Z‖ ≤ C) :
    ‖iteratedFDeriv ℝ n f Y - iteratedFDeriv ℝ n f X‖ ≤ C * ‖Y - X‖ := by
  have hg : ContDiff ℝ 1 (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show 1 + n ≤ n + 1 by omega))
  exact (convex_segment (𝕜 := ℝ) X Y).norm_image_sub_le_of_norm_fderiv_le
    (fun Z _ => hg.differentiable (by norm_num) Z)
    (fun Z hZ => by rw [norm_fderiv_iteratedFDeriv]; exact hb Z hZ)
    (left_mem_segment ℝ X Y) (right_mem_segment ℝ X Y)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Actual independent-parameter source quotients converge in the inverse source norm. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

theorem IndependentParameterSourceReserve.directional_derivative_measurable {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (hH : 1 ≤ H) (Y v : P) :
    Measurable (fun a : ℝ × Vec 2 => fderiv ℝ (f a.1 a.2) Y v) := by
  have hm := finite_independentParameterWordJet_measurable
    (fun a : ℝ × Vec 2 => f a.1 a.2) 1
    (fun a => ((Q.regular a.1).of_le (by exact_mod_cast hH)).comp₂ contDiff_const contDiff_id)
    Q.measurable (fun _ : Fin 1 => v) Y
  simpa only [realWordJet, iteratedFDeriv_one_apply] using hm

theorem IndependentParameterSourceReserve.quotient_error_ul_bound {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (hH : 2 ≤ H) (Y v : P) (h : ℝ) (hh : h ≠ 0) :
    cellUlNorm univ (fun t z =>
      h⁻¹ • (f t z (Y + h • v) - f t z Y) - fderiv ℝ (f t z) Y v) ≤
      ENNReal.ofReal (Q.budget 2 * |h| * ‖v‖ ^ 2) := by
  apply cell_source_ulNorm_le_pointwise
    (fun t z => h⁻¹ • (f t z (Y + h • v) - f t z Y) - fderiv ℝ (f t z) Y v)
    ((((Q.measurable (Y + h • v)).sub (Q.measurable Y)).const_smul h⁻¹).sub
      (Q.directional_derivative_measurable (by omega) Y v))
  intro t z
  have hreg : ContDiff ℝ ((2 : ℕ) : ℕ∞) (fun Z : Vec 2 × P => f t Z.1 Z.2) :=
    (Q.regular t).of_le (by exact_mod_cast hH)
  apply independent_parameter_quotient_bound (f t z)
    (hreg.comp₂ contDiff_const contDiff_id)
    (Q.budget 2) (Q.budget_nonneg 2) _ Y v h hh
  intro X
  have hb := Q.parameter_derivative_bound 2 hH t z X
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at hb
  exact hb

theorem IndependentParameterSourceReserve.quotient_error_ul_tendsto_zero {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (hH : 2 ≤ H) (Y v : P) :
    Tendsto (fun h : ℝ => cellUlNorm univ (fun t z =>
      h⁻¹ • (f t z (Y + h • v) - f t z Y) - fderiv ℝ (f t z) Y v))
      (𝓝[≠] 0) (𝓝 0) := by
  have hc : Continuous (fun h : ℝ => ENNReal.ofReal (Q.budget 2 * |h| * ‖v‖ ^ 2)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have ht : Tendsto (fun h : ℝ => ENNReal.ofReal (Q.budget 2 * |h| * ‖v‖ ^ 2))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero, mul_zero, zero_mul, ENNReal.ofReal_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Filter.Eventually.of_forall fun _ => bot_le)
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact Q.quotient_error_ul_bound hH Y v h hh

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! Genuine independent metric word derivatives, with original finite reserve prices. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentMetricWordJet (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ)
    (n : ℕ) (w : Fin n → P) (Y : P) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => realWordJet (fun X => G t X i j) n w Y

theorem IndependentParameterMetricReserve.word_entry_bound {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G) (n : ℕ) (hn : n ≤ H)
    (w : Fin n → P) (hw : ∀ i, ‖w i‖ ≤ 1) (Y : P) (t : ℝ) (i j : Fin 2) :
    |independentMetricWordJet G n w Y t i j| ≤ Q.budget n := by
  have hb := finite_realWordJet_derivative_bound (fun X => G t X i j) n 0
    ((Q.regular t i j).of_le (by simp)) w hw Y
  rw [norm_iteratedFDeriv_zero, Nat.add_zero, Real.norm_eq_abs] at hb
  exact hb.trans (Q.derivative_bound n hn t Y i j)

theorem IndependentParameterMetricReserve.word_entry_measurable {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G) (n : ℕ)
    (w : Fin n → P) (Y : P) (i j : Fin 2) :
    Measurable (fun t => independentMetricWordJet G n w Y t i j) :=
  finite_independentParameterWordJet_measurable (fun t X => G t X i j) n
    (fun t => (Q.regular t i j).of_le (by simp))
    (fun X => Q.measurable X i j) w Y

theorem independentMetricWordJet_cons {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G) (n : ℕ)
    (w : Fin n → P) (v Y : P) (t : ℝ) (i j : Fin 2) :
    independentMetricWordJet G (n + 1) (Fin.cons v w) Y t i j =
      fderiv ℝ (fun X => independentMetricWordJet G n w X t i j) Y v :=
  finite_realWordJet_cons_eq_fderiv (fun X => G t X i j) n
    ((Q.regular t i j).of_le (by simp)) w v Y

theorem IndependentParameterMetricReserve.word_derivative_bound {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G) (n r : ℕ) (hn : n + r ≤ H)
    (w : Fin n → P) (hw : ∀ i, ‖w i‖ ≤ 1) (Y : P) (t : ℝ) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ r (fun X => independentMetricWordJet G n w X t i j) Y‖ ≤
      Q.budget (n + r) :=
  (finite_realWordJet_derivative_bound (fun X => G t X i j) n r
    ((Q.regular t i j).of_le (by simp)) w hw Y).trans
      (Q.derivative_bound (n + r) hn t Y i j)

theorem IndependentParameterMetricReserve.word_quotient_entry_bound {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G) (n : ℕ) (hn : n + 1 ≤ H)
    (w : Fin n → P) (hw : ∀ i, ‖w i‖ ≤ 1)
    (Y v : P) (h : ℝ) (hh : h ≠ 0) (t : ℝ) (i j : Fin 2) :
    |h⁻¹ * (independentMetricWordJet G n w (Y + h • v) t i j -
      independentMetricWordJet G n w Y t i j)| ≤ Q.budget (n + 1) * ‖v‖ := by
  have hr : ContDiff ℝ 1 (fun X => independentMetricWordJet G n w X t i j) :=
    finite_realWordJet_contDiff (fun X => G t X i j) n 1
      ((Q.regular t i j).of_le (by simp)) w
  have hb (X : P) : ‖fderiv ℝ (fun Z => independentMetricWordJet G n w Z t i j) X‖ ≤
      Q.budget (n + 1) := by
    simpa only [norm_iteratedFDeriv_one] using Q.word_derivative_bound n 1 hn w hw X t i j
  simpa only [Real.norm_eq_abs, smul_eq_mul] using
    independent_parameter_first_quotient_bound _ hr _ hb Y v h hh

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! A changed derivative value and changed affine directions retain separate genuine small factors. -/

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem independent_multilinear_field_difference_bound (n : ℕ)
    (A₁ A₀ : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (L₁ L₀ : V →L[ℝ] E) (K δ : ℝ) (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hL₁ : ‖L₁‖ ≤ K) (hL₀ : ‖L₀‖ ≤ K) (hLd : ‖L₁ - L₀‖ ≤ δ) :
    ‖A₁.compContinuousLinearMap (fun _ => L₁) - A₀.compContinuousLinearMap (fun _ => L₀)‖ ≤
      ‖A₁ - A₀‖ * K ^ n + ‖A₁‖ * n * δ * K ^ n := by
  have he : A₁.compContinuousLinearMap (fun _ => L₁) - A₀.compContinuousLinearMap (fun _ => L₀) =
      (A₁ - A₀).compContinuousLinearMap (fun _ => L₀) +
        (A₁.compContinuousLinearMap (fun _ => L₁) - A₁.compContinuousLinearMap (fun _ => L₀)) := by
    ext w
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      sub_apply, add_apply]
    abel
  have hsrc : ‖(A₁ - A₀).compContinuousLinearMap (fun _ : Fin n => L₀)‖ ≤ ‖A₁ - A₀‖ * K ^ n := by
    have hh := (A₁ - A₀).norm_compContinuousLinearMap_le (fun _ : Fin n => L₀)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg L₀) hL₀ n) (norm_nonneg _))
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hsrc
    (independent_multilinear_composition_difference_bound n A₁ L₁ L₀ K δ hK hδ hL₁ hL₀ hLd))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set
open scoped ContDiff ENNReal
namespace AVRegularity.EntryWeakProofs

/-! Genuine primitive and directional source data are finite in the exact inverse norms. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

theorem IndependentParameterSourceReserve.ul_norm_bound {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f) (Y : P) :
    cellUlNorm univ (fun t z => f t z Y) ≤ ENNReal.ofReal (Q.budget 0) := by
  apply cell_source_ulNorm_le_pointwise (fun t z => f t z Y) (Q.measurable Y)
  intro t z
  simpa only [norm_iteratedFDeriv_zero] using Q.derivative_bound 0 (Nat.zero_le H) t (z, Y)

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! A spatial difference uses only spatial Lipschitz control, regardless of the size of family derivatives. -/

section
variable {P V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independent_spatial_difference_value_bound (f : P × V → E) (p : P)
    (hf : ContDiff ℝ 1 (fun X => f (p, X))) (C : ℝ)
    (ρ : ℝ) (hρ : ρ ≠ 0) (X W : V)
    (hb : ∀ Y ∈ segment ℝ X (X + ρ • W), ‖fderiv ℝ (fun Z => f (p, Z)) Y‖ ≤ C) :
    ‖ρ⁻¹ • (f (p, X + ρ • W) - f (p, X))‖ ≤ C * ‖W‖ := by
  have hh := independent_parameter_segment_lipschitz (fun Z => f (p, Z)) hf C X (X + ρ • W) hb
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hh
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg ρ))).trans_eq (by
    rw [mul_left_comm C, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hρ), one_mul])
end

/-! A native spatial interpolation retains its family parameter and stays in the reserved radius. -/

section
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem independent_spatial_segment_parameter (p : P) (X W : V) (Z : P × V)
    (hZ : Z ∈ segment ℝ (p, X) (p, W)) : Z.1 = p := by
  rcases hZ with ⟨a, b, _, _, hab, rfl⟩
  change a • p + b • p = p
  rw [← add_smul, hab, one_smul]

theorem independent_spatial_segment_snd (p : P) (X W : V) (Z : P × V)
    (hZ : Z ∈ segment ℝ (p, X) (p, W)) : Z.2 ∈ segment ℝ X W := by
  rcases hZ with ⟨a, b, ha, hb, hab, rfl⟩
  exact ⟨a, b, ha, hb, hab, rfl⟩

theorem independent_spatial_segment_norm_le (p : P) (X W : V) (Z : P × V) (R : ℝ)
    (hX : ‖X‖ ≤ R) (hW : ‖W‖ ≤ R) (hZ : Z ∈ segment ℝ (p, X) (p, W)) : ‖Z.2‖ ≤ R := by
  have hx : X ∈ Metric.closedBall (0 : V) R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hX
  have hw : W ∈ Metric.closedBall (0 : V) R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hW
  have hh := (convex_closedBall (0 : V) R).segment_subset hx hw
    (independent_spatial_segment_snd p X W Z hZ)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hh
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The zero-slow native sample retains stored parameters through a norm-one linear embedding. -/

def independentStoredParameterEmbedding (d : ℕ) : Vec d →L[ℝ] Vec (2 + d) :=
  ContinuousLinearMap.pi (fun i => if hi : i.val < 2 then 0 else
    ContinuousLinearMap.proj (⟨i.val - 2, by omega⟩ : Fin d))

theorem independentStoredParameterEmbedding_norm_le (d : ℕ) :
    ‖independentStoredParameterEmbedding d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
  intro i
  dsimp only [independentStoredParameterEmbedding, ContinuousLinearMap.pi_apply]
  split
  · simpa only [zero_apply, norm_zero] using norm_nonneg Y
  · exact norm_le_pi_norm Y _

theorem independentStoredParameterEmbedding_eq_packing (d : ℕ) (P : Vec d) :
    independentStoredParameterEmbedding d P = independentIntrinsicParameterPacking d 0 P := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [independentStoredParameterEmbedding, independentIntrinsicParameterPacking,
      ContinuousLinearMap.pi_apply, Fin.val_castAdd, dite_eq_left k.isLt, Fin.addCases_left]
    rfl
  · have hn : ¬(k.natAdd 2).val < 2 := by dsimp only [Fin.val_natAdd]; omega
    simp only [independentStoredParameterEmbedding, independentIntrinsicParameterPacking,
      ContinuousLinearMap.pi_apply, dite_eq_right hn, ContinuousLinearMap.proj_apply, Fin.addCases_right]
    congr 1
    apply Fin.ext
    dsimp only [Fin.val_natAdd]
    omega

def independentStoredZeroFastEmbedding (d : ℕ) : Vec d →L[ℝ] Vec 2 × Vec (2 + d) :=
  (0 : Vec d →L[ℝ] Vec 2).prod (independentStoredParameterEmbedding d)

theorem independentStoredZeroFastEmbedding_norm_le (d : ℕ) :
    ‖independentStoredZeroFastEmbedding d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro P
  change ‖((0 : Vec 2), independentStoredParameterEmbedding d P)‖ ≤ 1 * ‖P‖
  rw [one_mul, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  exact ((independentStoredParameterEmbedding d).le_opNorm P).trans
    ((mul_le_mul_of_nonneg_right (independentStoredParameterEmbedding_norm_le d) (norm_nonneg P)).trans_eq (one_mul _))

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Normalized finite differences keep a uniform full joint jet budget on bounded displacement sets. -/

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independent_scaled_difference_jet_bound (f : P → E) (n : ℕ)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (C : ℝ)
    (hb₀ : ∀ Y, ‖iteratedFDeriv ℝ n f Y‖ ≤ C)
    (hb₁ : ∀ Y, ‖iteratedFDeriv ℝ (n + 1) f Y‖ ≤ C)
    (ρ : ℝ) (hρ : ρ ≠ 0) (hρ₁ : |ρ| ≤ 1) (X V : P) :
    ‖iteratedFDeriv ℝ n (fun Y : P × P => ρ⁻¹ • (f (Y.1 + ρ • Y.2) - f Y.1)) (X, V)‖ ≤
      (2 : ℝ) ^ n * C * (‖V‖ + n) := by
  let L₀ := ContinuousLinearMap.fst ℝ P P
  let S := ContinuousLinearMap.snd ℝ P P
  let L₁ := L₀ + ρ • S
  have hL₀ : ‖L₀‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Y => by
    rw [one_mul]
    exact norm_fst_le Y)
  have hS : ‖S‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Y => by
    rw [one_mul]
    exact norm_snd_le Y)
  have hL₁ : ‖L₁‖ ≤ 2 := by
    have hh := norm_add_le L₀ (ρ • S)
    rw [norm_smul, Real.norm_eq_abs] at hh
    exact hh.trans ((add_le_add hL₀ (mul_le_of_le_one_right (abs_nonneg ρ) hS)).trans (by linarith))
  have hLd : ‖L₁ - L₀‖ ≤ |ρ| := by
    rw [show L₁ - L₀ = ρ • S by dsimp only [L₁]; abel, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg ρ) hS
  have hreg : ContDiff ℝ (n : ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ n)
  have hreg₀ := hreg.comp L₀.contDiff
  have hreg₁ := hreg.comp L₁.contDiff
  let A₀ := iteratedFDeriv ℝ n f X
  let A₁ := iteratedFDeriv ℝ n f (X + ρ • V)
  have hAd : ‖A₁ - A₀‖ ≤ C * (|ρ| * ‖V‖) := by
    have hh := independent_parameter_jet_difference_bound f n hf C hb₁ X (X + ρ • V)
    simpa only [A₀, A₁, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] using hh
  have hA₁ : ‖A₁‖ ≤ C := hb₀ _
  have hB := independent_multilinear_field_difference_bound n A₁ A₀ L₁ L₀ 2 |ρ|
    (by norm_num) (abs_nonneg ρ) hL₁ (hL₀.trans (by norm_num)) hLd
  have hB' : ‖A₁.compContinuousLinearMap (fun _ => L₁) - A₀.compContinuousLinearMap (fun _ => L₀)‖ ≤
      |ρ| * ((2 : ℝ) ^ n * C * (‖V‖ + n)) := by
    have hterm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA₁ (Nat.cast_nonneg n))
        (abs_nonneg ρ)) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    exact hB.trans ((add_le_add
      (mul_le_mul_of_nonneg_right hAd (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
      hterm).trans_eq (by ring))
  have hregdiff : ContDiff ℝ (n : ℕ∞) (f ∘ L₁ - f ∘ L₀) := hreg₁.sub hreg₀
  change ‖iteratedFDeriv ℝ n (ρ⁻¹ • (f ∘ L₁ - f ∘ L₀)) (X, V)‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (f := f ∘ L₁ - f ∘ L₀) (x := (X, V))
      (a := ρ⁻¹) hregdiff.contDiffAt,
    iteratedFDeriv_sub_apply (f := f ∘ L₁) (g := f ∘ L₀) hreg₁.contDiffAt hreg₀.contDiffAt,
    L₁.iteratedFDeriv_comp_right hreg (X, V) (le_refl _),
    L₀.iteratedFDeriv_comp_right hreg (X, V) (le_refl _)]
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  have he₁ : L₁ (X, V) = X + ρ • V := rfl
  have he₀ : L₀ (X, V) = X := rfl
  rw [he₁, he₀]
  exact (mul_le_mul_of_nonneg_left hB' (inv_nonneg.mpr (abs_nonneg ρ))).trans_eq (by
    rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hρ), one_mul])
end

/-! Normalized joint differences use only endpoint and interpolation-segment jet bounds. -/

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independent_scaled_difference_segment_jet_bound (f : P → E) (n : ℕ)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (C : ℝ)
    (ρ : ℝ) (hρ : ρ ≠ 0) (hρ₁ : |ρ| ≤ 1) (X V : P)
    (hb₀ : ‖iteratedFDeriv ℝ n f (X + ρ • V)‖ ≤ C)
    (hb₁ : ∀ Y ∈ segment ℝ X (X + ρ • V),
      ‖iteratedFDeriv ℝ (n + 1) f Y‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun Y : P × P => ρ⁻¹ • (f (Y.1 + ρ • Y.2) - f Y.1)) (X, V)‖ ≤
      (2 : ℝ) ^ n * C * (‖V‖ + n) := by
  let L₀ := ContinuousLinearMap.fst ℝ P P
  let S := ContinuousLinearMap.snd ℝ P P
  let L₁ := L₀ + ρ • S
  have hL₀ : ‖L₀‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Y => by
    rw [one_mul]
    exact norm_fst_le Y)
  have hS : ‖S‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Y => by
    rw [one_mul]
    exact norm_snd_le Y)
  have hL₁ : ‖L₁‖ ≤ 2 := by
    have hh := norm_add_le L₀ (ρ • S)
    rw [norm_smul, Real.norm_eq_abs] at hh
    exact hh.trans ((add_le_add hL₀ (mul_le_of_le_one_right (abs_nonneg ρ) hS)).trans (by linarith))
  have hLd : ‖L₁ - L₀‖ ≤ |ρ| := by
    rw [show L₁ - L₀ = ρ • S by dsimp only [L₁]; abel, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg ρ) hS
  have hreg : ContDiff ℝ (n : ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ n)
  have hreg₀ := hreg.comp L₀.contDiff
  have hreg₁ := hreg.comp L₁.contDiff
  let A₀ := iteratedFDeriv ℝ n f X
  let A₁ := iteratedFDeriv ℝ n f (X + ρ • V)
  have hAd : ‖A₁ - A₀‖ ≤ C * (|ρ| * ‖V‖) := by
    have hh := independent_parameter_segment_jet_difference_bound f n hf C X (X + ρ • V) hb₁
    simpa only [A₀, A₁, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] using hh
  have hA₁ : ‖A₁‖ ≤ C := hb₀
  have hB := independent_multilinear_field_difference_bound n A₁ A₀ L₁ L₀ 2 |ρ|
    (by norm_num) (abs_nonneg ρ) hL₁ (hL₀.trans (by norm_num)) hLd
  have hB' : ‖A₁.compContinuousLinearMap (fun _ => L₁) - A₀.compContinuousLinearMap (fun _ => L₀)‖ ≤
      |ρ| * ((2 : ℝ) ^ n * C * (‖V‖ + n)) := by
    have hterm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA₁ (Nat.cast_nonneg n))
        (abs_nonneg ρ)) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    exact hB.trans ((add_le_add
      (mul_le_mul_of_nonneg_right hAd (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
      hterm).trans_eq (by ring))
  have hregdiff : ContDiff ℝ (n : ℕ∞) (f ∘ L₁ - f ∘ L₀) := hreg₁.sub hreg₀
  change ‖iteratedFDeriv ℝ n (ρ⁻¹ • (f ∘ L₁ - f ∘ L₀)) (X, V)‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (f := f ∘ L₁ - f ∘ L₀) (x := (X, V))
      (a := ρ⁻¹) hregdiff.contDiffAt,
    iteratedFDeriv_sub_apply (f := f ∘ L₁) (g := f ∘ L₀) hreg₁.contDiffAt hreg₀.contDiffAt,
    L₁.iteratedFDeriv_comp_right hreg (X, V) (le_refl _),
    L₀.iteratedFDeriv_comp_right hreg (X, V) (le_refl _)]
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  have he₁ : L₁ (X, V) = X + ρ • V := rfl
  have he₀ : L₀ (X, V) = X := rfl
  rw [he₁, he₀]
  exact (mul_le_mul_of_nonneg_left hB' (inv_nonneg.mpr (abs_nonneg ρ))).trans_eq (by
    rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hρ), one_mul])
end

/-! Normalized chart differences need derivative bounds, not a global bound on the chart itself. -/

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independent_scaled_difference_segment_derivative_jet_bound (f : P → E) (n : ℕ)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (C : ℝ)
    (ρ : ℝ) (hρ : ρ ≠ 0) (hρ₁ : |ρ| ≤ 1) (X V : P)
    (hb₀ : n ≠ 0 → ‖iteratedFDeriv ℝ n f (X + ρ • V)‖ ≤ C)
    (hb₁ : ∀ Y ∈ segment ℝ X (X + ρ • V),
      ‖iteratedFDeriv ℝ (n + 1) f Y‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun Y : P × P => ρ⁻¹ • (f (Y.1 + ρ • Y.2) - f Y.1)) (X, V)‖ ≤
      (2 : ℝ) ^ n * C * (‖V‖ + n) := by
  by_cases hn : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, add_zero]
    have hh := independent_parameter_segment_lipschitz f hf C X (X + ρ • V) (fun Y hY => by
      have hb := hb₁ Y hY
      change ‖iteratedFDeriv ℝ 1 f Y‖ ≤ C at hb
      rw [norm_iteratedFDeriv_one] at hb
      exact hb)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hh
    rw [norm_smul, Real.norm_eq_abs, abs_inv]
    exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg ρ))).trans_eq (by
      rw [mul_left_comm C, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hρ), one_mul])
  · exact independent_scaled_difference_segment_jet_bound f n hf C ρ hρ hρ₁ X V (hb₀ hn) hb₁
end

end AVRegularity.EntryWeakProofs
end
