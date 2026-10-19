-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreCoefficientLinearSeries

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Literal Taylor coefficients of the quadratic metric and drift-mean fibre symbol. -/

/-- The actual degree-two coefficient of the metric contribution to the fibre symbol. -/
def fibreCoefficientMetricSymbol (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (p : ℕ × ℕ) (t : ℝ) : ℂ :=
  -(η : ℂ) * ∑ i : Fin 2, ∑ j : Fin 2,
    if p = cellJetDirection i + cellJetDirection j then (G t i j : ℂ) else 0

/-- The actual coordinate-shifted multiplier mean contribution to the fibre symbol. -/
def fibreCoefficientDriftSymbol (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ fibreCoefficientDirections p, -Complex.I *
    cellMean (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency j) t x *
      cellValue (r (fibreCoefficientPrevious p j)) t x)

/-- The literal Taylor family of the graph symbol, formed from the actual graph coefficients. -/
def fibreCoefficientSymbol (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (p : ℕ × ℕ) (t : ℝ) : ℂ :=
  fibreCoefficientMetricSymbol η G p t + fibreCoefficientDriftSymbol η v r p t

end AVRegularity.CycleEvolution
end

section
open Homogenization MeasureTheory
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Literal monomial weights commute with the convergent cell-pairing Cauchy product. -/

theorem fibreMean_monomial_pair (ξ : Fin 2 → ℂ) {p a : ℕ × ℕ}
    (ha : a ∈ fibreCoefficientPairs p) (f g : Vec 2 → ℂ) :
    cellMean (fun x => (fibreMonomial ξ a * f x) *
      (fibreMonomial ξ (fibreCoefficientComplement p a) * g x)) =
      fibreMonomial ξ p * cellMean (fun x => f x * g x) := by
  have he : (fun x => (fibreMonomial ξ a * f x) *
      (fibreMonomial ξ (fibreCoefficientComplement p a) * g x)) =
      (fun x => (fibreMonomial ξ a * fibreMonomial ξ (fibreCoefficientComplement p a)) *
        (f x * g x)) := by
    funext x
    ring
  unfold cellMean
  rw [he, integral_const_mul, fibreMonomial_convolution ξ ha]

theorem fibreMean_monomial_cauchy_product (ξ : Fin 2 → ℂ)
    (f g : ℕ × ℕ → Vec 2 → ℂ)
    (hf : (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * f p x)) < ⊤)
    (hg : (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * g p x)) < ⊤) :
    (∑' p, fibreMonomial ξ p * ∑ a ∈ fibreCoefficientPairs p,
      cellMean (fun x => f a x * g (fibreCoefficientComplement p a) x)) =
      cellMean (fun x => (∑' p, fibreMonomial ξ p * f p x) *
        ∑' p, fibreMonomial ξ p * g p x) := by
  have h := fibreMean_cauchy_product (fun p x => fibreMonomial ξ p * f p x)
    (fun p x => fibreMonomial ξ p * g p x) hf hg
  apply Eq.trans _ h
  apply tsum_congr
  intro p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact (fibreMean_monomial_pair ξ ha _ _).symm

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Convergent coordinate-shifted quadratic Taylor coefficients. -/

/-- The literal shifted quadratic convolution equals the product of its convergent input series. -/
theorem fibreTaylor_quadratic_series (ξ : Fin 2 → ℂ) (f : ℕ × ℕ → ℂ)
    (g : Fin 2 → ℕ × ℕ → ℂ)
    (hf : Summable (fun p => ‖fibreMonomial ξ p * f p‖))
    (hg : ∀ j, Summable (fun p => ‖fibreMonomial ξ p * g j p‖)) :
    (∑' p, fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
        f a * g j (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)) =
      (∑' p, fibreMonomial ξ p * f p) *
        ∑ j : Fin 2, ξ j * ∑' p, fibreMonomial ξ p * g j p := by
  let H := fun (j : Fin 2) (p : ℕ × ℕ) =>
    ∑ a ∈ fibreCoefficientPairs p, f a * g j (fibreCoefficientComplement p a)
  let A := fun (j : Fin 2) (p : ℕ × ℕ) => if j ∈ fibreCoefficientDirections p then
    fibreMonomial ξ p * H j (fibreCoefficientPrevious p j) else 0
  have hA j : Summable (A j) := fibreMonomial_shift_summable ξ j (H j)
    (fibreMonomial_convolution_summable ξ f (g j) hf (hg j))
  have htotal : (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
        f a * g j (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)) =
      (fun p => ∑ j : Fin 2, A j p) := by
    funext p
    calc
      _ = ∑ j ∈ fibreCoefficientDirections p, A j p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact (ite_eq_left hj).symm
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ite_eq_right hj)
  have hsum j : (∑' p, A j p) = ξ j *
      ((∑' p, fibreMonomial ξ p * f p) * ∑' p, fibreMonomial ξ p * g j p) := by
    have hs : (∑' p, A j p) = ξ j * ∑' p, fibreMonomial ξ p * H j p :=
      fibreMonomial_shift_tsum ξ j (H j)
    rw [hs]
    congr 1
    exact (fibreMonomial_cauchy_product ξ f (g j) hf (hg j)).symm
  rw [htotal, Summable.tsum_finsetSum (fun j _ => hA j)]
  simp_rw [hsum]
  simp only [Fin.sum_univ_two]
  ring

/-! Convergent coordinate-shifted quadratic Taylor coefficients. -/

/-- The literal shifted quadratic convolution equals the product of its convergent input series. -/
theorem fibreTaylor_quadratic_summable (ξ : Fin 2 → ℂ) (f : ℕ × ℕ → ℂ)
    (g : Fin 2 → ℕ × ℕ → ℂ)
    (hf : Summable (fun p => ‖fibreMonomial ξ p * f p‖))
    (hg : ∀ j, Summable (fun p => ‖fibreMonomial ξ p * g j p‖)) :
    Summable (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
        f a * g j (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)) := by
  let H := fun (j : Fin 2) (p : ℕ × ℕ) =>
    ∑ a ∈ fibreCoefficientPairs p, f a * g j (fibreCoefficientComplement p a)
  let A := fun (j : Fin 2) (p : ℕ × ℕ) => if j ∈ fibreCoefficientDirections p then
    fibreMonomial ξ p * H j (fibreCoefficientPrevious p j) else 0
  have hA j : Summable (A j) := fibreMonomial_shift_summable ξ j (H j)
    (fibreMonomial_convolution_summable ξ f (g j) hf (hg j))
  have htotal : (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
        f a * g j (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)) =
      (fun p => ∑ j : Fin 2, A j p) := by
    funext p
    calc
      _ = ∑ j ∈ fibreCoefficientDirections p, A j p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact (ite_eq_left hj).symm
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ite_eq_right hj)
  rw [htotal]
  simpa only [Fin.sum_univ_two] using (hA 0).add (hA 1)

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! The actual metric symbol coefficients are real and supported at even degree two. -/

theorem fibreCoefficientMetricSymbol_star (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ × ℕ) (t : ℝ) :
    star (fibreCoefficientMetricSymbol η G p t) = fibreCoefficientMetricSymbol η G p t := by
  simp only [fibreCoefficientMetricSymbol, Complex.star_def, map_mul, map_neg, map_sum,
    apply_ite, Complex.conj_ofReal, map_zero]

theorem fibreCoefficientMetricSymbol_reality (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ × ℕ) (t : ℝ) :
    star (fibreCoefficientMetricSymbol η G p t) =
      fibreRealitySign p * fibreCoefficientMetricSymbol η G p t := by
  by_cases hp : p.1 + p.2 = 2
  · have hs : fibreRealitySign p = 1 := by rw [fibreRealitySign, hp]; norm_num
    rw [hs, one_mul]
    exact fibreCoefficientMetricSymbol_star η G p t
  · have hne (i j : Fin 2) : p ≠ cellJetDirection i + cellJetDirection j := by
      have hi : (cellJetDirection i).1 + (cellJetDirection i).2 = 1 := by
        simpa using cellJetDirection_order (0 : ℕ × ℕ) i
      have hij := cellJetDirection_order (cellJetDirection i) j
      intro he
      rw [← he] at hij
      exact hp (by omega)
    have hz : fibreCoefficientMetricSymbol η G p t = 0 := by
      simp only [fibreCoefficientMetricSymbol, hne, ite_false, Finset.sum_const_zero, mul_zero]
    rw [hz, star_zero, mul_zero]

end AVRegularity.CycleEvolution
end

section
open Homogenization
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Uniform time and total weighted bounds for the literal quadratic metric symbol. -/

/-- The metric symbol coefficient has a uniform bound supported on its four actual quadratic directions. -/
theorem fibreCoefficientMetricSymbol_uniform_le (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t)) (p : ℕ × ℕ) :
    (⨆ t, ‖fibreCoefficientMetricSymbol η G p t‖ₑ) ≤
      ENNReal.ofReal |η| * ∑ i : Fin 2, ∑ j : Fin 2,
        if p = cellJetDirection i + cellJetDirection j then (2 : ℝ≥0∞) else 0 := by
  apply iSup_le
  intro t
  have he : ‖-(η : ℂ)‖ₑ = ENNReal.ofReal |η| := by
    rw [← ofReal_norm]
    simp
  rw [fibreCoefficientMetricSymbol, enorm_mul, he]
  apply mul_le_mul' le_rfl
  apply (enorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (enorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases hp : p = cellJetDirection i + cellJetDirection j
  · rw [ite_eq_left hp, ite_eq_left hp, ← ofReal_norm]
    have hb := cellMetric_entry_bound hG t 0 i j
    exact (ENNReal.ofReal_le_ofReal (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb)).trans_eq
      (by norm_num)
  · simp [hp]

/-- The actual quadratic metric symbol has a finite weighted coefficient total at every finite radius. -/
theorem fibreCoefficientMetricSymbol_weighted_le (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t)) (ρ : ℝ≥0∞) :
    (∑' p, fibreCoefficientWeight ρ p * ⨆ t, ‖fibreCoefficientMetricSymbol η G p t‖ₑ) ≤
      8 * ENNReal.ofReal |η| * ρ ^ 2 := by
  let H := fun (i j : Fin 2) (p : ℕ × ℕ) =>
    fibreCoefficientWeight ρ p * (if p = cellJetDirection i + cellJetDirection j then (2 : ℝ≥0∞) else 0)
  have hdeg (i j : Fin 2) :
      (cellJetDirection i + cellJetDirection j).1 + (cellJetDirection i + cellJetDirection j).2 = 2 := by
    have hi : (cellJetDirection i).1 + (cellJetDirection i).2 = 1 := by
      simpa using cellJetDirection_order (0 : ℕ × ℕ) i
    rw [cellJetDirection_order, hi]
  have hsum (i j : Fin 2) : (∑' p, H i j p) = 2 * ρ ^ 2 := by
    have he p : H i j p = if p = cellJetDirection i + cellJetDirection j then
        2 * fibreCoefficientWeight ρ (cellJetDirection i + cellJetDirection j) else 0 := by
      by_cases hp : p = cellJetDirection i + cellJetDirection j
      · subst p
        simp [H, mul_comm]
      · simp only [H, ite_eq_right hp, mul_zero]
    rw [tsum_congr he, tsum_ite_eq]
    rw [fibreCoefficientWeight, hdeg]
  calc
    _ ≤ ∑' p, fibreCoefficientWeight ρ p * (ENNReal.ofReal |η| *
        ∑ i : Fin 2, ∑ j : Fin 2,
          if p = cellJetDirection i + cellJetDirection j then (2 : ℝ≥0∞) else 0) :=
      ENNReal.tsum_le_tsum (fun p => mul_le_mul' le_rfl (fibreCoefficientMetricSymbol_uniform_le η G hG p))
    _ = ENNReal.ofReal |η| * ∑ i : Fin 2, ∑ j : Fin 2, ∑' p, H i j p := by
      have he : (fun p => fibreCoefficientWeight ρ p * (ENNReal.ofReal |η| *
          ∑ i : Fin 2, ∑ j : Fin 2,
            if p = cellJetDirection i + cellJetDirection j then (2 : ℝ≥0∞) else 0)) =
          (fun p => ENNReal.ofReal |η| * ∑ i : Fin 2, ∑ j : Fin 2, H i j p) := by
        funext p
        simp only [H, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he, ENNReal.tsum_mul_left]
      congr 1
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      apply Finset.sum_congr rfl
      intro i _
      exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ = _ := by
      simp_rw [hsum]
      simp only [Fin.sum_univ_two]
      ring

end AVRegularity.CycleEvolution
end

section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Exact convergent series for the literal quadratic metric symbol. -/

/-- The actual metric symbol coefficients sum to the literal quadratic symbol at every frequency. -/
theorem fibreCoefficientMetricSymbol_hasSum (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ) (t : ℝ) :
    HasSum (fun p => fibreMonomial ξ p * fibreCoefficientMetricSymbol η G p t)
      (-(η : ℂ) * fibreQuad (G t) ξ) := by
  let H := fun (i j : Fin 2) (p : ℕ × ℕ) =>
    fibreMonomial ξ p * (if p = cellJetDirection i + cellJetDirection j then (G t i j : ℂ) else 0)
  have hh (i j : Fin 2) : HasSum (H i j)
      (fibreMonomial ξ (cellJetDirection i + cellJetDirection j) * (G t i j : ℂ)) :=
    fibreMonomial_delta_hasSum ξ _ _
  have hs : HasSum (fun p => ∑ i : Fin 2, ∑ j : Fin 2, H i j p)
      (∑ i : Fin 2, ∑ j : Fin 2,
        fibreMonomial ξ (cellJetDirection i + cellJetDirection j) * (G t i j : ℂ)) := by
    simpa only [Fin.sum_univ_two] using ((hh 0 0).add (hh 0 1)).add ((hh 1 0).add (hh 1 1))
  have hm := hs.mul_left (-(η : ℂ))
  convert hm using 1
  · funext p
    simp only [fibreCoefficientMetricSymbol, H, Fin.sum_univ_two]
    ring
  · simp only [fibreQuad, Fin.sum_univ_two, fibreMonomial_add, fibreMonomial_direction]
    ring

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Literal quadratic coefficient forcing under absolute pointwise convergence. -/

/-- The quadratic forcing series is the literal product with its coordinate mean series. -/
theorem fibreCoefficientQuadraticSource_series (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2)
    (hf : Summable (fun p => ‖fibreMonomial ξ p * cellValue (r p) t x‖))
    (hg : ∀ j, Summable (fun p => ‖fibreMonomial ξ p *
      cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y *
        cellValue (r p) t y)‖)) :
    (∑' p, fibreMonomial ξ p * fibreCoefficientQuadraticSource η v r p t x) =
      Complex.I * (∑' p, fibreMonomial ξ p * cellValue (r p) t x) *
        ∑ j : Fin 2, ξ j * ∑' p, fibreMonomial ξ p *
          cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y *
            cellValue (r p) t y) := by
  let g := fun (j : Fin 2) (p : ℕ × ℕ) =>
    cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * cellValue (r p) t y)
  have hh := fibreTaylor_quadratic_series ξ (fun p => cellValue (r p) t x) g hf hg
  have he : (fun p => fibreMonomial ξ p * fibreCoefficientQuadraticSource η v r p t x) =
      (fun p => Complex.I * (fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
          cellValue (r a) t x * g j (fibreCoefficientComplement (fibreCoefficientPrevious p j) a))) := by
    funext p
    simp only [fibreCoefficientQuadraticSource, fibreCoefficientQuadraticTerm, mul_assoc,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [g]
    ring
  rw [he, tsum_mul_left, hh]
  ring

/-! Convergence of the actual quadratic scalar coefficient expression. -/

/-- Absolute value and multiplier-mean convergence justify the literal quadratic forcing series. -/
theorem fibreCoefficientQuadraticSource_summable (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2)
    (hf : Summable (fun p => ‖fibreMonomial ξ p * cellValue (r p) t x‖))
    (hg : ∀ j, Summable (fun p => ‖fibreMonomial ξ p *
      cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y *
        cellValue (r p) t y)‖)) :
    Summable (fun p => fibreMonomial ξ p * fibreCoefficientQuadraticSource η v r p t x) := by
  let g := fun (j : Fin 2) (p : ℕ × ℕ) =>
    cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * cellValue (r p) t y)
  have hh := fibreTaylor_quadratic_summable ξ (fun p => cellValue (r p) t x) g hf hg
  have he : (fun p => fibreMonomial ξ p * fibreCoefficientQuadraticSource η v r p t x) =
      (fun p => Complex.I * (fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
          cellValue (r a) t x * g j (fibreCoefficientComplement (fibreCoefficientPrevious p j) a))) := by
    funext p
    simp only [fibreCoefficientQuadraticSource, fibreCoefficientQuadraticTerm, mul_assoc,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [g]
    ring
  rw [he]
  exact hh.mul_left Complex.I

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual forcing of a monomial-scaled inverse coefficient. -/

/-- Projected scalar forcing of a monomial-scaled coefficient. -/
def fibreCoefficientScaledSource (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (ξ : Fin 2 → ℂ) (p : ℕ × ℕ) : ℝ → Vec 2 → ℂ :=
  fibreMonomial ξ p • (fun t => cellQ0 (fibreCoefficientSource η v r p t))

/-- Vector forcing of a monomial-scaled coefficient. -/
def fibreCoefficientScaledFlux (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (ξ : Fin 2 → ℂ) (p : ℕ × ℕ) :
    ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  fibreMonomial ξ p • fibreCoefficientFlux η G r p

end AVRegularity.CycleEvolution
end

section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! A constant-one Taylor coefficient gives a first-order L2 bound for the distance to one. -/

theorem fibreL2Series_sub_one_le (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (R : ℝ) (hR : 0 < R)
    (M : ℝ≥0∞) (hM : M < ⊤) (ha0 : ∀ t x, a 0 t x = 1)
    (hmajor : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p *
      ⨆ s, cellL2Norm (a p s)) ≤ M)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ R) (t : ℝ) :
    cellL2Norm (fun x => fibreSeriesFun a ξ t x - 1) ≤ ENNReal.ofReal (fibreNorm ξ / R) * M := by
  classical
  let b := fun p t x => if p = (0 : ℕ × ℕ) then (0 : ℂ) else a p t x
  let E := fun p => ⨆ s, cellL2Norm (b p s)
  have hb p : E p ≤ ⨆ s, cellL2Norm (a p s) := by
    by_cases hp : p = 0
    · simp [E, b, hp, cellL2Norm]
    · simp only [E, b, ite_eq_right hp]
      exact le_rfl
  have hB : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * E p) ≤ M :=
    (ENNReal.tsum_le_tsum (fun p => mul_le_mul' le_rfl (hb p))).trans hmajor
  have hz : E 0 = 0 := by simp [E, b, cellL2Norm]
  have hsB : (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * b p t x)) ≤
      ENNReal.ofReal (fibreNorm ξ / R) * M := by
    calc
      _ ≤ ∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * E p := by
        apply ENNReal.tsum_le_tsum
        intro p
        rw [cellL2Norm_const_complex_mul, ← ofReal_norm]
        exact mul_le_mul' le_rfl (le_iSup (fun s => cellL2Norm (b p s)) t)
      _ ≤ ENNReal.ofReal (fibreNorm ξ / R) *
          ∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * E p :=
        fibreMonomial_linear_energy_le R hR ξ hξ E hz
      _ ≤ _ := mul_le_mul' le_rfl hB
  have hsumB := cellL2Series_memLp_bound (fun p x => fibreMonomial ξ p * b p t x)
    (hsB.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM))
  have hsA := (fibreL2Series_norm_sum_le a R ξ hξ t).trans_lt (hmajor.trans_lt hM)
  have hsumA := cellL2Series_memLp_bound (fun p x => fibreMonomial ξ p * a p t x) hsA
  have hδ : HasSum (fun p => fibreMonomial ξ p * (if p = 0 then (1 : ℂ) else 0)) 1 := by
    simpa only [fibreMonomial, Prod.fst_zero, Prod.snd_zero, pow_zero, mul_one] using
      fibreMonomial_delta_hasSum ξ 0 1
  have he : (fun x => ∑' p, fibreMonomial ξ p * b p t x) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreSeriesFun a ξ t x - 1) := by
    filter_upwards [hsumA.2.2] with x hx
    have hterm p : fibreMonomial ξ p * b p t x =
        fibreMonomial ξ p * a p t x - fibreMonomial ξ p * (if p = 0 then 1 else 0) := by
      by_cases hp : p = 0
      · subst p
        simp [b, ha0 t x]
      · simp [b, hp]
    rw [tsum_congr hterm, hx.of_norm.tsum_sub hδ.summable, hδ.tsum_eq]
    rfl
  change eLpNorm (fun x => fibreSeriesFun a ξ t x - 1) 2 (volume.restrict AVenhance.unitCube) ≤ _
  rw [← eLpNorm_congr_ae he]
  exact hsumB.2.1.trans hsB

end AVRegularity.CycleEvolution
end

section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! The literal phase has zero first frequency derivative at the origin. -/

theorem fibreUniformMajorant_phase_fderiv_zero (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0)
    (hR : 0 < R) (M : ENNReal) (hM : M < ⊤)
    (ha : ∀ p, AEStronglyMeasurable (a p) volume)
    (hb : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ) ≤ M)
    (hz : ∀ p, p.1 + p.2 = 1 → ∀ τ, a p τ = 0)
    (s t : ℝ) (hst : s ≤ t) :
    fderiv ℂ (fun ξ : Fin 2 → ℂ => ∫ τ in s..t, fibreSeriesC a ξ τ) 0 = 0 := by
  have hp := fibreUniformMajorant_phase_hasFPowerSeriesOnBall a R hR M hM ha hb s t hst
  rw [hp.hasFPowerSeriesAt.fderiv_eq]
  have hc : fibreFormalSeries (fun p => ∫ τ in s..t, a p τ) 1 = 0 := by
    apply fibreFormalSeries_coeff_eq_zero
    intro p hp'
    simp only [hz p hp', intervalIntegral.integral_zero]
  rw [hc]
  exact map_zero _

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Literal coordinate formulas for the scaled coefficient flux. -/

/-- Every component of the actual coefficient flux is the coordinate predecessor expression. -/
theorem fibreCoefficientScaledFlux_coordinate (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (ξ : Fin 2 → ℂ) (p : ℕ × ℕ) (t : ℝ) (x : Vec 2) (k : Fin 2) :
    fibreCoefficientScaledFlux η G r ξ p t x k =
      (2 * Complex.I * (Real.sqrt η : ℂ)) *
        (fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
          (G t k j : ℂ) * cellValue (r (fibreCoefficientPrevious p j)) t x) := by
  let P := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) k
  change P (fibreMonomial ξ p • ∑ j ∈ fibreCoefficientDirections p,
    fibreGraphFlux η G (fibreCoordinateFrequency j)
      (cellValue (r (fibreCoefficientPrevious p j))) t x) = _
  rw [map_smul, map_sum]
  have he j : P (fibreGraphFlux η G (fibreCoordinateFrequency j)
      (cellValue (r (fibreCoefficientPrevious p j))) t x) =
      (2 * Complex.I * (Real.sqrt η : ℂ)) * (G t k j : ℂ) *
        cellValue (r (fibreCoefficientPrevious p j)) t x := by
    simp [P, fibreGraphFlux, fibreCoordinateFrequency, Pi.single_apply]
  simp_rw [he]
  simp only [smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! The literal convergent coefficient flux equals the graph flux. -/

/-- Actual convergence identifies the coefficient flux sum with the arbitrary-frequency graph flux. -/
theorem fibreCoefficientFlux_series_of_summable (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2)
    (hF : Summable (fun p => fibreCoefficientScaledFlux η G r ξ p t x))
    (hr : Summable (fun p => fibreMonomial ξ p * cellValue (r p) t x)) :
    (∑' p, fibreCoefficientScaledFlux η G r ξ p t x) =
      fibreGraphFlux η G ξ (fun s y => ∑' p, fibreMonomial ξ p * cellValue (r p) s y) t x := by
  apply WithLp.ofLp_injective
  funext k
  have hp := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) k).map_tsum hF
  change (∑' p, fibreCoefficientScaledFlux η G r ξ p t x) k = _
  have hp' : (∑' p, fibreCoefficientScaledFlux η G r ξ p t x) k =
      ∑' p, fibreCoefficientScaledFlux η G r ξ p t x k := hp
  rw [hp']
  simp_rw [fibreCoefficientScaledFlux_coordinate]
  rw [tsum_mul_left, fibreTaylor_linear_series ξ (fun j => (G t k j : ℂ))
    (fun p => cellValue (r p) t x) hr]
  simp only [fibreGraphFlux, PiLp.toLp_apply]
  ring

/-! Identification of the complete literal unprojected scalar coefficient series. -/

/-- Convergence of the actual scalar, value and mean series identifies the nonlinear unprojected forcing. -/
theorem fibreCoefficientSource_series_of_summable (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2)
    (hs : Summable (fun p => fibreMonomial ξ p * fibreCoefficientSource η v r p t x))
    (hf : Summable (fun p => ‖fibreMonomial ξ p * cellValue (r p) t x‖))
    (hg : ∀ j, Summable (fun p => ‖fibreMonomial ξ p *
      cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y *
        cellValue (r p) t y)‖)) :
    (∑' p, fibreMonomial ξ p * fibreCoefficientSource η v r p t x) =
      -Complex.I * fibreDriftCoupling η v ξ t x *
        (1 + ∑' p, fibreMonomial ξ p * cellValue (r p) t x) +
      Complex.I * (∑' p, fibreMonomial ξ p * cellValue (r p) t x) *
        ∑ j : Fin 2, ξ j * ∑' p, fibreMonomial ξ p *
          cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y *
            cellValue (r p) t y) := by
  let L := fun p => fibreMonomial ξ p * fibreCoefficientLinearSource η v r p t x
  let Q := fun p => fibreMonomial ξ p * fibreCoefficientQuadraticSource η v r p t x
  have hq : Summable Q := fibreCoefficientQuadraticSource_summable η v r ξ t x hf hg
  have he : (fun p => fibreMonomial ξ p * fibreCoefficientSource η v r p t x) = L + Q := by
    funext p
    change fibreMonomial ξ p * (fibreCoefficientLinearSource η v r p t x +
      fibreCoefficientQuadraticSource η v r p t x) = _
    exact mul_add _ _ _
  rw [he] at hs
  have hl : Summable L := by
    have hh := hs.sub hq
    have hfun : (L + Q) - Q = L := by
      funext p
      exact add_sub_cancel_right (L p) (Q p)
    change Summable ((L + Q) - Q) at hh
    rw [hfun] at hh
    exact hh
  rw [he]
  change (∑' p, (L p + Q p)) = _
  rw [hl.tsum_add hq]
  exact congrArg₂ (· + ·)
    (fibreCoefficientLinearSource_series η v r ξ t x hf.of_norm)
    (fibreCoefficientQuadraticSource_series η v r ξ t x hf hg)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Cell specialization of the strong-time variational helpers. The Sobolev slice
represents the cell L² trace almost everywhere in time. Endpoint data remain L² traces.
This helper predicate is a strong-time subclass. -/

/-- Strong H¹-in-time cell solution of a realified complex variational equation.
The spatial H¹ membership and its agreement with the trace are almost-everywhere data. -/
structure CellStrongVariationalSolution (a b : ℝ)
    (B : ℝ → TorusHk 1 ℂ →ₗ[ℝ] TorusHk 1 ℂ →ₗ[ℝ] ℝ)
    (q : ℝ → TorusHk 1 ℂ →ₗ[ℝ] ℝ) (u du : ℝ → CellHilbert)
    (slice : ℝ → TorusHk 1 ℂ) : Prop where
  variational : StrongVariationalSolution a b
    (torusHkValueCLM (E := ℂ) (K := 1)).toLinearMap B q u du slice
  derivative_L2 : MemLp du 2 (volume.restrict (uIcc a b))
  spatial_L2 : MemLp slice 2 (volume.restrict (uIcc a b))

/-- Test with the spatial slice only at good times to obtain the cell energy increment. -/
theorem CellStrongVariationalSolution.energy_increment {a b : ℝ}
    {B : ℝ → TorusHk 1 ℂ →ₗ[ℝ] TorusHk 1 ℂ →ₗ[ℝ] ℝ}
    {q : ℝ → TorusHk 1 ℂ →ₗ[ℝ] ℝ} {u du : ℝ → CellHilbert}
    {slice : ℝ → TorusHk 1 ℂ}
    (h : CellStrongVariationalSolution a b B q u du slice) :
    ‖u b‖ ^ 2 - ‖u a‖ ^ 2 =
      ∫ t in a..b, 2 * (B t (slice t) (slice t) + q t (slice t)) :=
  h.variational.energy_increment

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Metric
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! Quantitative complex derivatives of the literal phase from its actual coefficient majorant. -/

theorem fibreUniformMajorant_phase_iteratedFDeriv_le
    (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0) (hR : 0 < R) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ p, AEStronglyMeasurable (a p) volume)
    (hb : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ) ≤ ENNReal.ofReal M)
    (s t : ℝ) (hst : s ≤ t) (n : ℕ) (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ (R : ℝ) / 2) :
    ‖iteratedFDeriv ℂ n (fun ξ' : Fin 2 → ℂ => ∫ τ in s..t, fibreSeriesC a ξ' τ) ξ‖ ≤
      analyticBallDerivativeConstant n * (M * (t - s)) / ((R : ℝ) / 2) ^ n := by
  have hRreal : 0 < (R : ℝ) := hR
  have hi : ball ξ ((R : ℝ) / 2) ⊆ ball 0 (R : ℝ) := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    rw [mem_ball] at hz
    have ht := dist_triangle z ξ 0
    rw [dist_zero_right, dist_zero_right] at ht
    linarith
  apply analytic_ball_iterated_derivative_le n (half_pos hRreal)
    ((fibreUniformMajorant_phase_analyticOnNhd a R hR (ENNReal.ofReal M)
      ENNReal.ofReal_lt_top ha hb s t hst).mono hi)
  intro z hz
  have hz' := hi hz
  rw [mem_ball, dist_zero_right] at hz'
  exact fibreUniformMajorant_phase_norm_le a R M hM hb z hz'.le s t hst

theorem fibreUniformMajorant_phase_first_derivative_le
    (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0) (hR : 0 < R) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ p, AEStronglyMeasurable (a p) volume)
    (hb : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ) ≤ ENNReal.ofReal M)
    (hz : ∀ p, p.1 + p.2 = 1 → ∀ τ, a p τ = 0)
    (s t : ℝ) (hst : s ≤ t) (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ < (R : ℝ) / 2) :
    ‖fderiv ℂ (fun ξ' : Fin 2 → ℂ => ∫ τ in s..t, fibreSeriesC a ξ' τ) ξ‖ ≤
      (8 * (M * (t - s)) / (R : ℝ) ^ 2) * ‖ξ‖ := by
  apply analytic_ball_first_derivative_gain (show 0 < (R : ℝ) from hR)
    (fibreUniformMajorant_phase_analyticOnNhd a R hR (ENNReal.ofReal M)
      ENNReal.ofReal_lt_top ha hb s t hst)
  · intro z hz'
    rw [mem_ball, dist_zero_right] at hz'
    exact fibreUniformMajorant_phase_norm_le a R M hM hb z hz'.le s t hst
  · exact fibreUniformMajorant_phase_fderiv_zero a R hR (ENNReal.ofReal M)
      ENNReal.ofReal_lt_top ha hb hz s t hst
  · simpa only [mem_ball, dist_zero_right] using hξ

end AVRegularity.CycleEvolution
end
