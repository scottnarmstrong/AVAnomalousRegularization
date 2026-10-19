-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreCoefficientFamilyMajorant
import AVRegularity.CycleEvolution.FibreCoefficientSymbolHomogeneous

@[expose] public noncomputable section

section
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Exact convergent monomial series of one literal Taylor coefficient. -/

/-- A single monomial coefficient gives an actual convergent series with its literal value. -/
theorem fibreMonomial_delta_hasSum (ξ : Fin 2 → ℂ) (q : ℕ × ℕ) (c : ℂ) :
    HasSum (fun p => fibreMonomial ξ p * (if p = q then c else 0)) (fibreMonomial ξ q * c) := by
  have he : (fun p => fibreMonomial ξ p * (if p = q then c else 0)) =
      (fun p => if p = q then fibreMonomial ξ q * c else 0) := by
    funext p
    by_cases hp : p = q
    · subst p
      simp
    · simp only [ite_eq_right hp, mul_zero]
  rw [he]
  exact hasSum_ite_eq q _

end AVRegularity.CycleDamping.Graph
end

section
open scoped BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! All-frequency scalar homogeneous bounds from geometric coefficient estimates. -/

/-- Geometric scalar coefficient bounds give the literal homogeneous Taylor estimate at every frequency. -/
theorem fibreHomogeneous_scalar_le_of_geometric (a : ℕ × ℕ → ℝ → ℂ)
    (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (ha : ∀ p t, ‖a p t‖ ≤ K * A ^ (p.1 + p.2))
    (n : ℕ) (ξ : Fin 2 → ℂ) (t : ℝ) :
    ‖fibreHomogeneous a ξ n t‖ ≤ K * (2 * A) ^ n * fibreNorm ξ ^ n := by
  have he : fibreHomogeneous a ξ n t = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      fibreMonomial ξ p * a p t := by
    simp only [fibreHomogeneous, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  apply (norm_sum_le _ _).trans
  have hp p (hpn : p ∈ Finset.HasAntidiagonal.antidiagonal n) : ‖fibreMonomial ξ p * a p t‖ ≤
      K * A ^ n * fibreNorm ξ ^ n := by
    have ho : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hpn
    rw [norm_mul]
    calc
      _ ≤ fibreNorm ξ ^ n * (K * A ^ n) := by
        apply mul_le_mul (by simpa only [ho] using fibreMonomial_norm_le ξ p)
          (by simpa only [ho] using ha p t) (norm_nonneg _)
          (pow_nonneg (fibreNorm_nonneg ξ) n)
      _ = _ := by ring
  apply (Finset.sum_le_sum hp).trans
  rw [Finset.sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal]
  have hn : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.succ_le_of_lt ((show n < 2 ^ n from Nat.lt_two_pow_self))
  calc
    _ ≤ (2 : ℝ) ^ n * (K * A ^ n * fibreNorm ξ ^ n) :=
      mul_le_mul_of_nonneg_right hn
        (mul_nonneg (mul_nonneg hK (pow_nonneg hA n)) (pow_nonneg (fibreNorm_nonneg ξ) n))
    _ = _ := by rw [mul_pow]; ring

/-! Coordinate-weighted predecessor series for the literal Taylor flux. -/

/-- The literal coordinate predecessor sum is multiplication by the coordinate frequency polynomial. -/
theorem fibreTaylor_coordinate_series (ξ b : Fin 2 → ℂ) (f : Fin 2 → ℕ × ℕ → ℂ)
    (hs : ∀ j, Summable (fun p => fibreMonomial ξ p * f j p)) :
    (∑' p, fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * f j (fibreCoefficientPrevious p j)) =
      ∑ j : Fin 2, b j * ξ j * ∑' p, fibreMonomial ξ p * f j p := by
  let S := fun (j : Fin 2) (p : ℕ × ℕ) => if j ∈ fibreCoefficientDirections p then
    fibreMonomial ξ p * f j (fibreCoefficientPrevious p j) else 0
  let A := fun (j : Fin 2) (p : ℕ × ℕ) => b j * S j p
  have hS j : Summable (S j) := fibreMonomial_shift_summable ξ j (f j) (hs j)
  have hA j : Summable (A j) := (hS j).mul_left (b j)
  have htotal : (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * f j (fibreCoefficientPrevious p j)) = (fun p => ∑ j : Fin 2, A j p) := by
    funext p
    calc
      _ = ∑ j ∈ fibreCoefficientDirections p, A j p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [A, S]
        rw [ite_eq_left hj]
        ring
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by
        dsimp [A, S]
        rw [ite_eq_right hj, mul_zero])
  have hsum j : (∑' p, A j p) = b j * (ξ j * ∑' p, fibreMonomial ξ p * f j p) := by
    change (∑' p, b j * S j p) = _
    rw [tsum_mul_left]
    congr 1
    exact fibreMonomial_shift_tsum ξ j (f j)
  rw [htotal, Summable.tsum_finsetSum (fun j _ => hA j)]
  simp_rw [hsum]
  simp only [Fin.sum_univ_two]
  ring

/-! Coordinate-weighted predecessor series for the literal Taylor flux. -/

/-- The literal coordinate predecessor sum is multiplication by the coordinate frequency polynomial. -/
theorem fibreTaylor_coordinate_summable (ξ b : Fin 2 → ℂ) (f : Fin 2 → ℕ × ℕ → ℂ)
    (hs : ∀ j, Summable (fun p => fibreMonomial ξ p * f j p)) :
    Summable (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * f j (fibreCoefficientPrevious p j)) := by
  let S := fun (j : Fin 2) (p : ℕ × ℕ) => if j ∈ fibreCoefficientDirections p then
    fibreMonomial ξ p * f j (fibreCoefficientPrevious p j) else 0
  let A := fun (j : Fin 2) (p : ℕ × ℕ) => b j * S j p
  have hS j : Summable (S j) := fibreMonomial_shift_summable ξ j (f j) (hs j)
  have hA j : Summable (A j) := (hS j).mul_left (b j)
  have htotal : (fun p => fibreMonomial ξ p * ∑ j ∈ fibreCoefficientDirections p,
      b j * f j (fibreCoefficientPrevious p j)) = (fun p => ∑ j : Fin 2, A j p) := by
    funext p
    calc
      _ = ∑ j ∈ fibreCoefficientDirections p, A j p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [A, S]
        rw [ite_eq_left hj]
        ring
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by
        dsimp [A, S]
        rw [ite_eq_right hj, mul_zero])
  rw [htotal]
  simpa only [Fin.sum_univ_two] using (hA 0).add (hA 1)

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

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

end AVRegularity.CycleDamping.Graph
end

section
open scoped BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

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

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

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

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization
open scoped ENNReal BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

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

end AVRegularity.CycleDamping.Graph
end

section
open scoped BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

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

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

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

end AVRegularity.CycleDamping.Graph
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Quantitative control of literal finite sums of actual raw cell jets. -/

/-- An absolutely finite energy family has a literal finite-sum bound, obtained from the proved series bound. -/
theorem cellEnergyNorm_finset_sum_le_two {J : Type*} [DecidableEq J]
    (s : Finset J) (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j ∈ s, ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D j p.1 a p.2)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hfinite : ∀ j ∈ s, cellEnergyNorm Set.univ (D j) < ⊤) :
    cellEnergyNorm Set.univ (∑ j ∈ s, D j) ≤ 2 * ∑ j ∈ s, cellEnergyNorm Set.univ (D j) := by
  let F := fun j : s => D j.1
  have hs : (∑' j : s, cellEnergyNorm Set.univ (F j)) < ⊤ := by
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.mpr (fun j _ => hfinite j.1 j.2)
  have hb := cellEnergyNorm_tsum_le F (fun j a => hD j.1 j.2 a) hs
  have he : (∑ j ∈ s, D j) = (fun t a x => ∑' j : s, F j t a x) := by
    funext t a x
    rw [tsum_fintype]
    simp only [Finset.sum_apply, F]
    exact (Finset.sum_finset_coe (fun j => D j t a x) s).symm
  have hn : (∑' j : s, cellEnergyNorm Set.univ (F j)) =
      ∑ j ∈ s, cellEnergyNorm Set.univ (D j) := by
    rw [tsum_fintype]
    exact Finset.sum_finset_coe (fun j => cellEnergyNorm Set.univ (D j)) s
  rw [← he, hn] at hb
  exact hb

end AVRegularity.CycleDamping.Graph
end

section
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Elementary real bounds for the explicit coefficient radius. -/

/-- The explicit coefficient radius is at most one for every nonnegative drift bound. -/
theorem fibreCoefficientMajorantRadius_le_one {Cw : ℝ} (hCw : 0 ≤ Cw) :
    fibreCoefficientMajorantRadius Cw ≤ 1 := by
  unfold fibreCoefficientMajorantRadius
  have hd : 0 < 104 * (Cw + 8) := by positivity
  apply (div_le_iff₀ hd).mpr
  linarith

end AVRegularity.CycleDamping.Graph
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Exact projection of the nonlinear graph source on every time trace. -/

/-- Projection of the complete unprojected forcing equals the literal graph source for an actual mean-zero inverse. -/
theorem fibreGraphSource_projection (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (t : ℝ) :
    cellQ0 (fun x => -Complex.I * (fibreDriftCoupling η v ξ t x * (1 + cellValue D t x)) +
      Complex.I * cellValue D t x *
        cellMean (fun y => fibreDriftCoupling η v ξ t y * cellValue D t y)) =
      fibreGraphSource η v ξ (cellValue D) t := by
  let b := fibreDriftCoupling η v ξ
  let P := fun x => -Complex.I * (b t x * (1 + cellValue D t x))
  let m := cellMean (fun y => b t y * cellValue D t y)
  let Q := fun x => Complex.I * cellValue D t x * m
  have hb := fibreDriftCoupling_measurable η hv ξ
  have hB := fibreDriftCoupling_norm_le η Cw v hw ξ
  have hf := (hD.1.2.2.1 t (mem_univ t)).1
  have hp0 := cellAffineMultiplier_memLp (b t) (cellValue D t) (Cw * fibreNorm ξ)
    (hb.comp ((measurable_const (a := t)).prodMk measurable_id)) (hB t) hf
  have hp : MemLp P 2 (volume.restrict AVenhance.unitCube) := hp0.const_smul (-Complex.I)
  have heQ : Q = (Complex.I * m) • cellValue D t := by
    funext x
    simp only [Q, Pi.smul_apply, smul_eq_mul]
    ring
  have hq : MemLp Q 2 (volume.restrict AVenhance.unitCube) := by
    rw [heQ]
    exact hf.const_smul _
  have hm : cellMean Q = 0 := by
    rw [heQ, cellMean_complex_smul, hD.2.1 t, mul_zero]
  change cellQ0 (P + Q) = _
  rw [cellQ0_add P Q hp hq, cellQ0_eq_self_of_mean_zero Q hm]
  rfl

end AVRegularity.CycleDamping.Graph
end

section
open MeasureTheory Homogenization
open scoped BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Exact coordinate expansion of the actual drift multiplier mean. -/

local instance graphFibreCouplingMeanCoordinatesProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- The finite coordinate pairing recovers the literal arbitrary-frequency mean. -/
theorem fibreDriftCoupling_mean_coordinates (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (f : Vec 2 → ℂ)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    (∑ j : Fin 2, ξ j * cellMean (fun x =>
      fibreDriftCoupling η v (fibreCoordinateFrequency j) t x * f x)) =
      cellMean (fun x => fibreDriftCoupling η v ξ t x * f x) := by
  let b := fun j => fibreDriftCoupling η v (fibreCoordinateFrequency j) t
  have hb j : Measurable (b j) := (fibreDriftCoupling_measurable η hv
    (fibreCoordinateFrequency j)).comp ((measurable_const (a := t)).prodMk measurable_id)
  have hB j x : ‖b j x‖ ≤ Cw := by
    simpa only [fibreCoordinateFrequency_norm, mul_one] using
      fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) t x
  have hm j : Integrable (fun x => ξ j * (b j x * f x))
      (volume.restrict AVenhance.unitCube) :=
    ((cellMultiplier_memLp (b j) f Cw (hb j) (hB j) hf).const_smul (ξ j)).integrable (by norm_num)
  have he : (fun x => fibreDriftCoupling η v ξ t x * f x) =
      (fun x => ∑ j : Fin 2, ξ j * (b j x * f x)) := by
    funext x
    rw [← fibreDriftCoupling_coordinates η v ξ t x, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [b]
    ring
  rw [he]
  change _ = ∫ x, ∑ j : Fin 2, ξ j * (b j x * f x) ∂(volume.restrict AVenhance.unitCube)
  rw [integral_finsetSum _ (fun j _ => hm j)]
  apply Finset.sum_congr rfl
  intro j _
  exact (integral_const_mul (ξ j) (fun x => b j x * f x)).symm

end AVRegularity.CycleDamping.Graph
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Uniform time bounds for the literal drift-mean symbol coefficients. -/

/-- Actual lower inverse states control the coordinate mean symbol uniformly at every time. -/
theorem fibreCoefficientDriftSymbol_uniform_le (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {C : CellCoefficients} (A : ℕ × ℕ → CellInverseDatum C) (p : ℕ × ℕ) :
    (⨆ t, ‖fibreCoefficientDriftSymbol η v (fun a => (A a).raw) p t‖ₑ) ≤
      ∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw *
        cellEnergyNorm Set.univ (A (fibreCoefficientPrevious p j)).raw := by
  apply iSup_le
  intro t
  apply (enorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  let b := fibreDriftCoupling η v (fibreCoordinateFrequency j)
  have hb := fibreDriftCoupling_measurable η hv (fibreCoordinateFrequency j)
  have hB s x : ‖b s x‖ ≤ Cw := by
    simpa only [fibreCoordinateFrequency_norm, mul_one] using
      fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) s x
  have hi : ‖-Complex.I‖ₑ = 1 := by simp [enorm_eq_nnnorm]
  rw [enorm_mul, hi, one_mul]
  exact cellBoundedMean_energy_bound b Cw hb hB
    (A (fibreCoefficientPrevious p j)).isInverse.1 t

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Exact vanishing of the constant and linear symbol coefficients. -/

/-- The metric symbol is exactly quadratic and has no lower coefficients. -/
theorem fibreCoefficientMetricSymbol_low_order (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ × ℕ) (hp : p.1 + p.2 ≤ 1) (t : ℝ) :
    fibreCoefficientMetricSymbol η G p t = 0 := by
  have hne (i j : Fin 2) : p ≠ cellJetDirection i + cellJetDirection j := by
    have hi : (cellJetDirection i).1 + (cellJetDirection i).2 = 1 := by
      simpa using cellJetDirection_order (0 : ℕ × ℕ) i
    have hij := cellJetDirection_order (cellJetDirection i) j
    intro he
    rw [← he] at hij
    omega
  simp only [fibreCoefficientMetricSymbol, hne, ite_false, Finset.sum_const_zero, mul_zero]

/-- Any correction with zero constant coefficient gives a drift symbol without constant or linear terms. -/
theorem fibreCoefficientDriftSymbol_low_order (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (hr : r 0 = 0)
    (p : ℕ × ℕ) (hp : p.1 + p.2 ≤ 1) (t : ℝ) :
    fibreCoefficientDriftSymbol η v r p t = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have ho := fibreCoefficientPrevious_order hj
  have hz : fibreCoefficientPrevious p j = 0 := by
    apply Prod.ext
    · change (fibreCoefficientPrevious p j).1 = 0
      omega
    · change (fibreCoefficientPrevious p j).2 = 0
      omega
  rw [hz, hr]
  simp [cellValue, cellMean]

/-- The actual symbol family has exactly zero constant and linear coefficients. -/
theorem fibreCoefficientFamily_symbol_low_order (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (p : ℕ × ℕ) (hp : p.1 + p.2 ≤ 1) (t : ℝ) :
    fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw) p t = 0 := by
  rw [fibreCoefficientSymbol, fibreCoefficientMetricSymbol_low_order η G p hp t,
    fibreCoefficientDriftSymbol_low_order η v _
      (fibreCoefficientFamily_zero η Cw hη G hG hv hw) p hp t, zero_add]

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Geometric individual coefficient bounds from the proved total weighted majorant. -/

/-- A positive-radius unit weighted majorant bounds each coefficient by the inverse radius power. -/
theorem fibreCoefficient_individual_le (R : ℝ) (hR : 0 < R)
    (E : ℕ × ℕ → ℝ≥0∞)
    (hE : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * E p) ≤ 1) (p : ℕ × ℕ) :
    E p ≤ ENNReal.ofReal ((R⁻¹) ^ (p.1 + p.2)) := by
  let a := ENNReal.ofReal (R ^ (p.1 + p.2))
  have ha0 : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hR _))
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hh : a * E p ≤ 1 := by
    dsimp only [a]
    rw [ENNReal.ofReal_pow hR.le]
    exact (ENNReal.le_tsum p).trans hE
  calc
    E p = a⁻¹ * (a * E p) := (ENNReal.inv_mul_cancel_left ha0 hat).symm
    _ ≤ a⁻¹ * 1 := mul_le_mul' le_rfl hh
    _ = ENNReal.ofReal ((R⁻¹) ^ (p.1 + p.2)) := by
      rw [mul_one]
      dsimp only [a]
      rw [← ENNReal.ofReal_inv_of_pos (pow_pos hR _), inv_pow]

/-- Every actual coefficient of the constructed family has the geometric energy bound. -/
theorem fibreCoefficientFamily_individual_energy_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (p : ℕ × ℕ) :
    cellEnergyNorm Set.univ (fibreCoefficientFamily η Cw hη G hG hv hw p) ≤
      ENNReal.ofReal ((fibreCoefficientMajorantRadius Cw)⁻¹ ^ (p.1 + p.2)) :=
  fibreCoefficient_individual_le _ (fibreCoefficientMajorantRadius_pos hCw) _
    (fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw) p

/-- A positive-radius weighted total bound gives the corresponding individual geometric bound. -/
theorem fibreCoefficient_individual_of_total_le (R K : ℝ) (hR : 0 < R)
    (E : ℕ × ℕ → ℝ≥0∞)
    (hE : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * E p) ≤ ENNReal.ofReal K)
    (p : ℕ × ℕ) : E p ≤ ENNReal.ofReal (K * (R⁻¹) ^ (p.1 + p.2)) := by
  let a := ENNReal.ofReal (R ^ (p.1 + p.2))
  have ha0 : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hR _))
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hh : a * E p ≤ ENNReal.ofReal K := by
    dsimp only [a]
    rw [ENNReal.ofReal_pow hR.le]
    exact (ENNReal.le_tsum p).trans hE
  calc
    E p = a⁻¹ * (a * E p) := (ENNReal.inv_mul_cancel_left ha0 hat).symm
    _ ≤ a⁻¹ * ENNReal.ofReal K := mul_le_mul' le_rfl hh
    _ = ENNReal.ofReal (K * (R⁻¹) ^ (p.1 + p.2)) := by
      dsimp only [a]
      rw [← ENNReal.ofReal_inv_of_pos (pow_pos hR _),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hR.le _)), inv_pow]
      congr 1
      exact mul_comm _ _

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Absolute uniform time convergence of the actual drift-mean symbol coefficients. -/

/-- The actual drift symbol coefficients have a finite total weighted majorant uniform in time. -/
theorem fibreCoefficientFamily_weighted_drift_symbol_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) p *
      ⨆ t, ‖fibreCoefficientDriftSymbol η v r p t‖ₑ) ≤
      (2 * ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) * (3 * ENNReal.ofReal Cw + 8) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let E := fun p => cellEnergyNorm Set.univ (r p)
  let U := fun p => ⨆ t, ‖fibreCoefficientDriftSymbol η v r p t‖ₑ
  have hz : U 0 = 0 := by
    simp [U, fibreCoefficientDriftSymbol, fibreCoefficientDirections_zero]
  let A := fun p : ℕ × ℕ => fibreCoefficientStage η Cw hη G hG hv hw (p.1 + p.2) p
  apply fibreCoefficient_weighted_forcing_total_le _ (ENNReal.ofReal Cw) E U hz
    (fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw)
  intro p
  apply (fibreCoefficientDriftSymbol_uniform_le η Cw hv hw A p).trans
  have hl : (∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw * E (fibreCoefficientPrevious p j)) ≤
      ∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw *
        ((if p = cellJetDirection j then 1 else 0) + E (fibreCoefficientPrevious p j)) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul' le_rfl (le_add_left le_rfl)
  exact hl.trans ((le_add_right le_rfl).trans (le_add_right le_rfl))

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Every-time convergence and interchange for the actual coefficient multiplier means. -/

section
local instance graphFibreCoefficientMeanSeriesProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- The actual monomial value traces are absolutely L2 summable at every time. -/
theorem fibreCoefficientFamily_value_trace_summable (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * cellValue (r p) t x)) < ⊤ := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hs : (∑' p, cellEnergyNorm Set.univ (fibreMonomial ξ p • r p)) < ⊤ :=
    (fibreCoefficientFamily_series_energy_le η Cw hη hCw G hG hv hw ξ hξ).trans_lt (by simp)
  exact (ENNReal.tsum_le_tsum (fun p =>
    cellValue_cellL2Norm_le_energy (fibreMonomial ξ p • r p) t)).trans_lt hs

/-- Each actual coordinate multiplier mean series is absolutely convergent on every time trace. -/
theorem fibreCoefficientFamily_mean_summable_norm (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) (j : Fin 2) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    Summable (fun p => ‖fibreMonomial ξ p *
      cellMean (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency j) t x *
        cellValue (r p) t x)‖) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let b := fibreDriftCoupling η v (fibreCoordinateFrequency j) t
  have hb : Measurable b := (fibreDriftCoupling_measurable η hv
    (fibreCoordinateFrequency j)).comp ((measurable_const (a := t)).prodMk measurable_id)
  have hB x : ‖b x‖ ≤ Cw := by
    simpa only [fibreCoordinateFrequency_norm, mul_one] using
      fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) t x
  have hbl : MemLp b 2 (volume.restrict AVenhance.unitCube) :=
    MemLp.of_bound hb.aestronglyMeasurable Cw (Filter.Eventually.of_forall hB)
  exact fibreMean_monomial_summable_norm ξ b hbl (fun p => cellValue (r p) t)
    (fibreCoefficientFamily_value_trace_summable η Cw hη hCw G hG hv hw ξ hξ t)
end

/-! Absolute spatial L2 convergence of the actual unprojected scalar forcing series. -/

/-- The actual scalar forcing series is absolutely L2 convergent at every time throughout the coefficient disc. -/
theorem fibreCoefficientFamily_source_trace_summable (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * fibreCoefficientSource η v r p t x)) < ⊤ := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have he p : cellL2Norm (fun x => fibreMonomial ξ p * fibreCoefficientSource η v r p t x) =
      ENNReal.ofReal ‖fibreMonomial ξ p‖ * cellL2Norm (fibreCoefficientSource η v r p t) := by
    change eLpNorm (fibreMonomial ξ p • fibreCoefficientSource η v r p t) 2 _ = _
    rw [eLpNorm_const_smul, ofReal_norm]
    rfl
  change (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * fibreCoefficientSource η v r p t x)) < ⊤
  simp_rw [he]
  apply ((fibreMonomial_weighted_energy_le _ ξ hξ _).trans
    (fibreCoefficientFamily_weighted_source_trace_le η Cw hη hCw G hG hv hw t)).trans_lt
  finiteness

end AVRegularity.CycleDamping.Graph
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! All-frequency homogeneous energy bounds for the actual correction coefficients. -/

/-- Every actual homogeneous correction polynomial has the geometric Taylor energy bound at every frequency. -/
theorem fibreCoefficientFamily_homogeneous_energy_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (n : ℕ) (ξ : Fin 2 → ℂ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    cellEnergyNorm Set.univ (fibreHomogeneous r ξ n) ≤
      ENNReal.ofReal (2 * (2 * (fibreCoefficientMajorantRadius Cw)⁻¹) ^ n * fibreNorm ξ ^ n) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let R := fibreCoefficientMajorantRadius Cw
  let D := fun p => fibreMonomial ξ p • r p
  have hi p := fibreCoefficientFamily_scaled_isInverse η Cw hη G hG hv hw ξ p
  have hb := cellEnergyNorm_finset_sum_le_two (Finset.HasAntidiagonal.antidiagonal n) D
    (fun p _ a => (hi p).1.2.2.2.1 a) (fun p _ => (hi p).2.2)
  have hp p (hpn : p ∈ Finset.HasAntidiagonal.antidiagonal n) : cellEnergyNorm Set.univ (D p) ≤
      ENNReal.ofReal ((R⁻¹) ^ n * fibreNorm ξ ^ n) := by
    have ho : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hpn
    have he := fibreCoefficientFamily_individual_energy_le η Cw hη hCw G hG hv hw p
    have hm := cellEnergyNorm_complex_smul Set.univ (fibreMonomial ξ p) (r p)
      (cellSolution_gradient_aestronglyMeasurable
        (fibreCoefficientFamily_isInverse η Cw hη G hG hv hw p).1)
    apply hm.trans
    calc
      _ ≤ ENNReal.ofReal (fibreNorm ξ ^ n) * ENNReal.ofReal ((R⁻¹) ^ n) := by
        apply mul_le_mul'
        · rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by simpa only [ho] using fibreMonomial_norm_le ξ p)
        · simpa only [ho] using he
      _ = _ := by
        rw [← ENNReal.ofReal_mul (pow_nonneg (fibreNorm_nonneg ξ) n)]
        congr 1
        exact mul_comm _ _
  have hn : ((n + 1 : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n := by
    exact_mod_cast Nat.succ_le_of_lt ((show n < 2 ^ n from Nat.lt_two_pow_self))
  have hs : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, cellEnergyNorm Set.univ (D p)) ≤
      (2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((R⁻¹) ^ n * fibreNorm ξ ^ n) := by
    apply (Finset.sum_le_sum hp).trans
    rw [Finset.sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal]
    exact mul_le_mul' hn le_rfl
  change cellEnergyNorm Set.univ (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, D p) ≤ _
  apply hb.trans
  apply (mul_le_mul' le_rfl hs).trans
  have hpow : (2 : ℝ≥0∞) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
    simp [ENNReal.ofReal_pow]
  rw [hpow, ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]
  have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [htwo, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [R]
  rw [mul_pow]
  ring_nf
  exact le_rfl

end AVRegularity.CycleDamping.Graph
end
