-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.PlainDefectDerivative
import AVRegularity.EntryTerminal.Ingredients.PrepNorm.PrepNorm
import Mathlib.Algebra.Order.Star.Real

section
/-! The actual physical constituent of A(I-S)u at output order zero.
Its moment gain retains the m+L gradient reserve of the plain input.
No assertion that I-S regularizes rough H1 inputs is used.

The degenerate cases are included: m=0 is the D=2 constituent, L=0 is boundedness, rho=width
gives moment factor one, constants and zero data retain their actual flux. Empty
families and edgeless seeds have empty sums of these constituents; singleton
families and identity geometry need no different estimate. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.Construction.KernelDefect
open AVRegularity.KernelEnergy (torusKernelFluxTerm torusKernelFluxTerm_factorialNorm_le
  torusCarrierGradFactorial_nonneg)
namespace AVRegularity.Construction.Preservation.CommonPreparation

variable {E G H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]

/-- The fixed physical coefficient data for one order-(m+2) constituent. -/
structure PreparationPlainFluxCoefficient (ρ a b : ℝ) (m : ℕ)
    (E G H : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  B : ℝ → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 (m + 1) => G)) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => H)
  C : E →L[ℝ] G
  finite : coefficientSeminorm ρ 0 a b B ≠ ⊤
  smooth : ∀ t ∈ Set.Icc a b, ContDiff ℝ (0 : ℕ) (B t)
  periodic : ∀ t ∈ Set.Icc a b, IsZ2Periodic (B t)

variable {ρ a b : ℝ} {m L : ℕ}

/-- The literal weak defect is differentiated and multiplied in its original
order. The available higher input is never replaced by a low-order datum. -/
def preparationPlainDefectFlux (F : PreparationPlainFluxCoefficient ρ a b m E G H)
    (hρ : 0 < ρ) {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀) (S : KernelSpec)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (u : TorusHk (m + L + 1) E) :
    TorusHk 0 (PiLp 2 (fun _ : Fin 2 => H)) :=
  torusKernelFluxTerm (K := 0) (m := m) rfl ρ hρ a b F.B F.finite t ht
    (F.smooth t ht) (F.periodic t ht)
    (kdRealization (k := 0 + (m + 1)) (L := L) φ₀ hφ S t
      (mapTorusHk F.C (truncateTorusHk (by omega : (0 + (m + 1)) + L ≤ m + L + 1) u)))

/-- The shift constant uses the true input reserve. Its dependence on rho is
exactly rho to the negative m; the moment ratio carries the other L powers. -/
def preparationPlainDefectConstant (φ₀ : Vec 2 → ℝ) (Γ : ℝ) (m L : ℕ) : ℝ :=
  kdUniformMomentConst φ₀ L |Γ| * ((m + L).factorial : ℝ)

private theorem preparation_plain_defect_shift (hρ : 0 < ρ) (r : ℝ) (m L : ℕ) :
    r ^ L * derivativeReserveFactor ρ 0 (m + L) =
      ((m + L).factorial : ℝ) * (r / ρ) ^ L / ρ ^ m := by
  unfold derivativeReserveFactor
  rw [Nat.zero_add, Nat.factorial_zero, Nat.cast_one, div_one, pow_add, div_pow]
  field_simp

/-- Exact pointwise flux estimate, before the positive constituent and mass
sums. The moment constant is independent of the coefficient, kernel ORDER and data;
the actual kernel still appears in the defect and width gain. -/
def PlainDefectFluxStatement (E G H : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H] : Prop :=
  ∀    {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀),
    ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) → ∫ z, φ₀ z = 1 →
    Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (m L : ℕ) (Γ : ℝ),
    0 ≤ preparationPlainDefectConstant φ₀ Γ m L ∧
    ∀ (ρ a b : ℝ) (hρ : 0 < ρ)
      (F : PreparationPlainFluxCoefficient ρ a b m E G H) (S : KernelSpec) (t : ℝ)
      (ht : t ∈ Set.Icc a b), S.IsAdmissible Γ L → 0 < S.width →
      ∀ u : TorusHk (m + L + 1) E,
      Real.sqrt (factorialNormSq ρ (preparationPlainDefectFlux
        (E := E) (G := G) (H := H) (ρ := ρ) (a := a) (b := b)
        (m := m) (L := L) (φ₀ := φ₀) F hρ hφ S t ht u).val) ≤
        (coefficientSeminorm ρ 0 a b F.B).toReal *
          (preparationPlainDefectConstant φ₀ Γ m L * (S.width / ρ) ^ L / ρ ^ m) *
          ‖F.C‖ * Real.sqrt (gradFactorialNormSq ρ u.val)

/-- Density for the moment estimate, constant fiber contraction, the exact
gradient shift, and the coefficient multiplier give the physical flux. -/
theorem plain_defect_flux : PlainDefectFluxStatement E G H := by
  intro φ₀ hφ hd hnonneg hmass hsupp m L Γ
  refine ⟨mul_nonneg (kdMomentConst_nonneg φ₀ (kdUniformOrder L) L (abs_nonneg Γ)) (by positivity), ?_⟩
  intro ρ a b hρ F S t ht hadm hr u
  let V := mapTorusHk F.C
    (truncateTorusHk (by omega : (0 + (m + 1)) + L ≤ m + L + 1) u)
  let Y := kdRealization φ₀ hφ S t V
  let c := kdUniformMomentConst φ₀ L |Γ|
  let shift := derivativeReserveFactor ρ 0 (m + L)
  let X := gradFactorialNormSq ρ u.val
  have hc : 0 ≤ c := kdMomentConst_nonneg φ₀ (kdUniformOrder L) L (abs_nonneg Γ)
  have hshift : 0 ≤ shift := by unfold shift derivativeReserveFactor; positivity
  have hjet := preparation_plain_defect_jet_le hφ hd hnonneg hmass hsupp L Γ S t
    hadm hr V (m + 1) (by omega)
  have hmapped := preparation_plain_mapped_level_le
    (by omega : (0 + (m + 1)) + L ≤ m + L + 1) F.C u
    (⟨(m + 1) + L, by omega⟩ : Fin ((0 + (m + 1)) + L + 1))
  have hidx : (⟨(m + 1) + L, by omega⟩ : Fin (m + L + 1 + 1)) =
      ⟨(m + L) + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
  rw [hidx] at hmapped
  have hgrad := preparation_plain_gradient_level_le ρ hρ u
    (⟨m + L, by omega⟩ : Fin (m + L + 1))
  have hY : derivFactorialNormSq (m + 1) ρ Y.val ≤
      ((c * S.width ^ L * shift) ^ 2) * ‖F.C‖ ^ 2 * X := by
    have he : derivFactorialNormSq (K := 0) (m + 1) ρ Y.val =
        derivativeNormSq Y.val ⟨m + 1, by omega⟩ := by
      change (∑ i : Fin (0 + 1), factorialWeight ρ i.val *
        derivativeNormSq Y.val ⟨i.val + (m + 1), by omega⟩) = _
      rw [Fin.sum_univ_one]
      simp only [factorialWeight, Fin.val_zero, Nat.mul_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, one_pow, div_one, one_mul, Nat.zero_add]
    rw [he]
    calc
      _ ≤ (c * S.width ^ L) ^ 2 * derivativeNormSq V.val ⟨(m + 1) + L, by omega⟩ := hjet
      _ ≤ (c * S.width ^ L) ^ 2 * (‖F.C‖ ^ 2 *
          derivativeNormSq u.val ⟨m + L + 1, by omega⟩) :=
        mul_le_mul_of_nonneg_left hmapped (sq_nonneg _)
      _ ≤ (c * S.width ^ L) ^ 2 * (‖F.C‖ ^ 2 * (shift ^ 2 * X)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgrad (sq_nonneg _)) (sq_nonneg _)
      _ = _ := by ring
  have hflux := torusKernelFluxTerm_factorialNorm_le (K := 0) (m := m) rfl ρ hρ a b
    F.B F.finite t ht (F.smooth t ht) (F.periodic t ht) Y
    (c * S.width ^ L * shift) (mul_nonneg (mul_nonneg hc (pow_nonneg hr.le _)) hshift)
    ‖F.C‖ (norm_nonneg _) X (torusCarrierGradFactorial_nonneg _ _ _) hY
  have hcost : c * S.width ^ L * shift =
      preparationPlainDefectConstant φ₀ Γ m L * (S.width / ρ) ^ L / ρ ^ m := by
    dsimp only [shift, preparationPlainDefectConstant]
    rw [mul_assoc, preparation_plain_defect_shift hρ]
    dsimp only [c]
    ring
  rw [hcost] at hflux
  exact hflux

omit [FiniteDimensional ℝ E] in
/-- The actual constituent is strongly measurable on the window. The time
hypothesis is entrywise measurability of the coefficient, and the moment
kernel is the weak moving average. -/
theorem preparation_plain_defect_flux_stronglyMeasurable
    {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hsupp : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (F : PreparationPlainFluxCoefficient ρ a b m E G H) (hρ : 0 < ρ)
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => F.B p.1 p.2))
    (S : KernelSpec) (hH₁ : Measurable S.H₁) (hH₂ : Measurable S.H₂)
    (u : ℝ → TorusHk (m + L + 1) E) (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun t : Set.Icc a b =>
      preparationPlainDefectFlux (L := L) (φ₀ := φ₀) F hρ hφ S t t.property (u t)) := by
  let V : ℝ → TorusHk ((0 + (m + 1)) + L) G := fun t =>
    mapTorusHk F.C (truncateTorusHk (by omega) (u t))
  have hV : StronglyMeasurable V := by
    simpa only [mapTorusHkCLM_apply] using (mapTorusHkCLM ((0 + (m + 1)) + L) F.C).continuous.comp_stronglyMeasurable
      ((truncateTorusHk (by omega : (0 + (m + 1)) + L ≤ m + L + 1)).continuous.comp_stronglyMeasurable hu)
  have hY := kdRealization_stronglyMeasurable hφ hd hsupp S hH₁ hH₂ V hV
  exact KernelEnergy.torusKernelFluxTerm_time_stronglyMeasurable
    (K := 0) (m := m) rfl ρ hρ a b F.B F.finite hm F.smooth F.periodic
    (fun t : Set.Icc a b => kdRealization φ₀ hφ S t (V t))
    (hY.comp_measurable measurable_subtype_coe)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The readout of the joint operator of the copied family. One joint model of the
chain `preparationNeutralChain F H` is applied once; its copies are then summed back into
the original components. This module holds the readout definitions and the mass-norm
facts about slices and sums of copies. No constant depends on the datum.

The degenerate cases are included: `H = 0` has one copy, so the readout is the joint operator
itself; an empty component type makes every mass norm zero; a single component, order zero and
`D = 2` use the same formulas. -/

section
namespace CopyJoint

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The joint operator of the copied family, read back into the original components by
summing the copies at the model order. -/
def readout {H : ℕ} (K : ι × Fin (H + 1) → ℕ) (Mout : ℕ)
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1),
      TorusHk 0 (h u.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (x : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1)) (i : ι) : TorusHk Mout (h i) :=
  ∑ l : Fin (H + 1), truncateTorusHk (le_max_left Mout (K (i, l)))
    (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg x (i, l))

/-- The plain chain solution read back at time `t`, at order zero. -/
def plainReadout {H : ℕ} (K : ι × Fin (H + 1) → ℕ)
    (U : ∀ v : ι × Fin (H + 1), ℝ → TorusHk (K v) (h v.1)) (t : ℝ) (i : ι) :
    TorusHk 0 (h i) :=
  ∑ l : Fin (H + 1), truncateTorusHk (Nat.zero_le _) (U (i, l) t)

/-- The sum of finitely many mass-weighted families is controlled by the sum of norms. -/
theorem sqrt_massNormSq_sum_le {α : Type*} (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ)
    (hπ : ∀ i, 0 < π i) (s : Finset α) (X : α → ∀ i, TorusHk (K i) (h i)) :
    Real.sqrt (massNormSq ρ π (fun i => ((∑ a ∈ s, X a) i).val)) ≤
      ∑ a ∈ s, Real.sqrt (massNormSq ρ π (fun i => (X a i).val)) := by
  rw [← CoupledEnergy.Variational.massWeightedCarrierCLM_norm K ρ π hπ]
  simp_rw [← CoupledEnergy.Variational.massWeightedCarrierCLM_norm K ρ π hπ (X _)]
  exact Finset.le_sum_of_subadditive
    (fun Y : ∀ i, TorusHk (K i) (h i) =>
      ‖CoupledEnergy.Variational.massWeightedCarrierCLM K ρ π Y‖)
    (by rw [ContinuousLinearMap.map_zero, norm_zero])
    (fun Y Z => by rw [ContinuousLinearMap.map_add]; exact norm_add_le _ _) s X

/-- One copy has no more mass norm than the whole chain. -/
theorem massNormSq_slice_le {L : Type*} [Fintype L] (K : ι × L → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (X : ∀ v : ι × L, TorusHk (K v) (h v.1)) (l : L) :
    massNormSq (E := h) (K := fun i => K (i, l)) ρ π (fun i => (X (i, l)).val) ≤
      massNormSq (E := fun v : ι × L => h v.1) (K := K) ρ (fun v => π v.1)
        (fun v => (X v).val) := by
  classical
  unfold massNormSq
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun l' => (π i)⁻¹ * factorialNormSq ρ (X (i, l')).val)
    (fun l' _ => mul_nonneg (inv_nonneg.2 (hπ i).le) (factorialNormSq_nonneg ρ _)) (Finset.mem_univ l)

end CopyJoint
end

/-! The error clause `IsJointError` of the joint preparation for the copied family, read back
into the original components: the sum over the `H + 1` copies of the `L²` distance between the
solution and the joint model is at most `H + 1` times the joint error bound. The number of copies
is the fixed depth `H`, chosen before every datum; no norm of the datum is divided out.

The degenerate cases are included: `H = 0` is the joint error bound itself; an empty component
type gives zero on both sides; zero data give zero on both sides. -/

section
namespace CopyJoint

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem sqrt_massNormSq_neg (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (X : ∀ i, TorusHk (K i) (h i)) :
    Real.sqrt (massNormSq ρ π (fun i => ((-X) i).val)) =
      Real.sqrt (massNormSq ρ π (fun i => (X i).val)) := by
  rw [← CoupledEnergy.Variational.massWeightedCarrierCLM_norm K ρ π hπ,
    ← CoupledEnergy.Variational.massWeightedCarrierCLM_norm K ρ π hπ X,
    ContinuousLinearMap.map_neg, norm_neg]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The model readout minus the plain readout is minus the sum over copies of the joint error. -/
theorem readout_sub_plain_eq {H : ℕ} (K : ι × Fin (H + 1) → ℕ) (Mout : ℕ) (tp : ℝ)
    (jo : ∀ v : ι × Fin (H + 1), TorusHk (max Mout (K v)) (h v.1))
    (u : ∀ v : ι × Fin (H + 1), ℝ → TorusHk (K v) (h v.1)) (i : ι) :
    truncateTorusHk (Nat.zero_le Mout)
        (∑ l : Fin (H + 1), truncateTorusHk (le_max_left Mout (K (i, l))) (jo (i, l))) -
      ∑ l : Fin (H + 1), truncateTorusHk (Nat.zero_le _) (u (i, l) tp) =
    -∑ l : Fin (H + 1), truncateTorusHk (E := h i) (Nat.zero_le (K (i, l)))
      (u (i, l) tp - truncateTorusHk (le_max_right Mout (K (i, l))) (jo (i, l))) := by
  rw [map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_sub, neg_sub]
  rfl

variable [DecidableEq ι] {H : ℕ}

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Minus a sum of `H + 1` order-zero families, each of mass norm at most `B`. -/
theorem neg_sum_bound (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Z : Fin (H + 1) → ∀ i, TorusHk 0 (h i)) {B : ℝ}
    (hZ : ∀ l, Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun i => (Z l i).val)) ≤ B) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
      (fun i => ((-(∑ l, Z l)) i).val)) ≤ ((H : ℝ) + 1) * B := by
  rw [sqrt_massNormSq_neg _ 1 π hπ]
  refine (sqrt_massNormSq_sum_le (fun _ => 0) 1 π hπ Finset.univ _).trans ?_
  refine (Finset.sum_le_sum fun l _ => hZ l).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring



/-- The joint error of copy `l`, at order zero. -/
def gateErrSlice {H : ℕ} (K : ι × Fin (H + 1) → ℕ) (Mout : ℕ)
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1),
      TorusHk 0 (h u.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1)) (tp : ℝ)
    (f : ∀ v : ι × Fin (H + 1), TorusHk (K v) (h v.1))
    (u : ∀ v : ι × Fin (H + 1), ℝ → TorusHk (K v) (h v.1)) (l : Fin (H + 1)) (i : ι) :
    TorusHk 0 (h i) :=
  truncateTorusHk (E := h i) (Nat.zero_le (K (i, l)))
    (u (i, l) tp - truncateTorusHk (le_max_right Mout (K (i, l)))
      (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg
        (fun v => truncateTorusHk (Nat.zero_le _) (f v)) (i, l)))

omit [DecidableEq ι] in
/-- The copied-family error: the readout of the joint model of the buffered datum is within
`(H + 1)` times the joint error bound (`IsJointError`) of the readout of the chain solution
(order zero). -/
theorem readout_error_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι × Fin (H + 1) → ℕ)
    (Mout D : ℕ) (ν tS tp ρs ρold E Pacc CP : ℝ) (b : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι × Fin (H + 1)) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i'.1)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i.1)))
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1),
      TorusHk 0 (h u.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (hjerr : IsJointError (h := fun v : ι × Fin (H + 1) => h v.1) (fun v => π v.1) K Mout H D
      ν tS tp ρs ρold E Pacc CP b A Pd Pg)
    (f : ∀ v : ι × Fin (H + 1), TorusHk (K v) (h v.1)) (Fv : ι × Fin (H + 1) → ℝ)
    (hf : ∀ v, torusHkNorm ρold (le_refl (K v)) (f v) ≤ Fv v)
    (u : ∀ v : ι × Fin (H + 1), ℝ → TorusHk (K v) (h v.1))
    (w : ∀ v : ι × Fin (H + 1), ℝ → TorusHk (K v + 1) (h v.1))
    (hsol : IsCoupledWeakSolutionTorus ν tS tp b D K A f (fun _ _ => 0) (fun _ _ => 0) u w) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun i =>
      (truncateTorusHk (Nat.zero_le Mout)
        (readout K Mout Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v)) i) -
        plainReadout K u tp i).val)) ≤
      ((H : ℝ) + 1) * (CP * E ^ Pacc * Real.sqrt (∑ v, (π v.1)⁻¹ * Fv v ^ 2)) := by
  classical
  have hslice : ∀ l : Fin (H + 1), Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
      (fun i => (gateErrSlice K Mout Pd Pg tp f u l i).val)) ≤
      CP * E ^ Pacc * Real.sqrt (∑ v, (π v.1)⁻¹ * Fv v ^ 2) := by
    intro l
    have h1 := massNormSq_slice_le (h := h) (fun _ : ι × Fin (H + 1) => 0) 1 π hπ
      (fun v => truncateTorusHk (Nat.zero_le _)
        (u v tp - truncateTorusHk (le_max_right Mout (K v))
          (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg
            (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v))) l
    have h2 := EntryTerminal.Ingredients.massNormSq_trunc0_le
      (h := fun v : ι × Fin (H + 1) => h v.1) (fun v => π v.1) (fun v => hπ v.1) K ρs
      (fun v => u v tp - truncateTorusHk (le_max_right Mout (K v))
          (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg
            (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v))
    have h3 := hjerr f Fv hf u w hsol
    exact (Real.sqrt_le_sqrt (h1.trans h2)).trans h3
  have hdiff : (fun i => truncateTorusHk (Nat.zero_le Mout)
        (readout K Mout Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v)) i) -
        plainReadout K u tp i) = -(∑ l, gateErrSlice K Mout Pd Pg tp f u l) := by
    funext i
    have key := readout_sub_plain_eq K Mout tp
      (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg
        (fun v => truncateTorusHk (Nat.zero_le _) (f v))) u i
    rw [Pi.neg_apply, Finset.sum_apply]
    exact key
  exact (congrArg (fun F : ∀ i, TorusHk 0 (h i) =>
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun i => (F i).val))) hdiff).trans_le
    (neg_sum_bound π hπ _ hslice)

end CopyJoint
end

/-! The enhanced-jet bound of the readout of the copied family: the joint model clause for
the chain, the Schur bounds of its envelope and the datum bound give the mass-weighted jet
norm of the readout at any positive radius, with a constant that does not depend on the
datum. The copy count `H + 1` is the fixed depth.

The degenerate cases are included: `H = 0` is the single-family model bound; an empty component type
and the zero datum give zero on both sides. -/

section
namespace CopyJoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] {D : ℕ} {Part : Type*} {Ctx : Part → Type*} {H : ℕ}

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- A sum of `H + 1` families of order `N`, each of mass norm at most `B`. -/
theorem sum_bound (N : ℕ) (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (Z : Fin (H + 1) → ∀ i, TorusHk N (h i)) {B : ℝ}
    (hZ : ∀ l, Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π
      (fun i => (Z l i).val)) ≤ B) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => N) ρ π
      (fun i => ((∑ l, Z l) i).val)) ≤ ((H : ℝ) + 1) * B := by
  refine (sqrt_massNormSq_sum_le (fun _ => N) ρ π hπ Finset.univ _).trans ?_
  refine (Finset.sum_le_sum fun l _ => hZ l).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **The jet norm of the copied readout.** -/
theorem readout_jet_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι × Fin (H + 1) → ℕ) (Mout : ℕ)
    (F : ChartedFamily (ι × Fin (H + 1)) (fun v => h v.1) D Part Ctx)
    (A : Matrix (ι × Fin (H + 1)) (ι × Fin (H + 1)) ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (Θ E Pacc ρm C CP : ℝ)
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1),
      TorusHk 0 (h u.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (hjm : IsJointModel (h := fun v : ι × Fin (H + 1) => h v.1) (fun v => π v.1) K Mout H F A
      Θ E Pacc ρm C CP Pd Pg) {S : ℝ}
    (hrow : ∀ v, ∑ u, Real.sqrt (π u.1 / π v.1) * A v u ≤ S)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u.1 / π v.1) * A v u ≤ S) (hS : 0 ≤ S)
    {ρ : ℝ} (hρ : 0 < ρ) (hρm : 0 < ρm)
    (f : ∀ v : ι × Fin (H + 1), TorusHk (K v) (h v.1)) (Fv : ι × Fin (H + 1) → ℝ) {ρold : ℝ}
    (hf : ∀ v, torusHkNorm ρold (le_refl (K v)) (f v) ≤ Fv v) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => Mout) ρ π (fun i =>
      (readout K Mout Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v)) i).val)) ≤
      ((H : ℝ) + 1) * (CycleComparison.Reconstruction.jointModelConst C S H Mout (ρ / ρm) *
        Real.sqrt (∑ v, (π v.1)⁻¹ * Fv v ^ 2)) := by
  classical
  have hπ' : ∀ v : ι × Fin (H + 1), 0 < π v.1 := fun v => hπ v.1
  have hN : ∀ v : ι × Fin (H + 1), Mout ≤ max Mout (K v) := fun v => le_max_left _ _
  have hchain := CycleComparison.Reconstruction.jointModel_massNormSq_le (h := fun v : ι × Fin (H + 1) => h v.1)
    (fun v => π v.1) hπ' K Mout H F A hA Θ E Pacc ρm C CP Pd Pg hjm hrow hcol hS hρ hρm
    (le_refl Mout) hN f Fv hf
  have hslice : ∀ l : Fin (H + 1), Real.sqrt (massNormSq (E := h) (K := fun _ => Mout) ρ π
      (fun i => (truncateTorusHk (E := h i) (le_max_left Mout (K (i, l)))
        (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg
          (fun v => truncateTorusHk (Nat.zero_le _) (f v)) (i, l))).val)) ≤
      CycleComparison.Reconstruction.jointModelConst C S H Mout (ρ / ρm) *
        Real.sqrt (∑ v, (π v.1)⁻¹ * Fv v ^ 2) := fun l =>
    (Real.sqrt_le_sqrt (massNormSq_slice_le (h := h) (fun _ : ι × Fin (H + 1) => Mout) ρ π hπ
      (fun v => truncateTorusHk (hN v) (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1)
        K Mout H Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v)) v)) l)).trans hchain
  have hsum := sum_bound Mout ρ π hπ (fun l i => truncateTorusHk (E := h i)
    (le_max_left Mout (K (i, l)))
    (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg
      (fun v => truncateTorusHk (Nat.zero_le _) (f v)) (i, l))) hslice
  have hread : (fun i => readout K Mout Pd Pg (fun v => truncateTorusHk (Nat.zero_le _) (f v)) i) =
      ∑ l : Fin (H + 1), (fun i => truncateTorusHk (E := h i) (le_max_left Mout (K (i, l)))
        (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg
          (fun v => truncateTorusHk (Nat.zero_le _) (f v)) (i, l))) := by
    funext i
    rw [Finset.sum_apply]
    rfl
  exact (congrArg (fun F : ∀ i, TorusHk Mout (h i) =>
    Real.sqrt (massNormSq (E := h) (K := fun _ => Mout) ρ π (fun i => (F i).val))) hread).trans_le
    hsum

end CopyJoint
end

/-! Constant vectors are fixed by the readout of the copied family: the jets of a
finite sum of torus elements are the sums of the jets, the jets of a truncation are the
jets at the same index, and the zero copies carry the constant zero.

The degenerate cases are included: `H = 0`, an empty component type and a zero constant use the same
formulas. -/

section
namespace CopyJoint

section Jets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem torusHk_jet_add_ae (x y : TorusHk K E) (a : JetIndex2 K) :
    (x + y).toFunction.jet a =ᵐ[volume.restrict unitCube]
      fun z => x.toFunction.jet a z + y.toFunction.jet a z := by
  have h1 := periodicJetRepresentative_ae (x + y).val a
  have h2 := periodicJetRepresentative_ae x.val a
  have h3 := periodicJetRepresentative_ae y.val a
  have h4 := Lp.coeFn_add (x.val a) (y.val a)
  filter_upwards [h1, h2, h3, h4] with z e1 e2 e3 e4
  change periodicJetRepresentative (x + y).val a z = periodicJetRepresentative x.val a z +
    periodicJetRepresentative y.val a z
  rw [e1, e2, e3]
  exact e4

theorem torusHk_jet_zero_ae (a : JetIndex2 K) :
    (0 : TorusHk K E).toFunction.jet a =ᵐ[volume.restrict unitCube] fun _ => 0 := by
  have h1 := periodicJetRepresentative_ae (0 : TorusHk K E).val a
  have h4 := Lp.coeFn_zero E 2 (volume.restrict unitCube)
  filter_upwards [h1, h4] with z e1 e4
  change periodicJetRepresentative (0 : TorusHk K E).val a z = 0
  rw [e1]
  exact e4

theorem torusHk_jet_sum_ae {α : Type*} (s : Finset α) (X : α → TorusHk K E) (a : JetIndex2 K) :
    (∑ l ∈ s, X l).toFunction.jet a =ᵐ[volume.restrict unitCube]
      fun z => ∑ l ∈ s, (X l).toFunction.jet a z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using torusHk_jet_zero_ae (E := E) a
  | insert l s hl ih =>
    rw [Finset.sum_insert hl]
    filter_upwards [torusHk_jet_add_ae (X l) (∑ l ∈ s, X l) a, ih] with z e1 e2
    rw [e1, e2, Finset.sum_insert hl]

end Jets

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {H : ℕ}

/-- The jets at the value index of the readout are the sum of the copies' constants. -/
theorem readout_const (K : ι × Fin (H + 1) → ℕ) (Mout : ℕ)
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1),
      TorusHk 0 (h u.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (x : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1)) (c : ∀ v : ι × Fin (H + 1), h v.1)
    (hconst : ∀ v, (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg x
      v).toFunction.jet (valueIndex2 (max Mout (K v)))
      =ᵐ[volume.restrict unitCube] fun _ => c v) (i : ι) :
    (readout K Mout Pd Pg x i).toFunction.jet (valueIndex2 Mout)
      =ᵐ[volume.restrict unitCube] fun _ => ∑ l : Fin (H + 1), c (i, l) := by
  have hsum := torusHk_jet_sum_ae (E := h i) Finset.univ (fun l : Fin (H + 1) =>
    truncateTorusHk (E := h i) (le_max_left Mout (K (i, l)))
      (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg x (i, l)))
    (valueIndex2 Mout)
  have hl : ∀ l : Fin (H + 1), (truncateTorusHk (E := h i) (le_max_left Mout (K (i, l)))
      (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg x
        (i, l))).toFunction.jet (valueIndex2 Mout)
      =ᵐ[volume.restrict unitCube] fun _ => c (i, l) := fun l =>
    (AVRegularity.KernelEnergy.truncateTorusHk_toFunction_jet_ae (le_max_left Mout (K (i, l))) _ (valueIndex2 Mout)).trans
      (hconst (i, l))
  filter_upwards [hsum, ae_all_iff.mpr hl] with z e1 e2
  exact e1.trans (Finset.sum_congr rfl fun l _ => e2 l)
/-- The constant-vector clause of the joint model, for the chain. -/
def JointConstClause (K : ι × Fin (H + 1) → ℕ) (Mout : ℕ)
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1),
      TorusHk 0 (h u.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1)) : Prop :=
  ∀ (x : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1)) (c : ∀ v : ι × Fin (H + 1), h v.1),
    (∀ v, (x v).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun _ => c v) →
    ∀ v, (jointOperator (h := fun v : ι × Fin (H + 1) => h v.1) K Mout H Pd Pg x
      v).toFunction.jet (valueIndex2 (max Mout (K v)))
      =ᵐ[volume.restrict unitCube] fun _ => c v

/-- **Constants are fixed.** The buffered datum placed in copy zero, with zero in every new
copy, has the readout with the same constant value. -/
theorem readout_const_of_initial (K : ι × Fin (H + 1) → ℕ) (Mout : ℕ)
    (Pd : ∀ v : ι × Fin (H + 1), TorusHk 0 (h v.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (Pg : ℕ → ∀ v u : ι × Fin (H + 1),
      TorusHk 0 (h u.1) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v.1))
    (hJ : JointConstClause K Mout Pd Pg) (B : ∀ i, TorusHk (K (i, 0)) (h i)) (cv : ∀ i, h i)
    (hB : ∀ i, (truncateTorusHk (Nat.zero_le _) (B i)).toFunction.jet (valueIndex2 0)
      =ᵐ[volume.restrict unitCube] fun _ => cv i) (i : ι) :
    (readout K Mout Pd Pg
      (fun v => truncateTorusHk (Nat.zero_le _) (preparationNeutralInitial H K B v)) i
      ).toFunction.jet (valueIndex2 Mout)
      =ᵐ[volume.restrict unitCube] fun _ => cv i := by
  classical
  have hx : ∀ v : ι × Fin (H + 1),
      (truncateTorusHk (Nat.zero_le _) (preparationNeutralInitial H K B v)).toFunction.jet
        (valueIndex2 0) =ᵐ[volume.restrict unitCube]
      fun _ => if v.2 = 0 then cv v.1 else 0 := by
    rintro ⟨j, l⟩
    by_cases hl : l = 0
    · subst hl
      simp only [ite_true]
      rw [preparation_neutral_initial_zero_copy]
      exact hB j
    · simp only [hl, ite_false]
      rw [preparation_neutral_initial_positive_copy H K B (j, l) hl, ContinuousLinearMap.map_zero]
      exact torusHk_jet_zero_ae _
  have key := readout_const K Mout Pd Pg _ _ (hJ _ _ hx) i
  refine key.trans (Filter.Eventually.of_forall fun z => ?_)
  simp

end CopyJoint
end

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
