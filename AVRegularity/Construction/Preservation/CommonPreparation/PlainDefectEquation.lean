-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.CopyJointConst
import AVRegularity.EntryWeakAssembly.PairedForcingCostSchur
import AVRegularity.CycleComparison.Coarse.Defect.Final
import AVRegularity.CycleComparison.Error.WeakSolution

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Recover the original positive envelope from one consecutive copy edge,
and restrict a sampled envelope without introducing a new window price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The 1 -> 0 copy edge retains each original positive identity exactly once. -/
theorem source_pointwise_of_copies (F : ChartedFamily ι h D P Ctx)
    (H : ℕ) (hH : 1 ≤ H) (W : Set ℝ) (π : ι → ℝ) (K : ι → ℕ)
    (ν e E ρ : ℝ) (C : ℕ → ℝ) (J : ℕ) (A : ι → ι → ℝ)
    (hc : IsPointwiseMolecularEnvelope (preparationNeutralChain F H) (fun v => π v.1)
      (fun v => K v.1) (ChartedFamily.Domain.onWindow (preparationNeutralChain F H) W)
      ν e E ρ C J (fun v u => Real.sqrt (π u.1 / π v.1) * preparationNeutralMajorant A H v u)) :
    IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W)
      ν e E ρ C J (fun v u => Real.sqrt (π u / π v) * A v u) := by
  classical
  let l₁ : Fin (H + 1) := ⟨1, by omega⟩
  let l₀ : Fin (H + 1) := ⟨0, Nat.succ_pos H⟩
  have hedge : l₁.val = l₀.val + 1 := rfl
  constructor
  · intro p c v u γ d I tY htY z
    exact hc.1 p c (v, l₁) (u, l₀) ⟨γ, hedge⟩ d I tY htY z
  · intro v u j hj
    let term (γ : F.Γ v u) : ℝ≥0∞ := ENNReal.ofReal ‖(F.identity v u γ).map‖ *
      ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        pointwiseMolecularJet ρ e (K v) j
          (fun z : F.Index => ChartedFamily.Domain.onWindow F W z.1 z.2)
          (fun z => F.dimFlux ν e E z.1 z.2 v u γ d I) *
          (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
          ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))
    have hh := hc.2 (v, l₁) (u, l₀) j hj
    change ENNReal.ofReal (Real.sqrt (π u / π v)) *
      (∑ γ : (preparationNeutralChain F H).Γ (v, l₁) (u, l₀), term γ.val) ≤
      ENNReal.ofReal (C j * (E ^ j)⁻¹ * (Real.sqrt (π u / π v) * A v u)) at hh
    have he := Fintype.sum_equiv (preparationNeutralIdentityEquiv F H (v, l₁) (u, l₀) hedge)
      (fun γ => term γ.val) term (fun _ => rfl)
    rw [he] at hh
    exact hh

/-- Time restriction retains the same positive sampled constant. -/
theorem source_sampled_restrict (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (actual : ∀ p, Ctx p)
    (a b c d ν e E ρ C : ℝ) (B : ι → ι → ℝ)
    (hsub : Set.Icc a b ⊆ Set.Icc c d)
    (hs : IsSampledEnvelope F π K actual c d ν e E ρ C B) :
    IsSampledEnvelope F π K actual a b ν e E ρ C B := by
  refine ⟨fun v u γ k t ht => hs.1 v u γ k t (hsub ht), ?_⟩
  intro v u
  apply le_trans ?_ (hs.2 v u)
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply Finset.sum_le_sum
  intro γ _
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (CycleJointProofs.coefficientSeminorm_time_mono ρ (K v) a b c d hsub _) zero_le) zero_le

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.Construction.KernelDefect
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The physical plain-source rows, with their original component and identity
indices. Positive constituent prices are summed before the two Schur tests.
The actual rough higher input retains its gradient reserve.

The degenerate cases are included: empty component types and empty identity sets give empty sums;
one component, D=2, identity geometry and an edgeless seed use the same bound.
L=0 gives boundedness and width=rho gives moment ratio one. No mass is changed
and no component-count constant occurs. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type}
  [∀ i j α, NormedAddCommGroup (G i j α)] [∀ i j α, InnerProductSpace ℝ (G i j α)]
  [∀ i j α, FiniteDimensional ℝ (G i j α)] [∀ i j α, MeasurableSpace (G i j α)]
  [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)]

/-- The actual coefficients and kernels in a plain-source row. A constituent
index may include both the identity and its differential order. Each
constituent retains its actual kernel, including seed/fresh mixtures; the
shared moment constant is uniform over all admissible orders. -/
structure PreparationPlainRowData (h : ι → Type)
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    (G : ∀ i j, Γ i j → Type)
    [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] where
  φ : Vec 2 → ℝ
  integrable : Integrable φ
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ
  nonneg : ∀ z, 0 ≤ φ z
  mass : ∫ z, φ z = 1
  support : Function.support φ ⊆ Analysis.Convolution.closedEuclideanUnitBall
  ρ : ℝ
  radius_pos : 0 < ρ
  a : ℝ
  b : ℝ
  time_order : a ≤ b
  L : ℕ
  matrix_bound : ℝ
  K : ι → ℕ
  m : ∀ i j, Γ i j → ℕ
  reserve : ∀ i j α, m i j α + L ≤ K j
  coefficient : ∀ i j α, PreparationPlainFluxCoefficient ρ a b (m i j α) (h j) (G i j α) (h i)
  measurable : ∀ i j α,
    Measurable (fun p : Set.Icc a b × Vec 2 => (coefficient i j α).B p.1 p.2)
  kernel : ∀ i j, Γ i j → KernelSpec
  admissible : ∀ i j α, (kernel i j α).IsAdmissible matrix_bound L
  width_pos : ∀ i j α, 0 < (kernel i j α).width

namespace PreparationPlainRowData
variable (P : PreparationPlainRowData h G)

/-- One actual flux constituent, from the appropriate truncation of its source. -/
def term (i j : ι) (α : Γ i j) (t : ℝ) (ht : t ∈ Set.Icc P.a P.b)
    (u : TorusHk (P.K j + 1) (h j)) :
    TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)) :=
  preparationPlainDefectFlux (L := P.L) (φ₀ := P.φ) (P.coefficient i j α) P.radius_pos
    P.integrable (P.kernel i j α) t ht
    (truncateTorusHk (Nat.add_le_add_right (P.reserve i j α) 1) u)

/-- The row sum is taken in the physical Sobolev carrier. -/
def flux (i : ι) (t : ℝ) (ht : t ∈ Set.Icc P.a P.b)
    (u : ∀ j, TorusHk (P.K j + 1) (h j)) :
    TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ∑ j, ∑ α, P.term i j α t ht (u j)

/-- The literal positive price of a single constituent. -/
def termPrice (i j : ι) (α : Γ i j) : ℝ :=
  (coefficientSeminorm P.ρ 0 P.a P.b (P.coefficient i j α).B).toReal *
    (preparationPlainDefectConstant P.φ P.matrix_bound (P.m i j α) P.L *
      ((P.kernel i j α).width / P.ρ) ^ P.L / P.ρ ^ (P.m i j α)) *
    ‖(P.coefficient i j α).C‖

/-- Sum the positive constituent prices without squaring the identity count. -/
def price (i j : ι) : ℝ := ∑ α, P.termPrice i j α

/-- The finite undamped price at the molecular radius, with the factorial
shift of the true input reserve. The width gain is kept separate. -/
def basePrice (i j : ι) : ℝ := ∑ α,
  (coefficientSeminorm P.ρ 0 P.a P.b (P.coefficient i j α).B).toReal *
    preparationPlainDefectConstant P.φ P.matrix_bound (P.m i j α) P.L /
      P.ρ ^ (P.m i j α) * ‖(P.coefficient i j α).C‖

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)] in
/-- A common width ratio is extracted before any component or mass sum. -/
theorem price_gain (q : ℝ)
    (hw : ∀ i j α, (P.kernel i j α).width ≤ q * P.ρ) (i j : ι) :
    P.price i j ≤ q ^ P.L * P.basePrice i j := by
  unfold price basePrice
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  have hρ := P.radius_pos
  have hr := P.width_pos i j α
  have hc := kdMomentConst_nonneg P.φ (kdUniformOrder P.L) P.L (abs_nonneg P.matrix_bound)
  have hpow := pow_le_pow_left₀ (div_nonneg hr.le hρ.le)
    ((div_le_iff₀ hρ).mpr (hw i j α)) P.L
  have hfactor : 0 ≤ (coefficientSeminorm P.ρ 0 P.a P.b (P.coefficient i j α).B).toReal *
      preparationPlainDefectConstant P.φ P.matrix_bound (P.m i j α) P.L /
        P.ρ ^ (P.m i j α) * ‖(P.coefficient i j α).C‖ := by
    unfold preparationPlainDefectConstant
    positivity
  calc
    _ = ((coefficientSeminorm P.ρ 0 P.a P.b (P.coefficient i j α).B).toReal *
        preparationPlainDefectConstant P.φ P.matrix_bound (P.m i j α) P.L /
          P.ρ ^ (P.m i j α) * ‖(P.coefficient i j α).C‖) *
            ((P.kernel i j α).width / P.ρ) ^ P.L := by unfold termPrice; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hpow hfactor).trans_eq (mul_comm _ _)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)] in
/-- The same width gain passes through both weighted Schur tests. -/
theorem schur_gain (π : ι → ℝ) (q S : ℝ) (hq : 0 ≤ q)
    (hw : ∀ i j α, (P.kernel i j α).width ≤ q * P.ρ)
    (hs : SchurBound S (fun i j => Real.sqrt (π j / π i) * P.basePrice i j)) :
    SchurBound (q ^ P.L * S) (fun i j => Real.sqrt (π j / π i) * P.price i j) := by
  have hp (i j : ι) : Real.sqrt (π j / π i) * P.price i j ≤
      q ^ P.L * (Real.sqrt (π j / π i) * P.basePrice i j) :=
    (mul_le_mul_of_nonneg_left (P.price_gain q hw i j) (Real.sqrt_nonneg _)).trans_eq (by ring)
  constructor
  · intro i
    calc
      _ ≤ ∑ j, q ^ P.L * (Real.sqrt (π j / π i) * P.basePrice i j) :=
        Finset.sum_le_sum fun j _ => hp i j
      _ = q ^ P.L * ∑ j, Real.sqrt (π j / π i) * P.basePrice i j := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hs.1 i) (pow_nonneg hq _)
  · intro j
    calc
      _ ≤ ∑ i, q ^ P.L * (Real.sqrt (π j / π i) * P.basePrice i j) :=
        Finset.sum_le_sum fun i _ => hp i j
      _ = q ^ P.L * ∑ i, Real.sqrt (π j / π i) * P.basePrice i j := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hs.2 j) (pow_nonneg hq _)

omit [∀ i, MeasurableSpace (h i)] [∀ i j α, MeasurableSpace (G i j α)]
  [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i j, Fintype (Γ i j)]
  [∀ i j α, FiniteDimensional ℝ (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] in
theorem termPrice_nonneg (i j : ι) (α : Γ i j) : 0 ≤ P.termPrice i j α := by
  have hρ := P.radius_pos
  have hr := P.width_pos i j α
  have hc := kdMomentConst_nonneg P.φ (kdUniformOrder P.L) P.L (abs_nonneg P.matrix_bound)
  unfold termPrice preparationPlainDefectConstant
  positivity

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)] in
theorem price_nonneg (i j : ι) : 0 ≤ P.price i j :=
  Finset.sum_nonneg fun α _ => P.termPrice_nonneg i j α

omit [Fintype ι] [∀ i j, Fintype (Γ i j)] in
/-- The rough constituent estimate uses only its own high reserve, followed by
monotonicity of the source's full gradient energy. -/
theorem term_root_le (i j : ι) (α : Γ i j) (t : ℝ) (ht : t ∈ Set.Icc P.a P.b)
    (u : TorusHk (P.K j + 1) (h j)) :
    Real.sqrt (factorialNormSq P.ρ (P.term i j α t ht u).val) ≤
      P.termPrice i j α * Real.sqrt (gradFactorialNormSq P.ρ u.val) := by
  have hb := (plain_defect_flux (E := h j) (G := G i j α) (H := h i)
    P.integrable P.smooth P.nonneg P.mass P.support (P.m i j α) P.L P.matrix_bound).2
      P.ρ P.a P.b P.radius_pos (P.coefficient i j α) (P.kernel i j α) t ht
      (P.admissible i j α) (P.width_pos i j α)
      (truncateTorusHk (Nat.add_le_add_right (P.reserve i j α) 1) u)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (FullLift.gradFactorialNormSq_truncate_le (P.reserve i j α) P.ρ u.val))
    (P.termPrice_nonneg i j α))

private theorem flux_val (i : ι) (t : ℝ) (ht : t ∈ Set.Icc P.a P.b)
    (u : ∀ j, TorusHk (P.K j + 1) (h j)) :
    (P.flux i t ht u).val = ∑ j, ∑ α, (P.term i j α t ht (u j)).val := by
  change (torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => h i)) 0).toSubmodule.subtype
    (∑ j, ∑ α, P.term i j α t ht (u j)) = _
  simp only [map_sum]
  rfl

private theorem row_root_le (i : ι) (t : ℝ) (ht : t ∈ Set.Icc P.a P.b)
    (u : ∀ j, TorusHk (P.K j + 1) (h j)) :
    Real.sqrt (factorialNormSq P.ρ (P.flux i t ht u).val) ≤
      ∑ j, P.price i j * Real.sqrt (gradFactorialNormSq P.ρ (u j).val) := by
  classical
  rw [P.flux_val]
  calc
    _ ≤ ∑ j, Real.sqrt (factorialNormSq P.ρ
      (∑ α, (P.term i j α t ht (u j)).val)) :=
        KernelEnergy.factorialNorm_root_sum_le _ _ _
    _ ≤ ∑ j, ∑ α, Real.sqrt (factorialNormSq P.ρ (P.term i j α t ht (u j)).val) :=
      Finset.sum_le_sum fun j _ => KernelEnergy.factorialNorm_root_sum_le _ _ _
    _ ≤ ∑ j, ∑ α, P.termPrice i j α *
        Real.sqrt (gradFactorialNormSq P.ρ (u j).val) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun α _ => P.term_root_le i j α t ht (u j)
    _ = _ := by simp only [price, Finset.sum_mul]

/-- Both weighted Schur sums control the actual row flux with no loss in the
number of components or constituents. The same flux works for every mass. -/
theorem mass_flux_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (θ : ℝ)
    (hschur : SchurBound θ (fun i j => Real.sqrt (π j / π i) * P.price i j))
    (t : ℝ) (ht : t ∈ Set.Icc P.a P.b) (u : ∀ j, TorusHk (P.K j + 1) (h j)) :
    massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => 0)
      P.ρ π (fun i => (P.flux i t ht u).val) ≤
        θ ^ 2 * massGradNormSq (E := h) (K := P.K) P.ρ π (fun j => (u j).val) := by
  let X : ι → ℝ := fun j => Real.sqrt ((π j)⁻¹ * gradFactorialNormSq P.ρ (u j).val)
  let Y : ι → ℝ := fun i => Real.sqrt ((π i)⁻¹ * factorialNormSq P.ρ (P.flux i t ht u).val)
  have hY (i : ι) : 0 ≤ Y i ∧ Y i ≤ 1 * ∑ j,
      (Real.sqrt (π j / π i) * P.price i j) * X j := by
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    dsimp only [Y]
    rw [Real.sqrt_mul (inv_nonneg.mpr (hπ i).le), one_mul]
    calc
      _ ≤ Real.sqrt ((π i)⁻¹) *
          ∑ j, P.price i j * Real.sqrt (gradFactorialNormSq P.ρ (u j).val) :=
        mul_le_mul_of_nonneg_left (P.row_root_le i t ht u) (Real.sqrt_nonneg _)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [X]
        calc
          _ = P.price i j * (Real.sqrt ((π i)⁻¹) *
              Real.sqrt (gradFactorialNormSq P.ρ (u j).val)) := by ring
          _ = P.price i j * (Real.sqrt (π j / π i) *
              Real.sqrt ((π j)⁻¹ * gradFactorialNormSq P.ρ (u j).val)) :=
            congrArg (P.price i j * ·)
              (WeakEntryProofs.pfcSchurRootProduct _ _ _ (hπ i) (hπ j)).symm
          _ = _ := by ring
  have hs := KernelEnergy.finiteRootSchur
    (fun i j => Real.sqrt (π j / π i) * P.price i j) X Y 1 θ zero_lt_one
    (fun i j => mul_nonneg (Real.sqrt_nonneg _) (P.price_nonneg i j)) hschur.1 hschur.2 hY
  have hx : (∑ j, X j ^ 2) = massGradNormSq (E := h) (K := P.K) P.ρ π
      (fun j => (u j).val) := by
    apply Finset.sum_congr rfl
    intro j _
    exact Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (hπ j).le)
      (KernelEnergy.torusCarrierGradFactorial_nonneg _ _ _))
  have hy : (∑ i, Y i ^ 2) = massNormSq
      (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => 0) P.ρ π
      (fun i => (P.flux i t ht u).val) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (hπ i).le) (factorialNormSq_nonneg _ _))
  rwa [hy, hx, one_mul] at hs

omit [Fintype ι] [∀ i j, Fintype (Γ i j)] in
/-- Measurability of one actual constituent with its own input reserve. -/
theorem term_stronglyMeasurable (i j : ι) (α : Γ i j)
    (u : ℝ → TorusHk (P.K j + 1) (h j)) (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun t : Set.Icc P.a P.b => P.term i j α t t.property (u t)) := by
  let V : ℝ → TorusHk (P.m i j α + P.L + 1) (h j) :=
    fun t => truncateTorusHk (Nat.add_le_add_right (P.reserve i j α) 1) (u t)
  have hV : StronglyMeasurable V :=
    (truncateTorusHk (Nat.add_le_add_right (P.reserve i j α) 1)).continuous.comp_stronglyMeasurable hu
  exact preparation_plain_defect_flux_stronglyMeasurable
    (E := h j) (G := G i j α) (H := h i) (ρ := P.ρ) (a := P.a) (b := P.b)
    (m := P.m i j α) (L := P.L) (φ₀ := P.φ) P.integrable P.smooth P.support
    (P.coefficient i j α) P.radius_pos (P.measurable i j α) (P.kernel i j α)
    (P.admissible i j α).1 (P.admissible i j α).2.1 V hV

/-- The actual row sum is strongly measurable on the window. -/
theorem flux_stronglyMeasurable (i : ι) (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j))
    (hu : ∀ j, StronglyMeasurable (u j)) :
    StronglyMeasurable (fun t : Set.Icc P.a P.b => P.flux i t t.property (fun j => u j t)) := by
  exact Finset.stronglyMeasurable_fun_sum _ fun j _ =>
    Finset.stronglyMeasurable_fun_sum _ fun α _ => P.term_stronglyMeasurable i j α (u j) (hu j)

/-- The actual raw constituent, retaining coefficient-after-kernel order. -/
def rawTerm (i j : ι) (α : Γ i j) (t : ℝ)
    (u : TorusHk (P.K j + 1) (h j)) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i) :=
  (P.coefficient i j α).B t x (WithLp.toLp 2 fun w : DerivativeWord2 (P.m i j α + 1) =>
    (((P.coefficient i j α).C.compLpL 2 (volume.restrict unitCube)
      (u.val ⟨⟨P.m i j α + 1, by have := P.reserve i j α; omega⟩, w⟩)) -
      (P.kernel i j α).op P.φ P.integrable t
        ((P.coefficient i j α).C.compLpL 2 (volume.restrict unitCube)
          (u.val ⟨⟨P.m i j α + 1, by have := P.reserve i j α; omega⟩, w⟩))) x)

/-- The raw row flux in its original component and constituent order. -/
def rawFlux (i : ι) (t : ℝ) (u : ∀ j, TorusHk (P.K j + 1) (h j)) (x : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h i) := ∑ j, ∑ α, P.rawTerm i j α t (u j) x

end PreparationPlainRowData
end

/-! The physical plain-source row flux is genuinely L2 in time, not merely a
formal Bochner integral. The same clamped flux is fixed before the masses.

The degenerate cases are included: empty families and empty rows give zero; singleton families, D=2,
identity geometry, zero data and edgeless seeds retain the same flux. A
one-point window has zero time measure. Clamping is used only outside the
solution window and leaves every value inside it unchanged. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type}
  [∀ i j α, NormedAddCommGroup (G i j α)] [∀ i j α, InnerProductSpace ℝ (G i j α)]
  [∀ i j α, FiniteDimensional ℝ (G i j α)] [∀ i j α, MeasurableSpace (G i j α)]
  [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)]

namespace PreparationPlainRowData
variable (P : PreparationPlainRowData h G)

/-- The physical flux on the window, clamped outside it. -/
def fluxTime (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j)) (i : ι) (t : ℝ) :
    TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)) :=
  P.flux i (Set.projIcc P.a P.b P.time_order t)
    (Set.projIcc P.a P.b P.time_order t).property
    (fun j => u j (Set.projIcc P.a P.b P.time_order t))

theorem fluxTime_eq (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j)) (i : ι)
    {t : ℝ} (ht : t ∈ Set.Icc P.a P.b) :
    P.fluxTime u i t = P.flux i t ht (fun j => u j t) := by
  unfold fluxTime
  have he : (Set.projIcc P.a P.b P.time_order t : ℝ) = t := by
    simp only [Set.projIcc_of_mem _ ht]
  simp only [he]

/-- An a.e. strongly measurable higher input produces an a.e. strongly
measurable actual row flux. -/
theorem fluxTime_aestronglyMeasurable (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j))
    (hu : ∀ j, AEStronglyMeasurable (u j) (volume.restrict (Set.Icc P.a P.b))) (i : ι) :
    AEStronglyMeasurable (P.fluxTime u i) (volume.restrict (Set.Icc P.a P.b)) := by
  let v : ∀ j, ℝ → TorusHk (P.K j + 1) (h j) := fun j => (hu j).mk (u j)
  have hv : ∀ j, StronglyMeasurable (v j) := fun j => (hu j).stronglyMeasurable_mk
  have hfull : StronglyMeasurable (P.fluxTime v i) :=
    (P.flux_stronglyMeasurable i v hv).comp_measurable
      (continuous_projIcc (h := P.time_order)).measurable
  have heq : ∀ᵐ t ∂volume.restrict (Set.Icc P.a P.b), ∀ j, u j t = v j t :=
    ae_all_iff.mpr fun j => (hu j).ae_eq_mk
  refine hfull.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc, heq] with t ht hvt
  rw [P.fluxTime_eq v i ht, P.fluxTime_eq u i ht]
  exact congrArg (P.flux i t ht) (funext fun j => (hvt j).symm)

private theorem zero_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (ρ : ℝ) (u : TorusHk 0 E) : ‖u‖ ^ 2 = factorialNormSq ρ u.val := by
  change ‖u.val‖ ^ 2 = _
  rw [jet_norm_sq_eq_sum]
  change (∑ j : Fin 1, derivativeNormSq u.val j) =
    ∑ j : Fin 1, factorialWeight ρ j.val * derivativeNormSq u.val j
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  simp only [factorialWeight, Fin.val_zero, Nat.mul_zero, pow_zero,
    Nat.factorial_zero, Nat.cast_one, one_pow, div_one, one_mul]

private theorem mass_flux_nonneg (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j)) (t : ℝ) :
    0 ≤ massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => 0)
      P.ρ π (fun i => (P.fluxTime u i t).val) :=
  Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.mpr (hπ i).le) (factorialNormSq_nonneg _ _)

/-- The time-integrated weighted flux estimate includes actual L2 membership
of every row. In particular, none of the integrals is being assigned zero by
lack of integrability. The input is its genuine higher gradient energy. -/
theorem fluxTime_energy (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (θ : ℝ)
    (hschur : SchurBound θ (fun i j => Real.sqrt (π j / π i) * P.price i j))
    (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j))
    (hu : ∀ j, AEStronglyMeasurable (u j) (volume.restrict (Set.Icc P.a P.b)))
    (hint : Integrable (fun t => massGradNormSq (E := h) (K := P.K) P.ρ π
      (fun j => (u j t).val)) (volume.restrict (Set.Icc P.a P.b))) :
    (∀ i, MemLp (P.fluxTime u i) 2 (volume.restrict (Set.Icc P.a P.b))) ∧
    Integrable (fun t => massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
      (K := fun _ => 0) P.ρ π (fun i => (P.fluxTime u i t).val))
      (volume.restrict (Set.Icc P.a P.b)) ∧
    (∫ t in Set.Icc P.a P.b, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i))
      (K := fun _ => 0) P.ρ π (fun i => (P.fluxTime u i t).val)) ≤
      θ ^ 2 * ∫ t in Set.Icc P.a P.b, massGradNormSq (E := h) (K := P.K) P.ρ π
        (fun j => (u j t).val) := by
  let Z : ℝ → ℝ := fun t => massNormSq
    (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => 0) P.ρ π
    (fun i => (P.fluxTime u i t).val)
  let X : ℝ → ℝ := fun t => massGradNormSq (E := h) (K := P.K) P.ρ π
    (fun j => (u j t).val)
  have hpt : ∀ᵐ t ∂volume.restrict (Set.Icc P.a P.b), Z t ≤ θ ^ 2 * X t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp only [Z, X]
    simp_rw [P.fluxTime_eq u _ ht]
    exact P.mass_flux_le π hπ θ hschur t ht (fun j => u j t)
  have hz : ∀ t, 0 ≤ Z t := P.mass_flux_nonneg π hπ u
  have hm : AEStronglyMeasurable Z (volume.restrict (Set.Icc P.a P.b)) :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      ((kd_continuous_factorialNormSq P.ρ).comp_aestronglyMeasurable
        (continuous_subtype_val.comp_aestronglyMeasurable
          (P.fluxTime_aestronglyMeasurable u hu i))).const_mul _
  have hzint : Integrable Z (volume.restrict (Set.Icc P.a P.b)) :=
    (hint.const_mul (θ ^ 2)).mono' hm (hpt.mono fun t ht => by
      rwa [Real.norm_of_nonneg (hz t)])
  refine ⟨?_, hzint, ?_⟩
  · intro i
    have hae := P.fluxTime_aestronglyMeasurable u hu i
    rw [memLp_two_iff_integrable_sq_norm hae]
    have hc : ∀ t, ‖P.fluxTime u i t‖ ^ 2 ≤ π i * Z t := by
      intro t
      rw [zero_norm_sq]
      have hs : (π i)⁻¹ * factorialNormSq P.ρ (P.fluxTime u i t).val ≤ Z t :=
        Finset.single_le_sum (f := fun j => (π j)⁻¹ * factorialNormSq P.ρ (P.fluxTime u j t).val)
          (fun j _ => mul_nonneg (inv_nonneg.mpr (hπ j).le) (factorialNormSq_nonneg _ _))
          (Finset.mem_univ i)
      have hmul := mul_le_mul_of_nonneg_left hs (hπ i).le
      rwa [← mul_assoc, mul_inv_cancel₀ (hπ i).ne', one_mul] at hmul
    exact (hzint.const_mul (π i)).mono' (hae.norm.pow 2)
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hc t)
  · calc
      ∫ t in Set.Icc P.a P.b, Z t ≤ ∫ t in Set.Icc P.a P.b, θ ^ 2 * X t :=
        integral_mono_ae hzint (hint.const_mul _) hpt
      _ = _ := integral_const_mul _ _

/-- The physical scalar response to the actual defect flux has the required
moment gain. The input's higher gradient energy and the zero initial trace
are retained; the flux integral is parenthesized explicitly. -/
theorem forced_energy {ν : ℝ} {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ}
    (hd : Providers.WeakGen.Comparison.TorusDriftData ν P.ρ P.a P.b v Kmax)
    (hν : 0 < ν) (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (q S : ℝ) (hq : 0 ≤ q)
    (hw : ∀ i j α, (P.kernel i j α).width ≤ q * P.ρ)
    (hs : SchurBound S (fun i j => Real.sqrt (π j / π i) * P.basePrice i j))
    (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j))
    (hu : ∀ j, AEStronglyMeasurable (u j) (volume.restrict (Set.Icc P.a P.b)))
    (hint : Integrable (fun t => massGradNormSq (E := h) (K := P.K) P.ρ π
      (fun j => (u j t).val)) (volume.restrict (Set.Icc P.a P.b)))
    {z : ∀ i, ℝ → TorusHk 0 (h i)} {w : ∀ i, ℝ → TorusHk 1 (h i)}
    (hz : ∀ i, Providers.WeakGen.Comparison.IsTorusForcedRow ν P.a P.b v 2 0 0
      (P.fluxTime u i) (fun _ => 0) (z i) (w i)) (t : ℝ) (ht : t ∈ Set.Icc P.a P.b) :
    massNormSq P.ρ π (fun i => (z i t).val) +
      ν / 2 * (∫ r in Set.Icc P.a P.b, massGradNormSq P.ρ π (fun i => (w i r).val)) ≤
      8 / ν * ((q ^ P.L * S) ^ 2 * ∫ r in Set.Icc P.a P.b,
        massGradNormSq (E := h) (K := P.K) P.ρ π (fun j => (u j r).val)) := by
  obtain ⟨hF, _, hbound⟩ := P.fluxTime_energy π hπ (q ^ P.L * S) (P.schur_gain π q S hq hw hs) u hu hint
  have he := preparation_scalar_family_energy hd P.time_order P.radius_pos hν
    (Nat.zero_le Kmax) π hπ hF hz t ht
  have he' : massNormSq P.ρ π (fun i => (z i t).val) +
      ν / 2 * (∫ r in Set.Icc P.a P.b, massGradNormSq P.ρ π (fun i => (w i r).val)) ≤
      8 / ν * (∫ r in Set.Icc P.a P.b, massNormSq
        (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := fun _ => 0) P.ρ π
          (fun i => (P.fluxTime u i r).val)) := by
    simpa only [CoupledEnergy.Variational.torusMassNormSq_zero (fun _ => 0) P.ρ π hπ,
      mul_zero, zero_add] using he
  exact he'.trans (mul_le_mul_of_nonneg_left hbound (div_nonneg (by norm_num) hν.le))

end PreparationPlainRowData
end

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.Construction.KernelDefect
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Exact source splitting for the plain insertion. The physical coefficient
is applied after the moving kernel. The regularized source takes only the
low gradient input; equality with the weak average follows from its value
class, rather than a classical representative.

The degenerate cases are included: m=0 is the D=2 source; L=0 is an exact identity without a
smallness claim. Zero and constant inputs retain their actual flux. Empty and singleton
families, identity geometry and an edgeless seed use the same finite sums.
The two scalar rows have the same datum, so their difference has zero datum. -/

variable {E G H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
  {ρ a b : ℝ} {m L : ℕ}

omit [FiniteDimensional ℝ E] in
/-- The actual unregularized source at output order zero. -/
def preparationPlainSourceFlux (F : PreparationPlainFluxCoefficient ρ a b m E G H)
    (hρ : 0 < ρ) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (u : TorusHk (m + L + 1) E) : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => H)) :=
  KernelEnergy.torusKernelFluxTerm (K := 0) (m := m) rfl ρ hρ a b F.B F.finite t ht
    (F.smooth t ht) (F.periodic t ht)
    (mapTorusHk F.C (truncateTorusHk (by omega : 0 + (m + 1) ≤ m + L + 1) u))

/-- The actual regularized source uses only the low gradient input. -/
def preparationRegularizedSourceFlux (F : PreparationPlainFluxCoefficient ρ a b m E G H)
    (hρ : 0 < ρ) {φ : Vec 2 → ℝ} (hφ : Integrable φ) (S : KernelSpec)
    (c : ℕ → ℝ) (r : ℝ)
    (hS : IsSpatialRegularizerTorus ρ 0 (m + 2) a b c r (S.op (E := G) φ hφ))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (u : TorusHk 1 E) :
    TorusHk 0 (PiLp 2 (fun _ : Fin 2 => H)) :=
  KernelEnergy.torusKernelFluxTerm (K := 0) (m := m) rfl ρ hρ a b F.B F.finite t ht
    (F.smooth t ht) (F.periodic t ht)
    (truncateTorusHk (by omega : 0 + (m + 1) ≤ 0 + (m + 2) - 1)
      (KernelEnergy.torusRegularizedInput ρ 0 (m + 2) (by omega) a b c r F.C
        (S.op (E := G) φ hφ) hS t ht u))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
private theorem preparation_flux_action_sub
    (B : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (m + 1) => G) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => H)) (hρ : 0 < ρ)
    (hB : coefficientSeminorm ρ 0 a b B ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hs : ContDiff ℝ (0 : ℕ) (B t)) (hp : IsZ2Periodic (B t))
    (u v : TorusHk (0 + (m + 1)) G) :
    KernelEnergy.torusKernelFluxTerm rfl ρ hρ a b B hB t ht hs hp (u - v) =
      KernelEnergy.torusKernelFluxTerm rfl ρ hρ a b B hB t ht hs hp u -
      KernelEnergy.torusKernelFluxTerm rfl ρ hρ a b B hB t ht hs hp v := by
  apply KernelEnergy.torusCarrier_eq_of_value_ae
  filter_upwards [KernelEnergy.torusKernelFluxTerm_base_ae rfl ρ hρ a b B hB t ht hs hp (u - v),
    KernelEnergy.torusKernelFluxTerm_base_ae rfl ρ hρ a b B hB t ht hs hp u,
    KernelEnergy.torusKernelFluxTerm_base_ae rfl ρ hρ a b B hB t ht hs hp v,
    CycleComparison.Coarse.jet_sub_ae u v,
    CycleComparison.Coarse.jet_sub_ae
      (KernelEnergy.torusKernelFluxTerm rfl ρ hρ a b B hB t ht hs hp u)
      (KernelEnergy.torusKernelFluxTerm rfl ρ hρ a b B hB t ht hs hp v)] with x hd hu hv hi ho
  rw [ho, hd, hu, hv, ← (B t x).map_sub]
  apply congrArg (B t x)
  apply PiLp.ext
  intro word
  exact hi _

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [CompleteSpace H] in
/-- Uniqueness of weak jets identifies the regularizer lift of the low
input with the actual moving average of the higher input. -/
theorem preparation_regularized_source_input
    (F : PreparationPlainFluxCoefficient ρ a b m E G H)
    {φ : Vec 2 → ℝ} (hφ : Integrable φ) (S : KernelSpec) (c : ℕ → ℝ) (r : ℝ)
    (hS : IsSpatialRegularizerTorus ρ 0 (m + 2) a b c r (S.op (E := G) φ hφ))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (u : TorusHk (m + L + 1) E) :
    truncateTorusHk (by omega : 0 + (m + 1) ≤ 0 + (m + 2) - 1)
      (KernelEnergy.torusRegularizedInput ρ 0 (m + 2) (by omega) a b c r F.C
        (S.op (E := G) φ hφ) hS t ht (truncateTorusHk (by omega : 1 ≤ m + L + 1) u)) =
    FullLift.kernelSpecWeakAverage φ hφ S t
      (mapTorusHk F.C (truncateTorusHk (by omega : 0 + (m + 1) ≤ m + L + 1) u)) := by
  apply TorusHk.ext_value
  have he := KernelEnergy.torusRegularizedInput_value ρ 0 (m + 2) (by omega) a b c r
    F.C (S.op (E := G) φ hφ) hS t ht (truncateTorusHk (by omega : 1 ≤ m + L + 1) u)
  change (KernelEnergy.torusRegularizedInput ρ 0 (m + 2) (by omega) a b c r F.C
    (S.op (E := G) φ hφ) hS t ht (truncateTorusHk (by omega : 1 ≤ m + L + 1) u)).val
      (valueIndex2 (0 + (m + 2) - 1)) = _
  rw [he, FullLift.kernelSpecWeakAverage_component, mapTorusHk_jet_eq_compLp]
  rfl

/-- The literal plain-minus-kernel source is precisely the already estimated
rough defect carrier, for the same higher input and its actual low gradient. -/
theorem preparation_plain_source_split
    (F : PreparationPlainFluxCoefficient ρ a b m E G H) (hρ : 0 < ρ)
    {φ : Vec 2 → ℝ} (hφ : Integrable φ) (S : KernelSpec) (c : ℕ → ℝ) (r : ℝ)
    (hS : IsSpatialRegularizerTorus ρ 0 (m + 2) a b c r (S.op (E := G) φ hφ))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (u : TorusHk (m + L + 1) E) :
    preparationPlainSourceFlux (L := L) F hρ t ht u -
      preparationRegularizedSourceFlux F hρ hφ S c r hS t ht
        (truncateTorusHk (by omega : 1 ≤ m + L + 1) u) =
      preparationPlainDefectFlux (L := L) (φ₀ := φ) F hρ hφ S t ht u := by
  unfold preparationPlainSourceFlux preparationRegularizedSourceFlux
  rw [preparation_regularized_source_input F hφ S c r hS t ht u]
  unfold preparationPlainDefectFlux kdRealization
  rw [preparation_flux_action_sub]
  rfl

section Rows
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type}
  [∀ i j α, NormedAddCommGroup (G i j α)] [∀ i j α, InnerProductSpace ℝ (G i j α)]
  [∀ i j α, FiniteDimensional ℝ (G i j α)] [∀ i j α, MeasurableSpace (G i j α)]
  [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)]

/-- The spatial regularizers used by the actual kernel response of each
constituent. The defect estimate itself did not need these hypotheses. -/
structure PreparationPlainRowRegularizers (P : PreparationPlainRowData h G) where
  c : ∀ i j, Γ i j → ℕ → ℝ
  r : ∀ i j, Γ i j → ℝ
  regular : ∀ i j α, IsSpatialRegularizerTorus P.ρ 0 (P.m i j α + 2) P.a P.b
    (c i j α) (r i j α) ((P.kernel i j α).op (E := G i j α) P.φ P.integrable)

namespace PreparationPlainRowData
variable (P : PreparationPlainRowData h G) (R : PreparationPlainRowRegularizers P)

/-- The actual unregularized row forcing of a higher plain layer. -/
def plainSourceFluxTime (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j))
    (i : ι) (t : ℝ) : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)) :=
  let t' := Set.projIcc P.a P.b P.time_order t
  ∑ j, ∑ α, preparationPlainSourceFlux (L := P.L) (P.coefficient i j α) P.radius_pos
    t' t'.property (truncateTorusHk (Nat.add_le_add_right (P.reserve i j α) 1) (u j t'))

/-- The actual kernel row forcing reads only the low gradient of the preceding layer. -/
def regularizedSourceFluxTime (u : ∀ j, ℝ → TorusHk 1 (h j))
    (i : ι) (t : ℝ) : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)) :=
  let t' := Set.projIcc P.a P.b P.time_order t
  ∑ j, ∑ α, preparationRegularizedSourceFlux (P.coefficient i j α) P.radius_pos
    P.integrable (P.kernel i j α) (R.c i j α) (R.r i j α) (R.regular i j α)
    t' t'.property (u j t')

/-- Subtraction of the actual two source rows gives the estimated defect
carrier exactly, even for the clamped values outside the window. -/
theorem source_flux_split (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j)) (i : ι) (t : ℝ) :
    P.plainSourceFluxTime u i t -
      P.regularizedSourceFluxTime R
        (fun j s => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (P.K j))) (u j s)) i t =
      P.fluxTime u i t := by
  unfold plainSourceFluxTime regularizedSourceFluxTime fluxTime flux
  dsimp only
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro α _
  have he := preparation_plain_source_split (L := P.L) (P.coefficient i j α) P.radius_pos
    P.integrable (P.kernel i j α) (R.c i j α) (R.r i j α) (R.regular i j α)
    (Set.projIcc P.a P.b P.time_order t) (Set.projIcc P.a P.b P.time_order t).property
    (truncateTorusHk (Nat.add_le_add_right (P.reserve i j α) 1)
      (u j (Set.projIcc P.a P.b P.time_order t)))
  exact he

/-- The difference between a plain row and the scalar kernel response to
its preceding layer is the zero-data forced defect row. All weak-integral
clauses are inherited from weak-solution subtraction. -/
theorem source_difference_row {ν : ℝ} {v : ℝ → Vec 2 → Vec 2}
    (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j)) (i : ι) (f : TorusHk 0 (h i))
    {zp zk : ℝ → TorusHk 0 (h i)} {wp wk : ℝ → TorusHk 1 (h i)}
    (hp : IsTorusForcedRow ν P.a P.b v 2 0 f (P.plainSourceFluxTime u i)
      (fun _ => 0) zp wp)
    (hk : IsTorusForcedRow ν P.a P.b v 2 0 f
      (P.regularizedSourceFluxTime R
        (fun j s => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (P.K j))) (u j s)) i)
      (fun _ => 0) zk wk) :
    IsTorusForcedRow ν P.a P.b v 2 0 0 (P.fluxTime u i) (fun _ => 0)
      (fun t => zp t - zk t) (fun t => wp t - wk t) := by
  have hs := CycleComparison.Error.isCoupledWeakSolutionTorus_sub hp hk
  change IsTorusForcedRow ν P.a P.b v 2 0 (f - f)
    (fun t => P.plainSourceFluxTime u i t - P.regularizedSourceFluxTime R
      (fun j s => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (P.K j))) (u j s)) i t)
    (fun _ => 0 - 0) (fun t => zp t - zk t) (fun t => wp t - wk t) at hs
  have hflux := funext (P.source_flux_split R u i)
  simpa only [sub_self, hflux] using hs

end PreparationPlainRowData
end Rows

end AVRegularity.Construction.Preservation.CommonPreparation
end
