-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.PlainDefectEquation
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Instantiate the rough source rows with the actual native kernel operator.
The constituent index includes the differential order. Seed and fresh kernels
keep their own moment orders and are never replaced by a common kernel.

The degenerate cases are included: D=2 has exactly its order-two constituent; empty component and
identity types have empty rows. Singleton families, zero/constant inputs,
identity geometry, one-point windows and edgeless seeds use the same sums.
The operator and every time representative precede the datum and the mass. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type}
  [∀ i j α, NormedAddCommGroup (G i j α)] [∀ i j α, InnerProductSpace ℝ (G i j α)]
  [∀ i j α, FiniteDimensional ℝ (G i j α)] [∀ i j α, MeasurableSpace (G i j α)]
  [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)]
  {a b ρ ν : ℝ} {D : ℕ}

/-- The literal moment kernels and finite input reserve of the actual operator. -/
structure PreparationPlainKernelFrame
    (Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D) where
  φ : Vec 2 → ℝ
  integrable : Integrable φ
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ
  nonneg : ∀ z, 0 ≤ φ z
  mass : ∫ z, φ z = 1
  support : Function.support φ ⊆ Analysis.Convolution.closedEuclideanUnitBall
  spec : ∀ i j, Γ i j → KernelSpec
  literal : ∀ i j α, Q.S i j α = (spec i j α).op (E := G i j α) φ integrable
  matrix_bound : ℝ
  L : ℕ
  admissible : ∀ i j α, (spec i j α).IsAdmissible matrix_bound L
  width_pos : ∀ i j α, 0 < (spec i j α).width
  K : ι → ℕ
  reserve : ∀ j, D - 2 + L ≤ K j

/-- Differential orders two through D, indexed without dependent word casts. -/
def preparationPlainOrderEquiv (hD : 2 ≤ D) :
    Fin (D - 1) ≃ ↥(Finset.Icc 2 D) where
  toFun m := ⟨m.val + 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  invFun d := ⟨d.val - 2, by have := Finset.mem_Icc.mp d.property; omega⟩
  left_inv m := Fin.ext (by dsimp only; omega)
  right_inv d := Subtype.ext (by have := Finset.mem_Icc.mp d.property; dsimp only; omega)

namespace PreparationPlainKernelFrame
variable {Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D}
  (F : PreparationPlainKernelFrame Q)

/-- The physical row data, indexed by original identity and actual differential order. -/
def rows : PreparationPlainRowData h (fun i j (α : Γ i j × Fin (D - 1)) => G i j α.1) where
  φ := F.φ
  integrable := F.integrable
  smooth := F.smooth
  nonneg := F.nonneg
  mass := F.mass
  support := F.support
  ρ := ρ
  radius_pos := Q.radius_pos
  a := a
  b := b
  time_order := Q.htime
  L := F.L
  matrix_bound := F.matrix_bound
  K := F.K
  m := fun _ _ α => α.2.val
  reserve := fun _ j α => by have := F.reserve j; have := α.2.isLt; omega
  coefficient := fun i j α =>
    { B := Q.B i j α.1 (preparationPlainOrderEquiv Q.order_ge_two α.2)
      C := Q.C i j α.1
      finite := Q.hB_fin i j α.1 _
      smooth := Q.hB_smooth i j α.1 _
      periodic := Q.hB_per i j α.1 _ }
  measurable := fun i j α => Q.hB_meas i j α.1 _
  kernel := fun i j α => F.spec i j α.1
  admissible := fun i j α => F.admissible i j α.1
  width_pos := fun i j α => F.width_pos i j α.1

/-- The existing spatial regularizers restrict to each actual constituent order. -/
def regularizers : PreparationPlainRowRegularizers F.rows where
  c := fun _ _ _ => Q.c
  r := fun i j α => Q.r i j α.1
  regular := by
    intro i j α
    change IsSpatialRegularizerTorus ρ 0 (α.2.val + 2) a b Q.c (Q.r i j α.1)
      ((F.spec i j α.1).op F.φ F.integrable)
    rw [← F.literal]
    have hD : α.2.val + 2 ≤ D := by have := α.2.isLt; have := Q.order_ge_two; omega
    exact ⟨(Q.hS i j α.1).1, (Q.hS i j α.1).2.1,
      fun ell hell => (Q.hS i j α.1).2.2.1 ell (hell.trans hD),
      fun t ht ell hell z => (Q.hS i j α.1).2.2.2 t ht ell (hell.trans hD) z⟩

private theorem regularized_term_eq_fluxTerm (i j : ι) (α : Γ i j)
    (m : Fin (D - 1)) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (u : ∀ j, TorusHk 1 (h j)) :
    preparationRegularizedSourceFlux (F.rows.coefficient i j (α, m)) Q.radius_pos
      F.integrable (F.spec i j α) Q.c (Q.r i j α)
      (F.regularizers.regular i j (α, m)) t ht (u j) =
    Q.fluxTerm t ht u i j α (preparationPlainOrderEquiv Q.order_ge_two m) := by
  let d := preparationPlainOrderEquiv Q.order_ge_two m
  have htr : 0 + (m.val + 1) ≤ 0 + D - 1 := by
    have := m.isLt
    have := Q.order_ge_two
    omega
  have he : truncateTorusHk htr (Q.lift t ht u i j α) =
      KernelEnergy.torusRegularizedInput ρ 0 (m.val + 2) (by omega) a b Q.c
        (Q.r i j α) (Q.C i j α) ((F.spec i j α).op F.φ F.integrable)
        (F.regularizers.regular i j (α, m)) t ht (u j) := by
    apply TorusHk.ext_value
    change (Q.lift t ht u i j α).val (valueIndex2 (0 + D - 1)) = _
    rw [Q.lift_value, F.literal]
    exact (KernelEnergy.torusRegularizedInput_value ρ 0 (m.val + 2) (by omega) a b Q.c
      (Q.r i j α) (Q.C i j α) ((F.spec i j α).op F.φ F.integrable)
      (F.regularizers.regular i j (α, m)) t ht (u j)).symm
  change KernelEnergy.torusKernelFluxTerm (K := 0) (m := m.val) rfl ρ Q.radius_pos
    a b (Q.B i j α d) (Q.hB_fin i j α d) t ht
    (Q.hB_smooth i j α d t ht) (Q.hB_per i j α d t ht)
    (truncateTorusHk (by omega)
      (KernelEnergy.torusRegularizedInput ρ 0 (m.val + 2) (by omega) a b Q.c
        (Q.r i j α) (Q.C i j α) ((F.spec i j α).op F.φ F.integrable)
        (F.regularizers.regular i j (α, m)) t ht (u j))) = _
  rw [← he]
  rfl

/-- The row source produced by the constituent regularizers is the native
operator's actual flux, at every time of the solution window. -/
theorem regularized_source_eq_carrierFlux
    (u : ∀ j, ℝ → TorusHk 1 (h j)) (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    F.rows.regularizedSourceFluxTime F.regularizers u i t = Q.carrierFlux u i t := by
  classical
  rw [Q.carrierFlux_of_mem u i t ht, ← Q.assembledFlux_eq_flux t ht (fun j => u j t) i]
  unfold PreparationPlainRowData.regularizedSourceFluxTime
  simp only [rows, Set.projIcc_of_mem Q.htime ht]
  change (∑ j, ∑ α : Γ i j × Fin (D - 1),
    preparationRegularizedSourceFlux (F.rows.coefficient i j α) Q.radius_pos
      F.integrable (F.spec i j α.1) Q.c (Q.r i j α.1)
      (F.regularizers.regular i j α) t ht (u j t)) = _
  unfold KernelEnergy.TorusKernelOperator.assembledFlux
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro α _
  apply Fintype.sum_equiv (preparationPlainOrderEquiv Q.order_ge_two)
  intro m
  exact F.regularized_term_eq_fluxTerm i j α m t ht (fun j => u j t)

/-- A plain layer minus the native scalar kernel response is the estimated
zero-data defect row. The response is driven by the actual low gradient of
that same preceding plain layer. -/
theorem source_difference_native_row {v : ℝ → Vec 2 → Vec 2}
    (u : ∀ j, ℝ → TorusHk (F.K j + 1) (h j)) (i : ι) (f : TorusHk 0 (h i))
    {zp zk : ℝ → TorusHk 0 (h i)} {wp wk : ℝ → TorusHk 1 (h i)}
    (hp : Providers.WeakGen.Comparison.IsTorusForcedRow ν a b v 2 0 f
      (F.rows.plainSourceFluxTime u i) (fun _ => 0) zp wp)
    (hk : Providers.WeakGen.Comparison.IsTorusForcedRow ν a b v 2 0 f
      (Q.carrierFlux (fun j s => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (F.K j)))
        (u j s)) i) (fun _ => 0) zk wk) :
    Providers.WeakGen.Comparison.IsTorusForcedRow ν a b v 2 0 0
      (F.rows.fluxTime u i) (fun _ => 0) (fun t => zp t - zk t) (fun t => wp t - wk t) := by
  apply F.rows.source_difference_row F.regularizers u i f hp
  apply CycleJointProofs.PathReduction.torusRowSolution_forcing_congr ν a b v 2 0 f _ _ zk wk _ hk
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (F.regularized_source_eq_carrierFlux _ i t ht).symm

/-- Forced energy of the actual plain insertion minus the native kernel
response, with the moment gain and the higher plain reserve intact. -/
theorem source_difference_native_energy {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ}
    (hd : Providers.WeakGen.Comparison.TorusDriftData ν ρ a b v Kmax)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (q S : ℝ) (hq : 0 ≤ q)
    (hw : ∀ i j α, (F.spec i j α).width ≤ q * ρ)
    (hs : SchurBound S (fun i j => Real.sqrt (π j / π i) * F.rows.basePrice i j))
    (u : ∀ j, ℝ → TorusHk (F.K j + 1) (h j))
    (hu : ∀ j, AEStronglyMeasurable (u j) (volume.restrict (Set.Icc a b)))
    (hint : Integrable (fun t => massGradNormSq (E := h) (K := F.K) ρ π
      (fun j => (u j t).val)) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk 0 (h i))
    {zp zk : ∀ i, ℝ → TorusHk 0 (h i)} {wp wk : ∀ i, ℝ → TorusHk 1 (h i)}
    (hp : ∀ i, Providers.WeakGen.Comparison.IsTorusForcedRow ν a b v 2 0 (f i)
      (F.rows.plainSourceFluxTime u i) (fun _ => 0) (zp i) (wp i))
    (hk : ∀ i, Providers.WeakGen.Comparison.IsTorusForcedRow ν a b v 2 0 (f i)
      (Q.carrierFlux (fun j s => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (F.K j)))
        (u j s)) i) (fun _ => 0) (zk i) (wk i)) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    massNormSq ρ π (fun i => (zp i t - zk i t).val) +
      ν / 2 * (∫ r in Set.Icc a b, massGradNormSq ρ π (fun i => (wp i r - wk i r).val)) ≤
      8 / ν * ((q ^ F.L * S) ^ 2 * ∫ r in Set.Icc a b,
        massGradNormSq (E := h) (K := F.K) ρ π (fun j => (u j r).val)) := by
  have hrows : ∀ i, Providers.WeakGen.Comparison.IsTorusForcedRow ν a b v 2 0 0
      (F.rows.fluxTime u i) (fun _ => 0) (fun t => zp i t - zk i t)
        (fun t => wp i t - wk i t) :=
    fun i => F.source_difference_native_row u i (f i) (hp i) (hk i)
  exact F.rows.forced_energy (z := fun i t => zp i t - zk i t)
    (w := fun i t => wp i t - wk i t) hd Q.diffusivity_pos π hπ q S hq
    (fun i j α => hw i j α.1) hs u hu hint hrows t ht

end PreparationPlainKernelFrame

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.KernelDefect
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The uniform physical defect price, compared with a positive sampled
constituent majorant. The moment/factorial constant is fixed before the
kernels and datum. The conditional Schur assembly has one further ingredient:
the positive sampled-envelope price comparison, proved separately.

The degenerate cases are included: D=2, L=0, arbitrary larger or mixed seed/fresh orders,
empty and singleton families, zero/constants, identity geometry, one-point windows and edgeless
seeds use the same bound. No nontriviality of a fibre or positivity of a datum norm
is required. The actual kernels remain in the source and its width gain. -/

/-- The fixed shift cost, independent of all actual kernel orders. -/
def preparationPlainSampledConstant (φ : Vec 2 → ℝ) (Γ : ℝ) (D L : ℕ) : ℝ :=
  kdUniformMomentConst φ L |Γ| * ((D - 2 + L).factorial : ℝ)

theorem preparation_plain_sampled_constant_nonneg (φ : Vec 2 → ℝ) (Γ : ℝ) (D L : ℕ) :
    0 ≤ preparationPlainSampledConstant φ Γ D L :=
  mul_nonneg (kdMomentConst_nonneg φ (kdUniformOrder L) L (abs_nonneg Γ))
    (Nat.cast_nonneg _)

variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type}
  [∀ i j γ, NormedAddCommGroup (G i j γ)] [∀ i j γ, InnerProductSpace ℝ (G i j γ)]
  [∀ i j γ, FiniteDimensional ℝ (G i j γ)] [∀ i j γ, MeasurableSpace (G i j γ)]
  [∀ i j γ, BorelSpace (G i j γ)] [∀ i j γ, CompleteSpace (G i j γ)]
  {a b ρ ν : ℝ} {D : ℕ}
  {Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D}

/-- Pointwise positive price of the actual identities and differential orders.
The matrix already includes the sampled mass normalization. -/
def PlainSampledPriceStatement (F : PreparationPlainKernelFrame Q)
    (π : ι → ℝ) (C : ℝ) (B : ι → ι → ℝ) : Prop :=
  ∀ i j, Real.sqrt (π j / π i) * F.rows.basePrice i j ≤
    (ν * preparationPlainSampledConstant F.φ F.matrix_bound D F.L * C) * B i j

namespace PreparationPlainKernelFrame

/-- The sampled positive row/column budget pays the actual defect source,
with its width gain still handled separately by rows.schur_gain. -/
theorem schur_of_sampled_price (F : PreparationPlainKernelFrame Q)
    (π : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (B : ι → ι → ℝ) (S : ℝ)
    (hprice : PlainSampledPriceStatement F π C B) (hS : SchurBound S B) :
    SchurBound ((ν * preparationPlainSampledConstant F.φ F.matrix_bound D F.L * C) * S)
      (fun i j => Real.sqrt (π j / π i) * F.rows.basePrice i j) := by
  let T := ν * preparationPlainSampledConstant F.φ F.matrix_bound D F.L * C
  have hT : 0 ≤ T := mul_nonneg
    (mul_nonneg Q.diffusivity_pos.le (preparation_plain_sampled_constant_nonneg _ _ _ _)) hC
  constructor
  · intro i
    calc
      _ ≤ ∑ j, T * B i j := Finset.sum_le_sum fun j _ => hprice i j
      _ = T * ∑ j, B i j := (Finset.mul_sum ..).symm
      _ ≤ T * S := mul_le_mul_of_nonneg_left (hS.1 i) hT
  · intro j
    calc
      _ ≤ ∑ i, T * B i j := Finset.sum_le_sum fun i _ => hprice i j
      _ = T * ∑ i, B i j := (Finset.mul_sum ..).symm
      _ ≤ T * S := mul_le_mul_of_nonneg_left (hS.2 j) hT

end PreparationPlainKernelFrame

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.KernelDefect AVRegularity.CycleJointProofs
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The sampled positive constituent budget pays the actual rough defect
rows. The kernel orders never enter the constant. Coefficient order is
lowered only in the price, while every actual higher input reserve and
kernel remains in the physical flux.

The degenerate cases are included: D=2, L=0, arbitrary admissible moment orders, empty and singleton
families, zero/constants, identity geometry, trivial fibres, one-point windows and
edgeless seeds. No norm of the datum is divided out. -/

section Sampled
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}

private theorem preparation_sampled_positive_budget_real
    (family : ChartedFamily ι h D Part Ctx) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (K : ι → ℕ) (actual : ∀ p, Ctx p) (a b ν e E ρ C : ℝ)
    (hν : 0 < ν) (hρ : 0 < ρ) (B : ι → ι → ℝ)
    (hCB : ∀ i j, 0 ≤ C * B i j)
    (hs : IsSampledEnvelope family π K actual a b ν e E ρ C B) (i j : ι) :
    Real.sqrt (π j / π i) * (∑ γ : family.Γ i j, ∑ d ∈ Finset.Icc 2 D,
      (coefficientSeminorm ρ (K i) a b (constituentPhysical family ν e E actual i j γ d)).toReal /
        (ν * ρ ^ (d - 2)) * (((K i + d - 2).factorial : ℝ) / (K i).factorial)) ≤
      C * B i j := by
  classical
  let T := fun (γ : family.Γ i j) (d : ℕ) =>
    coefficientSeminorm ρ (K i) a b (constituentPhysical family ν e E actual i j γ d) *
      (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
        ENNReal.ofReal (((K i + d - 2).factorial : ℝ) / (K i).factorial)
  have hterm (γ : family.Γ i j) (d : ℕ) (hd : d ∈ Finset.Icc 2 D) : T γ d ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (sampledEnvelope_constituent_seminorm_ne_top family π hπ K actual a b ν e E ρ C
        hν hρ B hs i j γ d hd)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (mul_pos hν (pow_pos hρ _))).ne'))
      ENNReal.ofReal_ne_top
  have hinner (γ : family.Γ i j) : (∑ d ∈ Finset.Icc 2 D, T γ d) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun d hd => hterm γ d hd
  have he : (∑ γ : family.Γ i j, ∑ d ∈ Finset.Icc 2 D, T γ d).toReal =
      ∑ γ : family.Γ i j, ∑ d ∈ Finset.Icc 2 D,
        (coefficientSeminorm ρ (K i) a b (constituentPhysical family ν e E actual i j γ d)).toReal /
          (ν * ρ ^ (d - 2)) * (((K i + d - 2).factorial : ℝ) / (K i).factorial) := by
    rw [ENNReal.toReal_sum (fun γ _ => hinner γ)]
    apply Finset.sum_congr rfl
    intro γ _
    rw [ENNReal.toReal_sum (fun d hd => hterm γ d hd)]
    apply Finset.sum_congr rfl
    intro d _
    dsimp only [T]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (mul_pos hν (pow_pos hρ _)).le,
      ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    simp only [div_eq_mul_inv]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hs.2 i j)
  change (ENNReal.ofReal (Real.sqrt (π j / π i)) *
    (∑ γ : family.Γ i j, ∑ d ∈ Finset.Icc 2 D, T γ d)).toReal ≤ _ at hh
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), he,
    ENNReal.toReal_ofReal (hCB i j)] at hh
  exact hh
end Sampled

private theorem preparation_sampled_shift_price {x y c r ν t : ℝ} {K m D L : ℕ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hc : 0 ≤ c) (hr : 0 < r) (hν : 0 < ν)
    (ht : t ≤ 1) (hm : m ≤ D - 2) :
    x * (c * ((m + L).factorial : ℝ)) / r ^ m * t ≤
      (ν * (c * ((D - 2 + L).factorial : ℝ))) *
        (y / (ν * r ^ m) * (((K + m).factorial : ℝ) / K.factorial)) := by
  have hy : 0 ≤ y := hx.trans hxy
  have hfac : ((m + L).factorial : ℝ) ≤ (D - 2 + L).factorial := by
    exact_mod_cast Nat.factorial_le (Nat.add_le_add_right hm L)
  have hratio : (1 : ℝ) ≤ ((K + m).factorial : ℝ) / K.factorial := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < K.factorial)).mpr
    rw [one_mul]
    exact_mod_cast Nat.factorial_le (Nat.le_add_right K m)
  have hnn : 0 ≤ y * (c * ((D - 2 + L).factorial : ℝ)) / r ^ m :=
    div_nonneg (mul_nonneg hy (mul_nonneg hc (Nat.cast_nonneg _))) (pow_nonneg hr.le _)
  calc
    _ ≤ x * (c * ((m + L).factorial : ℝ)) / r ^ m :=
      mul_le_of_le_one_right
        (div_nonneg (mul_nonneg hx (mul_nonneg hc (Nat.cast_nonneg _))) (pow_nonneg hr.le _)) ht
    _ ≤ y * (c * ((D - 2 + L).factorial : ℝ)) / r ^ m := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hr.le _)
      exact (mul_le_mul_of_nonneg_right hxy (mul_nonneg hc (Nat.cast_nonneg _))).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac hc) hy)
    _ ≤ (y * (c * ((D - 2 + L).factorial : ℝ)) / r ^ m) *
        (((K + m).factorial : ℝ) / K.factorial) := le_mul_of_one_le_right hnn hratio
    _ = _ := by
      field_simp [hν.ne', (pow_pos hr m).ne']

section Native
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {Part : Type*} {Ctx : Part → Type*}
  {family : ChartedFamily ι h D Part Ctx} {a b ρ ν : ℝ}
  {Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
    (G := fun _ j _ => h j) a b ρ ν 0 D}

namespace PreparationPlainKernelFrame
/-- The chart certificate's positive sampled budget controls the actual
uniform defect basePrice. No common actual kernel order is requested. -/
theorem price_of_sampled (F : PreparationPlainKernelFrame Q)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (K : ι → ℕ) (e E : ℝ) (actual : ∀ p, Ctx p)
    (hB : ∀ i j γ d, Q.B i j γ d = constituentPhysical family ν e E actual i j γ d.val)
    (hC : ∀ i j γ, ‖Q.C i j γ‖ ≤ 1)
    (C : ℝ) (hCnonneg : 0 ≤ C) (B : ι → ι → ℝ) (hBn : ∀ i j, 0 ≤ B i j)
    (hs : IsSampledEnvelope family π K actual a b ν e E ρ C B) :
    PlainSampledPriceStatement F π C B := by
  classical
  intro i j
  let T := fun (γ : family.Γ i j) (d : ℕ) =>
    (coefficientSeminorm ρ (K i) a b (constituentPhysical family ν e E actual i j γ d)).toReal /
      (ν * ρ ^ (d - 2)) * (((K i + d - 2).factorial : ℝ) / (K i).factorial)
  let Z := ν * preparationPlainSampledConstant F.φ F.matrix_bound D F.L
  have hc : 0 ≤ kdUniformMomentConst F.φ F.L |F.matrix_bound| :=
    kdMomentConst_nonneg _ _ _ (abs_nonneg _)
  have hZ : 0 ≤ Z := mul_nonneg Q.diffusivity_pos.le
    (preparation_plain_sampled_constant_nonneg _ _ _ _)
  have hp (γ : family.Γ i j) (m : Fin (D - 1)) :
      (coefficientSeminorm ρ 0 a b (F.rows.coefficient i j (γ, m)).B).toReal *
        (preparationPlainDefectConstant F.φ F.matrix_bound m.val F.L) / ρ ^ m.val *
          ‖Q.C i j γ‖ ≤ Z * T γ (m.val + 2) := by
    let d := preparationPlainOrderEquiv Q.order_ge_two m
    have hd : d.val ∈ Finset.Icc 2 D := d.property
    have hco := ENNReal.toReal_mono
      (sampledEnvelope_constituent_seminorm_ne_top family π hπ K actual a b ν e E ρ C
        Q.diffusivity_pos Q.radius_pos B hs i j γ d.val hd)
      (FullLift.coefficientSeminorm_order_mono ρ (Nat.zero_le (K i)) a b
        (constituentPhysical family ν e E actual i j γ d.val))
    have he : (F.rows.coefficient i j (γ, m)).B =
        constituentPhysical family ν e E actual i j γ d.val := hB i j γ d
    have hco' := (congrArg (fun A => (coefficientSeminorm ρ 0 a b A).toReal) he).trans_le hco
    have hm : m.val ≤ D - 2 := by have := m.isLt; have := Q.order_ge_two; omega
    exact preparation_sampled_shift_price ENNReal.toReal_nonneg hco' hc Q.radius_pos
      Q.diffusivity_pos (hC i j γ) hm
  have hrow : F.rows.basePrice i j ≤ Z * ∑ γ : family.Γ i j,
      ∑ m : Fin (D - 1), T γ (m.val + 2) := by
    change (∑ α : family.Γ i j × Fin (D - 1), _) ≤ _
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ γ : family.Γ i j, ∑ m : Fin (D - 1), Z * T γ (m.val + 2) :=
        Finset.sum_le_sum fun γ _ => Finset.sum_le_sum fun m _ => hp γ m
      _ = _ := by simp only [Finset.mul_sum]
  have hsum (γ : family.Γ i j) : (∑ m : Fin (D - 1), T γ (m.val + 2)) =
      ∑ d ∈ Finset.Icc 2 D, T γ d := by
    rw [← Finset.sum_coe_sort (Finset.Icc 2 D)]
    apply Fintype.sum_equiv (preparationPlainOrderEquiv Q.order_ge_two)
    intro m
    rfl
  have hb := preparation_sampled_positive_budget_real family π hπ K actual a b ν e E ρ C
    Q.diffusivity_pos Q.radius_pos B (fun i j => mul_nonneg hCnonneg (hBn i j)) hs i j
  calc
    Real.sqrt (π j / π i) * F.rows.basePrice i j ≤
        Real.sqrt (π j / π i) * (Z * ∑ γ : family.Γ i j,
          ∑ m : Fin (D - 1), T γ (m.val + 2)) :=
      mul_le_mul_of_nonneg_left hrow (Real.sqrt_nonneg _)
    _ = Z * (Real.sqrt (π j / π i) * ∑ γ : family.Γ i j,
        ∑ d ∈ Finset.Icc 2 D, T γ d) := by simp_rw [hsum]; ring
    _ ≤ Z * (C * B i j) := mul_le_mul_of_nonneg_left hb hZ
    _ = _ := by dsimp only [Z]; ring
end PreparationPlainKernelFrame
end Native

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual plain/kernel response difference in the SAME physical energy
carrier used by the finite insertion identity. Its whole-family trace
supremum and its genuine higher time class share one moment-gain bound.

The degenerate cases are included: empty families and empty identity sets give zero energies. The
D=2, singleton, identity geometry, zero/constant datum, zero-length window and
edgeless seed cases retain the same operators. No norm is divided out;
absolute values also cover the vacuous negative Schur bound for empty types. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul
  preparationWeightedLowSMul preparationWeightedLowSpace

variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type}
  [∀ i j α, NormedAddCommGroup (G i j α)] [∀ i j α, InnerProductSpace ℝ (G i j α)]
  [∀ i j α, FiniteDimensional ℝ (G i j α)] [∀ i j α, MeasurableSpace (G i j α)]
  [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)]
  {a b ρ ν : ℝ} {D : ℕ}

namespace PreparationPlainKernelFrame
variable {Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D}
  (F : PreparationPlainKernelFrame Q)

/-- The native response to a preceding plain layer has the precise moment
error in the common path seminorm, before datum or mass-specific choices. -/
theorem source_difference_path_energy {v : ℝ → Vec 2 → Vec 2} {Kmax : ℕ}
    (hd : TorusDriftData ν ρ a b v Kmax)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (q S : ℝ) (hq : 0 ≤ q)
    (hw : ∀ i j α, (F.spec i j α).width ≤ q * ρ)
    (hs : SchurBound S (fun i j => Real.sqrt (π j / π i) * F.rows.basePrice i j))
    (u : ∀ j, ℝ → TorusHk (F.K j + 1) (h j))
    (hu : ∀ j, AEStronglyMeasurable (u j) (volume.restrict (Set.Icc a b)))
    (hint : Integrable (fun t => massGradNormSq (E := h) (K := F.K) ρ π
      (fun j => (u j t).val)) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, TorusHk 0 (h i))
    (zp zk : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b a)
    (wp wk : ∀ i, ℝ → TorusHk 1 (h i))
    (hp : ∀ i, IsTorusForcedRow ν a b v 2 0 (f i)
      (F.rows.plainSourceFluxTime u i) (fun _ => 0)
      (fun t => zp.1 (Set.projIcc a b Q.htime t) i) (wp i))
    (hk : ∀ i, IsTorusForcedRow ν a b v 2 0 (f i)
      (Q.carrierFlux (fun j s => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (F.K j)))
        (u j s)) i) (fun _ => 0)
      (fun t => zk.1 (Set.projIcc a b Q.htime t) i) (wk i))
    (hwp : zp.2 =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => coupledCarrierHighJets (fun _ => 0) (fun i => wp i t))
    (hwk : zk.2 =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => coupledCarrierHighJets (fun _ => 0) (fun i => wk i t)) :
    preparationWeightedPathEnergy (h := h) ρ π ν a b a (zp - zk) ≤
      7 * (q ^ F.L * |S| / Real.sqrt ν) * Real.sqrt (∫ t in Set.Icc a b,
        massGradNormSq (E := h) (K := F.K) ρ π (fun j => (u j t).val)) := by
  let z : PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b a := zp - zk
  change preparationWeightedPathEnergy (h := h) ρ π ν a b a z ≤ _
  let X := ∫ t in Set.Icc a b, massGradNormSq (E := h) (K := F.K) ρ π
    (fun j => (u j t).val)
  have hX : 0 ≤ X := integral_nonneg fun t => Finset.sum_nonneg fun i _ =>
    mul_nonneg (inv_nonneg.mpr (hπ i).le) (KernelEnergy.torusCarrierGradFactorial_nonneg ρ (F.K i) (u i t))
  let r := (q ^ F.L * |S| / Real.sqrt ν) * Real.sqrt X
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hcost : 8 / ν * ((q ^ F.L * S) ^ 2 * X) = 8 * r ^ 2 := by
    dsimp only [r]
    simp only [mul_pow, div_pow, sq_abs, Real.sq_sqrt Q.diffusivity_pos.le,
      Real.sq_sqrt hX]
    ring
  let A := preparationWeightedGradientCLM (h := h) ρ π
  have hsub : z.2 =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => coupledCarrierHighJets (fun _ => 0) (fun i => wp i t - wk i t) := by
    filter_upwards [Lp.coeFn_sub zp.2 zk.2, hwp, hwk] with t he hp hk
    change (zp.2 - zk.2) t = _
    rw [he]
    change zp.2 t - zk.2 t = _
    rw [hp, hk]
    rfl
  have hgrad : ‖A.compLpL 2 (volume.restrict (Set.Icc a b)) z.2‖ ^ 2 =
      ∫ t in Set.Icc a b, massGradNormSq ρ π (fun i => (wp i t - wk i t).val) :=
    preparation_weighted_gradient_time_normSq ρ π hπ a b z.2
      (fun i t => wp i t - wk i t) hsub
  have he (t : Set.Icc a b) :
      ‖massWeightedCarrierCLM (fun _ => 0) ρ π (z.1 t)‖ ^ 2 +
        ν / 2 * ‖A.compLpL 2 (volume.restrict (Set.Icc a b)) z.2‖ ^ 2 ≤ 8 * r ^ 2 := by
    rw [massWeightedCarrierCLM_normSq _ _ _ hπ, hgrad]
    have hb := F.source_difference_native_energy
      (zp := fun i t => zp.1 (Set.projIcc a b Q.htime t) i)
      (zk := fun i t => zk.1 (Set.projIcc a b Q.htime t) i)
      (wp := wp) (wk := wk) hd π hπ q S hq hw hs u hu hint f hp hk t t.property
    simp only [Set.projIcc_of_mem Q.htime t.property] at hb
    change _ ≤ 8 / ν * ((q ^ F.L * S) ^ 2 * X) at hb
    rw [hcost] at hb
    exact hb
  have hb := preparation_path_energy_of_squares Q.htime
    (massWeightedCarrierCLM (E := h) (fun _ => 0) ρ π) A Q.diffusivity_pos.le z hr he
  exact hb.trans_eq (by dsimp only [r, X]; ring)

end PreparationPlainKernelFrame

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Extract the physical low row from the actual descending-slot plain
solution. The source is identified spatially at EVERY time, so the transfer
preserves all integrability clauses of the integrated weak equation.

The degenerate cases are included: empty families have no row; singleton families, D=2,
constant/zero inputs, identity geometry and edgeless seeds use the same extraction. No
higher-order lift of a merely order-zero forcing is assumed. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The raw physical flux retains the original identity and differential
order exactly once. This is the torus analogue of the plane assembly. -/
theorem preparation_torus_raw_family_constituents
    {D : ℕ} {Part : Type*} {Ctx : Part → Type*}
    (family : ChartedFamily ι h D Part Ctx) (K : ι → ℕ)
    (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (U : ∀ j, TorusHk (K j + 1) (h j)) (i : ι) (t : ℝ) (x : Vec 2) :
    torusRawCouplingFlux K D t (edgeCoefficient family ν e E actual K) U i x =
      ∑ j, ∑ γ : family.Γ i j, ∑ d : admissibleOrders K D i j,
        constituentPhysical family ν e E actual i j γ d.val t x
          (WithLp.toLp 2 fun w : DerivativeWord2 (d.val - 1) =>
            (U j).toFunction.jet ⟨⟨d.val - 1,
              Nat.lt_succ_of_le (admissibleOrders_high_readout_bound K D i j d)⟩, w⟩ x) := by
  classical
  unfold torusRawCouplingFlux edgeCoefficient physicalCoefficient
  apply Finset.sum_congr rfl
  intro j _
  simp only [sum_apply]
  exact Finset.sum_comm

/-- A low carrier for the literal incoming flux gives a genuine forced row
of the plain solution. Only the solution is truncated; the flux already has
its correct order-zero carrier. -/
theorem preparation_plain_low_forced_row
    {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
    {A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)}
    {f : ∀ i, TorusHk (K i) (h i)}
    {u : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A f
      (fun _ _ => 0) (fun _ _ => 0) u w)
    (i : ι) (Q : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => h i)))
    (hQ : ∀ s ∈ Set.Icc a b, (Q s).toFunction.jet (valueIndex2 0) =ᵐ[
      volume.restrict unitCube] torusRawCouplingFlux K D s A (fun j => w j s) i) :
    IsTorusForcedRow ν a b v 2 0 (truncateTorusHk (Nat.zero_le (K i)) (f i)) Q
      (fun _ => 0) (fun t => truncateTorusHk (Nat.zero_le (K i)) (u i t))
      (fun t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le (K i))) (w i t)) := by
  have hc := truncate_continuousOn (Nat.zero_le (K i)) (hs.1 i)
  have hm := truncate_memLp (Nat.succ_le_succ (Nat.zero_le (K i))) (hs.2.1 i)
  have hl := truncate_lift_ae (Nat.zero_le (K i)) (hs.2.2.1 i)
  have hi := congrArg (truncateTorusHk (E := h i) (Nat.zero_le (K i))) (hs.2.2.2.1 i)
  refine ⟨fun _ => hc, fun _ => hm, fun _ => hl, fun _ => hi, ?_⟩
  intro _ t ht φ
  have hold := hs.2.2.2.2 i t ht φ
  refine coupledWeakIdentity_integrands_congr (volume.restrict unitCube) ν a t v v
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ hold
  · filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae
      (Nat.zero_le (K i)) (u i t) (valueIndex2 0)] with x hx
    exact congrArg (fun y => inner ℝ y _) hx.symm
  · filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae
      (Nat.zero_le (K i)) (f i) (valueIndex2 0)] with x hx
    exact congrArg (fun y => inner ℝ y _) hx.symm
  · intro s hs'
    have hsab : s ∈ Set.Icc a b := ⟨hs'.1.le, hs'.2.trans ht.2⟩
    filter_upwards [KernelEnergy.truncateTorusHk_toFunction_jet_ae
        (Nat.succ_le_succ (Nat.zero_le (K i))) (w i s)
        ⟨⟨1, by omega⟩, fun _ => 0⟩,
      KernelEnergy.truncateTorusHk_toFunction_jet_ae
        (Nat.succ_le_succ (Nat.zero_le (K i))) (w i s)
        ⟨⟨1, by omega⟩, fun _ => 1⟩,
      hQ s hsab,
      torusZero_rawJet_ae (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) (valueIndex2 (K i)),
      torusZero_rawJet_ae (E := h i) (K i) (valueIndex2 (K i)),
      torusZero_rawJet_ae (E := h i) 0 (valueIndex2 0)] with x h0 h1 hflux hF hg hg'
    refine weakIdentityRhs_congr_at _ _ _ _ _ _ _ _ _ _ _ _ s x (fun q => ?_) ?_ ?_
    · fin_cases q
      · exact h0.symm
      · exact h1.symm
    · change torusRawCouplingFlux K D s A (fun j => w j s) i x +
        (0 : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))).toFunction.jet
          (valueIndex2 (K i)) x = _
      rw [hF, ← hflux]
      simp only [Pi.zero_apply, zero_apply, Finset.sum_const_zero, zero_add, add_zero]
    · exact hg.trans hg'.symm

section Constituent
variable {E G H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
  {ρ a b : ℝ} {m L : ℕ}

omit [Fintype ι] [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- At every time the plain constituent is the physical coefficient applied
to the original ordered source jets, with its actual constant fibre map. -/
theorem preparation_plain_source_base_ae
    (F : PreparationPlainFluxCoefficient ρ a b m E G H) (hρ : 0 < ρ)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (u : TorusHk (m + L + 1) E) :
    (preparationPlainSourceFlux (L := L) F hρ t ht u).toFunction.jet (valueIndex2 0)
      =ᵐ[volume.restrict unitCube] fun x => F.B t x
        (WithLp.toLp 2 fun w : DerivativeWord2 (m + 1) =>
          F.C (u.toFunction.jet ⟨⟨m + 1, by omega⟩, w⟩ x)) := by
  let V := truncateTorusHk (by omega : 0 + (m + 1) ≤ m + L + 1) u
  have hb := KernelEnergy.torusKernelFluxTerm_base_ae (K := 0) (m := m) rfl ρ hρ
    a b F.B F.finite t ht (F.smooth t ht) (F.periodic t ht) (mapTorusHk F.C V)
  have hm : ∀ᵐ x ∂volume.restrict unitCube, ∀ w : DerivativeWord2 (m + 1),
      (mapTorusHk F.C V).toFunction.jet ⟨⟨m + 1, by omega⟩, w⟩ x =
        F.C (V.toFunction.jet ⟨⟨m + 1, by omega⟩, w⟩ x) :=
    ae_all_iff.mpr fun w => KernelEnergy.mapTorusHk_toFunction_jet_ae F.C V _
  have hv : ∀ᵐ x ∂volume.restrict unitCube, ∀ w : DerivativeWord2 (m + 1),
      V.toFunction.jet ⟨⟨m + 1, by omega⟩, w⟩ x =
        u.toFunction.jet ⟨⟨m + 1, by omega⟩, w⟩ x :=
    ae_all_iff.mpr fun w => KernelEnergy.truncateTorusHk_toFunction_jet_ae _ u _
  filter_upwards [hb, hm, hv] with x hbx hmx hvx
  change (KernelEnergy.torusKernelFluxTerm (K := 0) (m := m) rfl ρ hρ
    a b F.B F.finite t ht (F.smooth t ht) (F.periodic t ht)
    (mapTorusHk F.C V)).toFunction.jet (valueIndex2 0) x = _
  rw [hbx]
  apply congrArg (F.B t x)
  apply PiLp.ext
  intro w
  exact (hmx w).trans (congrArg F.C (hvx w))
end Constituent

section Rows
variable {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type}
  [∀ i j α, NormedAddCommGroup (G i j α)] [∀ i j α, InnerProductSpace ℝ (G i j α)]
  [∀ i j α, FiniteDimensional ℝ (G i j α)] [∀ i j α, MeasurableSpace (G i j α)]
  [∀ i j α, BorelSpace (G i j α)] [∀ i j α, CompleteSpace (G i j α)]

/-- The original ordered jets realize the full plain source row spatially
a.e. at EVERY time in the solution window, before any energy estimate. -/
theorem preparation_plain_row_source_base_ae (P : PreparationPlainRowData h G)
    (u : ∀ j, ℝ → TorusHk (P.K j + 1) (h j)) (i : ι) (t : ℝ)
    (ht : t ∈ Set.Icc P.a P.b) :
    (P.plainSourceFluxTime u i t).toFunction.jet (valueIndex2 0) =ᵐ[
      volume.restrict unitCube] fun x => ∑ j, ∑ α,
        (P.coefficient i j α).B t x (WithLp.toLp 2
          fun w : DerivativeWord2 (P.m i j α + 1) =>
            (P.coefficient i j α).C ((u j t).toFunction.jet
              ⟨⟨P.m i j α + 1, by have := P.reserve i j α; omega⟩, w⟩ x)) := by
  let T (j : ι) (α : Γ i j) := preparationPlainSourceFlux (L := P.L)
    (P.coefficient i j α) P.radius_pos t ht
    (truncateTorusHk (Nat.add_le_add_right (P.reserve i j α) 1) (u j t))
  have he : P.plainSourceFluxTime u i t = ∑ j, ∑ α, T j α := by
    simp only [PreparationPlainRowData.plainSourceFluxTime,
      Set.projIcc_of_mem P.time_order ht, T]
  rw [he]
  have ho := KernelEnergy.torusJet_sum_ae (fun j => ∑ α, T j α) (valueIndex2 0)
  have hi : ∀ᵐ x ∂volume.restrict unitCube, ∀ j,
      (∑ α, T j α).toFunction.jet (valueIndex2 0) x =
        ∑ α, (T j α).toFunction.jet (valueIndex2 0) x :=
    ae_all_iff.mpr fun j => KernelEnergy.torusJet_sum_ae (T j) _
  have hc : ∀ᵐ x ∂volume.restrict unitCube, ∀ j α,
      (T j α).toFunction.jet (valueIndex2 0) x =
        (P.coefficient i j α).B t x (WithLp.toLp 2
          fun w : DerivativeWord2 (P.m i j α + 1) =>
            (P.coefficient i j α).C ((u j t).toFunction.jet
              ⟨⟨P.m i j α + 1, by have := P.reserve i j α; omega⟩, w⟩ x)) := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro α
    have hb := preparation_plain_source_base_ae (P.coefficient i j α) P.radius_pos t ht
      (truncateTorusHk (Nat.add_le_add_right (P.reserve i j α) 1) (u j t))
    have ht' : ∀ᵐ x ∂volume.restrict unitCube, ∀ w : DerivativeWord2 (P.m i j α + 1),
        (truncateTorusHk (Nat.add_le_add_right (P.reserve i j α) 1) (u j t)).toFunction.jet
          ⟨⟨P.m i j α + 1, by omega⟩, w⟩ x =
        (u j t).toFunction.jet
          ⟨⟨P.m i j α + 1, by have := P.reserve i j α; omega⟩, w⟩ x :=
      ae_all_iff.mpr fun w => KernelEnergy.truncateTorusHk_toFunction_jet_ae _ (u j t) _
    filter_upwards [hb, ht'] with x hbx htx
    rw [hbx]
    apply congrArg ((P.coefficient i j α).B t x)
    apply PiLp.ext
    intro w
    exact congrArg (P.coefficient i j α).C (htx w)
  filter_upwards [ho, hi, hc] with x hox hix hcx
  rw [hox]
  exact Finset.sum_congr rfl fun j _ =>
    (hix j).trans (Finset.sum_congr rfl fun α _ => hcx j α)
end Rows

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual neutral-chain incoming flux of copy l+1 is the original
physical row applied to copy l. Original identities and every order 2..D
are retained exactly once; all other copies have empty identity types.

The degenerate cases are included: H=0 has no step, D=2 has one order, and empty families give empty
rows. Singleton, constant/zero, identity geometry and edgeless seed cases
require neither division nor a separate representation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D H Kbase : ℕ} {Part : Type*} {Ctx : Part → Type*}

omit [Fintype ι] in
/-- The descending reserve pays all the original differential orders at
one source-insertion step, independently of the component index. -/
theorem preparation_neutral_step_reserve (hD : 2 ≤ D) (l : Fin H) (i j : ι) :
    preparationNeutralSlots H D Kbase (i, l.succ) + D ≤
      preparationNeutralSlots H D Kbase (j, l.castSucc) + 2 := by
  have hl : H - l.val = H - (l.val + 1) + 1 := by have := l.isLt; omega
  change Kbase + (H - (l.val + 1)) * (D - 2) + D ≤
    Kbase + (H - l.val) * (D - 2) + 2
  rw [hl, Nat.add_mul, Nat.one_mul]
  omega

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- Exactly the preceding copy supplies the literal unregularized source. -/
theorem preparation_neutral_raw_flux_step
    (family : ChartedFamily ι h D Part Ctx) (hD : 2 ≤ D) (l : Fin H)
    (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (U : ∀ v : ι × Fin (H + 1),
      TorusHk (preparationNeutralSlots H D Kbase v + 1) (h v.1))
    (i : ι) (t : ℝ) (x : Vec 2) :
    torusRawCouplingFlux (preparationNeutralSlots H D Kbase) D t
      (edgeCoefficient (preparationNeutralChain family H) ν e E actual
        (preparationNeutralSlots H D Kbase)) U (i, l.succ) x =
      ∑ j, ∑ γ : family.Γ i j, ∑ d : ↥(Finset.Icc 2 D),
        constituentPhysical family ν e E actual i j γ d.val t x
          (WithLp.toLp 2 fun w : DerivativeWord2 (d.val - 1) =>
            (U (j, l.castSucc)).toFunction.jet ⟨⟨d.val - 1, by
              have hd := (Finset.mem_Icc.mp d.property).2
              have hr := preparation_neutral_step_reserve (Kbase := Kbase) hD l i j
              omega⟩, w⟩ x) := by
  classical
  rw [preparation_torus_raw_family_constituents]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single l.castSucc]
  · let eγ : (preparationNeutralChain family H).Γ (i, l.succ) (j, l.castSucc) ≃
        family.Γ i j :=
      { toFun := Subtype.val
        invFun := fun γ => ⟨γ, rfl⟩
        left_inv := fun γ => Subtype.ext rfl
        right_inv := fun _ => rfl }
    apply Fintype.sum_equiv eγ
    intro γ
    let ed : admissibleOrders (preparationNeutralSlots H D Kbase) D
        (i, l.succ) (j, l.castSucc) ≃ ↥(Finset.Icc 2 D) :=
      { toFun := fun d => ⟨d.val, (Finset.mem_filter.mp d.property).1⟩
        invFun := fun d => ⟨d.val, Finset.mem_filter.mpr ⟨d.property, by
          have hd := (Finset.mem_Icc.mp d.property).2
          exact (Nat.add_le_add_left hd _).trans
            (preparation_neutral_step_reserve (Kbase := Kbase) hD l i j)⟩⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
    apply Fintype.sum_equiv ed
    intro d
    rfl
  · intro l' _ hne
    have he : IsEmpty ((preparationNeutralChain family H).Γ (i, l.succ) (j, l')) :=
      ⟨fun γ => hne (Fin.ext (by have := γ.property; change l.val + 1 = l'.val + 1 at this; change l'.val = l.val; omega))⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

section NativeSource
variable {a b ρ ν : ℝ} {family : ChartedFamily ι h D Part Ctx}
  {Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
    (G := fun _ j _ => h j) a b ρ ν 0 D}

/-- Read the preceding neutral copy at the actual reserve used by the
moment defect. This is a truncation of its genuine higher carrier. -/
def preparationNeutralPrecedingInput (F : PreparationPlainKernelFrame Q)
    (l : Fin H)
    (hK : ∀ j, F.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (U : ∀ v : ι × Fin (H + 1), ℝ →
      TorusHk (preparationNeutralSlots H D Kbase v + 1) (h v.1)) :
    ∀ j, ℝ → TorusHk (F.K j + 1) (h j) :=
  fun j t => truncateTorusHk (Nat.succ_le_succ (hK j)) (U (j, l.castSucc) t)

/-- The actual plain source carrier is the entire incoming physical flux
of the next neutral copy, with no forcing identity left as a hypothesis. -/
theorem preparation_neutral_plain_source_base_ae
    (F : PreparationPlainKernelFrame Q) (l : Fin H)
    (hK : ∀ j, F.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hB : ∀ i j γ d, Q.B i j γ d =
      constituentPhysical family ν e E actual i j γ d.val)
    (hC : ∀ i j γ, Q.C i j γ = ContinuousLinearMap.id ℝ (h j))
    (U : ∀ v : ι × Fin (H + 1), ℝ →
      TorusHk (preparationNeutralSlots H D Kbase v + 1) (h v.1))
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (F.rows.plainSourceFluxTime (preparationNeutralPrecedingInput F l hK U) i t).toFunction.jet
      (valueIndex2 0) =ᵐ[volume.restrict unitCube]
      torusRawCouplingFlux (preparationNeutralSlots H D Kbase) D t
        (edgeCoefficient (preparationNeutralChain family H) ν e E actual
          (preparationNeutralSlots H D Kbase)) (fun v => U v t) (i, l.succ) := by
  classical
  let V := preparationNeutralPrecedingInput F l hK U
  have hb := preparation_plain_row_source_base_ae F.rows V i t ht
  have hv : ∀ᵐ x ∂volume.restrict unitCube, ∀ j (α : family.Γ i j × Fin (D - 1))
      (w : DerivativeWord2 (α.2.val + 1)),
      (V j t).toFunction.jet ⟨⟨α.2.val + 1, by
        have := F.reserve j; have := α.2.isLt; omega⟩, w⟩ x =
      (U (j, l.castSucc) t).toFunction.jet ⟨⟨α.2.val + 1, by
        have := F.reserve j; have := α.2.isLt; have := hK j; omega⟩, w⟩ x :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun α => ae_all_iff.mpr fun w =>
      KernelEnergy.truncateTorusHk_toFunction_jet_ae (Nat.succ_le_succ (hK j))
        (U (j, l.castSucc) t) _
  filter_upwards [hb, hv] with x hbx hvx
  rw [hbx, preparation_neutral_raw_flux_step family Q.order_ge_two l ν e E actual
    (fun v => U v t) i t x]
  change (∑ j, ∑ α : family.Γ i j × Fin (D - 1),
    (Q.B i j α.1 (preparationPlainOrderEquiv Q.order_ge_two α.2)) t x
      (WithLp.toLp 2 fun w : DerivativeWord2 (α.2.val + 1) =>
        (Q.C i j α.1) ((V j t).toFunction.jet ⟨⟨α.2.val + 1, by
          have := F.reserve j; have := α.2.isLt; omega⟩, w⟩ x))) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro γ _
  apply Fintype.sum_equiv (preparationPlainOrderEquiv Q.order_ge_two)
  intro m
  rw [hB, hC]
  apply congrArg (constituentPhysical family ν e E actual i j γ
    (preparationPlainOrderEquiv Q.order_ge_two m).val t x)
  apply PiLp.ext
  intro w
  exact hvx j (γ, m) w

/-- Extract the next plain layer from the genuine neutral-chain solution.
Every weak-integrability clause comes from that solution; the forcing is
exactly the source used by the already proved native-response difference. -/
theorem preparation_neutral_plain_forced_row
    (F : PreparationPlainKernelFrame Q) (l : Fin H)
    (hK : ∀ j, F.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hB : ∀ i j γ d, Q.B i j γ d =
      constituentPhysical family ν e E actual i j γ d.val)
    (hC : ∀ i j γ, Q.C i j γ = ContinuousLinearMap.id ℝ (h j))
    {v : ℝ → Vec 2 → Vec 2}
    {f : ∀ z : ι × Fin (H + 1), TorusHk (preparationNeutralSlots H D Kbase z) (h z.1)}
    {z : ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y) (h y.1)}
    {U : ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y + 1) (h y.1)}
    (hs : IsCoupledWeakSolutionTorus ν a b v D (preparationNeutralSlots H D Kbase)
      (edgeCoefficient (preparationNeutralChain family H) ν e E actual
        (preparationNeutralSlots H D Kbase)) f (fun _ _ => 0) (fun _ _ => 0) z U) (i : ι) :
    Providers.WeakGen.Comparison.IsTorusForcedRow ν a b v 2 0
      (truncateTorusHk (Nat.zero_le _) (f (i, l.succ)))
      (F.rows.plainSourceFluxTime (preparationNeutralPrecedingInput F l hK U) i)
      (fun _ => 0) (fun t => truncateTorusHk (Nat.zero_le _) (z (i, l.succ) t))
      (fun t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (U (i, l.succ) t)) := by
  exact preparation_plain_low_forced_row hs (i, l.succ) _
    (fun t ht => preparation_neutral_plain_source_base_ae F l hK e E actual hB hC U i t ht)
end NativeSource

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The literal incoming-stage moment frame on any supplied native operator
window. The incoming invariant already certifies every actual seed/fresh
kernel. Lowering its moment order retains its matrices and its actual order;
no common kernel order or second kernel-price estimate is introduced.
The degenerate cases are included: empty and singleton families, L=0, Dm=2, identity geometry,
constant data and edgeless seed stages use exactly the same specs and finite input reserve. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The native specs supply the physical moment frame, on the very operator
used by the scalar source. Only its finite source reserve is selected. -/
def preparation_native_plain_kernel_frame (F : Request hr D Dm bw j₀)
    (k : InvConsts) (Mnat : ℕ) (tA S θ : ℝ)
    (hinv : IsStageInvariant F.law F.P F.seedK F.freshK F.φ₀ F.hφ₀ Mnat k tA F.tf S θ F.G)
    {a b : ℝ}
    (Q : KernelEnergy.TorusKernelOperator (h := fun v : CompIn F.G.comps => hr v.1.root)
      (Γ := F.G.fam.Γ) (G := fun _ u _ => hr u.1.root)
      a b (rhoStar D F.c₀ F.G.level) (D.κ F.G.level) 0 Dm)
    (hkernel : Q.S = F.G.sysS F.P F.seedK F.freshK F.φ₀ F.hφ₀)
    (L Kbase : ℕ) (hL : L ≤ k.Lker) (hK : Dm - 2 + L ≤ Kbase)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) F.φ₀) (hnonneg : ∀ z, 0 ≤ F.φ₀ z)
    (hmass : ∫ z, F.φ₀ z = 1)
    (hsupport : Function.support F.φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall) :
    PreparationPlainKernelFrame Q := by
  obtain ⟨_, _, _, _, _, _, _, _, hspec, _⟩ := hinv
  refine {
    φ := F.φ₀
    integrable := F.hφ₀
    smooth := hsmooth
    nonneg := hnonneg
    mass := hmass
    support := hsupport
    spec := F.G.kernelOf F.P F.seedK F.freshK
    literal := ?_
    matrix_bound := k.Γk
    L := L
    admissible := ?_
    width_pos := ?_
    K := fun _ => Kbase
    reserve := fun _ => hK }
  · intro v u γ
    rw [hkernel]
    rfl
  · intro v u γ
    have hs := (hspec v u γ).1
    exact ⟨hs.1, hs.2.1, hs.2.2.1,
      (Nat.add_le_add_right hL 1).trans hs.2.2.2⟩
  · intro v u γ
    rw [(hspec v u γ).2.1]
    exact (F.G.fam.identity v u γ).record.width_pos

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The preceding-copy dissipation is the only new input to the path price
of a plain/native source defect. The scalar response estimate is already
proved; this assembly composes it with that actual dissipation, retaining
the factor from rank rescaling and the original full higher datum.

The degenerate cases are included: H=0 has no positive-copy application; empty and singleton
families, zero/constants, D=2, identity geometry, edgeless seeds and degenerate windows.
Only positive diffusivity is divided out, never a datum norm. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationWeightedCarrierSMul
  preparationWeightedLowSMul preparationWeightedLowSpace

variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D H : ℕ} {Part : Type*} {Ctx : Part → Type*}
  {family : ChartedFamily ι h D Part Ctx}

/-- The actual higher lift of one plain copy, truncated only to the reserve
used by its source defect. -/
def preparationPlainCopyHigh (Kc : ι × Fin (H + 1) → ℕ) (K : ι → ℕ)
    (l : Fin (H + 1)) (hK : ∀ j, K j ≤ Kc (j, l))
    (W : ∀ v : ι × Fin (H + 1), ℝ → TorusHk (Kc v + 1) (h v.1)) :
    ∀ j, ℝ → TorusHk (K j + 1) (h j) :=
  fun j t => truncateTorusHk (Nat.succ_le_succ (hK j)) (W (j, l) t)

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The positive plain copy, minus the native scalar response to its actual
preceding copy, has zero datum and the physical moment-gain energy bound.
Both spatial integrability and time integrability are obtained from the
actual descending-slot solution, rather than added to its hypotheses.

The degenerate cases are included: H=0 has no positive copy; D=2 has one order. Empty and singleton
families, zero/constant data, identity geometry and edgeless seeds keep the same
injected datum, actual kernels and ordered jets. The full higher datum is
put only in copy zero. No norm is divided out. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D H Kbase : ℕ} {Part : Type*} {Ctx : Part → Type*}
  {a b ρ ν : ℝ} {family : ChartedFamily ι h D Part Ctx}
  {Q : KernelEnergy.TorusKernelOperator (h := h) (Γ := family.Γ)
    (G := fun _ j _ => h j) a b ρ ν 0 D}

/-- Every added plain copy is genuinely zero-initial, and its source is
exactly the original physical coefficient acting on the preceding copy. -/
theorem preparation_neutral_positive_plain_row
    (F : PreparationPlainKernelFrame Q) (l : Fin H)
    (hK : ∀ j, F.K j ≤ preparationNeutralSlots H D Kbase (j, l.castSucc))
    (e E : ℝ) (actual : ∀ p, Ctx p)
    (hB : ∀ i j γ d, Q.B i j γ d =
      constituentPhysical family ν e E actual i j γ d.val)
    (hC : ∀ i j γ, Q.C i j γ = ContinuousLinearMap.id ℝ (h j))
    {v : ℝ → Vec 2 → Vec 2}
    (f : ∀ i, TorusHk (preparationNeutralSlots H D Kbase (i, 0)) (h i))
    {z : ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y) (h y.1)}
    {U : ∀ y : ι × Fin (H + 1), ℝ → TorusHk (preparationNeutralSlots H D Kbase y + 1) (h y.1)}
    (hs : IsCoupledWeakSolutionTorus ν a b v D (preparationNeutralSlots H D Kbase)
      (edgeCoefficient (preparationNeutralChain family H) ν e E actual
        (preparationNeutralSlots H D Kbase))
      (preparationNeutralInitial H (preparationNeutralSlots H D Kbase) f)
      (fun _ _ => 0) (fun _ _ => 0) z U) (i : ι) :
    IsTorusForcedRow ν a b v 2 0 0
      (F.rows.plainSourceFluxTime (preparationNeutralPrecedingInput F l hK U) i)
      (fun _ => 0) (fun t => truncateTorusHk (Nat.zero_le _) (z (i, l.succ) t))
      (fun t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (U (i, l.succ) t)) := by
  have hp := preparation_neutral_plain_forced_row F l hK e E actual hB hC hs i
  have hl : l.succ ≠ (0 : Fin (H + 1)) := by
    intro he
    have := congrArg Fin.val he
    change l.val + 1 = 0 at this
    omega
  have hf := preparation_neutral_initial_positive_copy H (preparationNeutralSlots H D Kbase)
    f (i, l.succ) hl
  rw [hf, map_zero] at hp
  exact hp

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Choose the genuine neutral evolution once and read every plain layer
into the SAME physical path space. The full higher buffered datum is
injected only into copy zero; each higher L2 class is linear by uniqueness
of the genuine lift. No energy estimate or mass-specific solution choice
is part of this construction.

The degenerate cases are included: H=0 retains its homogeneous copy; D=2, empty and singleton
families, zero or constant datum, identity geometry and edgeless seeds retain the same maps.
The layer slots may differ. Every-time spatial integrability is retained
in the actual descending-slot weak equation. -/

attribute [local instance] preparationNativeFamilyNormed preparationNativeFamilyModule
  preparationNativeContinuousModule preparationPlainNativeModule preparationPlainCarrierSMul
  preparationPlainFamilySMul
variable {ι : Type*} [Fintype ι] {h : ι → Type}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D H : ℕ} {Part : Type*} {Ctx : Part → Type*}
  {family : ChartedFamily ι h D Part Ctx}

local instance preparationNeutralSlotsMonoid (K : ι → ℕ) :
    AddCommMonoid (∀ i, TorusHk (K i) (h i)) := Pi.addCommMonoid

local instance preparationNeutralSlotsModule (K : ι → ℕ) :
    Module ℝ (∀ i, TorusHk (K i) (h i)) := Pi.module _ _ _

local instance preparationNeutralTraceModule (K : ι → ℕ) :
    Module ℝ (∀ i, ℝ → TorusHk (K i) (h i)) := Pi.module _ _ _

local instance preparationNeutralContinuousMonoid (a b : ℝ) :
    AddCommMonoid C(Set.Icc a b, ∀ i, TorusHk 0 (h i)) :=
  (ContinuousMap.instAddCommGroupContinuousMap (α := Set.Icc a b)
    (β := ∀ i, TorusHk 0 (h i))).toAddCommMonoid

-- Close the additive head once; subsequent linear-map constructors must
-- not search through the continuous-map norm and the Lp quotient again.
local instance preparationNeutralEnergyAdd (a b c : ℝ) :
    AddCommGroup (PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) :=
  @Prod.instAddCommGroup _ _ ContinuousMap.instAddCommGroupContinuousMap Lp.instAddCommGroup

local instance preparationNeutralEnergyMonoid (a b c : ℝ) :
    AddCommMonoid (PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) :=
  (preparationNeutralEnergyAdd (h := h) a b c).toAddCommMonoid

local instance preparationNeutralEnergyModule (a b c : ℝ) :
    Module ℝ (PreparationEnergyPath (∀ i, TorusHk 0 (h i))
      (CoupledHighHilbert (h := h) (fun _ => 0)) a b c) := Prod.instModule

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
