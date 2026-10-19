-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergy.TorusFactorialReadout
public import AVRegularity.KernelEnergy.TorusGraphProjection
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq
import AVRegularity.Proofs.Intermediate.KernelEnergy.KernelFluxBoundTorus
import AVRegularity.CoupledEnergy.Galerkin.PlainTestedIntegralEquation
import AVRegularity.CoupledEnergy.Galerkin.PlainComponentTest
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! Retain every regularizer gain to control the complete higher lifted carrier. -/

section
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

omit [FiniteDimensional ℝ G] in
theorem castTorusHk_norm {K L : ℕ} (he : K = L) (Y : TorusHk K G) :
    ‖castTorusHk he Y‖ = ‖Y‖ := by
  cases he
  rfl

theorem torusRegularizedInput_normSq_bound (ρ : ℝ) (hρ : 0 < ρ) (k D : ℕ) (hD : 2 ≤ D)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b) (c : ℕ → ℝ) (r : ℝ)
    (C : H →L[ℝ] G)
    (S : ℝ → Lp G 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp G 2 (volume.restrict AVenhance.unitCube))
    (hS : IsSpatialRegularizerTorus ρ k D a b c r S) (V : TorusHk (k + 1) H) :
    ‖torusRegularizedInput ρ k D hD a b c r C S hS t ht V‖ ^ 2 ≤
      ((k + (D - 2) + 2 : ℕ) : ℝ) * regularizerGainBudget c r D *
        (‖C‖ ^ 2 * factorialWeightMax ρ k) / factorialWeightMin ρ k * ‖V‖ ^ 2 := by
  obtain ⟨Y, hY, hb⟩ := torusRegularizer_exists_shifted_bounds ρ k D hD a b t ht c r C S hS V
  have hm : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  have hbase : 0 ≤ ‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg ‖C‖) hm) (sq_nonneg ‖V‖)
  have hB (m : ℕ) (hm : m ≤ D - 2 + 1) :
      derivFactorialNormSq m ρ (truncateJet (by omega : k + m ≤ k + (D - 2) + 1) Y.val) ≤
        regularizerGainBudget c r D * (‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2) :=
    (hb m hm).trans (mul_le_mul_of_nonneg_right (regularizer_gain_le_budget c r D m hD hm) hbase)
  have hnorm := shiftedJet_full_norm_bound ρ hρ (D - 2 + 1) Y.val
    (regularizerGainBudget c r D * (‖C‖ ^ 2 * factorialWeightMax ρ k * ‖V‖ ^ 2)) hB
  have he : k + (D - 2) + 1 = k + D - 1 := by omega
  have hcanon : castTorusHk he Y = torusRegularizedInput ρ k D hD a b c r C S hS t ht V := by
    apply TorusHk.ext_value
    rw [castTorusHk_valueIndex, torusRegularizedInput_value]
    exact hY
  rw [← hcanon, castTorusHk_norm]
  change ‖Y.val‖ ^ 2 ≤ _
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hnorm ⊢
  convert hnorm using 1
  ring
end

/-! The canonical lift and raw flux of a kernel on the torus. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def lift (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (k + 1) (h i))
    (i j : ι) (α : Γ i j) : TorusHk (k + D - 1) (G i j α) :=
  torusRegularizedInput ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) t ht (V j)

theorem lift_value (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (k + 1) (h i))
    (i j : ι) (α : Γ i j) :
    (P.lift t ht V i j α).val (valueIndex2 (k + D - 1)) =
      P.S i j α t ((P.C i j α).compLp ((V j).val (valueIndex2 (k + 1)))) :=
  torusRegularizedInput_value ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) t ht (V j)

def rawFlux (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (k + 1) (h i))
    (i : ι) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i) :=
  ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
    P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
      (P.lift t ht V i j α).toFunction.jet
        ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x)

theorem exists_flux (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (k + 1) (h i)) :
    ∃ Q : ∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)),
      (∀ i, (Q i).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
        P.rawFlux t ht V i) ∧
      massNormSq ρ P.π (fun i => (Q i).val) ≤
        (ν * P.θ) ^ 2 * massGradNormSq ρ P.π (fun i => (V i).val) := by
  obtain ⟨Y, Q, hY, hQ, hb⟩ := AVRegularity.Providers.kernel_flux_bound_torus
    a b P.htime ρ P.radius_pos ν P.diffusivity_pos k D P.order_ge_two P.π P.hπ
    P.B P.hB_meas P.hB_smooth P.hB_per P.hB_fin P.C P.S P.c P.r P.hr P.hS P.θ P.hθ P.hschur t ht V
  have he : Y = P.lift t ht V := by
    funext i j α
    apply TorusHk.ext_value
    exact (hY i j α).trans (P.lift_value t ht V i j α).symm
  rw [he] at hQ
  exact ⟨Q, hQ, hb⟩

def flux (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (k + 1) (h i)) :
    ∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  Classical.choose (P.exists_flux t ht V)

theorem flux_raw (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (k + 1) (h i)) (i : ι) :
    (P.flux t ht V i).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      P.rawFlux t ht V i := (Classical.choose_spec (P.exists_flux t ht V)).1 i

theorem flux_mass_bound (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (k + 1) (h i)) :
    massNormSq ρ P.π (fun i => (P.flux t ht V i).val) ≤
      (ν * P.θ) ^ 2 * massGradNormSq ρ P.π (fun i => (V i).val) :=
  (Classical.choose_spec (P.exists_flux t ht V)).2

end TorusKernelOperator
end

/-! Linearity of the canonical lift and of the raw flux in the input. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem lift_add (t : ℝ) (ht : t ∈ Set.Icc a b)
    (U V : ∀ i, TorusHk (k + 1) (h i)) (i j : ι) (α : Γ i j) :
    P.lift t ht (U + V) i j α = P.lift t ht U i j α + P.lift t ht V i j α :=
  (torusRegularizedInputLinearMap ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) t ht).map_add (U j) (V j)

theorem lift_smul (t : ℝ) (ht : t ∈ Set.Icc a b) (q : ℝ)
    (U : ∀ i, TorusHk (k + 1) (h i)) (i j : ι) (α : Γ i j) :
    P.lift t ht (fun i => q • U i) i j α = q • P.lift t ht U i j α :=
  (torusRegularizedInputLinearMap ρ k D P.order_ge_two a b P.c (P.r i j α) (P.C i j α)
    (P.S i j α) (P.hS i j α) t ht).map_smul q (U j)

theorem rawFlux_add_ae (t : ℝ) (ht : t ∈ Set.Icc a b)
    (U V : ∀ i, TorusHk (k + 1) (h i)) (i : ι) :
    P.rawFlux t ht (U + V) i =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => P.rawFlux t ht U i x + P.rawFlux t ht V i x := by
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      ∀ j (α : Γ i j) (a : JetIndex2 (k + D - 1)),
      (P.lift t ht (U + V) i j α).toFunction.jet a x =
        (P.lift t ht U i j α).toFunction.jet a x + (P.lift t ht V i j α).toFunction.jet a x := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro α
    apply ae_all_iff.mpr
    intro a
    rw [P.lift_add]
    exact torusJet_add_ae _ _ a
  filter_upwards [hj] with x hx
  unfold rawFlux
  have he (j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
      P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht (U + V) i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) =
      P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht U i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) +
      P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht V i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
    rw [← (P.B i j α d t x).map_add]
    congr 1
    apply PiLp.ext
    intro word
    exact hx j α _
  simp_rw [he, Finset.sum_add_distrib]

theorem rawFlux_smul_ae (t : ℝ) (ht : t ∈ Set.Icc a b) (q : ℝ)
    (U : ∀ i, TorusHk (k + 1) (h i)) (i : ι) :
    P.rawFlux t ht (fun i => q • U i) i =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => q • P.rawFlux t ht U i x := by
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      ∀ j (α : Γ i j) (a : JetIndex2 (k + D - 1)),
      (P.lift t ht (fun i => q • U i) i j α).toFunction.jet a x =
        q • (P.lift t ht U i j α).toFunction.jet a x := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro α
    apply ae_all_iff.mpr
    intro a
    rw [P.lift_smul]
    exact torusJet_smul_ae q _ a
  filter_upwards [hj] with x hx
  unfold rawFlux
  have he (j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
      P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht (fun i => q • U i) i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) =
      q • P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht U i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
    rw [← (P.B i j α d t x).map_smul]
    congr 1
    apply PiLp.ext
    intro word
    exact hx j α _
  simp_rw [he, Finset.smul_sum]

def fluxLinearMap (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (∀ i, TorusHk (k + 1) (h i)) →ₗ[ℝ] (∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) where
  toFun := P.flux t ht
  map_add' U V := by
    funext i
    apply torusCarrier_eq_of_value_ae
    filter_upwards [P.flux_raw t ht (U + V) i, P.flux_raw t ht U i, P.flux_raw t ht V i,
      P.rawFlux_add_ae t ht U V i,
      torusJet_add_ae (P.flux t ht U i) (P.flux t ht V i) (valueIndex2 k)] with x hsum hU hV ha hr
    exact hsum.trans (ha.trans ((congrArg₂ (· + ·) hU hV).symm.trans hr.symm))
  map_smul' q U := by
    funext i
    apply torusCarrier_eq_of_value_ae
    filter_upwards [P.flux_raw t ht (fun i => q • U i) i, P.flux_raw t ht U i,
      P.rawFlux_smul_ae t ht q U i,
      torusJet_smul_ae q (P.flux t ht U i) (valueIndex2 k)] with x hsum hU ha hr
    exact hsum.trans (ha.trans ((congrArg (q • ·) hU).symm.trans hr.symm))

end TorusKernelOperator
end

/-! The family of flux terms of the canonical kernel flux and their assembled flux. -/

section
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def fluxTerm (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (k + 1) (h i))
    (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  torusKernelFluxTerm (m := d.1 - 2) (r := d.1 - 1)
    (by have := Finset.mem_Icc.1 d.2; omega) ρ P.radius_pos a b
    (P.B i j α d) (P.hB_fin i j α d) t ht (P.hB_smooth i j α d t ht) (P.hB_per i j α d t ht)
    (truncateTorusHk (by have := Finset.mem_Icc.1 d.2; omega) (P.lift t ht V i j α))

theorem fluxTerm_raw (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (k + 1) (h i))
    (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
    (P.fluxTerm t ht V i j α d).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (P.lift t ht V i j α).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
  have hd := Finset.mem_Icc.1 d.2
  have hr : d.1 - 1 = (d.1 - 2) + 1 := by omega
  have hlow : k + ((d.1 - 2) + 1) ≤ k + D - 1 := by omega
  have hb := torusKernelFluxTerm_base_ae hr ρ P.radius_pos a b (P.B i j α d)
    (P.hB_fin i j α d) t ht (P.hB_smooth i j α d t ht) (P.hB_per i j α d t ht)
    (truncateTorusHk hlow (P.lift t ht V i j α))
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ word : DerivativeWord2 (d.1 - 1),
      (truncateTorusHk hlow (P.lift t ht V i j α)).toFunction.jet
        ⟨⟨d.1 - 1, by omega⟩, word⟩ x =
      (P.lift t ht V i j α).toFunction.jet ⟨⟨d.1 - 1, by omega⟩, word⟩ x := by
    apply ae_all_iff.mpr
    intro word
    exact truncateTorusHk_toFunction_jet_ae hlow (P.lift t ht V i j α) _
  filter_upwards [hb, hj] with x hx hjx
  exact hx.trans (congrArg (P.B i j α d t x) (PiLp.ext (fun word => hjx word)))

def assembledFlux (t : ℝ) (ht : t ∈ Set.Icc a b) (V : ∀ i, TorusHk (k + 1) (h i))
    (i : ι) : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D), P.fluxTerm t ht V i j α d

theorem assembledFlux_raw (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, TorusHk (k + 1) (h i)) (i : ι) :
    (P.assembledFlux t ht V i).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      P.rawFlux t ht V i := by
  classical
  apply torusJet_sum_ae_of_eq
  intro j
  apply torusJet_sum_ae_of_eq
  intro α
  apply torusJet_sum_ae_of_eq
  intro d
  exact P.fluxTerm_raw t ht V i j α d

theorem assembledFlux_eq_flux (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, TorusHk (k + 1) (h i)) (i : ι) :
    P.assembledFlux t ht V i = P.flux t ht V i := by
  apply torusCarrier_eq_of_value_ae
  exact (P.assembledFlux_raw t ht V i).trans (P.flux_raw t ht V i).symm

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergy

/-! Reuse the finite Fourier reconstruction to recover Sobolev-valued
measurability from the measurable value class, without extra time regularity. -/

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
variable {T : Type*} [MeasurableSpace T]

theorem torusCarrier_aestronglyMeasurable_of_value (μ : Measure T) (k : ℕ)
    (u : T → TorusHk k G)
    (hv : AEStronglyMeasurable (fun t => torusHkValueCLM (u t)) μ) :
    AEStronglyMeasurable u μ := by
  let K : Unit → ℕ := fun _ => k
  let family : ∀ _ : Unit, T → TorusHk k G := fun _ => u
  have hm (N : ℕ) : AEStronglyMeasurable (fun t => galerkinProj N (u t)) μ := by
    have hrow (r : CoupledFourierModeIndex (h := fun _ : Unit => G) N) :
        AEStronglyMeasurable (fun t => plainInitialCoefficients N K (fun i => family i t) r) μ := by
      have hi := (InnerProductSpace.toDual ℝ _
        (plainModeCellLp N r r.1 0 Fin.elim0)).continuous.comp_aestronglyMeasurable hv
      simpa only [plainInitialCoefficients_component, plainValueForcingCLM,
        ContinuousLinearMap.comp_apply, K, family] using! hi
    have hc : AEStronglyMeasurable (fun t => plainInitialCoefficients N K (fun i => family i t)) μ :=
      (aemeasurable_pi_iff.mpr (fun r => (hrow r).aemeasurable)).aestronglyMeasurable
    have hs := (coupledPlainSynthesis (h := fun _ : Unit => G) N () k).continuous.comp_aestronglyMeasurable hc
    have he (t : T) : coupledPlainSynthesis (h := fun _ : Unit => G) N () k
        (plainInitialCoefficients N K (fun i => family i t)) = galerkinProj N (u t) :=
      plainInitialCoefficients_synthesis (h := fun _ : Unit => G) N K (fun i => family i t) ()
    exact hs.congr (Eventually.of_forall he)
  exact aestronglyMeasurable_of_tendsto_ae atTop hm
    (Eventually.of_forall (fun t => galerkinProj_tendsto (u t)))


theorem torusCarrier_stronglyMeasurable_of_tests (k : ℕ) (u : T → TorusHk k G)
    (htest : ∀ φ : TorusHk 1 G, StronglyMeasurable
      (fun t => inner ℝ (torusHkValueCLM (u t)) (torusHkValueCLM φ))) :
    StronglyMeasurable u := by
  let K : Unit → ℕ := fun _ => k
  let family : ∀ _ : Unit, T → TorusHk k G := fun _ => u
  have hm (N : ℕ) : StronglyMeasurable (fun t => galerkinProj N (u t)) := by
    have hrow (r : CoupledFourierModeIndex (h := fun _ : Unit => G) N) :
        StronglyMeasurable (fun t => plainInitialCoefficients N K (fun i => family i t) r) := by
      simpa only [plainInitialCoefficients_mode_pairing, K, family] using!
        htest (coupledModeHk (h := fun _ : Unit => G) N r r.1 1)
    have hc : StronglyMeasurable (fun t => plainInitialCoefficients N K (fun i => family i t)) :=
      (measurable_pi_iff.mpr (fun r => (hrow r).measurable)).stronglyMeasurable
    have hs := (coupledPlainSynthesis (h := fun _ : Unit => G) N () k).continuous.comp_stronglyMeasurable hc
    have he (t : T) : coupledPlainSynthesis (h := fun _ : Unit => G) N () k
        (plainInitialCoefficients N K (fun i => family i t)) = galerkinProj N (u t) :=
      plainInitialCoefficients_synthesis (h := fun _ : Unit => G) N K (fun i => family i t) ()
    have hefun : (fun t => coupledPlainSynthesis (h := fun _ : Unit => G) N () k
        (plainInitialCoefficients N K (fun i => family i t))) = (fun t => galerkinProj N (u t)) := funext he
    rwa [hefun] at hs
  exact stronglyMeasurable_of_tendsto atTop hm (tendsto_pi_nhds.mpr (fun t => galerkinProj_tendsto (u t)))

theorem torusCarrier_stronglyMeasurable_of_value (k : ℕ) (u : T → TorusHk k G)
    (hv : StronglyMeasurable (fun t => torusHkValueCLM (u t))) : StronglyMeasurable u := by
  apply torusCarrier_stronglyMeasurable_of_tests k u
  intro φ
  exact hv.inner stronglyMeasurable_const

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Component factorial energies and their time-integrated gradients converge under Fourier cutoff. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem galerkinProj_factorialNormSq_tendsto (k : ℕ) (ρ : ℝ) (u : TorusHk k E) :
    Tendsto (fun N => factorialNormSq ρ (galerkinProj N u).val) atTop
      (𝓝 (factorialNormSq ρ u.val)) := by
  have hl := ((torusFactorialReadout (E := E) ρ k).continuous.tendsto u).comp (galerkinProj_tendsto u)
  simpa only [Function.comp_def, torusFactorialReadout_apply, AVRegularity.CoupledEnergy.Variational.factorialWeightedJet_normSq] using! hl.norm.pow 2

theorem galerkinProj_gradFactorial_integral_tendsto (k : ℕ) (a b ρ : ℝ)
    (w : ℝ → TorusHk (k + 1) E) (hw : MemLp w 2 (volume.restrict (Set.Icc a b))) :
    Tendsto (fun N => ∫ t in Set.Icc a b, gradFactorialNormSq ρ (galerkinProj N (w t)).val)
      atTop (𝓝 (∫ t in Set.Icc a b, gradFactorialNormSq ρ (w t).val)) := by
  have hl := galerkinProj_massGradNormSq_integral_tendsto (E := fun _ : Unit => E)
    (fun _ => k) a b ρ (fun _ => 1) (fun _ => w) (fun _ => hw)
  simpa only [massGradNormSq, Fintype.sum_unique, inv_one, one_mul] using hl

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergy

/-! Time measurability of the existing Sobolev multiplier, with only the
original joint measurability of the coefficient values. -/

variable {E F T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [MeasurableSpace T] {K : ℕ}
variable (μ : Measure T) [IsFiniteMeasure μ]
  (ρ : ℝ) (hρ : 0 < ρ) (C : T → Vec 2 → E →L[ℝ] F)
  (hm : Measurable (Function.uncurry C))
  (hc : ∀ t, ContDiff ℝ (K : ℕ) (C t)) (hp : ∀ t, AVenhance.IsZ2Periodic (C t))
  (A : Fin (K + 1) → ℝ)
  (hb : ∀ t l x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l)

include hm hρ in
theorem torusMultiplier_fixed_aestronglyMeasurable (u : TorusHk K E) :
    AEStronglyMeasurable (fun t => u.mulCoefficient (C t) (hc t) (hp t) (hb t)) μ := by
  apply torusCarrier_aestronglyMeasurable_of_integrable_tests μ K
  intro φ
  have hpair := coefficientPairing_stronglyMeasurable C hm
    (torusHkValueCLM u) (torusHkValueCLM φ)
  have he (t : T) : inner ℝ
      (torusHkValueCLM (u.mulCoefficient (C t) (hc t) (hp t) (hb t))) (torusHkValueCLM φ) =
      ∫ x in AVenhance.unitCube, inner ℝ (C t x (torusHkValueCLM u x)) (torusHkValueCLM φ x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [torusMulCoefficient_value_ae u (C t) (hc t) (hp t) (hb t)] with x hx
    exact congrArg (fun z => inner ℝ z (torusHkValueCLM φ x)) hx
  have hmeas := (hpair.aestronglyMeasurable (μ := μ)).congr (Eventually.of_forall (fun t => (he t).symm))
  let L : ℝ := (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l) *
    Real.sqrt (factorialWeightMax ρ K) / Real.sqrt (factorialWeightMin ρ K)
  have hbound (t : T) : ‖inner ℝ
      (torusHkValueCLM (u.mulCoefficient (C t) (hc t) (hp t) (hb t))) (torusHkValueCLM φ)‖ ≤
      ‖torusHkValueCLM (E := F) (K := K)‖ * (L * ‖u‖) * ‖torusHkValueCLM φ‖ := by
    have hi := torusMultiplier_norm_bound (C t) (hc t) (hp t) A (hb t) ρ hρ u
    have hv := (torusHkValueCLM (E := F) (K := K)).le_opNorm
      (u.mulCoefficient (C t) (hc t) (hp t) (hb t))
    have hn := hv.trans (mul_le_mul_of_nonneg_left hi (norm_nonneg _))
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  exact (integrable_const (‖torusHkValueCLM (E := F) (K := K)‖ * (L * ‖u‖) *
    ‖torusHkValueCLM φ‖)).mono' hmeas (Eventually.of_forall hbound)

include hm hρ in
theorem torusMultiplier_time_aestronglyMeasurable (u : T → TorusHk K E)
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun t => (u t).mulCoefficient (C t) (hc t) (hp t) (hb t)) μ := by
  exact timeOperator_aestronglyMeasurable μ
    (fun t => torusMultiplierCLM (C t) (hc t) (hp t) A (hb t) ρ hρ)
    (fun z => torusMultiplier_fixed_aestronglyMeasurable μ ρ hρ C hm hc hp A hb z) u hu

include hm in
theorem torusMultiplier_fixed_stronglyMeasurable (u : TorusHk K E) :
    StronglyMeasurable (fun t => u.mulCoefficient (C t) (hc t) (hp t) (hb t)) := by
  apply torusCarrier_stronglyMeasurable_of_tests K
  intro φ
  have hpair := coefficientPairing_stronglyMeasurable C hm
    (torusHkValueCLM u) (torusHkValueCLM φ)
  have he (t : T) : inner ℝ
      (torusHkValueCLM (u.mulCoefficient (C t) (hc t) (hp t) (hb t))) (torusHkValueCLM φ) =
      ∫ x in AVenhance.unitCube, inner ℝ (C t x (torusHkValueCLM u x)) (torusHkValueCLM φ x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [torusMulCoefficient_value_ae u (C t) (hc t) (hp t) (hb t)] with x hx
    exact congrArg (fun z => inner ℝ z (torusHkValueCLM φ x)) hx
  have hefun : (fun t => inner ℝ
      (torusHkValueCLM (u.mulCoefficient (C t) (hc t) (hp t) (hb t))) (torusHkValueCLM φ)) =
      (fun t => ∫ x in AVenhance.unitCube,
        inner ℝ (C t x (torusHkValueCLM u x)) (torusHkValueCLM φ x)) := funext he
  rw [hefun]
  exact hpair

include hm hρ in
theorem torusMultiplier_time_stronglyMeasurable (u : T → TorusHk K E)
    (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun t => (u t).mulCoefficient (C t) (hc t) (hp t) (hb t)) := by
  exact timeOperator_stronglyMeasurable
    (fun t => torusMultiplierCLM (C t) (hc t) (hp t) A (hb t) ρ hρ)
    (fun z => torusMultiplier_fixed_stronglyMeasurable C hm hc hp A hb z) u hu

end AVRegularity.KernelEnergy
end
