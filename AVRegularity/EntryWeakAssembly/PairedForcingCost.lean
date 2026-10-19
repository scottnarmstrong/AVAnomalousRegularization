-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Assembly.WeakEntryPairedForcing
public import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.KernelEnergyPlane.PlaneFluxTermFamily
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import AVRegularity.EntryTerminal.Ingredients.PrepCore.JetFacts
import AVRegularity.KernelEnergy.TorusKernelStrongTraceExistence
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! **The forcing equation, part 1: the lift-forced equation** (generic in the operator `P`).

A solution `(u, w, y)` of the kernel-regularized system with an arbitrary family of regularizers
`S'` (for instance the raw system, `S' = id`) is a solution of the coupled system whose flux is
the carrier flux `P.carrierFlux w` of the regularized lift of `w` for the regularizers of `P`,
plus the explicit forcing `P.liftForcing y w` (the flux of `y - P.higherInput w`).
* `fluxTermOf_raw`, `liftForcing_raw_ae`: the values of the forcing are the raw flux of `y` minus
  the raw flux of the regularized lift of `w`.
* `liftForced_weakSolution`: the equation. -/

section
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
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

omit [DecidableEq ι] in
theorem fluxTermOf_congr_time (t t' : ℝ) (ht : t ∈ Set.Icc a b) (ht' : t' ∈ Set.Icc a b)
    (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) (Y : TorusHk (k + D - 1) (G i j α))
    (e : t = t') : P.fluxTermOf t ht i j α d Y = P.fluxTermOf t' ht' i j α d Y := by
  subst e
  rfl

omit [DecidableEq ι] in
/-- The values of the flux term of a lift `Y`. -/
theorem fluxTermOf_raw (t : ℝ) (ht : t ∈ Set.Icc a b) (i j : ι) (α : Γ i j)
    (d : ↥(Finset.Icc 2 D)) (Y : TorusHk (k + D - 1) (G i j α)) :
    (P.fluxTermOf t ht i j α d Y).toFunction.jet (valueIndex2 k)
        =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        Y.toFunction.jet ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
  have hd := Finset.mem_Icc.1 d.2
  have hr : d.1 - 1 = (d.1 - 2) + 1 := by omega
  have hlow : k + ((d.1 - 2) + 1) ≤ k + D - 1 := by omega
  have hb := torusKernelFluxTerm_base_ae hr ρ P.radius_pos a b (P.B i j α d)
    (P.hB_fin i j α d) t ht (P.hB_smooth i j α d t ht) (P.hB_per i j α d t ht)
    (truncateTorusHk hlow Y)
  have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ word : DerivativeWord2 (d.1 - 1),
      (truncateTorusHk hlow Y).toFunction.jet ⟨⟨d.1 - 1, by omega⟩, word⟩ x =
      Y.toFunction.jet ⟨⟨d.1 - 1, by omega⟩, word⟩ x := by
    apply ae_all_iff.mpr
    intro word
    exact truncateTorusHk_toFunction_jet_ae hlow Y _
  filter_upwards [hb, hj] with x hx hjx
  exact hx.trans (congrArg (P.B i j α d t x) (PiLp.ext (fun word => hjx word)))

omit [DecidableEq ι] in
/-- The jets of a difference are the difference of the jets. -/
theorem torusJet_sub_ae' {K : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (f g : TorusHk K E) (a : JetIndex2 K) :
    (f - g).toFunction.jet a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => f.toFunction.jet a x - g.toFunction.jet a x := by
  have e : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  filter_upwards [torusJet_add_ae f ((-1 : ℝ) • g) a, torusJet_smul_ae (-1 : ℝ) g a] with x h1 h2
  rw [e, h1, h2, neg_one_smul, sub_eq_add_neg]

omit [DecidableEq ι] in
/-- The values of the lift forcing: the raw flux of `y` minus the raw flux of the regularized
lift of `w`. -/
theorem liftForcing_raw_ae (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i)) (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (P.liftForcing y w i t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => P.inputRawFlux y i t x - P.kernelRawFlux w i t x := by
  have hF : P.liftForcing y w i t = ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
      P.fluxTermOf t ht i j α d (y i j α t - P.higherInput w i j α t) := by
    unfold liftForcing
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun d _ => P.fluxTermOf_congr_time _ _ _ _ i j α d _ ?_
    rw [Set.projIcc_of_mem P.htime ht]
  rw [hF]
  have hterm : ∀ (j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)),
      (P.fluxTermOf t ht i j α d (y i j α t - P.higherInput w i j α t)).toFunction.jet
          (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (y i j α t).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) -
          P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            (P.higherInput w i j α t).toFunction.jet
              ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) := by
    intro j α d
    have hj : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ word : DerivativeWord2 (d.1 - 1),
        (y i j α t - P.higherInput w i j α t).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x =
          (y i j α t).toFunction.jet
              ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x -
            (P.higherInput w i j α t).toFunction.jet
              ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x := by
      apply ae_all_iff.mpr
      intro word
      exact torusJet_sub_ae' _ _ _
    filter_upwards [P.fluxTermOf_raw t ht i j α d (y i j α t - P.higherInput w i j α t), hj]
      with x hx hjx
    rw [hx, ← map_sub]
    congr 1
    ext word
    simpa [PiLp.sub_apply] using hjx word
  have hsum := torusJet_sum_ae_of_eq (K := k) (fun j : ι => ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
      P.fluxTermOf t ht i j α d (y i j α t - P.higherInput w i j α t)) (valueIndex2 k)
    (fun j x => ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
      (P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (y i j α t).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) -
        P.B i j α d t x (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
          (P.higherInput w i j α t).toFunction.jet
            ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x)))
    (fun j => by
      apply torusJet_sum_ae_of_eq
      intro α
      apply torusJet_sum_ae_of_eq
      intro d
      exact hterm j α d)
  filter_upwards [hsum] with x hx
  rw [hx]
  unfold inputRawFlux kernelRawFlux
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_sub_distrib]

omit [DecidableEq ι] in
/-- **The lift-forced equation**: a solution `(u, w, y)` of the kernel-regularized system (for
any regularizers `S'`) is a solution of the coupled system with the flux
`F + liftForcing y w + carrierFlux w` of the operator `P`. -/
theorem liftForced_weakSolution
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (f : ∀ i, TorusHk k (h i))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (u : ∀ i, ℝ → TorusHk k (h i)) (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    {S' : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube))}
    (hsol : IsKernelWeakSolutionTorus ν a b v k D P.B P.C S' f F g u w y) :
    IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient f
      (fun i t => F i t + (P.liftForcing y w i t + P.carrierFlux w i t)) g u w := by
  refine ⟨hsol.1, hsol.2.1, hsol.2.2.1, hsol.2.2.2.1, ?_⟩
  intro i t ht φ
  have hs : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hf : ∀ᵐ r ∂volume.restrict (Set.Ioc a t), ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      P.inputRawFlux y i r x + (F i r).toFunction.jet (valueIndex2 k) x =
      torusRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun j => w j r) i x +
        (F i r + (P.liftForcing y w i r + P.carrierFlux w i r)).toFunction.jet
          (valueIndex2 k) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hrI
    have hr := hs hrI
    filter_upwards [P.liftForcing_raw_ae y w i r hr, P.carrierFlux_raw w i r hr,
      torusJet_add_ae (F i r) (P.liftForcing y w i r + P.carrierFlux w i r) (valueIndex2 k),
      torusJet_add_ae (P.liftForcing y w i r) (P.carrierFlux w i r) (valueIndex2 k)]
      with x h1 h2 h3 h4
    rw [noLocalRawFlux_zero (h := h) (k := k) w i r x, zero_add, h3, h4, h1, h2]
    abel
  have hp : ∀ r ∈ Set.Ioc a t,
      Integrable (torusRawSpatialRhs (fun _ => k) 0 ν r v noLocalCoefficient
        (fun j s => F j s + (P.liftForcing y w j s + P.carrierFlux w j s)) g (fun j => w j r) i φ)
        (volume.restrict AVenhance.unitCube) := by
    intro r hr
    exact (torusRawSpatialRhs_integrable_and_integral (fun _ => k) 0 ν ρ P.radius_pos
      a b r (hs hr) v (hv r (hs hr)).continuous V hV (hvb r (hs hr))
      noLocalCoefficient (noLocalSeminorm (h := h) (k := k) (ρ := ρ) (a := a) (b := b))
      (fun j j' d => (noLocalSmoothOnInterval (h := h) (k := k) r (hs hr) j j' d).continuous)
      (fun j s => F j s + (P.liftForcing y w j s + P.carrierFlux w j s)) g (fun j => w j r)
      i φ).1
  exact weakIdentity_flux_congr_time (volume.restrict AVenhance.unitCube) ν a t v
    ((u i t).toFunction.jet (valueIndex2 k)) ((f i).toFunction.jet (valueIndex2 k))
    (φ.toFunction.jet (valueIndex2 1))
    (fun q => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => q⟩)
    (fun r q => (w i r).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => q⟩)
    (P.inputRawFlux y i) (fun r => (F i r).toFunction.jet (valueIndex2 k))
    (fun r => torusRawCouplingFlux (fun _ => k) 0 r noLocalCoefficient (fun j => w j r) i)
    (fun r => (F i r + (P.liftForcing y w i r + P.carrierFlux w i r)).toFunction.jet
      (valueIndex2 k))
    (fun r => (g i r).toFunction.jet (valueIndex2 k)) hf hp (hsol.2.2.2.2.2.2 i t ht φ)

end TorusKernelOperator
end

/-! **The forcing equation, part 2: the lift forcing is measurable and square integrable in time.**
* `derivFactorialNormSq_le_jetNormSq`: the factorial norm of the order-`r` derivative tensor is
  at most `wmax` times the squared jet norm.
* `fluxTermOf_norm_le`: the carrier flux term of a lift is a bounded linear function of the lift,
  with a bound that does not depend on the time.
* `liftForcing_aestronglyMeasurable`, `liftForcing_memLp`: time measurability and `L²` in time,
  for lifts `y` and gradient lifts `w` that are `L²` in time. -/

section
section Norm

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {μ : Measure (Vec 2)}

theorem derivFactorialNormSq_le_jetNormSq {K r : ℕ} (ρ : ℝ) (D : JetL2 μ (K + r) E) :
    derivFactorialNormSq r ρ D ≤ factorialWeightMax ρ K * ‖D‖ ^ 2 := by
  have hm : 0 ≤ factorialWeightMax ρ K :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (K + 1)))
  let g : Fin (K + 1) → Fin (K + r + 1) := fun i => ⟨i.val + r, by omega⟩
  have hg : Function.Injective g := by
    intro i i' h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [g] at this
    omega
  change (∑ i : Fin (K + 1), factorialWeight ρ i.val * derivativeNormSq D (g i)) ≤ _
  calc
    _ ≤ ∑ i : Fin (K + 1), factorialWeightMax ρ K * derivativeNormSq D (g i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (factorialWeight_le_max ρ i)
        (derivativeNormSq_nonneg D _)
    _ = factorialWeightMax ρ K * ∑ i : Fin (K + 1), derivativeNormSq D (g i) := by
      rw [Finset.mul_sum]
    _ ≤ factorialWeightMax ρ K * ∑ j : Fin (K + r + 1), derivativeNormSq D j :=
      mul_le_mul_of_nonneg_left
        (sum_comp_le_sum_nonneg g hg (derivativeNormSq D) (derivativeNormSq_nonneg D)) hm
    _ = _ := by rw [jet_norm_sq_eq_sum]

end Norm

variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
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

omit [DecidableEq ι] in
theorem fluxTermOf_time_stronglyMeasurable (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D))
    (Yt : Set.Icc a b → TorusHk (k + D - 1) (G i j α)) (hY : StronglyMeasurable Yt) :
    StronglyMeasurable (fun t : Set.Icc a b => P.fluxTermOf t t.property i j α d (Yt t)) := by
  have hlow : k + ((d.1 - 2) + 1) ≤ k + D - 1 := by
    have := Finset.mem_Icc.1 d.2
    omega
  have hY' := (truncateTorusHk (E := G i j α) hlow).continuous.comp_stronglyMeasurable hY
  exact torusKernelFluxTerm_time_stronglyMeasurable
    (by have := Finset.mem_Icc.1 d.2; omega) ρ P.radius_pos a b
    (P.B i j α d) (P.hB_fin i j α d) (P.hB_meas i j α d)
    (P.hB_smooth i j α d) (P.hB_per i j α d) _ hY'

omit [DecidableEq ι] in
/-- The carrier flux term of a lift is bounded by a multiple of the norm of the lift, with a
constant independent of the time. -/
theorem fluxTermOf_norm_le (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (ht : t ∈ Set.Icc a b) (Y : TorusHk (k + D - 1) (G i j α)),
      ‖P.fluxTermOf t ht i j α d Y‖ ≤ C * ‖Y‖ := by
  have hd := Finset.mem_Icc.1 d.2
  have hr : d.1 - 1 = (d.1 - 2) + 1 := by omega
  have hlow : k + ((d.1 - 2) + 1) ≤ k + D - 1 := by omega
  have hwmin := factorialWeightMin_pos ρ P.radius_pos (K := k)
  have hwmax : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  refine ⟨(coefficientSeminorm ρ k a b (P.B i j α d)).toReal *
    Real.sqrt (factorialWeightMax ρ k) * ‖truncateTorusHk (E := G i j α) hlow‖ /
      Real.sqrt (factorialWeightMin ρ k), by positivity, ?_⟩
  intro t ht Y
  set Z := truncateTorusHk hlow Y with hZ
  have hZn : ‖Z‖ ≤ ‖truncateTorusHk (E := G i j α) hlow‖ * ‖Y‖ :=
    (truncateTorusHk (E := G i j α) hlow).le_opNorm Y
  have hder : derivFactorialNormSq (d.1 - 2 + 1) ρ Z.val ≤
      1 ^ 2 * 1 ^ 2 * (factorialWeightMax ρ k * ‖Z‖ ^ 2) := by
    rw [one_pow, one_mul, one_mul]
    exact derivFactorialNormSq_le_jetNormSq ρ Z.val
  have hfl := torusKernelFluxTerm_factorialNorm_le (m := d.1 - 2) (r := d.1 - 1) hr ρ
    P.radius_pos a b (P.B i j α d) (P.hB_fin i j α d) t ht (P.hB_smooth i j α d t ht)
    (P.hB_per i j α d t ht) Z 1 zero_le_one 1 zero_le_one (factorialWeightMax ρ k * ‖Z‖ ^ 2)
    (mul_nonneg hwmax (sq_nonneg _)) hder
  have hQ := KernelEnergyPlane.jetNorm_le_factorialRoot ρ P.radius_pos
    (P.fluxTermOf t ht i j α d Y).val
  have hs0 : 0 ≤ (coefficientSeminorm ρ k a b (P.B i j α d)).toReal := ENNReal.toReal_nonneg
  have hroot : Real.sqrt (factorialWeightMax ρ k * ‖Z‖ ^ 2) =
      Real.sqrt (factorialWeightMax ρ k) * ‖Z‖ := by
    rw [Real.sqrt_mul hwmax, Real.sqrt_sq (norm_nonneg _)]
  have hfl' : Real.sqrt (factorialNormSq ρ (P.fluxTermOf t ht i j α d Y).val) ≤
      (coefficientSeminorm ρ k a b (P.B i j α d)).toReal *
        (Real.sqrt (factorialWeightMax ρ k) * (‖truncateTorusHk (E := G i j α) hlow‖ * ‖Y‖)) := by
    refine hfl.trans ?_
    rw [mul_one, mul_one, hroot]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZn (Real.sqrt_nonneg _)) hs0
  have hsw : 0 < Real.sqrt (factorialWeightMin ρ k) := Real.sqrt_pos.mpr hwmin
  calc
    ‖P.fluxTermOf t ht i j α d Y‖ = ‖(P.fluxTermOf t ht i j α d Y).val‖ := rfl
    _ ≤ Real.sqrt (factorialNormSq ρ (P.fluxTermOf t ht i j α d Y).val) /
        Real.sqrt (factorialWeightMin ρ k) := hQ
    _ ≤ ((coefficientSeminorm ρ k a b (P.B i j α d)).toReal *
        (Real.sqrt (factorialWeightMax ρ k) * (‖truncateTorusHk (E := G i j α) hlow‖ * ‖Y‖))) /
        Real.sqrt (factorialWeightMin ρ k) :=
      div_le_div_of_nonneg_right hfl' hsw.le
    _ = _ := by ring

omit [DecidableEq ι] in
/-- One term of the lift forcing is measurable in time. -/
theorem fluxTermOf_clamped_aestronglyMeasurable (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D))
    (Yt : ℝ → TorusHk (k + D - 1) (G i j α))
    (hY : AEStronglyMeasurable Yt (volume.restrict (Set.Icc a b))) :
    AEStronglyMeasurable (fun t : ℝ =>
      P.fluxTermOf (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property i j α d (Yt t))
      (volume.restrict (Set.Icc a b)) := by
  let mk : ℝ → TorusHk (k + D - 1) (G i j α) := AEStronglyMeasurable.mk Yt hY
  have hmk : StronglyMeasurable mk := hY.stronglyMeasurable_mk
  have hsub : StronglyMeasurable (fun s : Set.Icc a b => mk (s : ℝ)) :=
    hmk.comp_measurable measurable_subtype_coe
  have hH := P.fluxTermOf_time_stronglyMeasurable i j α d (fun s : Set.Icc a b => mk (s : ℝ)) hsub
  have hFm : StronglyMeasurable (fun t : ℝ =>
      P.fluxTermOf (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property i j α d
        (mk (Set.projIcc a b P.htime t))) :=
    hH.comp_measurable (continuous_projIcc (h := P.htime)).measurable
  refine hFm.aestronglyMeasurable.congr ?_
  filter_upwards [hY.ae_eq_mk, ae_restrict_mem measurableSet_Icc] with t ht1 ht2
  have hp : (↑(Set.projIcc a b P.htime t) : ℝ) = t := by
    rw [Set.projIcc_of_mem P.htime ht2]
  refine (congrArg (P.fluxTermOf _ _ i j α d) ?_).symm
  rw [hp]
  exact ht1

omit [DecidableEq ι] in
/-- **The lift forcing is measurable in time** when the lifts are `L²` in time. -/
theorem liftForcing_aestronglyMeasurable
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hy : ∀ i j α, MemLp (y i j α) 2 (volume.restrict (Set.Icc a b)))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    AEStronglyMeasurable (P.liftForcing y w i) (volume.restrict (Set.Icc a b)) := by
  classical
  have hterm : ∀ (j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), AEStronglyMeasurable
      (fun t : ℝ => P.fluxTermOf (Set.projIcc a b P.htime t)
        (Set.projIcc a b P.htime t).property i j α d (y i j α t - P.higherInput w i j α t))
      (volume.restrict (Set.Icc a b)) := fun j α d =>
    P.fluxTermOf_clamped_aestronglyMeasurable i j α d _
      ((hy i j α).aestronglyMeasurable.sub (P.higherInput_memLp w hw i j α).aestronglyMeasurable)
  have hsum := Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset ι) fun j _ =>
    Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Γ i j)) fun α _ =>
    Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset ↥(Finset.Icc 2 D)) fun d _ =>
    hterm j α d
  exact hsum

omit [DecidableEq ι] in
/-- **The lift forcing is `L²` in time** when the lifts are. -/
theorem liftForcing_memLp
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (hy : ∀ i j α, MemLp (y i j α) 2 (volume.restrict (Set.Icc a b)))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) :
    MemLp (P.liftForcing y w i) 2 (volume.restrict (Set.Icc a b)) := by
  classical
  choose C hC0 hCb using fun (j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) =>
    P.fluxTermOf_norm_le i j α d
  have hterm : ∀ (j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)),
      MemLp (fun t => C j α d * (‖y i j α t‖ + ‖P.higherInput w i j α t‖)) 2
        (volume.restrict (Set.Icc a b)) := fun j α d =>
    (((hy i j α).norm).add (P.higherInput_memLp w hw i j α).norm).const_mul (C j α d)
  have hg : MemLp (fun t => ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
      C j α d * (‖y i j α t‖ + ‖P.higherInput w i j α t‖)) 2
      (volume.restrict (Set.Icc a b)) :=
    memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun α _ =>
      memLp_finsetSum _ fun d _ => hterm j α d
  refine hg.mono' (P.liftForcing_aestronglyMeasurable y w hy hw i) (Filter.Eventually.of_forall fun t => ?_)
  unfold liftForcing
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  refine (hCb j α d _ _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (hC0 j α d)

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end
end

section
/-! **The forcing cost, step 3: the forcing at a fixed time.**
For the `TorusKernelOperator` of the paired system with real components, identity component maps
`C` and regularizers `S = (isoPairedKernel r n).op`:
* `pfc_term_sq`: `|∇^{s+1} (I - S) u|²_{ρ,K} ≤ ((r/ρ)^L pfcChat_s / r^s)² |∇u|²_{ρ,L_w}`
  (the gain of step 1 and the factorial reserve shift);
* `pfc_fluxTerm_bound`: the same for one flux term, with the coefficient seminorm (terms of order
  above `n0` have coefficient seminorm zero);
* `pfc_time_mass_bound`: `‖F(t)‖²_{ρ;π} ≤ ((r/ρ)^L ν θ)² ∑ π_j⁻¹ |∇W_j|²_{ρ,L_w}` when the Schur
  matrix with constants `pfcChat` is bounded by `θ`. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
  AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.WeakEntryProofs

section Gain

theorem pfc_deriv_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {μ : Measure (Vec 2)} {K r : ℕ}
    (ρ : ℝ) (D : JetL2 μ (K + r) E) :
    derivFactorialNormSq r ρ D = ∑ a : DerivativeWord2 r, factorialNormSq ρ (derivativeJet a D) := by
  rw [derivativeArray_factorialNormSq]
  unfold derivFactorialNormSq derivativeNormSq
  apply Finset.sum_congr rfl
  intro j _
  have hidx : shiftedJetOrder (K := K) (r := r) j =
      ⟨j.val + r, by have := j.isLt; omega⟩ := by
    apply Fin.ext
    simp [shiftedJetOrder, Nat.add_comm]
  rw [hidx]

variable {φ₀ : Vec 2 → ℝ}

/-- The kernel constant of the term of order `s + 2`: the gain constant times the factorial
reserve `(K+L+s)!/(K+L)!`. -/
def pfcChat (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, euclideanNorm z ≤ 1) (hφ : Integrable φ₀)
    (n : ℕ+) (L : ℕ) (hL : L < 2 * (n : ℕ)) (k s : ℕ) : ℝ :=
  Classical.choose (exists_pfc_derivFactorial_gain.{0} hc hd hnonneg hmass hsupp hφ n L hL k
    (s + 1)) * (((k + L + s).factorial : ℝ) / ((k + L).factorial : ℝ))

theorem pfcChat_nonneg (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, euclideanNorm z ≤ 1) (hφ : Integrable φ₀)
    (n : ℕ+) (L : ℕ) (hL : L < 2 * (n : ℕ)) (k s : ℕ) :
    0 ≤ pfcChat hc hd hnonneg hmass hsupp hφ n L hL k s :=
  mul_nonneg (Classical.choose_spec (exists_pfc_derivFactorial_gain.{0} hc hd hnonneg hmass hsupp
    hφ n L hL k (s + 1))).1 (by positivity)

/-- **One term of the forcing, in the jet norm**: the `(s+1)`-fold derivative of the difference
`(I - S_w) u` is at most `(r/ρ)^L pfcChat_s / r^s` times the gradient energy of `u` at the
higher order `L_w`. -/
theorem pfc_term_sq (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, euclideanNorm z ≤ 1) (hφ : Integrable φ₀)
    (n : ℕ+) (L : ℕ) (hL : L < 2 * (n : ℕ)) (k s : ℕ) {Lw : ℕ} (hs : k + L + s ≤ Lw)
    (r ρ : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ) (t : ℝ) (W : TorusHk (Lw + 1) ℝ)
    (Y : TorusHk (k + (s + 1)) ℝ)
    (hY : Y.val (valueIndex2 (k + (s + 1))) = W.val (valueIndex2 (Lw + 1)) -
      (isoPairedKernel r n).op φ₀ hφ t (W.val (valueIndex2 (Lw + 1)))) :
    derivFactorialNormSq (s + 1) ρ Y.val ≤
      (((r / ρ) ^ L) * (pfcChat hc hd hnonneg hmass hsupp hφ n L hL k s / r ^ s)) ^ 2 *
        gradFactorialNormSq ρ W.val := by
  have hρ : 0 < ρ := hr.trans_le hrρ
  obtain ⟨hD0, hD⟩ := Classical.choose_spec (exists_pfc_derivFactorial_gain.{0} hc hd hnonneg
    hmass hsupp hφ n L hL k (s + 1))
  set D := Classical.choose (exists_pfc_derivFactorial_gain.{0} hc hd hnonneg hmass hsupp hφ n L
    hL k (s + 1)) with hDdef
  have hle : k + L + (s + 1) ≤ Lw + 1 := by omega
  have h1 := hD ℝ r ρ hr hrρ t (truncateTorusHk hle W) Y hY
  have hKL : (k + L) + s ≤ Lw := by omega
  have hres := AVRegularity.CoupledEnergy.Variational.torusGradientReserveTensor_factorialNorm_le
    ρ hρ s hKL W
  have he : factorialNormSq ρ
      (AVRegularity.CoupledEnergy.Variational.torusGradientReserveTensor s hKL W).val =
      derivFactorialNormSq (K := k + L) (s + 1) ρ (truncateTorusHk hle W).val :=
    (AVRegularity.CoupledEnergy.Variational.torusDerivativeTensor_factorialNormSq (K := k + L)
      (r := s + 1) ρ (truncateTorusHk hle W)).trans (pfc_deriv_eq ρ _).symm
  rw [he] at hres
  set Rf := derivativeReserveFactor ρ (k + L) s with hRf
  have hRf0 : 0 ≤ Rf := by rw [hRf]; unfold derivativeReserveFactor; positivity
  have hG0 : 0 ≤ gradFactorialNormSq ρ W.val := by
    unfold gradFactorialNormSq
    exact Finset.sum_nonneg fun j _ => mul_nonneg (factorialWeight_nonneg ρ _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h2 : derivFactorialNormSq (K := k + L) (s + 1) ρ (truncateTorusHk hle W).val ≤
      Rf ^ 2 * gradFactorialNormSq ρ W.val := by
    have hnn : 0 ≤ derivFactorialNormSq (K := k + L) (s + 1) ρ (truncateTorusHk hle W).val := by
      rw [← he]; exact factorialNormSq_nonneg _ _
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hres 2
    rw [Real.sq_sqrt hnn, mul_pow, Real.sq_sqrt hG0] at this
    exact this
  have hRle : Rf ≤ (r ^ s)⁻¹ * (((k + L + s).factorial : ℝ) / ((k + L).factorial : ℝ)) := by
    rw [hRf]
    unfold derivativeReserveFactor
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (pow_pos hr s) (pow_le_pow_left₀ hr.le hrρ s))
      (by positivity)
  have hQ0 : 0 ≤ (r / ρ) ^ L := by positivity
  have h3 : D * (r / ρ) ^ L * Rf ≤ ((r / ρ) ^ L) *
      (pfcChat hc hd hnonneg hmass hsupp hφ n L hL k s / r ^ s) := by
    unfold pfcChat
    rw [← hDdef]
    calc D * (r / ρ) ^ L * Rf ≤ D * (r / ρ) ^ L *
          ((r ^ s)⁻¹ * (((k + L + s).factorial : ℝ) / ((k + L).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hRle (mul_nonneg hD0 hQ0)
      _ = _ := by ring
  calc derivFactorialNormSq (s + 1) ρ Y.val ≤
        (D * (r / ρ) ^ L) ^ 2 * derivFactorialNormSq (K := k + L) (s + 1) ρ
          (truncateTorusHk hle W).val := h1
    _ ≤ (D * (r / ρ) ^ L) ^ 2 * (Rf ^ 2 * gradFactorialNormSq ρ W.val) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (D * (r / ρ) ^ L * Rf) ^ 2 * gradFactorialNormSq ρ W.val := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg (mul_nonneg hD0 hQ0) hRf0) h3 2) hG0

end Gain

/-- **A flux term whose coefficient has seminorm zero vanishes in the factorial norm.** -/
theorem pfc_fluxTerm_zero {K m r : ℕ} (hr : r = m + 1) (ρ : ℝ) (hρ : 0 < ρ) (a b : ℝ)
    (A : ℝ → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 r => ℝ)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => ℝ)))
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (Y : TorusHk (K + (m + 1)) ℝ) (h0 : coefficientSeminorm ρ K a b A = 0) :
    Real.sqrt (factorialNormSq ρ (torusKernelFluxTerm hr ρ hρ a b A hA t ht hC hp Y).val) ≤ 0 := by
  let hword : DerivativeWord2 (m + 1) = DerivativeWord2 r :=
    congrArg DerivativeWord2 hr.symm
  let e : DerivativeWord2 (m + 1) ≃ DerivativeWord2 r := Equiv.cast hword
  let L := derivativeWordArrayIsometry (E := ℝ) e
  let W := torusDerivativeTensor (K := K) (r := m + 1) Y
  have hmul := torusMultiplyIntervalCoefficient_factorialNorm_le ρ hρ K a b A hA
    t ht hC hp (mapTorusHk L.toContinuousLinearMap W)
  calc _ ≤ (coefficientSeminorm ρ K a b A).toReal *
        Real.sqrt (factorialNormSq ρ (mapTorusHk L.toContinuousLinearMap W).val) := hmul
    _ = 0 := by rw [h0]; simp

theorem pfc_compLp_id {μ : Measure (Vec 2)} (f : Lp ℝ 2 μ) :
    (ContinuousLinearMap.id ℝ ℝ).compLp f = f :=
  Lp.ext ((ContinuousLinearMap.coeFn_compLp' _ f).trans (Filter.Eventually.of_forall fun _ => rfl))

section Operator

variable {ι : Type*} [Fintype ι] {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {a b ρ ν : ℝ} {k D : ℕ} {φ₀ : Vec 2 → ℝ}

/-- **One flux term of the forcing** (`B_{α,d} ∇^{d-1} (I - S_w) u`): its factorial norm is at most
`(r/ρ)^L` times the kernel price of the term times the gradient energy of `u` at the higher
order `L_w`. -/
theorem pfc_fluxTerm_bound
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, euclideanNorm z ≤ 1) (hφ : Integrable φ₀)
    (n : ℕ+) (L : ℕ) (hL : L < 2 * (n : ℕ))
    (P : TorusKernelOperator (h := fun _ : ι => ℝ) (Γ := Γ) (G := fun _ _ _ => ℝ) a b ρ ν k D)
    (r : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ)
    (hCid : ∀ i j (α : Γ i j), P.C i j α = ContinuousLinearMap.id ℝ ℝ)
    (hSop : ∀ i j (α : Γ i j), P.S i j α = (isoPairedKernel r n).op φ₀ hφ)
    (n0 : ℕ) (hzero : ∀ i j (α : Γ i j) (d : ↥(Finset.Icc 2 D)), n0 < d.1 →
      coefficientSeminorm ρ k a b (P.B i j α d) = 0)
    {Lw : ℕ} (hLw : k + L + n0 ≤ Lw + 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) ℝ) (w : ∀ i, ℝ → TorusHk (k + 1) ℝ)
    (W : ι → TorusHk (Lw + 1) ℝ)
    (hyv : ∀ i j (α : Γ i j), (y i j α t).val (valueIndex2 (k + D - 1)) =
      (w j t).val (valueIndex2 (k + 1)))
    (hWv : ∀ j, (W j).val (valueIndex2 (Lw + 1)) = (w j t).val (valueIndex2 (k + 1)))
    (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
    Real.sqrt (factorialNormSq ρ
        (P.fluxTermOf t ht i j α d (y i j α t - P.higherInput w i j α t)).val) ≤
      (r / ρ) ^ L * ((coefficientSeminorm ρ k a b (P.B i j α d)).toReal *
        (pfcChat hc hd hnonneg hmass hsupp hφ n L hL k (d.1 - 2) / r ^ (d.1 - 2)) *
        ‖P.C i j α‖ * Real.sqrt (gradFactorialNormSq ρ (W j).val)) := by
  have hρ : 0 < ρ := P.radius_pos
  have hdm := Finset.mem_Icc.1 d.2
  have hG0 : 0 ≤ gradFactorialNormSq ρ (W j).val := by
    unfold gradFactorialNormSq
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (factorialWeight_nonneg ρ _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hQ0 : 0 ≤ (r / ρ) ^ L := by positivity
  by_cases hdn : d.1 ≤ n0
  · have hCn : ‖P.C i j α‖ = 1 := by rw [hCid]; exact ContinuousLinearMap.norm_id
    have hord : k + (d.1 - 2 + 1) ≤ k + D - 1 := by omega
    have hv : (y i j α t - P.higherInput w i j α t).val (valueIndex2 (k + D - 1)) =
        (w j t).val (valueIndex2 (k + 1)) -
          (isoPairedKernel r n).op φ₀ hφ t ((w j t).val (valueIndex2 (k + 1))) := by
      change (y i j α t).val (valueIndex2 (k + D - 1)) -
        (P.higherInput w i j α t).val (valueIndex2 (k + D - 1)) = _
      rw [P.higherInput_of_mem w i j α t ht, P.lift_value, hSop, hCid, pfc_compLp_id, hyv]
    have hterm := pfc_term_sq hc hd hnonneg hmass hsupp hφ n L hL k (d.1 - 2) (Lw := Lw)
      (by omega) r ρ hr hrρ t (W j)
      (truncateTorusHk hord (y i j α t - P.higherInput w i j α t))
      (by
        change (y i j α t - P.higherInput w i j α t).val (valueIndex2 (k + D - 1)) = _
        rw [hv, hWv j])
    unfold TorusKernelOperator.fluxTermOf
    have hmain := torusKernelFluxTerm_factorialNorm_le (m := d.1 - 2) (r := d.1 - 1)
      (by omega) ρ P.radius_pos a b (P.B i j α d) (P.hB_fin i j α d) t ht
      (P.hB_smooth i j α d t ht) (P.hB_per i j α d t ht)
      (truncateTorusHk hord (y i j α t - P.higherInput w i j α t))
      ((r / ρ) ^ L) hQ0
      (pfcChat hc hd hnonneg hmass hsupp hφ n L hL k (d.1 - 2) / r ^ (d.1 - 2))
      (div_nonneg (pfcChat_nonneg hc hd hnonneg hmass hsupp hφ n L hL k _) (by positivity))
      (gradFactorialNormSq ρ (W j).val) hG0 (by rw [← mul_pow] ; exact hterm)
    rw [hCn]
    refine hmain.trans (le_of_eq ?_)
    ring
  · have h0 := hzero i j α d (not_le.mp hdn)
    have hz := pfc_fluxTerm_zero (K := k) (m := d.1 - 2) (r := d.1 - 1) (by omega) ρ P.radius_pos
      a b (P.B i j α d) (P.hB_fin i j α d) t ht (P.hB_smooth i j α d t ht)
      (P.hB_per i j α d t ht)
      (truncateTorusHk (by omega : k + (d.1 - 2 + 1) ≤ k + D - 1)
        (y i j α t - P.higherInput w i j α t)) h0
    unfold TorusKernelOperator.fluxTermOf
    refine hz.trans ?_
    rw [h0]
    simp

theorem pfc_torusHk_sum_val {α : Type*} [Fintype α] {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (f : α → TorusHk K E) : (∑ x, f x).val = ∑ x, (f x).val :=
  map_sum ((torusHkGraph (E := E) K).toSubmodule.subtype) f Finset.univ

theorem pfc_fluxTermOf_clamp
    (P : TorusKernelOperator (h := fun _ : ι => ℝ) (Γ := Γ) (G := fun _ _ _ => ℝ) a b ρ ν k D)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D))
    (Y : TorusHk (k + D - 1) ℝ) :
    P.fluxTermOf (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property i j α d Y =
      P.fluxTermOf t ht i j α d Y := by
  have key : ∀ (t₁ t₂ : ℝ) (h1 : t₁ ∈ Set.Icc a b) (h2 : t₂ ∈ Set.Icc a b), t₁ = t₂ →
      P.fluxTermOf t₁ h1 i j α d Y = P.fluxTermOf t₂ h2 i j α d Y := by
    intro _ _ _ _ h
    subst h
    rfl
  exact key _ _ _ _ (by rw [Set.projIcc_of_mem P.htime ht])

/-- **The mass of the forcing at a time**, against the gradient energy of the higher lift. -/
theorem pfc_time_mass_bound
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, euclideanNorm z ≤ 1) (hφ : Integrable φ₀)
    (n : ℕ+) (L : ℕ) (hL : L < 2 * (n : ℕ))
    (P : TorusKernelOperator (h := fun _ : ι => ℝ) (Γ := Γ) (G := fun _ _ _ => ℝ) a b ρ ν k D)
    (r : ℝ) (hr : 0 < r) (hrρ : r ≤ ρ)
    (hCid : ∀ i j (α : Γ i j), P.C i j α = ContinuousLinearMap.id ℝ ℝ)
    (hSop : ∀ i j (α : Γ i j), P.S i j α = (isoPairedKernel r n).op φ₀ hφ)
    (n0 : ℕ) (hzero : ∀ i j (α : Γ i j) (d : ↥(Finset.Icc 2 D)), n0 < d.1 →
      coefficientSeminorm ρ k a b (P.B i j α d) = 0)
    {Lw : ℕ} (hLw : k + L + n0 ≤ Lw + 2)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) ℝ) (w : ∀ i, ℝ → TorusHk (k + 1) ℝ)
    (W : ι → TorusHk (Lw + 1) ℝ)
    (hyv : ∀ i j (α : Γ i j), (y i j α t).val (valueIndex2 (k + D - 1)) =
      (w j t).val (valueIndex2 (k + 1)))
    (hWv : ∀ j, (W j).val (valueIndex2 (Lw + 1)) = (w j t).val (valueIndex2 (k + 1)))
    (θ : ℝ)
    (hschur : SchurBound θ (kernelSchurMatrix ν ρ P.π k D a b
      (pfcChat hc hd hnonneg hmass hsupp hφ n L hL k) (fun _ _ _ => r) P.C P.B)) :
    massNormSq (E := fun _ => PiLp 2 (fun _ : Fin 2 => ℝ)) (K := fun _ => k) ρ P.π
        (fun i => (P.liftForcing y w i t).val) ≤
      ((r / ρ) ^ L * ν * θ) ^ 2 * ∑ j : ι, (P.π j)⁻¹ * gradFactorialNormSq ρ (W j).val := by
  have hQ : 0 < (r / ρ) ^ L := pow_pos (div_pos hr (hr.trans_le hrρ)) L
  have hX : ∀ j, 0 ≤ ((r / ρ) ^ L) ^ 2 * gradFactorialNormSq ρ (W j).val := fun j =>
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => mul_nonneg
      (factorialWeight_nonneg ρ _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have h := pfc_flux_mass_schur (E := fun _ : ι => ℝ) (G := fun _ _ _ => ℝ) ρ ν θ
    P.diffusivity_pos k D a b P.π P.hπ P.B P.C (pfcChat hc hd hnonneg hmass hsupp hφ n L hL k)
    (fun _ _ _ => r) (fun _ _ _ => hr)
    (fun _ _ _ m _ => pfcChat_nonneg hc hd hnonneg hmass hsupp hφ n L hL k m)
    (fun i => (P.liftForcing y w i t).val)
    (fun j => ((r / ρ) ^ L) ^ 2 * gradFactorialNormSq ρ (W j).val) hX
    (fun i j α d => (P.fluxTermOf (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property
      i j α d (y i j α t - P.higherInput w i j α t)).val)
    (fun i => by
      unfold TorusKernelOperator.liftForcing
      rw [pfc_torusHk_sum_val]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pfc_torusHk_sum_val]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [pfc_torusHk_sum_val])
    (fun i j α d => by
      have hb := pfc_fluxTerm_bound hc hd hnonneg hmass hsupp hφ n L hL P r hr hrρ hCid hSop n0
        hzero hLw t ht y w W hyv hWv i j α d
      rw [pfc_fluxTermOf_clamp P t ht]
      refine hb.trans (le_of_eq ?_)
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hQ.le]
      ring)
    hschur
  refine h.trans (le_of_eq ?_)
  have : ∀ j, (P.π j)⁻¹ * (((r / ρ) ^ L) ^ 2 * gradFactorialNormSq ρ (W j).val) =
      ((r / ρ) ^ L) ^ 2 * ((P.π j)⁻¹ * gradFactorialNormSq ρ (W j).val) := fun j => by ring
  simp_rw [this, ← Finset.mul_sum]
  ring

end Operator

end AVRegularity.WeakEntryProofs
end
end
end

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs

/-! **The forcing cost, step 4: the arithmetic, coefficient, integral and measurability inputs of
the assembly.** `pfc_const_arith` (scale arithmetic), the band bound `κ_M ≤ 2`,
`pfc_Gw_physCoeff_zero` (no coefficient above the order `1 + J_w N_w`), `pfc_lintegral_bound`,
`pfc_strongEnergy_sq_ge`, `pfc_grad_aemeasurable` (the gradient energy of a lift with a.e.
measurable values is measurable in time). -/

open AVRegularity.WeakEntryProofs.Assembly

/-- The scale arithmetic of the forcing cost: with `r = ε^{1+σ}`, `ρ = c ε` and `ε^σ ≤ c`,
`((r/ρ)^L κ θ)² ≤ (Q²/c^{2L}) ε^{2(χ+σL)} κ²` for `θ ≤ Q ε^χ`. -/
theorem pfc_const_arith {ε c σ χ Q κ θ : ℝ} (L : ℕ) (hε : 0 < ε) (hc : 0 < c)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ Q * ε ^ χ) :
    ((ε ^ (1 + σ) / (c * ε)) ^ L * κ * θ) ^ 2 ≤
      (Q ^ 2 / c ^ (2 * L)) * ε ^ (2 * (χ + σ * L)) * κ ^ 2 := by
  have hQ0 : 0 ≤ Q * ε ^ χ := hθ0.trans hθ
  have h1 : ε ^ (1 + σ) / (c * ε) = ε ^ σ / c := by
    rw [Real.rpow_add hε, Real.rpow_one]
    field_simp
  have h2 : (ε ^ σ / c) ^ L = ε ^ (σ * L) / c ^ L := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
  have h3 : ε ^ (2 * (χ + σ * L)) = (ε ^ χ) ^ 2 * (ε ^ (σ * L)) ^ 2 := by
    rw [← Real.rpow_natCast (ε ^ χ), ← Real.rpow_natCast (ε ^ (σ * L)), ← Real.rpow_mul hε.le,
      ← Real.rpow_mul hε.le, ← Real.rpow_add hε]
    congr 1
    push_cast
    ring
  have hθ2 : θ ^ 2 ≤ Q ^ 2 * (ε ^ χ) ^ 2 := by
    calc θ ^ 2 ≤ (Q * ε ^ χ) ^ 2 := pow_le_pow_left₀ hθ0 hθ 2
      _ = _ := by ring
  rw [h1, h2]
  have hcL : 0 < c ^ L := pow_pos hc L
  have hc2 : c ^ (2 * L) = (c ^ L) ^ 2 := by rw [pow_mul']
  rw [hc2, h3]
  have e1 : ((ε ^ (σ * L) / c ^ L) * κ * θ) ^ 2 =
      (ε ^ (σ * L)) ^ 2 / (c ^ L) ^ 2 * κ ^ 2 * θ ^ 2 := by
    rw [mul_pow, mul_pow, div_pow]
  rw [e1]
  have hε2 : 0 ≤ (ε ^ (σ * L)) ^ 2 / (c ^ L) ^ 2 := by positivity
  calc (ε ^ (σ * L)) ^ 2 / (c ^ L) ^ 2 * κ ^ 2 * θ ^ 2
      ≤ (ε ^ (σ * L)) ^ 2 / (c ^ L) ^ 2 * κ ^ 2 * (Q ^ 2 * (ε ^ χ) ^ 2) :=
        mul_le_mul_of_nonneg_left hθ2 (by positivity)
    _ = _ := by field_simp

section Coefficients

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}

/-- **The physical coefficients of `Gw` vanish above the order `1 + J_w N_w`.** -/
theorem pfc_Gw_physCoeff_zero {x : WeakEntryData plan C} (g : WeakEntryStages x)
    (v u : CompIn g.Gw.comps) (γ : g.Gw.fam.Γ v u) (d : ℕ) (hd : 1 + A.Jw * A.Nw < d) :
    g.Gw.physCoeff v u γ d = fun _ _ => 0 := by
  obtain ⟨e, hB⟩ := weakEncoding_physCoeff g.encoding
  obtain ⟨v0, rfl⟩ := g.relabel.surjective v
  obtain ⟨u0, rfl⟩ := g.relabel.surjective u
  obtain ⟨γ0, rfl⟩ := (e v0 u0).surjective γ
  rw [hB]
  have horder := EntryWeakProofs.weakConstruction_output_maxOrder_bound x.P
    ⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, x.M + A.Jw⟩ x.M A.Jw (x.D.termRW A.σw x.M) 0 g.stage
    g.construction x.M le_rfl (by have := A.Jw_pos; omega)
  funext t y
  exact CycleJointProofs.constituentPhysical_zero_above_max (g.stage x.M).fam
    (x.D.kap (g.stage x.M).level) (x.D.eps (g.stage x.M).level)
    (x.D.eps ((g.stage x.M).level - 1)) (g.stage x.M).actual v0 u0 γ0 d
    (lt_of_le_of_lt (horder v0 u0 γ0) hd) t y

end Coefficients

section Integral

open scoped ENNReal

/-- **The time integral of a pointwise energy bound.** -/
theorem pfc_lintegral_bound {V : Type*} [Fintype V] {μ : Measure ℝ} (m : ℝ → ℝ) (f : V → ℝ → ℝ)
    (c : V → ℝ) (K0 : ℝ) (hK0 : 0 ≤ K0) (hc : ∀ v, 0 ≤ c v) (hf0 : ∀ v s, 0 ≤ f v s)
    (hmeas : ∀ v, AEMeasurable (f v) μ)
    (hpt : ∀ᵐ s ∂μ, m s ≤ K0 * ∑ v, c v * f v s) :
    ∫⁻ s, ENNReal.ofReal (m s) ∂μ ≤
      ENNReal.ofReal K0 * ∑ v, ENNReal.ofReal (c v) * ∫⁻ s, ENNReal.ofReal (f v s) ∂μ := by
  calc ∫⁻ s, ENNReal.ofReal (m s) ∂μ ≤
        ∫⁻ s, ENNReal.ofReal K0 * ∑ v, ENNReal.ofReal (c v) * ENNReal.ofReal (f v s) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hpt] with s hs
          calc ENNReal.ofReal (m s) ≤ ENNReal.ofReal (K0 * ∑ v, c v * f v s) :=
                ENNReal.ofReal_le_ofReal hs
            _ = _ := by
              rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_sum_of_nonneg
                (fun v _ => mul_nonneg (hc v) (hf0 v s))]
              simp only [ENNReal.ofReal_mul (hc _)]
    _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum' _
            (fun v _ => ((hmeas v).ennreal_ofReal.const_mul _))]
          congr 1
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The strong energy squared dominates the dissipation part. -/
theorem pfc_strongEnergy_sq_ge {ι : Type*} [Fintype ι] {K : ℕ} (ρ Bc : ℝ) (π : ι → ℝ)
    (t₀ t₁ : ℝ) (u : ∀ _ : ι, ℝ → TorusHk K ℝ) (w : ∀ _ : ι, ℝ → TorusHk (K + 1) ℝ) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal Bc *
        ∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (gradFactorialNormSq ρ (w v s).val)) ≤
      strongEnergy (h := fun _ : ι => ℝ) ρ Bc π t₀ t₁ u w ^ 2 := by
  unfold strongEnergy
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  exact Finset.sum_le_sum fun v _ => by gcongr; exact le_add_self

end Integral

section Measurability

theorem pfc_grad_continuous (Lw : ℕ) (ρ : ℝ) :
    Continuous fun W : TorusHk (Lw + 1) ℝ => gradFactorialNormSq ρ W.val := by
  unfold gradFactorialNormSq
  refine continuous_finsetSum _ fun j _ => continuous_const.mul
    (continuous_finsetSum _ fun w _ => ?_)
  have h1 : Continuous fun W : TorusHk (Lw + 1) ℝ =>
      W.val ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩ :=
    (PiLp.continuous_apply 2 _ _).comp continuous_subtype_val
  exact (h1.norm).pow 2

/-- A time family of higher jets whose values are a.e. those of a measurable family is
measurable in its gradient energy. -/
theorem pfc_grad_aemeasurable {Lw K : ℕ} (ρ : ℝ) (μ : Measure ℝ) (W : ℝ → TorusHk (Lw + 1) ℝ)
    (U : ℝ → TorusHk K ℝ) (hU : AEStronglyMeasurable U μ)
    (hv : ∀ᵐ t ∂μ, (W t).val (valueIndex2 (Lw + 1)) = (U t).val (valueIndex2 K)) :
    AEMeasurable (fun t => gradFactorialNormSq ρ (W t).val) μ := by
  have h1 : AEStronglyMeasurable (fun t => AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (U t)) μ :=
    (AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (E := ℝ) (K := K)).continuous.comp_aestronglyMeasurable hU
  have h2 : AEStronglyMeasurable (fun t => AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (W t)) μ := by
    refine h1.congr ?_
    filter_upwards [hv] with t ht
    exact ht.symm
  have h3 := AVRegularity.KernelEnergy.torusCarrier_aestronglyMeasurable_of_value μ (Lw + 1) W h2
  exact ((pfc_grad_continuous Lw ρ).comp_aestronglyMeasurable h3).aemeasurable

end Measurability

end AVRegularity.WeakEntryProofs
end
end

section
/-! **The difference equation with an explicit forcing** (`WeakEntryPairedForcingStatement`, the
first half of the paired difference).

The raw family `U` solves the kernel-regularized system of `Gw` with the identity kernels; by
`liftForced_weakSolution` it solves the coupled system whose flux is the flux `P.carrierFlux Uw`
of the paired kernel on `U` plus the forcing `F = weakPairedForcing`, the flux of
`(I - S_w) U` (the raw lift `Uk` minus the regularized lift of `Uw`). The paired solution `V`
solves the same coupled system with the forcing `0` (`kernelWeakSolution_forcedWeakSolution`).
The forcing is `L²` in time (`liftForcing_memLp`), so the difference of the two solutions solves
the coupled system with zero data and the forcing `F + P.carrierFlux (Uw - Vw)`
(`torusWeakSolution_flux_difference`). -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
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

omit [DecidableEq ι] in
/-- **The difference of a solution of any kernel-regularized system and a solution of the system
of `P`** solves the coupled system with zero data and the flux
`liftForcing y w + P.carrierFlux (w - w')`. -/
theorem liftForced_difference
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hmeas : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hvb : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (f : ∀ i, TorusHk k (h i))
    (u u' : ∀ i, ℝ → TorusHk k (h i)) (w w' : ∀ i, ℝ → TorusHk (k + 1) (h i))
    (y y' : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    {S' : ∀ i j (α : Γ i j), ℝ → (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
      (Lp (G i j α) 2 (volume.restrict AVenhance.unitCube))}
    (hsol : IsKernelWeakSolutionTorus ν a b v k D P.B P.C S' f (fun _ _ => 0) (fun _ _ => 0)
      u w y)
    (hsol' : IsKernelWeakSolutionTorus ν a b v k D P.B P.C P.S f (fun _ _ => 0) (fun _ _ => 0)
      u' w' y') :
    IsCoupledWeakSolutionTorus ν a b v 0 (fun _ => k) noLocalCoefficient (fun _ => 0)
      (fun i t => P.liftForcing y w i t + P.carrierFlux (fun j s => w j s - w' j s) i t)
      (fun _ _ => 0) (fun i t => u i t - u' i t) (fun i t => w i t - w' i t) := by
  have hsolU := P.liftForced_weakSolution v hv V hV hvb f (fun _ _ => 0) (fun _ _ => 0) u w y hsol
  have hsolV := P.kernelWeakSolution_forcedWeakSolution v hv V hV hvb f (fun _ _ => 0)
    (fun _ _ => 0) u' w' y' hsol'
  have hF1 : ∀ i, MemLp (fun t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) +
      (P.liftForcing y w i t + P.carrierFlux w i t)) 2 (volume.restrict (Set.Icc a b)) :=
    fun i => timeMemLp_pointwise_add _ 2 _ _ (timeMemLp_zero _ 2)
      (timeMemLp_pointwise_add _ 2 _ _ (P.liftForcing_memLp y w hsol.2.2.2.2.1 hsol.2.1 i)
        (P.carrierFlux_memLp_of_family w hsol.2.1 i))
  have hF2 : ∀ i, MemLp (fun t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) +
      P.carrierFlux w' i t) 2 (volume.restrict (Set.Icc a b)) :=
    fun i => timeMemLp_pointwise_add _ 2 _ _ (timeMemLp_zero _ 2)
      (P.carrierFlux_memLp_of_family w' hsol'.2.1 i)
  have hdiff := torusWeakSolution_flux_difference (fun _ => k) 0 ν ρ P.radius_pos P.htime v hmeas
    (fun t ht => (hv t ht).continuous) V hvb noLocalCoefficient noLocalSeminorm
    noLocalMeasurable (fun t ht i j d => noLocalSmoothOnInterval t ht i j d)
    (fun i t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) +
      (P.liftForcing y w i t + P.carrierFlux w i t))
    (fun i t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) + P.carrierFlux w' i t)
    (fun _ _ => 0) hF1 hF2 (fun i => timeIntegrable_zero _) w w' u u' f hsolU hsolV
  have he : (fun i t => (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) +
      (P.liftForcing y w i t + P.carrierFlux w i t) -
      ((0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) + P.carrierFlux w' i t)) =
      (fun i t => P.liftForcing y w i t + P.carrierFlux (fun j s => w j s - w' j s) i t) := by
    funext i t
    rw [P.carrierFlux_sub]
    simp only [zero_add]
    abel
  rw [he] at hdiff
  exact hdiff

end TorusKernelOperator
end AVRegularity.KernelEnergy

namespace AVRegularity.WeakEntryProofs
open AVRegularity.WeakEntryProofs.Assembly AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational

/-- **The difference equation**: the difference of the raw and the paired solution solves the paired system with the
explicit forcing `weakPairedForcing`, which is measurable in time. -/
theorem weak_entry_paired_forcing (plan : WeakEntryGluePlan) :
    WeakEntryPairedForcingStatement plan := by
  intro hcommon hok B A R C x g s law hm f θ hθ r Uk hU V Vw Vk hV
  let P := weakPairedOp hcommon hok g s law hm
  have hφ := Velocity.streamSeq_admissible B.hζ x.base128 x.streams x.M
  obtain ⟨hv, -, -, ⟨V0, hV0⟩, hmeas⟩ := Construction.Preservation.Buffer.stream_kernel_drift_data
    hφ (s.tq (x.M + 1)) (x.a + A.T₀)
  have hV0' : ∀ t ∈ Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀), ∀ y,
      ‖streamVel (x.D.Φ x.M) t y‖ ≤ max V0 0 := fun t ht y => (hV0 t ht y).trans (le_max_left _ _)
  have hwU : ∀ i, MemLp (rerootFamily g.relabel (r.Urw x.M) i) 2
      (volume.restrict (Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀))) := hU.2.1
  exact ⟨P.liftForced_difference (streamVel (x.D.Φ x.M)) hv hmeas (max V0 0) (le_max_right _ _)
    hV0' _ _ _ _ _ _ _ hU hV,
    fun v => P.liftForcing_aestronglyMeasurable Uk _ hU.2.2.2.2.1 hwU v⟩

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.KernelEnergy
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs

/-! **Moment cancellation, the cost of the forcing** (`WeakEntryPairedForcingCostStatement`).
The forcing `F = ∑ a^phys ∇^{d-1} (I - S_w) u` has, at a fixed time, the mass bound of step 3
against the gradient energy of `Whi` (the higher lift of the higher-order lemma), with the gain `(r_w/ρ_M)^L` of
step 1 and the Schur sums `Cp C_led ε^{χ_w}` of step 2. Integrating in time, and using that the
band gives `κ_M ≤ 2`, gives the statement with `C_mom = 2 (Cp C_led)² / c^{2L}`. -/

open AVRegularity.WeakEntryProofs.Assembly

theorem pfc_grad_nonneg {K : ℕ} (ρ : ℝ) (W : JetL2 (volume.restrict unitCube) (K + 1) ℝ) :
    0 ≤ gradFactorialNormSq ρ W :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (factorialWeight_nonneg ρ _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem weak_entry_paired_forcing_cost (plan : WeakEntryGluePlan) :
    WeakEntryPairedForcingCostStatement plan := by
  intro hcommon hok hcost B A R C
  have hc := Providers.hasCompactSupport_of_unitBall A.support
  have hsupp : ∀ z ∈ Function.support A.φ₀, Analysis.Convolution.euclideanNorm z ≤ 1 :=
    fun z hz => A.support hz
  have hL : R.L < 2 * (R.nW : ℕ) := by have := R.kernel_order; omega
  set cc := pfcChat hc A.smooth A.nonneg A.mass hsupp A.hφ₀ R.nW R.L hL R.Kw with hcc
  set Q := pfcPriceConst R cc * (weakStoredLedgerData A).C with hQ
  have hQ0 : 0 ≤ Q := mul_nonneg (pfcPriceConst_nonneg R cc) (weakStoredLedgerData A).positive.le
  have hcK := weak_entry_radius_spec (plan.radiusBudget R)
  have hc0 : 0 < plan.radius R := hcK.1
  refine ⟨Q ^ 2 / plan.radius R ^ (2 * R.L), by positivity, ?_⟩
  intro x g s law hm f θ hsol r Uk hUk Uhi Whi hUhi hWhi
  -- scales
  have hε := weakPaired_eps_pos x
  have hεx : x.D.eps x.M = ocEpsilon B.q A.Λ x.M := weakPaired_eps_eq x
  have hεpos : 0 < x.D.eps x.M := by rw [hεx]; exact hε
  have hρeq : x.D.termRStar (plan.radius R) x.M = plan.radius R * x.D.eps x.M := rfl
  have hreq : x.D.termRW A.σw x.M = x.D.eps x.M ^ (1 + A.σw) := rfl
  have hσc : x.D.eps x.M ^ A.σw ≤ plan.radius R := by
    rw [hεx]; exact hcost R C x.j₀ x.M x.base128 x.level_ge
  have hr0 : 0 < x.D.termRW A.σw x.M := weakPaired_width_pos x
  have hrρ : x.D.termRW A.σw x.M ≤ x.D.termRStar (plan.radius R) x.M := by
    rw [hreq, hρeq, Real.rpow_add hεpos, Real.rpow_one]
    nlinarith [hεpos]
  have hκ0 : 0 < x.D.κ x.M := weakPaired_kappa_pos x
  -- the operator
  let P := weakPairedOp hcommon hok g s law hm
  have hCid : ∀ i j (α : g.Gw.fam.Γ i j), P.C i j α = ContinuousLinearMap.id ℝ ℝ :=
    fun _ _ _ => rfl
  have hSop : ∀ i j (α : g.Gw.fam.Γ i j), P.S i j α =
      (isoPairedKernel (x.D.termRW A.σw x.M) R.nW).op A.φ₀ A.hφ₀ :=
    fun i j α => sysS_constKernel x.P (isoPairedKernel (x.D.termRW A.σw x.M) R.nW) A.φ₀ A.hφ₀
      i j α
  have hzero : ∀ i j (α : g.Gw.fam.Γ i j) (d : ↥(Finset.Icc 2 x.Dm)), 1 + A.Jw * A.Nw < d.1 →
      coefficientSeminorm (x.D.termRStar (plan.radius R) x.M) R.Kw (s.tq (x.M + 1))
        (x.a + A.T₀) (P.B i j α d) = 0 := by
    intro i j α d hd
    have h0 : P.B i j α d = fun _ _ => 0 := pfc_Gw_physCoeff_zero g i j α d.1 hd
    rw [h0]
    exact CycleJointProofs.coefficientSeminorm_zero_function _ _ _ _
  have hschur := pfc_schur hok g law hm (Classical.choose (weakEncoding_physCoeff g.encoding))
    (Classical.choose_spec (weakEncoding_physCoeff g.encoding)) (s.tq (x.M + 1))
    (x.a + A.T₀) cc
  obtain ⟨-, hmem, -, -, -, hy, -⟩ := hUk
  let μ : Measure ℝ := volume.restrict (Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀))
  let m0 : ℕ := A.Jw * A.Nw + R.L
  let Uw := rerootFamily g.relabel (r.Urw x.M)
  let Wf : CompIn g.Gw.comps → ℝ → TorusHk (R.Kw + m0 + 1) ℝ := fun u t =>
    weakHighLift g m0 (Whi x.M) (g.relabel.symm u) t
  have hyv : ∀ᵐ t ∂μ, ∀ i j (α : g.Gw.fam.Γ i j),
      (Uk i j α t).val (valueIndex2 (R.Kw + x.Dm - 1)) = (Uw j t).val (valueIndex2 (R.Kw + 1)) := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro α
    filter_upwards [hy i j α] with t ht
    rw [ht, sysS_constKernel, EntryTerminal.Ingredients.isoPairedKernel_zero_op A.hφ₀ A.mass,
      ContinuousLinearMap.id_apply]
    exact pfc_compLp_id _
  have hWv : ∀ u, ∀ᵐ t ∂μ,
      (Wf u t).val (valueIndex2 (R.Kw + m0 + 1)) = (Uw u t).val (valueIndex2 (R.Kw + 1)) := by
    intro u
    filter_upwards [hWhi (g.relabel.symm u)] with t ht
    exact congrArg (fun z => z.val (valueIndex2 (R.Kw + 1))) ht
  have hθ0 : 0 ≤ pfcPriceConst R cc * (weakStoredLedgerData A).C *
      x.D.eps x.M ^ weakChi B.α B.q A.η₀ :=
    mul_nonneg (mul_nonneg (pfcPriceConst_nonneg R cc) (weakStoredLedgerData A).positive.le)
      (Real.rpow_nonneg hεpos.le _)
  let K0 : ℝ := ((x.D.termRW A.σw x.M / x.D.termRStar (plan.radius R) x.M) ^ R.L * x.D.κ x.M *
    (pfcPriceConst R cc * (weakStoredLedgerData A).C *
      x.D.eps x.M ^ weakChi B.α B.q A.η₀)) ^ 2
  have hpt : ∀ᵐ t ∂μ, massNormSq (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law)
      (fun v => (weakPairedForcing hcommon hok g s law hm Uw Uk v t).val) ≤
      K0 * ∑ u, (g.Gw.mass law u)⁻¹ *
        gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M) (Wf u t).val := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, hyv, ae_all_iff.2 hWv] with t ht hy hW
    exact pfc_time_mass_bound hc A.smooth A.nonneg A.mass hsupp A.hφ₀ R.nW R.L hL P
      (x.D.termRW A.σw x.M) hr0 hrρ hCid hSop (1 + A.Jw * A.Nw) hzero (Lw := R.Kw + m0)
      (by omega) t ht Uk Uw (fun u => Wf u t) hy (fun u => hW u) _ hschur
  have hmeas : ∀ u, AEMeasurable
      (fun t => gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M) (Wf u t).val) μ :=
    fun u => pfc_grad_aemeasurable _ μ (Wf u) (Uw u) (hmem u).aestronglyMeasurable (hWv u)
  have hint := pfc_lintegral_bound (μ := μ)
    (fun t => massNormSq (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law)
      (fun v => (weakPairedForcing hcommon hok g s law hm Uw Uk v t).val))
    (fun u t => gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M) (Wf u t).val)
    (fun u => (g.Gw.mass law u)⁻¹) K0 (sq_nonneg _)
    (fun u => inv_nonneg.2 (weakPaired_mass_pos g law hm u).le)
    (fun u t => pfc_grad_nonneg _ _) hmeas hpt
  have hK : K0 ≤ (Q ^ 2 / plan.radius R ^ (2 * R.L)) *
      x.D.eps x.M ^ (2 * (weakChi B.α B.q A.η₀ + A.σw * R.L)) * x.D.κ x.M ^ 2 :=
    pfc_const_arith (ε := x.D.eps x.M) (c := plan.radius R) (σ := A.σw)
      (χ := weakChi B.α B.q A.η₀) (Q := Q) (κ := x.D.κ x.M) (θ := pfcPriceConst R cc *
        (weakStoredLedgerData A).C * x.D.eps x.M ^ weakChi B.α B.q A.η₀) R.L hεpos hc0
      hθ0 (le_of_eq (by rw [hQ]))
  have hre : ∀ v : CompIn (g.stage x.M).comps,
      (g.Gw.mass law (g.relabel v))⁻¹ = (weakMass x.D A.Nw A.Jw A.η₀ v.1)⁻¹ := fun v => by
    rw [weakEncoding_mass A.Nw A.Jw A.η₀ _ _ (g.stage x.M) g.Gw g.relabel g.encoding law hm v]
  have hsum : (∑ u, ENNReal.ofReal ((g.Gw.mass law u)⁻¹) *
      ∫⁻ t, ENNReal.ofReal (gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M)
        (Wf u t).val) ∂μ) =
      ∑ v : CompIn (g.stage x.M).comps, ENNReal.ofReal ((weakMass x.D A.Nw A.Jw A.η₀ v.1)⁻¹) *
        ∫⁻ t, ENNReal.ofReal (gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M)
          (weakHighLift g m0 (Whi x.M) v t).val) ∂μ := by
    rw [← g.relabel.sum_comp]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hre v]
    have hsv := g.relabel.symm_apply_apply v
    simp only [Wf]
    generalize g.relabel.symm (g.relabel v) = w at hsv ⊢
    subst hsv
    rfl
  have hSE := pfc_strongEnergy_sq_ge (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M)
    (fun v : CompIn (g.stage x.M).comps => weakMass x.D A.Nw A.Jw A.η₀ v.1)
    (s.tq (x.M + 1)) (x.a + A.T₀) (weakHighFamily g m0 (Uhi x.M)) (weakHighLift g m0 (Whi x.M))
  calc _ ≤ _ := hint
    _ = ENNReal.ofReal K0 * ∑ v : CompIn (g.stage x.M).comps,
        ENNReal.ofReal ((weakMass x.D A.Nw A.Jw A.η₀ v.1)⁻¹) *
          ∫⁻ t, ENNReal.ofReal (gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M)
            (weakHighLift g m0 (Whi x.M) v t).val) ∂μ := by rw [hsum]
    _ ≤ ENNReal.ofReal ((Q ^ 2 / plan.radius R ^ (2 * R.L)) *
          x.D.eps x.M ^ (2 * (weakChi B.α B.q A.η₀ + A.σw * R.L)) * x.D.κ x.M ^ 2) *
        ∑ v : CompIn (g.stage x.M).comps,
        ENNReal.ofReal ((weakMass x.D A.Nw A.Jw A.η₀ v.1)⁻¹) *
          ∫⁻ t, ENNReal.ofReal (gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M)
            (weakHighLift g m0 (Whi x.M) v t).val) ∂μ :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hK) _
    _ = ENNReal.ofReal ((Q ^ 2 / plan.radius R ^ (2 * R.L)) *
          x.D.eps x.M ^ (2 * (weakChi B.α B.q A.η₀ + A.σw * R.L)) * x.D.κ x.M) *
        ∑ v : CompIn (g.stage x.M).comps,
        ENNReal.ofReal ((weakMass x.D A.Nw A.Jw A.η₀ v.1)⁻¹) *
          (ENNReal.ofReal (x.D.κ x.M) *
          ∫⁻ t, ENNReal.ofReal (gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M)
            (weakHighLift g m0 (Whi x.M) v t).val) ∂μ) := by
        rw [show (Q ^ 2 / plan.radius R ^ (2 * R.L)) *
          x.D.eps x.M ^ (2 * (weakChi B.α B.q A.η₀ + A.σw * R.L)) * x.D.κ x.M ^ 2 =
          ((Q ^ 2 / plan.radius R ^ (2 * R.L)) *
          x.D.eps x.M ^ (2 * (weakChi B.α B.q A.η₀ + A.σw * R.L)) * x.D.κ x.M) * x.D.κ x.M by ring,
          ENNReal.ofReal_mul (by have := hκ0; positivity), mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [mul_left_comm]
    _ ≤ _ := by
        gcongr

end AVRegularity.WeakEntryProofs
end
end
end
