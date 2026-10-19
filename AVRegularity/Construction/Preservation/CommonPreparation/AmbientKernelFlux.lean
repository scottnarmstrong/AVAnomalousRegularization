-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.CascadeCover
import AVRegularity.CycleComparison.Error.WeakSolution
import AVRegularity.Families.TorusCompatible.WeakStage
public import AVRegularity.Proofs.WeakGen.Comparison.GateInputs
import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
import AVRegularity.Proofs.Intermediate.CoupledEnergy.CoupledEnergyTorus

section
section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual whole-window Eulerian inputs of the descending-copy solver
from short native chart certificates. One global positive native envelope
is used in the sampling bound, without summing independent window prices.
Only joint measurability needs local-to-global gluing of the same function.
The degenerate cases are included: empty and singleton families, D=2 and order zero, identity
geometry, edgeless families, zero coefficients and empty or point windows.
The constant precedes all types, stages, windows, radii and masses. -/

/-- Whole-window finite/measurable/smooth/periodic coefficients and their
one sampled Schur budget. This is the precise solver/price input, never a
whole-window preparation chart or an assumed weak evolution. -/
def LocalPreparationCoefficientDataStatement : Prop :=
  ∀ (D Kmax Jchart Jm : ℕ), Kmax + D + 2 ≤ Jchart → Kmax + D + 2 ≤ Jm →
  ∀ Cm Cchart : ℕ → ℝ, ∃ Cprep : ℝ, 1 ≤ Cprep ∧
  ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (a b Cpad Cage : ℝ) (Npad : ℕ) (ν e ρ : ℝ),
    0 < ocTauPP α q Λ m → 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
  ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)]
    {Part : Type*} {Ctx : Part → Type*} (F : ChartedFamily ι h D Part Ctx)
    (π : ι → ℝ), (∀ i, 0 < π i) →
  ∀ (K : ι → ℕ), (∀ i, K i ≤ Kmax) → ∀ (actual : ∀ pc, Ctx pc) (B : ι → ι → ℝ),
    (∀ v u, 0 ≤ B v u) →
    (∃ n : ℕ, e⁻¹ = (n : ℝ)) →
    F.IsTimeMeasurable → (∀ p, Measurable (F.weight p)) →
    IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)) →
    (∀ (c d : ℝ), a ≤ c → c ≤ d → d ≤ b → d - c ≤ 2 * ocTauPP α q Λ m →
      ∃ (l₀ : ℤ) (P : ℕ), IsPreparationChartCertificate α q Λ m φ hφ c d
        Cpad Cage Npad Jchart Cchart l₀ P F) →
    IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc a b))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
    (∀ v u d, coefficientSeminorm ρ (K v) a b
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d) ≠ ⊤) ∧
    (∀ v u d, Measurable (fun z : Set.Icc a b × Vec 2 =>
      edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d z.1 z.2)) ∧
    (∀ v u d t, t ∈ Set.Icc a b → ContDiff ℝ (K v : ℕ)
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d t)) ∧
    (∀ v u d t, t ∈ Set.Icc a b → IsZ2Periodic
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K v u d t)) ∧
    ∀ v u, schurMatrix (h := h) ν ρ π K D a b
      (edgeCoefficient F ν e (ocEpsilon q Λ (m - 1)) actual K) v u ≤ Cprep * B v u

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **`LocalPreparationCoefficientDataStatement` from the sampled envelope**. With the constant `C_prep` of the sampled envelope (local-to-global sampling,
`LocalPreparationSampledEnvelopeStatement`), on the whole window `[a, b]`:
- finiteness of the coefficient seminorms and the Schur budget `≤ C_prep · B`:
  `sampled_edgeCoefficient_schur` at the sampled envelope;
- joint measurability: the gluing of the SAME edge coefficients over the short certified windows
  (`edgeCoefficient_window_measurable`), with the smoothness of the family
  from the pointwise envelope;
- smoothness in space: every constituent is `C^{K_v}` (the sampled envelope), and the edge
  coefficient is their finite sum;
- periodicity: torus compatibility and `e⁻¹ ∈ ℕ` (`edgeCoefficient_periodic`).

No long-window chart, no new Cauchy estimate and no sum of window prices enter.

For an empty or edgeless family all sums are empty and the coefficients are zero. -/

universe u₁ u₂ u₃ u₄

/-- The edge coefficients are smooth in space at every time of the window of a sampled envelope. -/
theorem edgeCoefficient_contDiff_of_sampled {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*}
    {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (K : ι → ℕ)
    (actual : ∀ p, Ctx p) {a b ν e E ρ C : ℝ} {B : ι → ι → ℝ}
    (hsamp : IsSampledEnvelope F π K actual a b ν e E ρ C B) (v u : ι)
    (d : admissibleOrders K D v u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (K v : ℕ) (edgeCoefficient F ν e E actual K v u d t) := by
  show ContDiff ℝ (K v : ℕ)
    (fun x => ∑ γ : F.Γ v u, constituentPhysical F ν e E actual v u γ d.1 t x)
  exact ContDiff.sum fun γ _ => hsamp.1 v u γ d.1 t ht

/-- **`LocalPreparationCoefficientDataStatement` from the sampled envelope.** -/
theorem localPreparationCoefficientData_of_sampled
    (hS : LocalPreparationSampledEnvelopeStatement.{u₁, u₂, u₃, u₄}) :
    LocalPreparationCoefficientDataStatement.{u₁, u₂, u₃, u₄} := by
  intro D Kmax Jchart Jm hJc hJm Cm Cchart
  obtain ⟨Cprep, hC1, hS'⟩ := hS D Kmax Jchart Jm hJc hJm Cm Cchart
  refine ⟨Cprep, hC1, ?_⟩
  intro α q Λ m φ hφ a b Cpad Cage Npad ν e ρ hτ hν hρ hρe heE ι _ _ h _ _ _ Part Ctx F π hπ K hK
    actual B hB hNe hTm hWm hT hcert henv
  have hsamp := hS' α q Λ m φ hφ a b Cpad Cage Npad ν e ρ hτ hν hρ hρe heE F π hπ K hK actual B
    hB hcert henv
  have hschur := fun v u => CycleComparison.Error.sampled_edgeCoefficient_schur F π hπ K actual
    a b ν e (ocEpsilon q Λ (m - 1)) ρ Cprep hν hρ (by linarith) B hB hsamp v u
  exact ⟨fun v u d => (hschur v u).1 d,
    fun v u d => edgeCoefficient_window_measurable F hτ hcert ν e _ (fun v => K v + Jm)
      henv.1 hTm hWm actual K v u d,
    fun v u d t ht => edgeCoefficient_contDiff_of_sampled F π K actual hsamp v u d t ht,
    fun v u d t _ => hT.edgeCoefficient_periodic ν e hNe K v u d t,
    fun v u => (hschur v u).2⟩

/-- **The local preparation coefficient data** (at sampled envelope). -/
theorem localPreparationCoefficientData : LocalPreparationCoefficientDataStatement :=
  localPreparationCoefficientData_of_sampled local_preparation_sampled_envelope

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Finite positive sums for copied coefficient data.
Domain restriction is supplied by the shared family producer. -/

/-- An entrywise positive price transfers both finite Schur budgets. -/
theorem schur_of_entrywise_price {ι : Type*} [Fintype ι]
    (A B : ι → ι → ℝ) (C S : ℝ) (hC : 0 ≤ C)
    (hprice : ∀ v u, A v u ≤ C * B v u)
    (hrow : ∀ v, ∑ u, B v u ≤ S) (hcol : ∀ u, ∑ v, B v u ≤ S) :
    SchurBound (C * S) A := by
  constructor
  · intro v
    calc
      _ ≤ ∑ u, C * B v u := Finset.sum_le_sum fun u _ => hprice v u
      _ = C * ∑ u, B v u := (Finset.mul_sum ..).symm
      _ ≤ C * S := mul_le_mul_of_nonneg_left (hrow v) hC
  · intro u
    calc
      _ ≤ ∑ v, C * B v u := Finset.sum_le_sum fun v _ => hprice v u
      _ = C * ∑ v, B v u := (Finset.mul_sum ..).symm
      _ ≤ C * S := mul_le_mul_of_nonneg_left (hcol u) hC

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Real scaling of the actual plain-family equation. This is the torus
adaptation of the plane scaling identity, retaining spatial
integrability at every time and the higher Sobolev lifts.

Empty or singleton families, H=0, the zero datum and edgeless seeds preserve the exact
equation; no norm or mass is divided out. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {K : ι → ℕ} {D : ℕ} {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
  {A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}

omit [∀ i, FiniteDimensional ℝ (h i)] in
private theorem preparation_plain_flux_smul (c t : ℝ)
    (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) :
    torusRawCouplingFlux K D t A (fun j => c • w j) i =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => c • torusRawCouplingFlux K D t A w i x := by
  have hall : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j, ∀ α : JetIndex2 (K j + 1),
      (c • w j).toFunction.jet α x = c • (w j).toFunction.jet α x := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro α
    exact KernelEnergy.torusJet_smul_ae c (w j) α
  filter_upwards [hall] with x hx
  unfold torusRawCouplingFlux
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← map_smul]
  congr 1
  apply (WithLp.ext_iff 2).mpr
  funext word
  exact hx j _

/-- Scaling preserves all five clauses of the actual coupled torus equation. -/
theorem preparation_plain_solution_smul (c : ℝ)
    {f : ∀ i, TorusHk (K i) (h i)}
    {F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionTorus ν a b v D K A (fun i => c • f i)
      (fun i t => c • F i t) (fun i t => c • g i t)
      (fun i t => c • u i t) (fun i t => c • w i t) := by
  refine ⟨fun i => (hs.1 i).const_smul c, fun i => (hs.2.1 i).const_smul c, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hs.2.2.1 i] with s hsu
    change truncateTorusHk (Nat.le_succ (K i)) (c • w i s) = c • u i s
    rw [map_smul, hsu]
  · intro i
    change c • u i a = c • f i
    rw [hs.2.2.2.1 i]
  · intro i t ht φ
    let p := φ.toFunction.jet (valueIndex2 1)
    let dp := fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
    let du := fun s k => (w i s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
    let Q := fun s => torusRawCouplingFlux K D s A (fun j => w j s) i
    let ff := fun s => (F i s).toFunction.jet (valueIndex2 (K i))
    let gg := fun s => (g i s).toFunction.jet (valueIndex2 (K i))
    have hscaled := coupledWeakIdentity_smul (volume.restrict AVenhance.unitCube) c ν a t v
      _ _ p dp du Q ff gg (hs.2.2.2.2 i t ht φ)
    apply coupledWeakIdentity_integrands_congr (volume.restrict AVenhance.unitCube) ν a t v v
      _ _ _ _ p p dp dp (c • du) _ (c • Q) _ (c • ff) _ (c • gg) _ _ _ _ hscaled
    · filter_upwards [KernelEnergy.torusJet_smul_ae c (u i t) (valueIndex2 (K i))] with x hx
      exact congrArg (fun z => inner ℝ z (p x)) hx.symm
    · filter_upwards [KernelEnergy.torusJet_smul_ae c (f i) (valueIndex2 (K i))] with x hx
      exact congrArg (fun z => inner ℝ z (p x)) hx.symm
    · intro s _
      apply weakIdentityRhs_congr_ae (volume.restrict AVenhance.unitCube) ν s v v p p dp dp
        (c • du) _ (c • Q) _ (c • ff) _ (c • gg) _
        Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
      · intro k
        exact (KernelEnergy.torusJet_smul_ae c (w i s)
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩).symm
      · exact (preparation_plain_flux_smul c s (fun j => w j s) i).symm
      · exact (KernelEnergy.torusJet_smul_ae c (F i s) (valueIndex2 (K i))).symm
      · exact (KernelEnergy.torusJet_smul_ae c (g i s) (valueIndex2 (K i))).symm

/-- Clamp a continuous trace outside its actual time window without changing
any part of the coupled weak equation or its higher representative. -/
theorem preparation_plain_solution_trace_congr
    (hab : a ≤ b) {f : ∀ i, TorusHk (K i) (h i)}
    {F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u u' : ∀ i, ℝ → TorusHk (K i) (h i)}
    {w : ∀ i, ℝ → TorusHk (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionTorus ν a b v D K A f F g u w)
    (hu : ∀ i, ∀ t ∈ Set.Icc a b, u' i t = u i t) :
    IsCoupledWeakSolutionTorus ν a b v D K A f F g u' w := by
  refine ⟨fun i => (hs.1 i).congr (fun t ht => hu i t ht), hs.2.1, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [hs.2.2.1 i, ae_restrict_mem measurableSet_Icc] with t hwt ht
    exact hwt.trans (hu i t ht).symm
  · intro i
    exact (hu i a ⟨le_rfl, hab⟩).trans (hs.2.2.2.1 i)
  · intro i t ht φ
    simpa only [hu i t ht] using hs.2.2.2.2 i t ht φ

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual scalar forced equation, via the coupled energy estimate `coupled_energy_torus`.
An empty kernel family identifies scalar superposition with the already proved
kernel superposition. No artificial regularizer or additional PDE assumption
is introduced: there are no edges or regularizer inputs.

Zero datum or forcing, an edgeless seed and a zero-length interval are included. An empty
outer family later applies this componentwise statement vacuously. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A scalar equation has an empty kernel graph. Every kernel condition is
vacuous and the Schur matrix is exactly zero. -/
def preparationScalarKernel {ν ρ a b : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν)
    (k : ℕ) : KernelEnergy.TorusKernelOperator (h := fun _ : Fin 1 => E)
      (Γ := fun _ _ => Empty) (G := fun _ _ _ => E) a b ρ ν k 2 where
  htime := hab
  radius_pos := hρ
  diffusivity_pos := hν
  order_ge_two := le_rfl
  π := fun _ => 1
  hπ := fun _ => zero_lt_one
  B := fun _ _ α => nomatch α
  hB_meas := fun _ _ α => nomatch α
  hB_smooth := fun _ _ α => nomatch α
  hB_per := fun _ _ α => nomatch α
  hB_fin := fun _ _ α => nomatch α
  C := fun _ _ α => nomatch α
  S := fun _ _ α => nomatch α
  c := fun _ => 0
  r := fun _ _ α => nomatch α
  hr := fun _ _ α => nomatch α
  hS := fun _ _ α => nomatch α
  θ := 0
  hθ := by norm_num
  hschur := by
    constructor <;> intro i <;>
      simp only [kernelSchurMatrix, Finset.univ_eq_empty, Finset.sum_empty, mul_zero,
        Finset.sum_const_zero, le_refl]

/-- The unique input family on an empty edge type. -/
def preparationScalarEmptyInput (k : ℕ) :
    ∀ (_ _ : Fin 1) (_ : Empty), ℝ → TorusHk (k + 2 - 1) E :=
  fun _ _ α => nomatch α

/-- Convert the literal scalar row to the empty-kernel equation. -/
theorem preparation_scalar_row_to_kernel {ν ρ a b : ℝ}
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) {v : ℝ → Vec 2 → Vec 2} {k : ℕ}
    {f : TorusHk k E} {F : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E))}
    {g u : ℝ → TorusHk k E} {w : ℝ → TorusHk (k + 1) E}
    (hs : IsTorusForcedRow ν a b v 2 k f F g u w) :
    IsKernelWeakSolutionTorus ν a b v k 2
      (preparationScalarKernel (E := E) hab hρ hν k).B
      (preparationScalarKernel (E := E) hab hρ hν k).C
      (preparationScalarKernel (E := E) hab hρ hν k).S
      (fun _ => f) (fun _ => F) (fun _ => g) (fun _ => u) (fun _ => w)
      (preparationScalarEmptyInput k) := by
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
    (fun _ _ α => nomatch α), (fun _ _ α => nomatch α), ?_⟩
  intro i t ht φ
  simpa only [zero_apply, Finset.sum_const_zero,
    Finset.univ_eq_empty, Finset.sum_empty] using hs.2.2.2.2 i t ht φ

/-- Convert the empty-kernel equation back to the literal scalar row. -/
theorem preparation_scalar_kernel_to_row {ν ρ a b : ℝ}
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) {v : ℝ → Vec 2 → Vec 2} {k : ℕ}
    {f : TorusHk k E} {F : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E))}
    {g u : ℝ → TorusHk k E} {w : ℝ → TorusHk (k + 1) E}
    {y : ∀ (_ _ : Fin 1) (_ : Empty), ℝ → TorusHk (k + 2 - 1) E}
    (hs : IsKernelWeakSolutionTorus ν a b v k 2
      (preparationScalarKernel (E := E) hab hρ hν k).B
      (preparationScalarKernel (E := E) hab hρ hν k).C
      (preparationScalarKernel (E := E) hab hρ hν k).S
      (fun _ => f) (fun _ => F) (fun _ => g) (fun _ => u) (fun _ => w) y) :
    IsTorusForcedRow ν a b v 2 k f F g u w := by
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro i t ht φ
  simpa only [zero_apply, Finset.sum_const_zero,
    Finset.univ_eq_empty, Finset.sum_empty] using hs.2.2.2.2.2.2 i t ht φ

/-- Actual scalar forced existence is a singleton use of `coupled_energy_torus`. -/
theorem preparation_scalar_forced_exists {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax)
    (f : TorusHk k E) (F : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b))) :
    ∃ (u : ℝ → TorusHk k E) (w : ℝ → TorusHk (k + 1) E),
      IsTorusForcedRow ν a b v 2 k f F (fun _ => 0) u w := by
  obtain ⟨α, B, lam, hα, hB, hlam, hjets, hscale, hstrain⟩ := hd.jets
  have he := Providers.coupled_energy_torus a b hab ρ hρ ν hν v hd.bdd hd.meas hd.smooth hd.div
    hd.per α B lam hα hB hlam Kmax hjets hscale hstrain 2 le_rfl
    (ι := Fin 1) (h := fun _ => E)
    (fun _ => 1) (fun _ => zero_lt_one) (fun _ => k) (fun _ => hk) (fun _ _ _ _ _ => 0)
    (fun _ _ _ => measurable_const) (fun _ _ _ _ _ => contDiff_const)
    (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ => by
      rw [CycleComparison.Coarse.coefficientSeminorm_const_zero]
      exact ENNReal.zero_ne_top)
    (CycleComparison.Coarse.zeroCoupling_schur ν ρ _ _ 2 a b)
    (fun _ => f) (fun _ => F) (fun _ => hF)
    (fun _ _ => 0) (fun _ => CoupledEnergy.Variational.timeIntegrable_zero _)
  obtain ⟨u, w, hs⟩ := he.1
  have hu : u = fun _ => u 0 := funext fun j => congrArg u (Subsingleton.elim j 0)
  have hw : w = fun _ => w 0 := funext fun j => congrArg w (Subsingleton.elim j 0)
  rw [hu, hw] at hs
  exact ⟨u 0, w 0, hs⟩
end

/-! One linear scalar forced evolution before its initial datum and flux.
The flux is an actual square-integrable time function, not an assumed response.
The native solution, superposition and uniqueness all use the same drift.

The degenerate cases are included: zero forcing/datum, a singleton, the componentwise empty case,
identity geometry, the smallest order and a zero-length window.
The source space does not quotient away its every-time Sobolev representatives. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Actual scalar fluxes with their time-L2 integrability. -/
def preparationScalarFluxSpace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (k : ℕ) (a b : ℝ) :
    Submodule ℝ (ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E))) where
  carrier := {F | MemLp F 2 (volume.restrict (Set.Icc a b))}
  zero_mem' := CoupledEnergy.Variational.timeMemLp_zero _ 2
  add_mem' := fun hf hg => CoupledEnergy.Variational.timeMemLp_pointwise_add _ 2 _ _ hf hg
  smul_mem' := fun c _ hf => CycleJointProofs.normedCurve_memLp_smul c _ _ hf

abbrev PreparationScalarDatum (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (k : ℕ) (a b : ℝ) :=
  TorusHk k E × preparationScalarFluxSpace E k a b

local instance preparationScalarFluxModule (k : ℕ) (a b : ℝ) :
    Module ℝ (preparationScalarFluxSpace E k a b) :=
  Submodule.module (preparationScalarFluxSpace E k a b)

local instance preparationScalarFluxSMul (k : ℕ) (a b : ℝ) :
    SMul ℝ (preparationScalarFluxSpace E k a b) :=
  (preparationScalarFluxModule (E := E) k a b).toDistribMulAction.toDistribSMul.toSMul

/-- The scalar initial-value problem, for every initial datum and actual flux. -/
structure PreparationScalarEvolution (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (k : ℕ) where
  value : PreparationScalarDatum E k a b → ℝ → TorusHk k E
  gradient : PreparationScalarDatum E k a b → ℝ → TorusHk (k + 1) E
  solution : ∀ x, IsTorusForcedRow ν a b v 2 k x.1 x.2.val (fun _ => 0) (value x) (gradient x)

/-- Choose actual scalar forced solutions from `coupled_energy_torus`. -/
def preparationScalarEvolution {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax) :
    PreparationScalarEvolution (E := E) ν a b v k := by
  classical
  choose u w hs using fun x : PreparationScalarDatum E k a b =>
    preparation_scalar_forced_exists hd hab hρ hν hk x.1 x.2.val x.2.property
  exact ⟨u, w, hs⟩

/-- Scalar uniqueness identifies sums, including sums of the actual flux functions. -/
theorem preparation_scalar_evolution_add {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax)
    (T : PreparationScalarEvolution (E := E) ν a b v k)
    (x z : PreparationScalarDatum E k a b) : ∀ t ∈ Set.Icc a b,
      T.value (x + z) t = T.value x t + T.value z t := by
  let R := preparationScalarKernel (E := E) hab hρ hν k
  have hx := preparation_scalar_row_to_kernel hab hρ hν (T.solution x)
  have hz := preparation_scalar_row_to_kernel hab hρ hν (T.solution z)
  have hs := preparation_kernel_solution_add R v (fun _ => x.1) (fun _ => z.1)
    (fun _ => x.2.val) (fun _ => z.2.val) 0 0
    (fun _ => T.value x) (fun _ => T.value z)
    (fun _ => T.gradient x) (fun _ => T.gradient z)
    (preparationScalarEmptyInput k) (preparationScalarEmptyInput k) hx hz
  simp only [add_zero] at hs
  have hr := preparation_scalar_kernel_to_row hab hρ hν hs
  exact torusForcedRow_unique hd hab hρ hν le_rfl hk (x + z).2.property
    (CoupledEnergy.Variational.timeIntegrable_zero _) (T.solution (x + z)) hr

/-- Scalar uniqueness identifies multiplication of both initial datum and flux. -/
theorem preparation_scalar_evolution_smul {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax)
    (T : PreparationScalarEvolution (E := E) ν a b v k)
    (c : ℝ) (x : PreparationScalarDatum E k a b) : ∀ t ∈ Set.Icc a b,
      T.value (c • x : PreparationScalarDatum E k a b) t = c • T.value x t := by
  let R := preparationScalarKernel (E := E) hab hρ hν k
  have hx := preparation_scalar_row_to_kernel hab hρ hν (T.solution x)
  have hs := preparation_kernel_solution_smul R v (fun _ => x.1)
    (fun _ => x.2.val) 0
    (fun _ => T.value x) (fun _ => T.gradient x) (preparationScalarEmptyInput k) c hx
  simp only [Pi.zero_apply, smul_zero] at hs
  have hr := preparation_scalar_kernel_to_row hab hρ hν hs
  exact torusForcedRow_unique hd hab hρ hν le_rfl hk (c • x : PreparationScalarDatum E k a b).2.property
    (CoupledEnergy.Variational.timeIntegrable_zero _) (T.solution (c • x : PreparationScalarDatum E k a b)) hr

/-- A single linear response before the initial datum and the actual source. -/
def ScalarForcedEvolutionStatement (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (k : ℕ) : Prop :=
  ∃ L : PreparationScalarDatum E k a b →ₗ[ℝ] (ℝ → TorusHk k E),
    ∀ x, ∃ w, IsTorusForcedRow ν a b v 2 k x.1 x.2.val (fun _ => 0) (L x) w

/-- The literal forced scalar evolution is linear in both inputs. -/
theorem scalar_forced_evolution_of_drift {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax) :
    ScalarForcedEvolutionStatement E ν a b v k := by
  let T := preparationScalarEvolution (E := E) hd hab hρ hν hk
  let R := preparationScalarKernel (E := E) hab hρ hν k
  let L : PreparationScalarDatum E k a b →ₗ[ℝ] (ℝ → TorusHk k E) :=
    { toFun := fun x t => T.value x (Set.projIcc a b hab t)
      map_add' := fun x z => by
        funext t
        exact preparation_scalar_evolution_add hd hab hρ hν hk T x z _
          (Set.projIcc a b hab t).property
      map_smul' := fun c x => by
        funext t
        exact preparation_scalar_evolution_smul hd hab hρ hν hk T c x _
          (Set.projIcc a b hab t).property }
  refine ⟨(L : _), fun x => ⟨T.gradient x, ?_⟩⟩
  have hs := preparation_scalar_row_to_kernel hab hρ hν (T.solution x)
  have hc := preparation_kernel_solution_trace_congr R v (fun _ => x.1)
    (fun _ => x.2.val) 0
    (fun _ => T.value x) (fun _ => L x) (fun _ => T.gradient x)
    (preparationScalarEmptyInput k) hs (fun _ t ht => by
      change T.value x (Set.projIcc a b hab t) = T.value x t
      rw [Set.projIcc_of_mem hab ht])
  exact preparation_scalar_kernel_to_row hab hρ hν hc
end

/-! Scalar forced evolution with its linear higher time class and actual energy.
This is the scalar-response ingredient of the source-insertion route. Existence,
uniqueness and the energy estimate are reused, rather than reproved.

The degenerate cases are included: zero datum/flux, singleton or empty outer families, k=0,
identity geometry, an edgeless seed and a zero-length time window.
Only the higher time class is linear; arbitrary representatives need not be. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

attribute [local instance] preparationScalarFluxModule preparationScalarFluxSMul

local instance preparationResponseNativeNormed (k : ℕ) :
    NormedAddCommGroup (TorusHk k E) := inferInstance
local instance preparationResponseNativeModule (k : ℕ) :
    Module ℝ (TorusHk k E) := inferInstance
local instance preparationResponseDatumAdd (k : ℕ) (a b : ℝ) :
    AddCommGroup (PreparationScalarDatum E k a b) := inferInstance
local instance preparationResponseDatumMonoid (k : ℕ) (a b : ℝ) :
    AddCommMonoid (PreparationScalarDatum E k a b) :=
  (preparationResponseDatumAdd (E := E) k a b).toAddCommMonoid
local instance preparationResponseDatumModule (k : ℕ) (a b : ℝ) :
    Module ℝ (PreparationScalarDatum E k a b) := inferInstance
local instance preparationResponseAEEqAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (ℝ →ₘ[μ] TorusHk k E) := AEEqFun.instAddCommGroup
local instance preparationResponseLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (TorusHk k E) 2 μ) := Lp.instAddCommGroup
local instance preparationResponseLpMonoid (k : ℕ) (μ : Measure ℝ) :
    AddCommMonoid (Lp (TorusHk k E) 2 μ) :=
  (preparationResponseLpAdd (E := E) k μ).toAddCommMonoid
local instance preparationResponseLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (TorusHk k E) 2 μ) := Lp.instModule
local instance preparationResponseLpSMul (k : ℕ) (μ : Measure ℝ) :
    SMul ℝ (Lp (TorusHk k E) 2 μ) :=
  (preparationResponseLpModule (E := E) k μ).toDistribMulAction.toDistribSMul.toSMul

private theorem preparation_scalar_truncation_injective {K L : ℕ} (hKL : K ≤ L) :
    Function.Injective (truncateTorusHk (E := E) hKL) := by
  intro f g hfg
  apply TorusHk.ext_value
  exact congrArg (fun z : TorusHk K E => z.val (valueIndex2 K)) hfg

/-- Almost-everywhere linear trajectories induce a linear map of time classes. -/
theorem preparation_time_class_linear {X V : Type*}
    [AddCommGroup X] [Module ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure ℝ) (W : X → ℝ → V) (hW : ∀ x, MemLp (W x) 2 μ)
    (ha : ∀ x z, W (x + z) =ᵐ[μ] fun t => W x t + W z t)
    (hc : ∀ (c : ℝ) x, W (c • x) =ᵐ[μ] fun t => c • W x t) :
    ∃ V : X →ₗ[ℝ] Lp V 2 μ, ∀ x, V x = (hW x).toLp (W x) := by
  let V (x : X) : Lp V 2 μ := (hW x).toLp (W x)
  refine ⟨{ toFun := V, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
  · intro x z
    apply Lp.ext
    filter_upwards [(hW (x + z)).coeFn_toLp, (hW x).coeFn_toLp,
      (hW z).coeFn_toLp, Lp.coeFn_add (V x) (V z), ha x z]
      with t hxz hx hz hv hw
    change V (x + z) t = (V x + V z) t
    rw [hv, Pi.add_apply, hxz, hx, hz, hw]
  · intro c x
    apply Lp.ext
    filter_upwards [(hW (c • x)).coeFn_toLp, (hW x).coeFn_toLp,
      Lp.coeFn_smul c (V x), hc c x] with t hcx hx hv hw
    change V (c • x) t = (c • V x) t
    rw [hv, Pi.smul_apply, hcx, hx, hw]

/-- An injective lift of a linear time trace is additive almost everywhere. -/
theorem preparation_time_lift_add {X V H : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup H] [Module ℝ H] (μ : Measure ℝ)
    (L : X →ₗ[ℝ] (ℝ → H)) (T : V →ₗ[ℝ] H) (hT : Function.Injective T)
    (W : X → ℝ → V) (hw : ∀ x, ∀ᵐ t ∂μ, T (W x t) = L x t) (x z : X) :
    W (x + z) =ᵐ[μ] fun t => W x t + W z t := by
  filter_upwards [hw (x + z), hw x, hw z] with t hxz hx hz
  apply hT
  rw [T.map_add, hxz, hx, hz]
  exact congrFun (L.map_add x z) t

/-- An injective lift of a linear time trace is homogeneous almost everywhere. -/
theorem preparation_time_lift_smul {X V H : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup H] [Module ℝ H] (μ : Measure ℝ)
    (L : X →ₗ[ℝ] (ℝ → H)) (T : V →ₗ[ℝ] H) (hT : Function.Injective T)
    (W : X → ℝ → V) (hw : ∀ x, ∀ᵐ t ∂μ, T (W x t) = L x t) (c : ℝ) (x : X) :
    W (c • x) =ᵐ[μ] fun t => c • W x t := by
  filter_upwards [hw (c • x), hw x] with t hcx hx
  apply hT
  rw [T.map_smul, hcx, hx]
  exact congrFun (L.map_smul c x) t

private theorem preparation_time_higher_linear {X V H : Type*}
    [AddCommGroup X] [Module ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [AddCommGroup H] [Module ℝ H] (μ : Measure ℝ)
    (L : X →ₗ[ℝ] (ℝ → H)) (T : V →ₗ[ℝ] H) (hT : Function.Injective T)
    (W : X → ℝ → V) (hm : ∀ x, MemLp (W x) 2 μ)
    (ha : ∀ x, ∀ᵐ t ∂μ, T (W x t) = L x t) :
    ∃ V : X →ₗ[ℝ] Lp V 2 μ, ∀ x, V x = (hm x).toLp (W x) :=
  preparation_time_class_linear μ W hm
    (preparation_time_lift_add μ L T hT W ha)
    (preparation_time_lift_smul μ L T hT W ha)

/-- Both energy readouts are linear before the data. The chosen higher
representative is retained separately from its linear L2 class. -/
structure PreparationScalarResponse (ν a b : ℝ) (v : ℝ → Vec 2 → Vec 2) (k : ℕ) where
  trace : PreparationScalarDatum E k a b →ₗ[ℝ] (ℝ → TorusHk k E)
  higher : PreparationScalarDatum E k a b →ₗ[ℝ]
    Lp (TorusHk (k + 1) E) 2 (volume.restrict (Set.Icc a b))
  gradient : PreparationScalarDatum E k a b → ℝ → TorusHk (k + 1) E
  gradient_memLp : ∀ x, MemLp (gradient x) 2 (volume.restrict (Set.Icc a b))
  solution : ∀ x, IsTorusForcedRow ν a b v 2 k x.1 x.2.val
    (fun _ => 0) (trace x) (gradient x)
  higher_eq : ∀ x, higher x = (gradient_memLp x).toLp (gradient x)

private theorem preparation_scalar_response_of_realization {ν a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {k : ℕ}
    (L : PreparationScalarDatum E k a b →ₗ[ℝ] (ℝ → TorusHk k E))
    (W : PreparationScalarDatum E k a b → ℝ → TorusHk (k + 1) E)
    (hW : ∀ x, IsTorusForcedRow ν a b v 2 k x.1 x.2.val (fun _ => 0) (L x) (W x)) :
    Nonempty (PreparationScalarResponse (E := E) ν a b v k) := by
  have hm := fun x => (hW x).2.1 0
  have ha := fun x => (hW x).2.2.1 0
  beta_reduce at hm ha
  let T := (truncateTorusHk (E := E) (Nat.le_succ k)).toLinearMap
  have hT : Function.Injective T := preparation_scalar_truncation_injective _
  obtain ⟨V, hV⟩ := preparation_time_higher_linear _ L T hT W hm ha
  exact ⟨{
    trace := L
    higher := V
    gradient := W
    gradient_memLp := hm
    solution := hW
    higher_eq := hV }⟩

/-- Linearity of the continuous trace forces linearity of its higher L2 class. -/
theorem preparation_scalar_response_of_linear_trace {ν a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {k : ℕ}
    (L : PreparationScalarDatum E k a b →ₗ[ℝ] (ℝ → TorusHk k E))
    (hL : ∀ x, ∃ w, IsTorusForcedRow ν a b v 2 k x.1 x.2.val (fun _ => 0) (L x) w) :
    Nonempty (PreparationScalarResponse (E := E) ν a b v k) := by
  classical
  choose W hW using hL
  exact preparation_scalar_response_of_realization L W hW

/-- The scalar forced response exists with both linear energy readouts. -/
theorem preparation_scalar_response_exists {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax) :
    Nonempty (PreparationScalarResponse (E := E) ν a b v k) := by
  obtain ⟨L, hL⟩ := scalar_forced_evolution_of_drift (E := E) hd hab hρ hν hk
  exact preparation_scalar_response_of_linear_trace L hL
end

/-! Scalar response factors through the forcing's time-L2 class. The existing
forcing-congruence theorem retains spatial integrability at every time. The
forcing class lives in ambient jets. A fixed closed-graph readout produces
actual Sobolev fluxes and is the identity on every actual forcing; the initial
datum is retained. No linear choice of time representatives is asserted.

Zero forcing or datum, singleton and empty outer families, edgeless seeds and zero-length
windows are included. Trace
identification is on the closed solution window; higher classes agree in L2. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
attribute [local instance] preparationScalarFluxModule preparationScalarFluxSMul


/-- Ambient forcing jets, with no closed-submodule instance chain in their L2 class. -/
abbrev PreparationScalarFluxAmbient (E : Type*) [NormedAddCommGroup E] [MeasurableSpace E] (k : ℕ) :=
  JetL2 (volume.restrict AVenhance.unitCube) k (PiLp 2 (fun _ : Fin 2 => E))

/-- Initial data and an ambient forcing class; no linear representative section is used. -/
abbrev PreparationScalarClassDatum (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (k : ℕ) (a b : ℝ) :=
  TorusHk k E × Lp (PreparationScalarFluxAmbient E k) 2 (volume.restrict (Set.Icc a b))

local instance preparationClassFluxAdd (k : ℕ) (a b : ℝ) :
    AddCommGroup (Lp (PreparationScalarFluxAmbient E k) 2 (volume.restrict (Set.Icc a b))) :=
  Lp.instAddCommGroup
local instance preparationClassFluxMonoid (k : ℕ) (a b : ℝ) :
    AddCommMonoid (Lp (PreparationScalarFluxAmbient E k) 2 (volume.restrict (Set.Icc a b))) :=
  (preparationClassFluxAdd (E := E) k a b).toAddCommMonoid

local instance preparationClassFluxModule (k : ℕ) (a b : ℝ) :
    Module ℝ (Lp (PreparationScalarFluxAmbient E k) 2 (volume.restrict (Set.Icc a b))) :=
  Lp.instModule (E := PreparationScalarFluxAmbient E k)
    (p := 2) (μ := volume.restrict (Set.Icc a b))

local instance preparationClassDatumAdd (k : ℕ) (a b : ℝ) :
    AddCommGroup (PreparationScalarClassDatum E k a b) := inferInstance
local instance preparationClassDatumMonoid (k : ℕ) (a b : ℝ) :
    AddCommMonoid (PreparationScalarClassDatum E k a b) :=
  (preparationClassDatumAdd (E := E) k a b).toAddCommMonoid
local instance preparationClassDatumModule (k : ℕ) (a b : ℝ) :
    Module ℝ (PreparationScalarClassDatum E k a b) := Prod.instModule

local instance preparationClassDatumSMul (k : ℕ) (a b : ℝ) :
    SMul ℝ (PreparationScalarClassDatum E k a b) :=
  (preparationClassDatumModule (E := E) k a b).toDistribMulAction.toDistribSMul.toSMul

/-- Recover a genuine forcing carrier from ambient jets by the graph projection. -/
def preparationScalarFluxReadout (k : ℕ) :
    PreparationScalarFluxAmbient E k →L[ℝ] TorusHk k (PiLp 2 (fun _ : Fin 2 => E)) :=
  CoupledEnergy.Variational.closedSubmoduleReadout
    (torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => E)) k)

/-- The fixed readout preserves every actual native forcing. -/
theorem preparation_scalar_flux_readout_carrier (k : ℕ)
    (F : TorusHk k (PiLp 2 (fun _ : Fin 2 => E))) :
    preparationScalarFluxReadout (E := E) k F.val = F := by
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr F.property

/-- Choose a measurable time representative and read its actual Sobolev flux.
This is not a linear section; scalar uniqueness removes representative choices. -/
def preparationScalarClassRepresentative (k : ℕ) (a b : ℝ)
    (x : PreparationScalarClassDatum E k a b) : PreparationScalarDatum E k a b := by
  refine (x.1, ⟨fun t => preparationScalarFluxReadout (E := E) k (x.2 t), ?_⟩)
  change MemLp (fun t => preparationScalarFluxReadout (E := E) k (x.2 t)) 2
    (volume.restrict (Set.Icc a b))
  exact CoupledEnergy.Variational.closedSubmoduleReadout_memLp _ (Lp.memLp x.2)

/-- Pass an actual source to its ambient class, retaining the initial datum. -/
def preparationScalarDatumClass (k : ℕ) (a b : ℝ)
    (x : PreparationScalarDatum E k a b) : PreparationScalarClassDatum E k a b := by
  let F : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E)) := x.2.val
  have hF : MemLp F 2 (volume.restrict (Set.Icc a b)) := x.2.property
  have hm := CoupledEnergy.Variational.torusJet_memLp
    (E := PiLp 2 (fun _ : Fin 2 => E)) (f := F) k hF
  exact (x.1, hm.toLp (fun t => (F t).val))

/-- The ambient source class represents the actual native forcing almost everywhere. -/
theorem preparation_scalar_datum_class_ae (k : ℕ) (a b : ℝ)
    (x : PreparationScalarDatum E k a b) :
    (preparationScalarDatumClass (E := E) k a b x).2 =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => (x.2.val t).val := by
  dsimp only [preparationScalarDatumClass]
  exact MemLp.coeFn_toLp _

/-- A homogeneous actual datum has exactly its initial datum and zero forcing class. -/
theorem preparation_scalar_zero_forcing_class (k : ℕ) (a b : ℝ) (f : TorusHk k E) :
    preparationScalarDatumClass (E := E) k a b (f, 0) = (f, 0) := by
  refine Prod.ext rfl ?_
  apply Lp.ext
  filter_upwards [preparation_scalar_datum_class_ae k a b (f, 0),
    Lp.coeFn_zero (PreparationScalarFluxAmbient E k) 2 (volume.restrict (Set.Icc a b))]
    with t ht hz
  refine ht.trans (Eq.trans ?_ hz.symm)
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply]

attribute [local instance]
  preparationResponseNativeNormed preparationResponseNativeModule
  preparationResponseDatumAdd preparationResponseDatumMonoid preparationResponseDatumModule
  preparationResponseLpAdd preparationResponseLpMonoid preparationResponseLpModule preparationResponseLpSMul

/-- Equal initial data give the same scalar row. -/
private theorem torusRowSolution_initial_congr {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {D k : ℕ}
    {f f' : TorusHk k E} {Q : ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => E))}
    {u : ℝ → TorusHk k E} {w : ℝ → TorusHk (k + 1) E} (hf : f = f')
    (hs : CycleJointProofs.PathReduction.IsTorusRowSolution ν a b v D k f Q u w) :
    CycleJointProofs.PathReduction.IsTorusRowSolution ν a b v D k f' Q u w := hf ▸ hs

/-- Time-a.e. forcing equality gives the same continuous trace and higher class. -/
theorem preparation_scalar_response_time_congr {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax)
    (R : PreparationScalarResponse (E := E) ν a b v k)
    (x z : PreparationScalarDatum E k a b) (hinit : x.1 = z.1)
    (hflux : x.2.val =ᵐ[volume.restrict (Set.Icc a b)] z.2.val) :
    (∀ t ∈ Set.Icc a b, R.trace x t = R.trace z t) ∧ R.higher x = R.higher z := by
  have hx := CycleJointProofs.PathReduction.torusRowSolution_forcing_congr ν a b v 2 k
    x.1 x.2.val z.2.val (R.trace x) (R.gradient x) hflux (R.solution x)
  replace hx := torusRowSolution_initial_congr hinit hx
  have ht := torusForcedRow_unique hd hab hρ hν le_rfl hk z.2.property
    (CoupledEnergy.Variational.timeIntegrable_zero _) hx (R.solution z)
  refine ⟨ht, ?_⟩
  rw [R.higher_eq, R.higher_eq]
  apply Lp.ext
  filter_upwards [(R.gradient_memLp x).coeFn_toLp, (R.gradient_memLp z).coeFn_toLp,
    (R.solution x).2.2.1 0, (R.solution z).2.2.1 0,
    ae_restrict_mem measurableSet_Icc] with t hxt hzt hxw hzw hI
  rw [hxt, hzt]
  apply TorusHk.ext_value
  exact congrArg (fun y : TorusHk k E => y.val (valueIndex2 k))
    ((hxw.trans (ht t hI)).trans hzw.symm)

/-- Both response readouts descend to the same forcing quotient. -/
def ScalarTimeClassResponseStatement {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2} {k : ℕ}
    (R : PreparationScalarResponse (E := E) ν a b v k) : Prop :=
  ∃ (L : PreparationScalarClassDatum E k a b →ₗ[ℝ] (ℝ → TorusHk k E))
    (H : PreparationScalarClassDatum E k a b →ₗ[ℝ]
      Lp (TorusHk (k + 1) E) 2 (volume.restrict (Set.Icc a b))),
    (∀ x, ContinuousOn (L x) (Set.Icc a b)) ∧
    (∀ x, L x a = x.1) ∧
    (∀ x, ∀ t ∈ Set.Icc a b, L (preparationScalarDatumClass (E := E) k a b x) t = R.trace x t) ∧
    (∀ x, H (preparationScalarDatumClass (E := E) k a b x) = R.higher x)

private theorem preparation_scalar_class_add {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax)
    (R : PreparationScalarResponse (E := E) ν a b v k)
    (x z : PreparationScalarClassDatum E k a b) :
    (∀ t ∈ Set.Icc a b,
      R.trace (preparationScalarClassRepresentative (E := E) k a b (x + z)) t =
        R.trace (preparationScalarClassRepresentative (E := E) k a b x) t +
          R.trace (preparationScalarClassRepresentative (E := E) k a b z) t) ∧
    R.higher (preparationScalarClassRepresentative (E := E) k a b (x + z)) =
      R.higher (preparationScalarClassRepresentative (E := E) k a b x) +
        R.higher (preparationScalarClassRepresentative (E := E) k a b z) := by
  let S := preparationScalarClassRepresentative (E := E) k a b
  have hflux : (S (x + z)).2.val =ᵐ[volume.restrict (Set.Icc a b)] (S x + S z).2.val := by
    filter_upwards [Lp.coeFn_add x.2 z.2] with t ht
    exact (congrArg (preparationScalarFluxReadout (E := E) k) ht).trans
      ((preparationScalarFluxReadout (E := E) k).map_add (x.2 t) (z.2 t))
  have hc := preparation_scalar_response_time_congr hd hab hρ hν hk R
    (S (x + z)) (S x + S z) rfl hflux
  exact ⟨fun t ht => ((hc.1 t ht).trans (congrFun (R.trace.map_add (S x) (S z)) t)),
    hc.2.trans (R.higher.map_add (S x) (S z))⟩

private theorem preparation_scalar_class_smul {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax)
    (R : PreparationScalarResponse (E := E) ν a b v k)
    (c : ℝ) (x : PreparationScalarClassDatum E k a b) :
    (∀ t ∈ Set.Icc a b,
      R.trace (preparationScalarClassRepresentative (E := E) k a b (c • x)) t =
        c • R.trace (preparationScalarClassRepresentative (E := E) k a b x) t) ∧
    R.higher (preparationScalarClassRepresentative (E := E) k a b (c • x)) =
      c • R.higher (preparationScalarClassRepresentative (E := E) k a b x) := by
  let S := preparationScalarClassRepresentative (E := E) k a b
  have hflux : (S (c • x)).2.val =ᵐ[volume.restrict (Set.Icc a b)] (c • S x).2.val := by
    filter_upwards [Lp.coeFn_smul c x.2] with t ht
    exact (congrArg (preparationScalarFluxReadout (E := E) k) ht).trans
      ((preparationScalarFluxReadout (E := E) k).map_smul c (x.2 t))
  have hc := preparation_scalar_response_time_congr hd hab hρ hν hk R
    (S (c • x)) (c • S x) rfl hflux
  exact ⟨fun t ht => ((hc.1 t ht).trans (congrFun (R.trace.map_smul c (S x)) t)),
    hc.2.trans (R.higher.map_smul c (S x))⟩

private theorem preparation_scalar_class_actual {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax)
    (R : PreparationScalarResponse (E := E) ν a b v k)
    (x : PreparationScalarDatum E k a b) :
    (∀ t ∈ Set.Icc a b,
      R.trace (preparationScalarClassRepresentative (E := E) k a b (preparationScalarDatumClass (E := E) k a b x)) t = R.trace x t) ∧
    R.higher (preparationScalarClassRepresentative (E := E) k a b (preparationScalarDatumClass (E := E) k a b x)) = R.higher x := by
  let S := preparationScalarClassRepresentative (E := E) k a b
  have hflux : (S (preparationScalarDatumClass (E := E) k a b x)).2.val
      =ᵐ[volume.restrict (Set.Icc a b)] x.2.val := by
    filter_upwards [preparation_scalar_datum_class_ae k a b x] with t ht
    exact (congrArg (preparationScalarFluxReadout (E := E) k) ht).trans
      (preparation_scalar_flux_readout_carrier k (x.2.val t))
  exact preparation_scalar_response_time_congr hd hab hρ hν hk R
    (S (preparationScalarDatumClass (E := E) k a b x)) x rfl hflux

/-- Actual scalar uniqueness makes the class response linear, without a linear
choice of representatives in the actual forcing space. -/
theorem preparation_scalar_time_class_response {ν ρ a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {k Kmax : ℕ} (hd : TorusDriftData ν ρ a b v Kmax)
    (hab : a ≤ b) (hρ : 0 < ρ) (hν : 0 < ν) (hk : k ≤ Kmax)
    (R : PreparationScalarResponse (E := E) ν a b v k) :
    ScalarTimeClassResponseStatement R := by
  let S := preparationScalarClassRepresentative (E := E) k a b
  let L : PreparationScalarClassDatum E k a b →ₗ[ℝ] (ℝ → TorusHk k E) :=
    { toFun := fun x t => R.trace (S x) (Set.projIcc a b hab t)
      map_add' := fun x z => by
        funext t
        exact (preparation_scalar_class_add hd hab hρ hν hk R x z).1 _
          (Set.projIcc a b hab t).property
      map_smul' := fun c x => by
        funext t
        exact (preparation_scalar_class_smul hd hab hρ hν hk R c x).1 _
          (Set.projIcc a b hab t).property }
  let H : PreparationScalarClassDatum E k a b →ₗ[ℝ]
      Lp (TorusHk (k + 1) E) 2 (volume.restrict (Set.Icc a b)) :=
    { toFun := fun x => R.higher (S x)
      map_add' := fun x z => (preparation_scalar_class_add hd hab hρ hν hk R x z).2
      map_smul' := fun c x => (preparation_scalar_class_smul hd hab hρ hν hk R c x).2 }
  refine ⟨L, H, ?_, ?_, ?_, fun x => (preparation_scalar_class_actual hd hab hρ hν hk R x).2⟩
  · intro x
    apply ((R.solution (S x)).1 0).congr
    intro t ht
    change R.trace (S x) (Set.projIcc a b hab t) = R.trace (S x) t
    rw [Set.projIcc_of_mem hab ht]
  · intro x
    change R.trace (S x) (Set.projIcc a b hab a) = x.1
    rw [Set.projIcc_left]
    exact (R.solution (S x)).2.2.2.1 0
  · intro x t ht
    change R.trace (S (preparationScalarDatumClass (E := E) k a b x)) (Set.projIcc a b hab t) = R.trace x t
    rw [Set.projIcc_of_mem hab ht]
    exact (preparation_scalar_class_actual hd hab hρ hν hk R x).1 t ht
end

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The actual kernel flux acts linearly on ambient higher time classes and
lands directly in ambient forcing classes. This avoids an Lp-of-Sobolev-graph
module chain in the kernel-insertion map. The fixed scalar readout then
recovers the genuine forcing; equality with actual carrier fluxes is explicit.

The degenerate cases are included: empty and singleton families, zero data, no edges, smallest
orders, identity geometry and zero-length windows keep the same flux operation. No
unprojected equation for arbitrary off-graph forcing is asserted. -/

attribute [local instance] preparationResponseNativeNormed preparationResponseNativeModule
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
  {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
  [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
  [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
  [∀ i j α, CompleteSpace (G i j α)] {a b ρ ν : ℝ} {k D : ℕ}
variable (P : KernelEnergy.TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

/-- The actual native kernel flux, viewed in ambient forcing jets. -/
def preparationAmbientKernelFluxPoint (i : ι) (t : ℝ) :
    CoupledHighHilbert (h := h) (fun _ => k) →L[ℝ] PreparationScalarFluxAmbient (h i) k :=
  (torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => h i)) k).toSubmodule.subtypeL.comp
    (P.clampedAmbientFluxCLM i t)

/-- Inside the solution window the ambient source is exactly the canonical kernel flux. -/
theorem preparation_clamped_kernel_flux_eq (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (U : CoupledHighHilbert (h := h) (fun _ => k)) :
    P.clampedAmbientFluxCLM i t U = P.flux t ht
      (KernelEnergy.TorusKernelOperator.ambientCarrierCLM (h := h) (k := k) U) i := by
  classical
  change P.flux (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property
    (KernelEnergy.TorusKernelOperator.ambientCarrierCLM (h := h) (k := k) U) i = _
  rw [Set.projIcc_of_mem P.htime ht]

/-- Strong measurability survives the fixed ambient inclusion. -/
theorem preparation_ambient_kernel_flux_measurable (i : ι)
    (U : CoupledHighHilbert (h := h) (fun _ => k)) :
    StronglyMeasurable (fun t => preparationAmbientKernelFluxPoint P i t U) :=
  (torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => h i)) k).toSubmodule.subtypeL.continuous.comp_stronglyMeasurable
    (P.clampedAmbientFluxCLM_stronglyMeasurable i U)

/-- A finite bound for the ambient flux action, independent of its input. -/
def preparationAmbientKernelFluxBudget (i : ι) : ℝ :=
  ‖(torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => h i)) k).toSubmodule.subtypeL‖ *
    P.ambientFluxBudget

/-- The finite ambient operator budget is nonnegative. -/
theorem preparation_ambient_kernel_flux_budget_nonneg (i : ι) :
    0 ≤ preparationAmbientKernelFluxBudget P i := by
  change 0 ≤ ‖(torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => h i)) k).toSubmodule.subtypeL‖ *
    P.ambientFluxBudget
  exact mul_nonneg
    (norm_nonneg ((torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => h i)) k).toSubmodule.subtypeL))
    P.ambientFluxBudget_nonneg

/-- The native operator bound passes through the ambient inclusion. -/
theorem preparation_ambient_kernel_flux_norm_le (i : ι) (t : ℝ) :
    ‖preparationAmbientKernelFluxPoint P i t‖ ≤ preparationAmbientKernelFluxBudget P i := by
  let J := (torusHkGraph (E := PiLp 2 (fun _ : Fin 2 => h i)) k).toSubmodule.subtypeL
  change ‖J.comp (P.clampedAmbientFluxCLM i t)‖ ≤ ‖J‖ * P.ambientFluxBudget
  have hc := ContinuousLinearMap.opNorm_comp_le J (P.clampedAmbientFluxCLM i t)
  exact hc.trans (mul_le_mul_of_nonneg_left
    (P.clampedAmbientFluxCLM_norm_le i t) (norm_nonneg J))

/-- One linear Bochner operator before both the input trajectory and its weight. -/
def preparationAmbientKernelTimeFlux (i : ι) :
    CoupledHighTime (h := h) (fun _ => k) a b →L[ℝ]
      Lp (PreparationScalarFluxAmbient (h i) k) 2 (volume.restrict (Set.Icc a b)) :=
  KernelEnergy.timeOperatorCLM (volume.restrict (Set.Icc a b))
    (preparationAmbientKernelFluxPoint P i) (preparation_ambient_kernel_flux_measurable P i)
    (preparationAmbientKernelFluxBudget P i)
    (preparation_ambient_kernel_flux_budget_nonneg P i)
    (preparation_ambient_kernel_flux_norm_le P i)

/-- Its time representative is exactly the ambient actual flux a.e. -/
theorem preparation_ambient_kernel_time_flux_ae (i : ι)
    (U : CoupledHighTime (h := h) (fun _ => k) a b) :
    preparationAmbientKernelTimeFlux P i U =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => (P.clampedAmbientFluxCLM i t (U t)).val :=
  KernelEnergy.timeOperatorValue_ae (volume.restrict (Set.Icc a b))
    (preparationAmbientKernelFluxPoint P i) (preparation_ambient_kernel_flux_measurable P i)
    (preparationAmbientKernelFluxBudget P i) (preparation_ambient_kernel_flux_budget_nonneg P i)
    (preparation_ambient_kernel_flux_norm_le P i) U

/-- Actual zero-initial scalar data for the native switched source. -/
def preparationKernelScalarDatum (i : ι)
    (U : CoupledHighTime (h := h) (fun _ => k) a b) : PreparationScalarDatum (h i) k a b :=
  (0, ⟨fun t => P.clampedAmbientFluxCLM i t (U t), P.limitFlux_memLp U i⟩)

/-- Its actual datum class is exactly the linear ambient kernel source. -/
theorem preparation_kernel_scalar_datum_class (i : ι)
    (U : CoupledHighTime (h := h) (fun _ => k) a b) :
    preparationScalarDatumClass (E := h i) k a b (preparationKernelScalarDatum P i U) =
      (0, preparationAmbientKernelTimeFlux P i U) := by
  refine Prod.ext rfl ?_
  apply Lp.ext
  filter_upwards [preparation_scalar_datum_class_ae k a b (preparationKernelScalarDatum P i U),
    preparation_ambient_kernel_time_flux_ae P i U] with t ht hf
  exact ht.trans hf.symm

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
