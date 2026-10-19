-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Frontier.GradeSourceProduction
public import AVRegularity.Construction.Preservation.Frontier.GradeRows.ExtendedLedger
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.CycleComparison.Coarse.Energy.Word
import AVRegularity.Proofs.WeakGen.Comparison.GateInputs
import AVRegularity.Proofs.Results.Construction.SuccessorExists
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.KernelEnergy.TorusKernelResidualODE
import AVRegularity.Proofs.ComplexContext.Assemble
import AVRegularity.Proofs.Results.Construction.ComparisonLiftPositiveLayer
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier

/-! Zero extension from retained columns to the full family. All spatial representatives
are compared almost everywhere; the supplied higher lifts remain literal at every time. -/

section
open KernelEnergy FullLift
open scoped Classical
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Extend the retained unknown by zero, not by a choice of representative. -/
def Frame.extendedUnknown (F : Frame D hr Dm bw j₀) (u : CompIn F.G'.comps) (t : ℝ) :
    TorusHk (F.k + 1) (hr u.1.root) :=
  if hu : IsRetained F.m F.H F.J u.1 then
    F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t else 0

/-- Extend supplied kernel lifts by zero in the same columns. -/
def Frame.extendedHigher (F : Frame D hr Dm bw j₀)
    (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u) (t : ℝ) :
    TorusHk (F.k + Dm - 1) (hr u.1.root) :=
  if IsRetained F.m F.H F.J u.1 then F.yom v u γ t else 0

theorem frontier_extended_unknown_memLp (F : Frame D hr Dm bw j₀)
    (hw : ∀ u, MemLp (F.Yw u) 2 (volume.restrict (Set.Icc F.tp F.tf))) :
    ∀ u, MemLp (F.extendedUnknown u) 2 (volume.restrict (Set.Icc F.tp F.tf)) := by
  classical
  intro u
  change MemLp (fun t => F.extendedUnknown u t) 2 _
  by_cases hu : IsRetained F.m F.H F.J u.1
  · simpa only [Frame.extendedUnknown, dite_eq_left hu] using hw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩
  · simp only [Frame.extendedUnknown, dite_eq_right hu]
    exact AVRegularity.Providers.WeakGen.Comparison.torusHk_memLp_zero (F.k + 1) _

/-- Zero extension preserves exactly the marked gradient square, including empty families. -/
theorem frontier_extended_gradient_mass (F : Frame D hr Dm bw j₀) (t : ℝ) :
    massGradNormSq (rhoEnh D F.cr F.m)
      (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
      (fun v => (F.extendedUnknown v t).val) =
    massGradNormSq (rhoEnh D F.cr F.m)
      (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
      (fun v => (F.Yw v t).val) := by
  classical
  unfold massGradNormSq
  rw [finite_own_component_sum (show F.Gr.comps ⊆ F.G'.comps from Finset.filter_subset _ _) _ ?_]
  · apply Finset.sum_congr rfl
    intro v _
    have hv := (Finset.mem_filter.1 v.2).2
    simp only [Frame.extendedUnknown, dite_eq_left hv]
    rfl
  · intro v hv
    have hn : ¬IsRetained F.m F.H F.J v.1 := fun hh =>
      hv (Finset.mem_filter.2 ⟨v.2, hh⟩)
    simp only [Frame.extendedUnknown, dite_eq_right hn, Submodule.coe_zero, gradFactorialNormSq,
      WithLp.ofLp_zero, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, mul_zero]

/-- Selecting output rows can only decrease the mass square. -/
theorem frontier_selected_mass_le (F : Frame D hr Dm bw j₀)
    (hπ : ∀ v : CompIn F.G'.comps, 0 < F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
    (V : ∀ v : CompIn F.G'.comps, TorusHk F.k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) :
    massNormSq (rhoEnh D F.cr F.m)
      (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
      (fun v => (if F.select true v.1 then V v else 0).val) ≤
    massNormSq (rhoEnh D F.cr F.m)
      (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) (fun v => (V v).val) := by
  classical
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : F.select true v.1
  · simp only [ite_eq_left hv, le_refl]
  · simp only [ite_eq_right hv, Submodule.coe_zero, CycleComparison.Coarse.factorialNormSq_zero_jet,
      mul_zero]
    exact mul_nonneg (inv_nonneg.mpr (hπ v).le) (factorialNormSq_nonneg _ _)

/-- Arbitrary supplied lifts give the literal omitted flux at every time. -/
theorem frontier_extended_flux_raw (F : Frame D hr Dm bw j₀)
    (P : TorusKernelOperator (h := fun v : CompIn F.G'.comps => hr v.1.root)
      (Γ := F.G'.fam.Γ) (G := fun _ u _ => hr u.1.root)
      F.tp F.tf (rhoEnh D F.cr F.m) (D.κ (F.m - 1)) F.k Dm)
    (hB : P.B = fun v u γ (d : ↥(Finset.Icc 2 Dm)) => F.G'.physCoeff v u γ d.1)
    (v : CompIn F.G'.comps) (t : ℝ) (ht : t ∈ Set.Icc F.tp F.tf) :
    (gradeRowSuppliedFlux P F.extendedHigher v t).toFunction.jet (valueIndex2 F.k)
      =ᵐ[volume.restrict AVenhance.unitCube]
        omittedFlux F.G' F.k (IsRetained F.m F.H F.J) F.yom v t := by
  classical
  have hz : ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      ∀ u : CompIn F.G'.comps, ∀ word : JetIndex2 (F.k + Dm - 1),
        (0 : TorusHk (F.k + Dm - 1) (hr u.1.root)).toFunction.jet word x = 0 :=
    ae_all_iff.mpr fun u => ae_all_iff.mpr fun word => by
      filter_upwards [torusHk_toFunction_jet_ae
          (0 : TorusHk (F.k + Dm - 1) (hr u.1.root)) word,
        (Lp.coeFn_zero (E := hr u.1.root) (p := 2)
          (μ := volume.restrict unitCube))] with x hx hz
      exact hx.trans hz
  filter_upwards [grade_row_supplied_flux_raw P F.extendedHigher v t ht, hz] with x hx hzx
  refine hx.trans ?_
  unfold omittedFlux
  rw [hB]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : IsRetained F.m F.H F.J u.1
  · simp only [Frame.extendedHigher, ite_eq_left hu]
  · simp only [ite_eq_right hu, Frame.extendedHigher]
    apply Finset.sum_eq_zero
    intro γ _
    apply Finset.sum_eq_zero
    intro d _
    have he : (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
        (0 : TorusHk (F.k + Dm - 1) (hr u.1.root)).toFunction.jet
          ⟨⟨d.1 - 1, by have := Finset.mem_Icc.1 d.2; omega⟩, word⟩ x) = 0 :=
      PiLp.ext fun word => hzx u _
    rw [he, map_zero]
end

/-! The grade-row estimate is the kernel-flux mass bound on the extended family.
No equation for the extended unknown is required: it is a zero extension of the retained
unknown, while the higher lifts are identified only almost everywhere in time. -/

section
open KernelEnergy AVRegularity.CoupledEnergy.Variational
open scoped Classical
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Kernel values for the zero-extended supplied lifts. -/
theorem grade_rows_kernel_values (F : Frame D hr Dm bw j₀)
    (P : TorusKernelOperator (h := fun v : CompIn F.G'.comps => hr v.1.root)
      (Γ := F.G'.fam.Γ) (G := fun _ u _ => hr u.1.root)
      F.tp F.tf (rhoEnh D F.cr F.m) (D.κ (F.m - 1)) F.k Dm)
    (hC : P.C = fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) => ContinuousLinearMap.id ℝ (hr u.1.root))
    (hy : ∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        (F.yom v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
          P.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val
            (valueIndex2 (F.k + 1)))): ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf), ∀ v u γ,
      (F.extendedHigher v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
        P.S v u γ t ((P.C v u γ).compLp
          ((F.extendedUnknown u t).val (valueIndex2 (F.k + 1)))) := by
  classical
  apply ae_all_iff.mpr
  intro v
  apply ae_all_iff.mpr
  intro u
  apply ae_all_iff.mpr
  intro γ
  by_cases hu : IsRetained F.m F.H F.J u.1
  · filter_upwards [hy v u γ hu] with t ht
    simpa only [Frame.extendedHigher, ite_eq_left hu, Frame.extendedUnknown,
      dite_eq_left hu, hC, AVRegularity.Providers.WeakGen.Comparison.id_compLp_eq] using ht
  · filter_upwards [] with t
    simp only [Frame.extendedHigher, ite_eq_right hu, Frame.extendedUnknown,
      dite_eq_right hu, Submodule.coe_zero, WithLp.ofLp_zero, Pi.zero_apply]
    rw [show (P.C v u γ).compLp (0 : Lp (hr u.1.root) 2
        (volume.restrict unitCube)) = 0 from ((P.C v u γ).compLpₗ 2 (volume.restrict unitCube)).map_zero, map_zero]

/-- The pointwise grade-row mass bound on the good time set. -/
theorem grade_rows_selected_flux_bound (F : Frame D hr Dm bw j₀)
    (P : TorusKernelOperator (h := fun v : CompIn F.G'.comps => hr v.1.root)
      (Γ := F.G'.fam.Γ) (G := fun _ u _ => hr u.1.root)
      F.tp F.tf (rhoEnh D F.cr F.m) (D.κ (F.m - 1)) F.k Dm)
    (hπ : P.π = fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
    (hθ : 0 ≤ P.θ) (hθle : P.θ ≤ 1)
    (hvalues : ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf), ∀ v u γ,
      (F.extendedHigher v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
        P.S v u γ t ((P.C v u γ).compLp
          ((F.extendedUnknown u t).val (valueIndex2 (F.k + 1))))) : ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        massNormSq (rhoEnh D F.cr F.m)
          (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) (fun v => (if F.select true v.1 then gradeRowSuppliedFlux P F.extendedHigher v t else 0).val) ≤
        (D.κ (F.m - 1)) ^ 2 * massGradNormSq (rhoEnh D F.cr F.m)
          (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
          (fun v => (F.Yw v t).val) := by
  classical
  have hmass (v : CompIn F.G'.comps) :
      0 < F.G'.mass F.law v / F.G'.marker F.law v ^ 2 := by simpa only [hπ] using P.hπ v
  filter_upwards [hvalues, ae_restrict_mem measurableSet_Icc] with t hvt ht
  have he : ∀ v, gradeRowSuppliedFlux P F.extendedHigher v t =
      P.flux t ht (fun u => F.extendedUnknown u t) v := fun v =>
    (grade_row_supplied_flux_eq_canonical P F.extendedHigher F.extendedUnknown t ht hvt v).trans
      (P.carrierFlux_of_mem F.extendedUnknown v t ht)
  have hselect := frontier_selected_mass_le F hmass
    (fun v => gradeRowSuppliedFlux P F.extendedHigher v t)
  have hflux := P.flux_mass_bound t ht (fun u => F.extendedUnknown u t)
  rw [hπ, frontier_extended_gradient_mass F t] at hflux
  have hs : (D.κ (F.m - 1) * P.θ) ^ 2 ≤ (D.κ (F.m - 1)) ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hθ hθle)
  have hgrad0 := massGradNormSq_nonneg
    (E := fun v : CompIn F.Gr.comps => hr v.1.root) (K := fun _ => F.k)
    (rhoEnh D F.cr F.m) (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2)
    (fun v => hmass ⟨v.1, (Finset.mem_filter.1 v.2).1⟩)
    (fun v => (F.Yw v t).val)
  simp_rw [he] at hselect ⊢
  exact hselect.trans (hflux.trans (mul_le_mul_of_nonneg_right hs hgrad0))

/-- Grade rows at one stage, including their time-L² representatives.
Empty or singleton families, zero data and edgeless seeds are covered.
Exceptional times of supplied higher lifts are retained in the literal realization. -/
theorem grade_rows_of_kernel_operator (F : Frame D hr Dm bw j₀)
    (P : TorusKernelOperator (h := fun v : CompIn F.G'.comps => hr v.1.root)
      (Γ := F.G'.fam.Γ) (G := fun _ u _ => hr u.1.root)
      F.tp F.tf (rhoEnh D F.cr F.m) (D.κ (F.m - 1)) F.k Dm)
    (hB : P.B = fun v u γ (d : ↥(Finset.Icc 2 Dm)) => F.G'.physCoeff v u γ d.1)
    (hC : P.C = fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) => ContinuousLinearMap.id ℝ (hr u.1.root))
    (hπ : P.π = fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
    (hθ : 0 ≤ P.θ) (hθle : P.θ ≤ 1)
    (hw : ∀ u, MemLp (F.Yw u) 2 (volume.restrict (Set.Icc F.tp F.tf)))
    (hy : ∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        (F.yom v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
          P.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val
            (valueIndex2 (F.k + 1)))) : OutsideRowCauchyStatement F true 1 := by
  classical
  have hvalues := grade_rows_kernel_values F P hC hy
  let OF : F.RowFlux := fun v t => if F.select true v.1 then
    gradeRowSuppliedFlux P F.extendedHigher v t else 0
  have hLp : ∀ v, MemLp (OF v) 2 (volume.restrict (Set.Icc F.tp F.tf)) := by
    intro v
    by_cases hv : F.select true v.1
    · simp only [OF, ite_eq_left hv]
      exact grade_row_supplied_flux_memLp P F.extendedHigher F.extendedUnknown
        (frontier_extended_unknown_memLp F hw) hvalues v
    · simp only [OF, ite_eq_right hv]
      exact AVRegularity.Providers.WeakGen.Comparison.torusHk_memLp_zero F.k _
  refine ⟨OF, ?_, hLp, ?_⟩
  · intro v t ht
    by_cases hv : F.select true v.1
    · simp only [OF, ite_eq_left hv]
      exact frontier_extended_flux_raw F P hB v t ht
    · simp only [OF, ite_eq_right hv]
      filter_upwards [torusHk_toFunction_jet_ae
          (0 : TorusHk F.k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) (valueIndex2 F.k),
        (Lp.coeFn_zero (E := PiLp 2 (fun _ : Fin 2 => hr v.1.root)) (p := 2)
          (μ := volume.restrict unitCube))] with x hx hz
      exact hx.trans hz
  · have hbound := grade_rows_selected_flux_bound F P hπ hθ hθle hvalues
    have hOi := CycleComparison.Error.integrable_massNormSq
      (rhoEnh D F.cr F.m) (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) OF hLp
    have hWi := CycleComparison.Error.integrable_massGradNormSq
      (rhoEnh D F.cr F.m) (fun v => F.Gr.mass F.law v / F.Gr.marker F.law v ^ 2) F.Yw hw
    have hi := integral_mono_ae hOi (hWi.const_mul ((D.κ (F.m - 1)) ^ 2)) hbound
    rw [integral_const_mul] at hi
    have hν : 0 < D.κ (F.m - 1) := P.diffusivity_pos
    change (D.κ (F.m - 1))⁻¹ * _ ≤ (1 * F.rowGain true) ^ 2 * F.sourceDissipation true
    simp only [Frame.rowGain, Frame.sourceDissipation, Bool.true_or, ite_true, one_mul, one_pow]
    exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hν.le)).trans_eq (by
      field_simp)
end

/-! The extended context certificate already constructed,
exposed before restricting its components. Adapted from that construction;
the three statements used (`successor_generated`, `successor_ledger`, `gen_carrier_calculus`),
their constants and floors are preserved. -/

section
open AVRegularity.Providers

/-- The full successor, including grade H+1 and length J+1, is context-certified and transverse.
The positive reserve at grade H+1 is the producer reserve, not the retained reserve. -/
theorem extended_successor_context_certified (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ mStar : ℕ,
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      G'.IsSlotTransverse ∧ G'.IsContextCertified kI :=
  by
  obtain ⟨Λ₁, hΛ₁, hgen⟩ := successor_generated α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₂, -, hled⟩ := successor_ledger α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₃, -, hcalc⟩ := gen_carrier_calculus α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λ₁ (max Λ₂ Λ₃), le_max_of_le_left hΛ₁, fun Λ hΛ => ?_⟩
  obtain ⟨c₁, hc₁, hgen⟩ := hgen Λ ((le_max_left _ _).trans hΛ)
  obtain ⟨c₂, hc₂, hled⟩ := hled Λ (((le_max_left _ _).trans (le_max_right _ _)).trans hΛ)
  have hcalc := hcalc Λ (((le_max_right _ _).trans (le_max_right _ _)).trans hΛ)
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro φ₀ hφ₀ hφs hφn hφi hφsupp bw hbw0 hbw1 Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc0 hc0max
    hcr0 hcr1 hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsch hNaux hKres
    hseedA hsX hsZ
  have hgen := hgen φ₀ hφ₀ hφs hφn hφi hφsupp bw hbw0 hbw1 Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc0
    (hc0max.trans (min_le_left _ _)) hcr0 hcr1 hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres
    npad sX sZ σ₀ a σ hsch hNaux hKres hseedA hsX hsZ
  obtain ⟨thr, hled⟩ := hled φ₀ hφ₀ hφs hφn hφi hφsupp bw hbw0 hbw1 Q T₀ hQ hT₀ Ce τe kS r₀ D₀
    hCe hτe hc0 (hc0max.trans (min_le_right _ _)) hcr0 hcr1 hσf hlamC H J N p nk Lc Lf Lpr Acl
    Naux Nout Kres npad sX sZ σ₀ a σ hsch hNaux hKres hseedA hsX hsZ
  obtain ⟨Υ₀, hcalc⟩ := hcalc bw hbw0 hbw1
  have hΥ100 : (100 : ℝ) ≤ max (max Υ₀ (4 * (8 * Real.pi ^ 2))) 100 := le_max_right _ _
  obtain ⟨κ, hκ, hcalc⟩ := hcalc 1 (max (max Υ₀ (4 * (8 * Real.pi ^ 2))) 100)
    ⟨le_rfl, le_max_left _ _⟩
  refine ⟨thr, 1, max (max Υ₀ (4 * (8 * Real.pi ^ 2))) 100, le_rfl, by linarith,
    fun kI hadm => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hHprod, -⟩ := id hadm
  obtain ⟨CIthr, Cwthr, hled⟩ := hled 1 _ le_rfl hΥ100 κ hκ kI hadm
  refine ⟨CIthr, Cwthr, fun CI Cw j₀ hLA hcs => ?_⟩
  obtain ⟨mStar, hled⟩ := hled CI Cw j₀ hcs
  refine ⟨max mStar (j₀ + 2), ?_⟩
  intro D hDα hDq hDΛ hDζ hΦ M hκb hterm Mnat hMnat law hlaw hr _ _ _ _ _ _ seedK freshK hfresh
    seed n tS tf hseed m hm hmn hnM G G' hcas hlev hinv hSucc
  have hgen' := (hgen thr 1 _ le_rfl (by linarith) kI hadm CIthr Cwthr CI Cw j₀ hLA hcs
    (max mStar (j₀ + 2)) D hDα hDq hDΛ hDζ hΦ M hκb hterm Mnat hMnat law hlaw seedK freshK hfresh
    seed n tS tf hseed m hm hmn hnM G G' hcas hlev hinv hSucc).2
  have hledG := hled D hDα hDq hDΛ hDζ hΦ M hκb hterm Mnat hMnat law hlaw seedK freshK hfresh
    seed n tS tf hseed m ⟨hLA, (le_max_left _ _).trans hm⟩ hmn hnM G G' hcas hlev hinv hSucc
  have hjm : j₀ + 2 ≤ m := (le_max_right _ _).trans hm
  have hlev' : G'.level = G.level - 1 := hSucc.2.1
  have hj0 : j₀ ≤ G'.level := by omega
  have h1 : 1 ≤ G'.level := by omega
  have hres : ∀ v : CompIn G'.comps, 0 ≤ compReserve kI v.1 := fun v =>
    CascadeInvariants.compReserve_nonneg_of_succ kI (H := H) hHprod
      (CascadeInvariants.grade_le_of_succ (CascadeInvariants.grade_le_of_cascade hseed.2.1 hcas) hSucc v)
  have hcert := GenStage.isContextCertified_of_gates G' kI κ
    (fun p hp Δ hΔ leaf hL e hs hsf f hf => hcalc j₀ hcs D hDα hDq hDΛ hDζ hΦ M hκb hterm
      G'.level p h1 hj0 hp Δ hΔ leaf hL e hs hsf f hf) hres hledG
  exact ⟨hgen', hcert⟩
end

/-! Full extended-family certificates under the unchanged production prefix. Constants are
joined before the late stage, birth law and root spaces; kernel inheritance starts with the
incoming invariant and the single fresh kernel, including cross-root transfer. -/

section
open AVRegularity.Construction.Preservation.Assembly FullLift

/-- The extended family certificates needed by the grade row bound.
Empty or singleton families and edgeless seeds are covered.
The producer reserve at grade H+1 is used, with no retained-stage assumption on those rows. -/
def ExtendedStageCertificatesStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ mStar : ℕ,
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ tA : ℝ, tS ≤ tA →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      let Gr := G'
      Gr.IsNatural Mnat ∧ Gr.IsShiftInvariant ∧ Gr.IsSlotTransverse ∧
        Gr.IsContextCertified kI ∧
        markedLedger (Gr.mass law) (Gr.marker law) Gr.fam ≤
          CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe ∧
        (∀ v u (γ : Gr.fam.Γ v u),
          (Gr.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
            v u γ).width = (Gr.fam.identity v u γ).record.width ∧
          ∀ ρ : ℝ, 0 < ρ → IsSpatialRegularizerTorus ρ 0
            (succSchedD D₀ N p (H + 1)) (tA + 3 * ocTau α q Λ m) tf kI.cker
            (Gr.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
              v u γ).width
            (Gr.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
              φ₀ hφ₀ v u γ))

private theorem extended_template_compact {φ₀ : Vec 2 → ℝ}
    (h : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall) :
    HasCompactSupport φ₀ := by
  let L := (Homogenization.HilbertVec.continuousLinearEquivVec 2).symm
  have heq : Analysis.Convolution.closedEuclideanUnitBall = L ⁻¹' Metric.closedBall 0 1 := by
    ext z
    simp only [Analysis.Convolution.closedEuclideanUnitBall, Set.mem_ofPred_eq, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right, Analysis.Convolution.euclideanNorm]
    rfl
  have hc : IsCompact Analysis.Convolution.closedEuclideanUnitBall := by
    rw [heq]
    exact L.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall 0 1)
  exact HasCompactSupport.of_support_subset_isCompact hc h

/-- The statements `successor_generated`, `successor_ledger` and `gen_carrier_calculus`, the full
marked-ledger recurrence and the inherited kernel regularizers produce all extended certificates
uniformly; no new coefficient price is estimated. -/
theorem extended_stage_certificates (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : ExtendedStageCertificatesStatement α s q ζ := by
  classical
  obtain ⟨Λc, hΛc, hc⟩ := extended_successor_context_certified α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hl⟩ := Providers.successor_ledger α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λk, hΛk, hk⟩ := extended_marked_ledger α s q ζ hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λc (max Λl Λk), by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cc, hcc, hc⟩ := hc Λ (by omega)
  obtain ⟨cl, hcl, hl⟩ := hl Λ (by omega)
  obtain ⟨ck, hck, hk⟩ := hk Λ (by omega)
  refine ⟨min cc (min cl ck), lt_min hcc (lt_min hcl hck), ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨tc, CHc, Υc, hCHc, hΥc, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  obtain ⟨tl, hl⟩ := hl φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans ((min_le_right _ _).trans (min_le_left _ _))) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  obtain ⟨tk, CHk, Υk, hCHk, hΥk, hk⟩ := hk φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans ((min_le_right _ _).trans (min_le_right _ _))) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc
  obtain ⟨cf, _hcf, mf, hmf, hf⟩ := uniform_fresh_kernel_regularizer φ₀
    (extended_template_compact hφsupport) hφsmooth nk.toPNat' α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ h128
  let tbase := certificateThresholdJoin tc (certificateThresholdJoin tl tk)
  let thr : InvConsts := { tbase with cker := fun j => max (tbase.cker j) (cf j) }
  let CH := max CHc CHk
  let Υ := max Υc (max Υk 100)
  have hCH : 1 ≤ CH := hCHc.trans (le_max_left _ _)
  have hΥ : 0 < Υ := hΥc.trans_le (le_max_left _ _)
  have hΥ100 : (100 : ℝ) ≤ Υ := (le_max_right _ _).trans (le_max_right _ _)
  let κ := Providers.ComplexContext.complexContextKappa bw 0
  have hκ : MajOK bw κ := Providers.ComplexContext.complexContextKappa_majOK le_rfl
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  have hb : IsInvariantAdmissible kS tbase kI H J N p nk Kres Lpr Lc Lf σ₀
      (ocDelta α q) q (ocC α q) := invariant_admissible_of_threshold_bounds (a := tbase) (b := thr)
    le_rfl le_rfl le_rfl (fun _ => le_rfl) (fun _ => le_max_left _ _) hkI
  have hcI := invariant_admissible_threshold_left hb
  have hlkI := invariant_admissible_threshold_right hb
  have hlI := invariant_admissible_threshold_left hlkI
  have hkI' := invariant_admissible_threshold_right hlkI
  obtain ⟨CIc, Cwc, hc⟩ := hc kI hcI
  obtain ⟨CIl, Cwl, hl⟩ := hl CH Υ hCH hΥ100 κ hκ kI hlI
  obtain ⟨CIk, Cwk, hk⟩ := hk kI hkI'
  refine ⟨max CIc (max CIl CIk), max Cwc (max Cwl Cwk), ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLc : IsLedgerAdmissible Ce CI Cw CIc Cwc :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1,
      (le_max_left _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLl : IsLedgerAdmissible Ce CI Cw CIl Cwl :=
    ⟨hledger.1, ((le_max_left _ _).trans (le_max_right _ _)).trans hledger.2.1,
      ((le_max_left _ _).trans (le_max_right _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLk : IsLedgerAdmissible Ce CI Cw CIk Cwk :=
    ⟨hledger.1, ((le_max_right _ _).trans (le_max_right _ _)).trans hledger.2.1,
      ((le_max_right _ _).trans (le_max_right _ _)).trans hledger.2.2.1, hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  have hsc := IsCarrierStart.mono hA hT (le_max_left _ _) (le_max_left _ _)
    (zero_le_one.trans hCHc) hΥc.le hstart
  have hsk := IsCarrierStart.mono hA hT (le_max_right _ _)
    ((le_max_left _ _).trans (le_max_right _ _)) (zero_le_one.trans hCHk) hΥk.le hstart
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hLc hsc
  obtain ⟨ml, hl⟩ := hl CI Cw j₀ hstart
  obtain ⟨mk, hk⟩ := hk CI Cw j₀ hLk hsk
  refine ⟨max mc (max ml (max mk (mf + 1))), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  have hmc : mc ≤ m := by omega
  have hml : ml ≤ m := by omega
  have hmk : mk ≤ m := by omega
  have hmf' : mf ≤ m - 1 := by omega
  have hm2 : 2 ≤ m := by omega
  have hcontext := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmc hn hnM G G' hcascade hlevel ⟨tA, htA, hG⟩ hactual
  have hwitness := hl D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m ⟨hLl, hml⟩ hn hnM G G' hcascade hlevel
    ⟨tA, htA, hG⟩ hactual
  have hmarked := hk D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmk hn hnM tA htA G G' hcascade hlevel hG hactual
    κ hwitness
  have htags := hG.2.1
  have hkerOld := hG.2.2.2.2.2.2.2.2.1
  have hwidth : ∀ v u (γ : G.fam.Γ v u),
      (G.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK v u γ).width =
        (G.fam.identity v u γ).record.width := fun v u γ => (hkerOld v u γ).2.1
  have hborn : (freshK (G.level - 1)).width =
      (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p).rb (G.level - 1) :=
    (hfresh _ (by omega) (by omega)).1
  have hwidthFull := actual_successor_kernel_width_matching hr D _ bw j₀ _ _ seedK freshK
    G G' htags hwidth hborn hactual
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hkap : 0 < D.kap G.level := by
    unfold OCData.kap
    rw [hterm]
    exact CycleReference.bandChain_pos (by omega) hζ hband (Nat.min_le_right _ _)
  have hcell : 0 ≤ D.cellScaleSq G.level := div_nonneg (sq_nonneg _) hkap.le
  have hshift : G'.IsShiftInvariant :=
    successor_shift_invariant_of_cellScaleSq_nonneg hζD hcell hG.1 hG.2.2.2.1 hactual
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hFreshSpec := hfresh (G.level - 1) (by omega) (by omega)
  have hκfresh : 0 < D.κ (G.level - 1) := CycleReference.bandChain_pos
    (by omega) hζD hbandD (by rw [hlevel, hterm]; omega)
  have hwidthFresh : 0 < (freshK (G.level - 1)).width := by
    rw [hFreshSpec.1]
    unfold freshWidth freshLength
    exact mul_pos (mul_pos (hkI.2.1.symm ▸ hcr) (Real.sqrt_pos.2
      (mul_pos hκfresh (Construction.Stream.ocTauPP_pos (by omega)))))
      (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos (by omega)) _)
  have hFreshReg (ρ : ℝ) : IsSpatialRegularizerTorus (G := ℝ) ρ 0
      (succSchedD D₀ N p (H + 1)) (tA + 3 * ocTau α q Λ m) tf kI.cker
      (freshK (G.level - 1)).width ((freshK (G.level - 1)).op φ₀ hφ₀) := by
    have hh := hf ℝ D hDα hDq hDΛ hDζ hseq hbandD (G.level - 1)
      (by omega) (by rw [hlevel, hterm]; omega) (freshK (G.level - 1))
      hFreshSpec.2.1 hwidthFresh hFreshSpec.2.2 ρ (tA + 3 * ocTau α q Λ m) tf 0
      (succSchedD D₀ N p (H + 1))
    exact spatial_regularizer_constants_mono hh hwidthFresh.le (fun j _ =>
      (le_max_right _ _).trans (invariant_admissible_kernel_bounds hkI j).2)
  refine ⟨hactual.2.2.2.1, hshift, hcontext.1, hcontext.2, hmarked, ?_⟩
  intro v u γ
  refine ⟨hwidthFull v u γ, ?_⟩
  intro ρ hρ
  apply extended_successor_kernel_regularizers _ _ G G' hactual seedK freshK φ₀ hφ₀
    ρ (tA + 3 * ocTau α q Λ m) tf 0 kI.cker ?_ (hFreshReg ρ) v u γ
  intro v₀ u₀ γ₀
  apply Buffer.spatialRegularizerTorus_time_restrict
    ((hkerOld v₀ u₀ γ₀).2.2.2.2 ρ hρ 0 (Nat.zero_le _))
  intro t ht
  exact ⟨le_trans (le_add_of_nonneg_right (mul_nonneg (by norm_num)
    (Construction.Stream.ocTau_pos (by omega : 1 ≤ Λ)).le)) ht.1, ht.2⟩
end

end AVRegularity.Construction.Preservation.Frontier
end
