-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleDamping.ReferenceSourceMode
import AVRegularity.CycleReference.CorrectorMeanGeometry
import AVRegularity.CycleReference.SingleModeFlux
public import AVRegularity.Proofs.GenSem.LiftGen.Drift
public import AVRegularity.Proofs.GenSem.CoeffArr.MonoSource
public import AVRegularity.Construction.Uniqueness.SuccessorFluxUnique
import AVRegularity.EntryWeak.NormalizedPulseTransverse
import AVRegularity.Proofs.Results.Construction.LiftPathDecomposition.Decomp

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity
namespace AVRegularity.Providers.GenSem

/-! **Parallel invariance of the finite-past cell inverse.** A finite-past cell inverse
whose source is invariant under the parallel translations `z ↦ z + s e_p` (and whose drift is
periodic and parallel invariant) is itself parallel invariant (`cellFieldInverse_par_invariant`).

The source is not assumed periodic: the cell problem reads it only on the cube, so it may be
replaced by its periodization `f(fract z)` (`periodize`), which is periodic and still parallel
invariant (`isCellFieldInverse_periodize`); the translation invariance of cell inverses then
applies. The pulse drift of an odd slot is periodic (`ocPulseCellDrift_periodic`) and parallel
invariant (`ocPulseCellDrift_par`). -/

/-! ### The pulse drift -/

theorem ocPulseCellDrift_periodic {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (m : ℕ) (ν : ℝ) {k : ℤ}
    (hk : Odd k) (t : ℝ) : AVenhance.IsZ2Periodic (ocPulseCellDrift α q Λ ζ m ν k t) := by
  intro n z
  unfold ocPulseCellDrift
  congr 2
  by_cases he : ocEpsilon q Λ m = 0
  · simp [he]
  · have hc := fun j => CycleDamping.scaled_cell_cosine_periodic (ocEpsilon q Λ m) he 0 j n z
    simp only [zero_add] at hc
    rcases CycleReference.odd_int_mod_four hk with h1 | h3
    · rw [CycleReference.ocShearVel_horizontal h1, CycleReference.ocShearVel_horizontal h1, hc 0]
    · rw [CycleReference.ocShearVel_vertical h3, CycleReference.ocShearVel_vertical h3, hc 1]

theorem ocPulseCellDrift_par {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} (m : ℕ) (ν : ℝ) {k : ℤ}
    (hk : Odd k) (t : ℝ) (z : Vec 2) (s : ℝ) :
    ocPulseCellDrift α q Λ ζ m ν k t (z + s • basisVec (parIdx k)) =
      ocPulseCellDrift α q Λ ζ m ν k t z := by
  unfold ocPulseCellDrift
  congr 2
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · have hp : parIdx k = 1 := by simp [parIdx, show ¬ k % 4 = 3 by omega]
    rw [hp, CycleReference.ocShearVel_horizontal h1, CycleReference.ocShearVel_horizontal h1]
    simp
  · have hp : parIdx k = 0 := by simp [parIdx, h3]
    rw [hp, CycleReference.ocShearVel_vertical h3, CycleReference.ocShearVel_vertical h3]
    simp

/-! ### Periodization of a source -/

/-- The `ℤ²`-periodization `f(fract z)` of a function on the cell. -/
def periodize {β : Type*} (f : Vec 2 → β) (z : Vec 2) : β := f fun i => Int.fract (z i)

theorem periodize_of_mem {β : Type*} (f : Vec 2 → β) {z : Vec 2}
    (hz : z ∈ AVenhance.unitCube) : periodize f z = f z := by
  unfold periodize
  congr 1
  funext i
  have := hz i (Set.mem_univ i)
  exact Int.fract_eq_self.mpr ⟨this.1.le, this.2⟩

theorem periodize_periodic {β : Type*} (f : Vec 2 → β) : AVenhance.IsZ2Periodic (periodize f) := by
  intro n z
  unfold periodize
  congr 1
  funext i
  simp [AVenhance.latticeShift, Int.fract_add_intCast]

theorem periodize_par {β : Type*} {f : Vec 2 → β} {p : Fin 2}
    (hf : ∀ z (s : ℝ), f (z + s • basisVec p) = f z) (z : Vec 2) (s : ℝ) :
    periodize f (z + s • basisVec p) = periodize f z := by
  unfold periodize
  have e : (fun i => Int.fract ((z + s • basisVec p) i)) =
      (fun i => Int.fract (z i)) + (Int.fract (z p + s) - Int.fract (z p)) • basisVec p := by
    funext i
    by_cases hi : i = p
    · subst hi
      simp
    · simp [hi]
  rw [e, hf]

/-- A cell inverse of `g` is a cell inverse of the periodization of `g`. -/
theorem isCellFieldInverse_periodize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {sZ : ℕ} {t₀ t₁ : ℝ} {g c : ℝ → Vec 2 → E}
    (hc : IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g c) :
    IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) (fun t => periodize (g t)) c := by
  refine ⟨hc.1, fun ℓ => ?_⟩
  obtain ⟨hs, hrest⟩ := hc.2 ℓ
  refine ⟨CycleEvolution.cellSolution_source_congr_sections _ _ _ _ _ _ _
    (Filter.Eventually.of_forall fun r =>
      ae_restrict_of_forall_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
        fun x hx => by simp only [periodize_of_mem _ hx])
    (Filter.Eventually.of_forall fun _ => Filter.EventuallyEq.rfl) hs, hrest⟩

/-- **Parallel invariance of the finite-past cell inverse.** -/
theorem cellFieldInverse_par_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {sZ : ℕ} {t₀ t₁ lo A Mv : ℝ} (ht : t₀ ≤ t₁) (hW : Uniqueness.WindowData G v t₀ t₁ lo A Mv)
    (p : Fin 2) (hv : ∀ t z (s : ℝ), v t (z + s • basisVec p) = v t z)
    (hvp : ∀ t ∈ Icc t₀ t₁, AVenhance.IsZ2Periodic (v t)) {g c : ℝ → Vec 2 → E}
    (hg : ∀ t ∈ Icc t₀ t₁, ∀ z (s : ℝ), g t (z + s • basisVec p) = g t z)
    (hc : IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g c) :
    ∀ t ∈ Icc t₀ t₁, ∀ z (s : ℝ), c t (z + s • basisVec p) = c t z := by
  intro t ht' z s
  exact Uniqueness.cellFieldInverse_translate_invariant ht hW (s • basisVec p)
    (fun t z => hv t z s) hvp (g := fun t => periodize (g t))
    (fun t htI z => periodize_par (hg t htI) z s) (fun t _ => periodize_periodic _)
    (isCellFieldInverse_periodize hc) t ht' z

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity AVRegularity.Providers.Transverse Set
namespace AVRegularity.Providers.GenSem

/-! **The finite-past cell inverse is the `Gen` transverse inverse, without time-uniform
mode bounds** (`cellField_eq_cellInv_modes`).

The route, mode by mode:
* the transverse modes `A_h(τ)` of a transverse cell inverse solve the scalar mode equation from
  zero (`phaseCoeff_cellFieldInverse_sub`, `phaseCoeff_cellFieldInverse_start`);
* so do the semantic amplitudes, written in cell time as Duhamel amplitudes with unit time
  scale (`semAmp_eq_modeW`, `modeW_sub`);
* the two agree by uniqueness for the scalar linear integral equation
  (`eq_of_linear_integral_eq`), and the zero modes vanish (zero cell mean);
* Fourier inversion of the `C¹` coefficient (Parseval, `summable_phaseCoeff_of_contDiff`) gives
  the semantics.

Without time-uniform mode bounds, the source needs only to be continuous and transverse at
each time of the window, and the drift only to have no transverse component. The coefficient is
assumed transverse. -/

/-- **The semantic amplitude in cell time** is the Duhamel amplitude with unit time scale, the
rescaled metric entry and the rescaled flux mode. -/
theorem semAmp_eq_modeW (D : OCData) (i : ℕ) (q : Fin 2) (ch : RealChain) (hcpos : 0 < D.cellScaleSq i)
    (Fh : ℝ → ℂ) (h : ℤ) (τ₀ τ : ℝ) :
    (2 * Real.pi * Complex.I * (h : ℂ) / (D.cellScaleSq i : ℂ)) *
        ∫ s in D.cellScaleSq i * τ₀..D.cellScaleSq i * τ,
          modeKernel D i q ch h (D.cellScaleSq i * τ) s * Fh s =
      modeW 1 (fun u => ch.famMetric D (D.cellScaleSq i * u) q q)
        (fun σ => Fh (D.cellScaleSq i * σ)) τ₀ h τ := by
  set c := D.cellScaleSq i with hcdef
  have hc0 : c ≠ 0 := hcpos.ne'
  have e1 : ∫ s in c * τ₀..c * τ, modeKernel D i q ch h (c * τ) s * Fh s =
      c • ∫ σ in τ₀..τ, modeKernel D i q ch h (c * τ) (c * σ) * Fh (c * σ) := by
    rw [intervalIntegral.integral_comp_mul_left
      (fun s => modeKernel D i q ch h (c * τ) s * Fh s) hc0, smul_smul, mul_inv_cancel₀ hc0,
      one_smul]
  have e2 : ∀ σ, modeKernel D i q ch h (c * τ) (c * σ) =
      modeK 1 (fun u => ch.famMetric D (c * u) q q) h τ σ := by
    intro σ
    have hi : ∫ u in σ..τ, ch.famMetric D (c * u) q q =
        c⁻¹ * ∫ u in c * σ..c * τ, ch.famMetric D u q q := by
      rw [intervalIntegral.integral_comp_mul_left (fun u => ch.famMetric D u q q) hc0,
        smul_eq_mul]
    have hx : -(4 * Real.pi ^ 2 * (h : ℝ) ^ 2 / c) * ∫ u in c * σ..c * τ, ch.famMetric D u q q =
        -(modeRate 1 h) * ∫ u in σ..τ, ch.famMetric D (c * u) q q := by
      rw [hi, modeRate, div_one, div_eq_mul_inv]
      ring
    unfold modeKernel modeK
    rw [← hcdef, hx]
  have hc0' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
  rw [e1, modeW, modeCoup, Complex.real_smul]
  simp_rw [e2]
  rw [Complex.ofReal_one, div_one, ← mul_assoc, div_mul_cancel₀ _ hc0']

/-- **The finite-past cell inverse is the `Gen` transverse inverse** (no mode bounds). -/
theorem cellField_eq_cellInv_modes (D : OCData) (hζ : IsFastProfile D.ζ) (i : ℕ) (p : ℤ)
    (ch : RealChain) (hcpos : 0 < D.cellScaleSq i) {τ₀ τ₁ : ℝ} {sZ : ℕ} (hsZ : 1 ≤ sZ)
    (S : ℝ → Vec 2 → ℝ) (fgen : GenSort.Sem .cell)
    (hfg : ∀ τ ∈ Icc τ₀ τ₁, fgen (D.cellScaleSq i * τ) ch = S τ)
    (hScont : ∀ τ ∈ Icc τ₀ τ₁, Continuous (S τ))
    (hStr : ∀ τ ∈ Icc τ₀ τ₁, IsTransverse (transverseIndex p) (S τ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hGm : ∀ τ ∈ Icc τ₀ τ₁, G τ = ch.famMetric D (D.cellScaleSq i * τ))
    (hvq : ∀ τ ∈ Icc τ₀ τ₁, ∀ x, v τ x (transverseIndex p) = 0)
    (C : ℝ → Vec 2 → ℝ) (hC : IsCellFieldInverse G v sZ τ₀ τ₁ (fun _ => 0) S C)
    (hCtr : ∀ τ ∈ Icc τ₀ τ₁, IsTransverse (transverseIndex p) (C τ))
    (F : Fin 2 → GenSort.Sem .cell) (hF : F (transverseIndex p) = transversePrimitiveSem p fgen) :
    ∀ τ ∈ Icc τ₀ τ₁, ∀ z, C τ z =
      transverseInverseSem D i p F (D.cellScaleSq i * τ₀) (fun _ _ _ => 0)
        (D.cellScaleSq i * τ) ch z := by
  set c := D.cellScaleSq i with hcdef
  set q := transverseIndex p with hq
  intro τ hτ z
  have h01 : τ₀ ≤ τ₁ := hτ.1.trans hτ.2
  have hτ₀ : τ₀ ∈ Icc τ₀ τ₁ := ⟨le_rfl, h01⟩
  have ha'c : Continuous fun u => ch.famMetric D (c * u) q q :=
    ((continuous_apply q).comp ((continuous_apply q).comp
      (continuous_famMetric D hζ ch))).comp (continuous_const.mul continuous_id)
  have hFh : ∀ h : ℤ, ∀ σ ∈ Icc τ₀ τ₁,
      phaseCoeff q (F q (c * σ) ch) h = primAmp q (S σ) h := by
    intro h σ hσ
    rw [hq, hF, phaseCoeff_transversePrimitive' p fgen (c * σ) ch
      (by rw [hfg σ hσ]; exact hScont σ hσ) h, hfg σ hσ]
  have hmode : ∀ h : ℤ, (2 * Real.pi * Complex.I * (h : ℂ) / (c : ℂ)) *
      ∫ s in c * τ₀..c * τ, modeKernel D i q ch h (c * τ) s * phaseCoeff q (F q s ch) h =
      phaseCoeff q (C τ) h := by
    intro h
    by_cases hh : h = 0
    · subst hh
      rw [phaseCoeff_cellFieldInverse_zero hC hτ (hCtr τ hτ)]
      simp
    rw [semAmp_eq_modeW D i q ch hcpos _ h τ₀ τ]
    have hsubA : ∀ t ∈ Icc τ₀ τ₁, _ := fun t ht =>
      phaseCoeff_cellFieldInverse_sub (q := q) hsZ hC hCtr hStr hScont hvq h le_rfl ht.1 ht.2
    have hkc : Continuous fun σ => -(4 * Real.pi ^ 2 * (h : ℝ) ^ 2) * ch.famMetric D (c * σ) q q :=
      continuous_const.mul ha'c
    have hφeq : EqOn (fun σ => ((-(4 * Real.pi ^ 2 * (h : ℝ) ^ 2) * G σ q q : ℝ) : ℂ) *
        phaseCoeff q (C σ) h + phaseCoeff q (S σ) h)
        (fun σ => ((-(4 * Real.pi ^ 2 * (h : ℝ) ^ 2) * ch.famMetric D (c * σ) q q : ℝ) : ℂ) *
          phaseCoeff q (C σ) h + phaseCoeff q (S σ) h) (Ioc τ₀ τ₁) := fun σ hσ => by
      simp only [hGm σ ⟨hσ.1.le, hσ.2⟩]
    have hAi := (hsubA τ₁ ⟨h01, le_rfl⟩).1.congr_fun hφeq measurableSet_Ioc
    have hA : ∀ t ∈ Icc τ₀ τ₁, phaseCoeff q (C t) h - phaseCoeff q (C τ₀) h =
        ∫ σ in Ioc τ₀ t, ((-(4 * Real.pi ^ 2 * (h : ℝ) ^ 2) * ch.famMetric D (c * σ) q q : ℝ) : ℂ) *
          phaseCoeff q (C σ) h + phaseCoeff q (S σ) h := by
      intro t ht
      rw [(hsubA t ht).2]
      exact setIntegral_congr_fun measurableSet_Ioc (hφeq.mono (Ioc_subset_Ioc_right ht.2))
    have hÂc : ContinuousOn (fun σ => phaseCoeff q (C σ) h) (Icc τ₀ τ₁) :=
      continuousOn_of_integral_eq hAi hA
    have hfi : IntegrableOn (fun σ => phaseCoeff q (S σ) h) (Ioc τ₀ τ₁) := by
      have hkA : IntegrableOn (fun σ =>
          ((-(4 * Real.pi ^ 2 * (h : ℝ) ^ 2) * ch.famMetric D (c * σ) q q : ℝ) : ℂ) *
            phaseCoeff q (C σ) h) (Ioc τ₀ τ₁) :=
        (((Complex.continuous_ofReal.comp hkc).continuousOn.mul hÂc).integrableOn_compact
          isCompact_Icc).mono_set Ioc_subset_Icc_self
      exact (hAi.sub hkA).congr_fun (fun σ _ => by simp) measurableSet_Ioc
    set F'' : ℝ → ℂ := indicator (Icc τ₀ τ₁) (fun σ => primAmp q (S σ) h) with hF''
    have hF''i : ∀ x y, IntervalIntegrable F'' volume x y := by
      have hI : Integrable F'' := by
        rw [hF'', integrable_indicator_iff measurableSet_Icc,
          integrableOn_Icc_iff_integrableOn_Ioc]
        have e : (fun σ => primAmp q (S σ) h) =
            fun σ => (2 * Real.pi * Complex.I * (h : ℂ))⁻¹ * phaseCoeff q (S σ) h :=
          funext fun σ => by simp [primAmp, hh]
        rw [e]
        exact hfi.const_mul _
      exact fun x y => hI.intervalIntegrable
    have hc0 : (2 * Real.pi * Complex.I * (h : ℂ)) ≠ 0 := by
      have : (h : ℂ) ≠ 0 := by exact_mod_cast hh
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) this
    have hcoup : ∀ σ ∈ Icc τ₀ τ₁, modeCoup 1 h * F'' σ = phaseCoeff q (S σ) h := fun σ hσ => by
      simp only [hF'', indicator_of_mem hσ, modeCoup, primAmp, hh, ite_false, Complex.ofReal_one,
        div_one]
      rw [mul_inv_cancel_left₀ hc0]
    have hBc : Continuous (modeW 1 (fun u => ch.famMetric D (c * u) q q) F'' τ₀ h) :=
      continuous_modeW ha'c hF''i 1 τ₀ h
    have hB : ∀ t ∈ Icc τ₀ τ₁, modeW 1 (fun u => ch.famMetric D (c * u) q q) F'' τ₀ h t -
        modeW 1 (fun u => ch.famMetric D (c * u) q q) F'' τ₀ h τ₀ =
        ∫ σ in Ioc τ₀ t, ((-(4 * Real.pi ^ 2 * (h : ℝ) ^ 2) * ch.famMetric D (c * σ) q q : ℝ) : ℂ) *
          modeW 1 (fun u => ch.famMetric D (c * u) q q) F'' τ₀ h σ + phaseCoeff q (S σ) h := by
      intro t ht
      rw [modeW_sub ha'c hF''i 1 τ₀ h τ₀ t, intervalIntegral.integral_of_le ht.1]
      refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
      have hσ' : σ ∈ Icc τ₀ τ₁ := ⟨hσ.1.le, hσ.2.trans ht.2⟩
      simp only [modeRate, div_one, hcoup σ hσ']
    have hBi : IntegrableOn (fun σ =>
        ((-(4 * Real.pi ^ 2 * (h : ℝ) ^ 2) * ch.famMetric D (c * σ) q q : ℝ) : ℂ) *
          modeW 1 (fun u => ch.famMetric D (c * u) q q) F'' τ₀ h σ + phaseCoeff q (S σ) h)
        (Ioc τ₀ τ₁) :=
      ((((Complex.continuous_ofReal.comp hkc).mul hBc).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioc_subset_Icc_self).add hfi
    have h0 : phaseCoeff q (C τ₀) h = modeW 1 (fun u => ch.famMetric D (c * u) q q) F'' τ₀ h τ₀ := by
      rw [phaseCoeff_cellFieldInverse_start hC (hCtr τ₀ hτ₀) h, modeW_start]
    have key := eq_of_linear_integral_eq hkc hAi hA hBi hB h0 τ hτ
    rw [key]
    exact modeW_congr h hτ.1 (fun _ _ => rfl) fun σ hσ => by
      have hσ' : σ ∈ Icc τ₀ τ₁ := ⟨hσ.1, hσ.2.trans hτ.2⟩
      rw [hFh h σ hσ', hF'', indicator_of_mem hσ']
  have hC1 : ContDiff ℝ 1 (C τ) := (hC.1 τ hτ).of_le (by exact_mod_cast hsZ)
  have hper : AVenhance.IsZ2Periodic (C τ) := periodic_of_cellFieldInverse hC hτ
  have hs := hasSum_transverse_of_summable hC1.continuous hper (hCtr τ hτ)
    (summable_phaseCoeff_of_contDiff q hC1 hper) z
  unfold transverseInverseSem
  have e : ∀ h : ℤ, (modeKernel D i q ch h (c * τ) (c * τ₀) *
        phaseCoeff q ((fun _ _ _ => (0 : ℝ)) (c * τ₀) ch) h +
      (2 * Real.pi * Complex.I * (h : ℂ) / (c : ℂ)) *
        ∫ s in c * τ₀..c * τ, modeKernel D i q ch h (c * τ) s * phaseCoeff q (F q s ch) h) *
      Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (z q : ℂ)) =
      phaseCoeff q (C τ) h * modeExp q h z := by
    intro h
    rw [hmode h, phaseCoeff_zero, mul_zero, zero_add]
    rfl
  rw [tsum_congr e, hs.tsum_eq, Complex.ofReal_re]

end AVRegularity.Providers.GenSem
end
end

section
section
/-! **The cell source of the lift coefficients has zero cell mean.** The mean of every
coefficient entry of the cell inverse vanishes (`IsCellFieldInverse`), hence the array `srcArr`
(`-(A - P₀A) + ∑ C_j ∘ P₀A`, with `P₀A` independent of `z`) has zero cell mean. For a transverse
function the zeroth transverse Fourier coefficient is the cell mean. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory AVRegularity.Providers.Transverse
  Set

namespace AVRegularity.Providers.GenSem

/-! ### Means of the arrays -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

omit [DecidableEq ι] in
theorem continuous_liftAArr_z (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} {τ : ℝ}
    (hreg : LiftRegular Q Cc w τ hh n (0 + Dm + 2)) (v : ι) (m : ℕ) (α : DerivativeWord2 m)
    (X : Vec 2) : Continuous fun z => liftAArr Q Cc w hh n τ v m α X z :=
  ((arrSmooth_liftAArr Q Cc w (r := 0) hreg v).continuous m α).comp
    (continuous_const.prodMk continuous_id)

omit [DecidableEq ι] in
theorem continuous_srcArr_z (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} {τ : ℝ}
    (hreg : ∀ u, LiftRegular Q Cc u τ hh n (n + Dm + 2)) (v : ι) (m : ℕ)
    (α : DerivativeWord2 m) (X : Vec 2) :
    Continuous fun z => srcArr Q Cc w hh n τ v m α X z := by
  have h0 : LiftRegular Q Cc w τ hh n (0 + Dm + 2) :=
    (hreg w).mono le_rfl le_rfl (by omega)
  have ha := continuous_liftAArr_z Q Cc w h0 v m α X
  unfold srcArr
  simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Finset.sum_apply]
  refine Continuous.add (Continuous.neg (ha.sub continuous_const)) ?_
  refine continuous_finsetSum _ fun j hj => continuous_finsetSum _ fun p hp =>
    continuous_finsetSum _ fun u _ => ?_
  have hj' := Finset.mem_Icc.mp hj
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  unfold compArr
  refine continuous_finsetSum _ fun m' _ => continuous_finsetSum _ fun α' _ =>
    Continuous.mul ?_ continuous_const
  exact (((hreg u).coeff p.1 (by omega) j (by omega) m' α' v).continuous.comp
    (continuous_const.prodMk continuous_id))

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **The lift relation at the slow offsets of a set.** `IsLiftLocal Q U sZ t₀ t₁ N H Cc`
asks the clauses of the lift relation only at the slow offsets of `U`, pointwise. It is what the
representation of the lift coefficients (`LiftGenSetup`) uses: the coefficients of `LiftGenSetup`
may be cut-off copies of the true lifts, which agree with them only near `U`.
* `IsLiftSequence.toLocal`, `IsLiftSequenceOn.toLocal`: the global and the localized relations give
  the local one on (subsets of) their sets.
* `liftCoeff_isCellFieldInverse_local`: the cell problem of a coefficient at `X ∈ U`.
* `IsLiftLocal.of_agree`: the local relation transfers to lift data and coefficients that agree with
  the given ones on an open set containing `U` (cut-off copies). -/

open AVRegularity.Providers.PathDecomp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The lift relation at the slow offsets of `U`. -/
structure IsLiftLocal {Dm : ℕ} (Q : LiftOperatorData ι (fun _ => ℝ) Dm) (U : Set (Vec 2))
    (sZ : ℕ) (t₀ t₁ : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) : Prop where
  init : ∀ a₀ : Vec 2 → ∀ _ : ι, ℝ, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X ∈ U, ∀ z,
    liftApply 0 (Cc 0 0) (fun _ => a₀) t X z = a₀ X
  zero0 : ∀ hh, 1 ≤ hh → hh ≤ H → ∀ m α t, ∀ X ∈ U, ∀ z v u, Cc hh 0 m α t X z v u = 0
  zeroN : ∀ hh, hh ≤ H → ∀ n, N < n → ∀ m α t, ∀ X ∈ U, ∀ z v u, Cc hh n m α t X z v u = 0
  zeroM : ∀ hh, hh ≤ H → ∀ n m, n < m → ∀ α t, ∀ X ∈ U, ∀ z v u, Cc hh n m α t X z v u = 0
  perm : ∀ hh, hh ≤ H → ∀ n m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) t, ∀ X ∈ U,
    Cc hh n m (α ∘ σ) t X = Cc hh n m α t X
  inv : ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ a₀ : Vec 2 → ∀ _ : ι, ℝ,
    ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ X ∈ U,
      IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ t₀ t₁ (fun _ => 0)
        (fun t z => liftCellSource Q Cc (fun _ => a₀) hh n t X z)
        (fun t z => liftApply n (Cc hh n) (fun _ => a₀) t X z)

omit [DecidableEq ι] in
theorem IsLiftSequenceOn.toLocal {Dm : ℕ} {Q : LiftOperatorData ι (fun _ => ℝ) Dm}
    {Ω U : Set (Vec 2)} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N H Cc)
    (hU : U ⊆ Ω) : IsLiftLocal Q U sZ t₀ t₁ N H Cc where
  init a₀ ha₀ t ht X _ z := hC.1 a₀ ha₀ t ht X z
  zero0 hh h1 hH m α t X _ z v u := hC.2.1 hh h1 hH m α t X z v u
  zeroN hh hH n hn m α t X _ z v u := hC.2.2.1 hh hH n hn m α t X z v u
  zeroM hh hH n m hnm α t X _ z v u := hC.2.2.2.1 hh hH n m hnm α t X z v u
  perm hh hH n m α σ t X _ := congrFun (congrFun (hC.2.2.2.2.1 hh hH n m α σ) t) X
  inv hh hH n hn1 hnN a₀ ha₀ X hX := hC.2.2.2.2.2.2 hh hH n hn1 hnN a₀ ha₀ X (hU hX)

/-- **The cell problem of a lift coefficient, locally** at a slow offset `X ∈ U`. -/
theorem liftCoeff_isCellFieldInverse_local {Dm : ℕ} (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    {U : Set (Vec 2)} {sZ : ℕ} (hsZ : 1 ≤ sZ) {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} (hC : IsLiftLocal Q U sZ t₀ t₁ N H Cc) {hh n : ℕ}
    (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) {X : Vec 2} (hX : X ∈ U) {m : ℕ} (hmn : m ≤ n)
    (I : DerivativeWord2 m) (v u : ι) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ t₀ t₁ (fun _ => 0)
      (fun t z => ((m.factorial : ℝ))⁻¹ *
        liftCellSource Q Cc (fun _ => monoField u X I) hh n t X z v)
      (fun t z => Cc hh n m I t X z v u 1) := by
  have h7 := hC.inv hh hhH n hn1 hnN (monoField u X I) (contDiff_monoField u X I) X hX
  have hL := isCellFieldInverse_clm hsZ
    (((m.factorial : ℝ))⁻¹ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) v) h7
  have hfact : ((m.factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  convert hL using 1
  · funext x; simp
  · funext t z; simp [smul_eq_mul]
  · funext t z
    simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [liftApply_monoField_at hmn u X I t (fun σ α => hC.perm hh hhH n m α σ t X hX) z v]
    field_simp

omit [DecidableEq ι] in
/-- **Transfer of the local lift relation** to lift data and coefficients agreeing with the given
ones on an open set `O ⊇ U`. -/
theorem IsLiftLocal.of_agree {Dm : ℕ} {Q Q' : LiftOperatorData ι (fun _ => ℝ) Dm}
    {O U : Set (Vec 2)} (hO : IsOpen O) (hUO : U ⊆ O) (hQ : Uniqueness.DataAgreeOn O Q Q')
    {sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ} {Cc Cc' : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}
    (hCc : ∀ hh n m (α : DerivativeWord2 m) t, ∀ X ∈ O, Cc hh n m α t X = Cc' hh n m α t X)
    (hC : IsLiftLocal Q O sZ t₀ t₁ N H Cc) : IsLiftLocal Q' U sZ t₀ t₁ N H Cc' where
  init a₀ ha₀ t ht X hX z := by
    have e := Uniqueness.liftApply_locEq (n := 0) (B := Cc 0 0) (B' := Cc' 0 0)
      (a := fun _ => a₀) (a' := fun _ => a₀) (t := t) hO
      (fun m _ α X' hX' => hCc 0 0 m α t X' hX') (fun _ _ => rfl) X (hUO hX) z
    rw [← e]
    exact hC.init a₀ ha₀ t ht X (hUO hX) z
  zero0 hh h1 hH m α t X hX z v u := by
    rw [← hCc hh 0 m α t X (hUO hX)]
    exact hC.zero0 hh h1 hH m α t X (hUO hX) z v u
  zeroN hh hH n hn m α t X hX z v u := by
    rw [← hCc hh n m α t X (hUO hX)]
    exact hC.zeroN hh hH n hn m α t X (hUO hX) z v u
  zeroM hh hH n m hnm α t X hX z v u := by
    rw [← hCc hh n m α t X (hUO hX)]
    exact hC.zeroM hh hH n m hnm α t X (hUO hX) z v u
  perm hh hH n m α σ t X hX := by
    rw [← hCc hh n m (α ∘ σ) t X (hUO hX), ← hCc hh n m α t X (hUO hX)]
    exact hC.perm hh hH n m α σ t X (hUO hX)
  inv hh hH n hn1 hnN a₀ ha₀ X hX := by
    have hX' := hUO hX
    have eG : (fun t => Matrix.of (Q'.G t X)) = fun t => Matrix.of (Q.G t X) :=
      funext fun t => by rw [hQ.metric t X hX']
    have eS : (fun t z => liftCellSource Q' Cc' (fun _ => a₀) hh n t X z) =
        fun t z => liftCellSource Q Cc (fun _ => a₀) hh n t X z :=
      funext fun t => funext fun z => (Uniqueness.liftCellSource_agree hQ (t₀ := t) (t₁ := t) hO
        hh n hn1 (fun hh' n' _ τ _ m α X'' hX'' => hCc hh' n' m α τ X'' hX'')
        (Set.left_mem_Icc.mpr le_rfl) (fun _ => a₀) X hX' z).symm
    have eA : (fun t z => liftApply n (Cc' hh n) (fun _ => a₀) t X z) =
        fun t z => liftApply n (Cc hh n) (fun _ => a₀) t X z :=
      funext fun t => funext fun z => (Uniqueness.liftApply_locEq (t := t) hO
        (fun m _ α X'' hX'' => hCc hh n m α t X'' hX'') (fun _ _ => rfl) X hX' z).symm
    rw [eG, ← hQ.drift, eS, eA]
    exact hC.inv hh hH n hn1 hnN a₀ ha₀ X hX'

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open Set Filter Topology Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Cut-off lift coefficients.** The lifts of `SuccSource.IsLiftFamily` are regular only
on the admissible offsets `Ω`. The representation (`LiftGenSetup`) asks the lift coefficients to be
jointly regular everywhere, so it is fed the cut-off `χ(X) Cc(X)` (`cutoffCoeff`), with a smooth
`χ` equal to `1` near the offsets used and supported in `Ω`.
* `contDiff_cutoff`: a function `C^R` on `Ω × ℝ²` times such a `χ` is `C^R` everywhere.
* `exists_ball_cutoff`: around a point of an open `Ω` there is a smooth `χ` with `χ = 1` on a ball
  and `tsupport χ ⊆ Ω`.
* `cutoffCoeff_eq`: the cut-off coefficients agree with the original ones where `χ = 1`, so the
  cut-off of a localized lift sequence satisfies the local lift relation on that ball. -/

/-- A function `C^R` on `Ω × ℝ²`, multiplied by a smooth function of `X` supported in `Ω`, is `C^R`
everywhere. -/
theorem contDiff_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set (Vec 2)}
    (hΩ : IsOpen Ω) {χ : Vec 2 → ℝ} {R : WithTop ℕ∞} (hχ : ContDiff ℝ R χ) (hsupp : tsupport χ ⊆ Ω)
    {F : Vec 2 × Vec 2 → E} (hF : ContDiffOn ℝ R F (Ω ×ˢ univ)) :
    ContDiff ℝ R (fun p => χ p.1 • F p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 ∈ Ω
  · have hmem : Ω ×ˢ univ ∈ 𝓝 p := (hΩ.prod isOpen_univ).mem_nhds ⟨hp, trivial⟩
    exact (hχ.comp contDiff_fst).contDiffAt.smul (hF.contDiffAt hmem)
  · have hnot : p.1 ∉ tsupport χ := fun h => hp (hsupp h)
    have hev : (fun q : Vec 2 × Vec 2 => χ q.1 • F q) =ᶠ[𝓝 p] fun _ => 0 := by
      have : ∀ᶠ q in 𝓝 p, q.1 ∉ tsupport χ :=
        (continuous_fst.tendsto p).eventually ((isClosed_tsupport χ).isOpen_compl.mem_nhds hnot)
      filter_upwards [this] with q hq
      rw [image_eq_zero_of_notMem_tsupport hq, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **A smooth cut-off around a point of an open set**: `χ = 1` on a ball, `tsupport χ ⊆ Ω`. -/
theorem exists_ball_cutoff {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) {X₀ : Vec 2} (hX₀ : X₀ ∈ Ω) :
    ∃ r > 0, ∃ χ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ tsupport χ ⊆ Ω ∧
      ∀ X ∈ Metric.ball X₀ r, χ X = 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ X₀ hX₀
  let b : ContDiffBump X₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨ε / 4, by positivity, b, b.contDiff, ?_, fun X hX => b.one_of_mem_closedBall
    (Metric.ball_subset_closedBall hX)⟩
  rw [b.tsupport_eq]
  exact (Metric.closedBall_subset_ball (show ε / 2 < ε by linarith)).trans hball

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The cut-off `χ(X) Cc(X)` of lift coefficients by a function of the slow offset. -/
def cutoffCoeff (χ : Vec 2 → ℝ) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) :
    ℕ → ℕ → LiftCoeff ι (fun _ => ℝ) :=
  fun hh n m α t X z v u => χ X • Cc hh n m α t X z v u

omit [Fintype ι] [DecidableEq ι] in
theorem cutoffCoeff_eq {χ : Vec 2 → ℝ} {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} {O : Set (Vec 2)}
    (hχ : ∀ X ∈ O, χ X = 1) (hh n m : ℕ) (α : DerivativeWord2 m) (t : ℝ) {X : Vec 2}
    (hX : X ∈ O) : cutoffCoeff χ Cc hh n m α t X = Cc hh n m α t X := by
  funext z v u
  simp [cutoffCoeff, hχ X hX]

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **The cell source of the lift coefficients is time-uniformly represented.**
`CoeffRepBelow V Cc hh n` records that the coefficients of every earlier pair `(hh', k)`
(`hh' < hh`, or `hh' = hh` and `k < n`) are time-uniformly represented. Then `A_n^{(hh)}` and
the cell source (`GenSem.srcArr`, and the cell source of a monomial field at its centre, normalised by
`(m!)⁻¹`) are time-uniformly represented. -/

namespace UEnv

variable {V : UEnv (RealChain × ℝ)} {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

/-- The coefficients of all earlier pairs `(hh', k)` are time-uniformly represented. -/
def CoeffRepBelow (V : UEnv (RealChain × ℝ)) (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) : Prop :=
  ∀ hh' k, (hh' < hh ∨ (hh' = hh ∧ k < n)) → ∀ m α (v u : ι),
    V.IsURep (fun l X z => Cc l.1 hh' k m α l.2 X z v u 1)

omit [Fintype ι] [DecidableEq ι] in
theorem CoeffRepBelow.mono {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} {hh n hh₁ n₁ : ℕ}
    (h : V.CoeffRepBelow Cc hh n) (h1 : hh₁ ≤ hh) (h2 : n₁ ≤ n) : V.CoeffRepBelow Cc hh₁ n₁ :=
  fun hh' k hk => h hh' k (by omega)

omit [Fintype ι] [DecidableEq ι] in
/-- The aggregate of the coefficients of the source edges (the only way the source flux sees
them) is uniformly represented. -/
def EdgeURep (V : UEnv (RealChain × ℝ)) {Dm : ℕ}
    (Q : RealChain → LiftOperatorData ι (fun _ => ℝ) Dm) : Prop :=
  ∀ (v u : ι) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (k : Fin 2),
    V.IsURep (fun l X z => (((Q l.1).edge v u d).map fun γ => γ.map 1 * γ.coeff α l.2 X z k).sum)

omit [Fintype ι] [DecidableEq ι] in
theorem urepArr_entryArr {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} {hh' k : ℕ}
    (h : ∀ m α (v u : ι), V.IsURep (fun l X z => Cc l.1 hh' k m α l.2 X z v u 1)) (w v : ι) :
    V.URepArr (fun l => GenSem.entryArr (Cc l.1 hh' k) k w l.2 v) := by
  intro m α
  by_cases hm : m ≤ k
  · exact (h m α v w).congr fun τ _ X _ z => by simp [GenSem.entryArr, hm]
  · exact (isURep_const V 0).congr fun τ _ X _ z => by simp [GenSem.entryArr, hm]

omit [Fintype ι] [DecidableEq ι] in
theorem urepArr_cArr {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} {hh' k : ℕ}
    (h : ∀ m α (v u : ι), V.IsURep (fun l X z => Cc l.1 hh' k m α l.2 X z v u 1)) (v u : ι) :
    V.URepArr (fun l => GenSem.cArr (Cc l.1 hh' k) l.2 v u) := fun m α => h m α v u

omit [DecidableEq ι] in
/-- **`A_n^{(hh)}` of the test field is uniformly represented.** -/
theorem URepArr.liftAArr (hV : V.Ok) (Q : RealChain → LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} (hn : 1 ≤ n) {η : ℝ}
    (hη : ∀ l ∈ V.W, (Q l.1).η = η)
    (hGr : ∀ i j, V.IsURep (fun l X _ => (Q l.1).G l.2 X i j))
    (hvr : ∀ k, V.IsURep (fun l _ z => (Q l.1).v l.2 z k))
    (hed : V.EdgeURep Q)
    (hC : V.CoeffRepBelow Cc hh n)
    (hreg : ∀ l ∈ V.W, LiftRegular (Q l.1) (Cc l.1) w l.2 hh n (n + Dm + 2)) (v : ι) :
    V.URepArr (fun l => GenSem.liftAArr (Q l.1) (Cc l.1) w hh n l.2 v) := by
  have hsm : ∀ l ∈ V.W, ∀ hh' k, hh' ≤ hh → k ≤ n → ∀ u,
      ArrSmooth (n + Dm + 2) (GenSem.entryArr (Cc l.1 hh' k) k w l.2 u) := fun l hl hh' k h1 h2 u =>
    arrSmooth_entryArr _ _ _ _ _ ((hreg l hl).coeff hh' h1 k h2 · · u)
  have hG : ∀ l ∈ V.W, ∀ i j,
      ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => (Q l.1).G l.2 p.1 i j) :=
    fun l hl i j => ((hreg l hl).metric i j).of_le (by exact_mod_cast (by omega : 1 ≤ n + Dm + 2))
  unfold GenSem.liftAArr
  refine URepArr.sub (URepArr.add ?_ ?_) ?_
  · exact (URepArr.cellB1Arr hV (G := fun A => (Q A).G) (vel := fun A => (Q A).v) (η := η)
      hGr hvr
      (urepArr_entryArr (hC hh (n - 1) (Or.inr ⟨rfl, by omega⟩)) w v)
      (fun l hl => (hsm l hl hh (n - 1) le_rfl (by omega) v).mono (by omega)) hG).congr
      fun l hl => by simp only [hη l hl]
  · by_cases h2 : 2 ≤ n
    · simp only [h2, ite_true]
      exact (URepArr.cellB2Arr hV (G := fun A => (Q A).G) (η := η) hGr
        (urepArr_entryArr (hC hh (n - 2) (Or.inr ⟨rfl, by omega⟩)) w v)
        (fun l hl => (hsm l hl hh (n - 2) le_rfl (by omega) v).mono (by omega)) hG).congr
        fun l hl => by simp only [hη l hl]
    · simp only [h2, ite_false]
      exact urepArr_zero V
  · by_cases h0 : hh = 0
    · simp only [h0, ite_true]
      exact urepArr_zero V
    · simp only [h0, ite_false]
      refine URepArr.sum _ fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      have hjn : j ≤ n := by omega
      exact (URepG.sourceG hV (fun A => (Q A).edge) (Real.sqrt η)
        (A := fun u l => GenSem.entryArr (Cc l.1 (hh - 1) (n - j)) (n - j) w l.2 u)
        (fun u => urepArr_entryArr (hC (hh - 1) (n - j) (Or.inl (by omega))) w u)
        (fun l hl u => (hsm l hl (hh - 1) (n - j) (by omega) (by omega) u).mono (by omega))
        hed (fun l hl v u d γ hγ α k => ((hreg l hl).edge v u d γ hγ α k).of_le
          (by exact_mod_cast (by omega : 1 ≤ n + Dm + 2))) v j).congr
        fun l hl => by simp only [hη l hl]

omit [DecidableEq ι] in
/-- **The cell source `srcArr` is uniformly represented.** -/
theorem URepArr.srcArr (hV : V.Ok) (Q : RealChain → LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} (hn : 1 ≤ n) {η : ℝ}
    (hη : ∀ l ∈ V.W, (Q l.1).η = η)
    (hGr : ∀ i j, V.IsURep (fun l X _ => (Q l.1).G l.2 X i j))
    (hvr : ∀ k, V.IsURep (fun l _ z => (Q l.1).v l.2 z k))
    (hed : V.EdgeURep Q)
    (hC : V.CoeffRepBelow Cc hh n)
    (hreg : ∀ l ∈ V.W, ∀ u, LiftRegular (Q l.1) (Cc l.1) u l.2 hh n (n + Dm + 2)) (v : ι) :
    V.URepArr (fun l => GenSem.srcArr (Q l.1) (Cc l.1) w hh n l.2 v) := by
  have hA := URepArr.liftAArr hV Q Cc w hn hη hGr hvr hed hC (fun l hl => hreg l hl w) v
  unfold GenSem.srcArr
  refine URepArr.add (URepArr.neg (URepArr.sub hA hA.meanArr)) ?_
  refine URepArr.sum _ fun j hj => URepArr.sum _ fun p hp => URepArr.sum _ fun u _ => ?_
  have hj' := Finset.mem_Icc.mp hj
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hB : V.URepArr (fun l => GenSem.meanArr (GenSem.liftAArr (Q l.1) (Cc l.1) w p.2 (n - j) l.2 u)) :=
    (URepArr.liftAArr hV Q Cc w (by omega) hη hGr hvr hed (hC.mono (by omega) (by omega))
      (fun l hl => (hreg l hl w).mono (by omega) (by omega) (by omega)) u).meanArr
  refine URepArr.compArr hV.hζ hV.hρ hV.hU j 0
    (urepArr_cArr (hC p.1 j (by omega)) v u) hB (fun l _ m α X z z' => rfl) ?_
  intro l hl
  exact arrSlowSmooth_meanArr (arrSmooth_liftAArr (Q l.1) (Cc l.1) w (r := j)
    ((hreg l hl w).mono (by omega) (by omega) (by omega)) u)

/-- **The normalised cell source of a monomial field at its centre is uniformly represented.** -/
theorem isURep_cellSource (hV : V.Ok) (Q : RealChain → LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (u : ι) {hh n : ℕ} (hn : 1 ≤ n) {η : ℝ}
    (hη : ∀ l ∈ V.W, (Q l.1).η = η)
    (hGr : ∀ i j, V.IsURep (fun l X _ => (Q l.1).G l.2 X i j))
    (hvr : ∀ k, V.IsURep (fun l _ z => (Q l.1).v l.2 z k))
    (hed : V.EdgeURep Q)
    (hC : V.CoeffRepBelow Cc hh n)
    (hreg : ∀ l ∈ V.W, ∀ w, LiftRegular (Q l.1) (Cc l.1) w l.2 hh n (n + Dm + 2)) {m : ℕ}
    (hm : m ≤ n + 1) (I : DerivativeWord2 m) (v : ι) :
    V.IsURep (fun l X z => ((m.factorial : ℝ))⁻¹ *
      liftCellSource (Q l.1) (Cc l.1) (fun _ => monoField u X I) hh n l.2 X z v) := by
  have h : V.IsURep (fun l X z => ∑ σ : Equiv.Perm (Fin m),
      GenSem.srcArr (Q l.1) (Cc l.1) u hh n l.2 v m (I ∘ σ) X z) :=
    IsURep.sum _ fun σ _ => URepArr.srcArr hV Q Cc u hn hη hGr hvr hed hC hreg v m (I ∘ σ)
  exact (h.smul ((m.factorial : ℝ))⁻¹).congr fun l hl X _ z => by
    rw [liftCellSource_monoField (Q l.1) (Cc l.1) u (hreg l hl u) X z v I hm]

end UEnv

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open Set Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **The `reg` premise of `LiftGenSetup` from its ingredients.** `LiftRegular` of the family lift
data and the (cut-off) lift coefficients splits into:
* the metric, smooth in the slow offset (`familyLiftData_metric_contDiff`, from the chain geometry);
* the pulse drift, smooth in the fast variable (`familyLiftData_drift_contDiff`);
* the joint regularity of the coefficients and of the source edges, which are hypotheses of
  `liftRegular_of` (the coefficients from box regularity and the cut-off, the edges from the
  source construction). -/

section
variable {ι : Type} {Dm : ℕ}

theorem familyLiftData_metric_contDiff (D : OCData) (m : ℕ) (k : ℤ) {A : RealChain}
    (hA : A.WellSlotted) (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (t : ℝ)
    (i j : Fin 2) (R : ℕ) :
    ContDiff ℝ (R : WithTop ℕ∞)
      (fun p : Vec 2 × Vec 2 => (familyLiftData D m k A ρ edge).G t p.1 i j) :=
  ((EntryWeakProofs.familyLiftData_metric_entry_smooth D m k A hA ρ edge t i j).comp
    contDiff_fst).of_le (by exact_mod_cast le_top)

theorem familyLiftData_drift_contDiff (D : OCData) (m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (t : ℝ) (c : Fin 2) (R : ℕ) :
    ContDiff ℝ (R : WithTop ℕ∞)
      (fun p : Vec 2 × Vec 2 => (familyLiftData D m k A ρ edge).v t p.2 c) := by
  have hs := EntryWeakProofs.ocShearVel_spatial_smooth D.α D.q D.Λ m k
  have hv : ContDiff ℝ (⊤ : ℕ∞) (ocPulseCellDrift D.α D.q D.Λ D.ζ m (D.kap m) k t) := by
    unfold ocPulseCellDrift
    exact ((hs.comp (contDiff_id.const_smul (ocEpsilon D.q D.Λ m))).const_smul
      (ocPulse D.α D.q D.Λ D.ζ m k (ocEll D.q D.Λ m (D.kap m) ^ 2 * t))).const_smul
      (ocEll D.q D.Λ m (D.kap m) ^ 2 / ocEpsilon D.q D.Λ m)
  exact (((contDiff_pi.mp hv) c).comp contDiff_snd).of_le (by exact_mod_cast le_top)

/-- **`LiftRegular` from its ingredients.** -/
theorem liftRegular_of (D : OCData) (m : ℕ) (k : ℤ) {A : RealChain} (hA : A.WellSlotted)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}
    (w : ι) (t : ℝ) (hh n R : ℕ)
    (hcoeff : ∀ hh' ≤ hh, ∀ k' ≤ n, ∀ (m' : ℕ) (α : DerivativeWord2 m') (v : ι),
      ContDiff ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => Cc hh' k' m' α t p.1 p.2 v w 1))
    (hedge : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ),
      γ ∈ (familyLiftData D m k A ρ edge).edge v u d → ∀ α c,
        ContDiff ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => γ.coeff α t p.1 p.2 c)) :
    LiftRegular (familyLiftData D m k A ρ edge) Cc w t hh n R where
  coeff := hcoeff
  metric := fun i j => familyLiftData_metric_contDiff D m k hA ρ edge t i j R
  drift := fun c => familyLiftData_drift_contDiff D m k A ρ edge t c R
  edge := hedge

/-- The scalar entries of the cut-off coefficients are jointly `C^R` once the true coefficients are
`C^R` on `Ω × ℝ²` and the cut-off is supported in `Ω`. -/
theorem contDiff_cutoffCoeff {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) {χ : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hsupp : tsupport χ ⊆ Ω) {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}
    {hh n m : ℕ} {α : DerivativeWord2 m} {t : ℝ} {v w : ι} {R : ℕ}
    (hC : ContDiffOn ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => Cc hh n m α t p.1 p.2 v w 1)
      (Ω ×ˢ univ)) :
    ContDiff ℝ (R : WithTop ℕ∞)
      (fun p : Vec 2 × Vec 2 => cutoffCoeff χ Cc hh n m α t p.1 p.2 v w 1) := by
  have := contDiff_cutoff hΩ (hχ.of_le (by exact_mod_cast le_top)) hsupp hC
  simpa [cutoffCoeff] using this
end

/-! **The lift premises of `LiftGenSetup` from a localized lift sequence.** For a lift
sequence on an open set `Ω ∋ 0` (`IsLiftSequenceOn`, box regularity `(sX, sZ)`) there are a ball
`B ∋ 0` and cut-off coefficients that
* agree with the lift sequence on `B`;
* satisfy the local lift relation on `B` (the `loc` premise);
* are jointly `C^R` in `(X, z)` everywhere, for `R ≤ min sX sZ` (the coefficient part of the `reg`
  premise; box-to-joint, `IsBoxSmoothOn.contDiffOn_uncurry`, and the cut-off).
With the floors `N + Dm + 2 ≤ sX, sZ` this is the order `n + Dm + 2` asked by `reg` for all
`n ≤ N`. -/

section
variable {ι : Type} [Fintype ι]

/-- The scalar entries of a box-regular coefficient are jointly `C^R` on `Ω × ℝ²`. -/
theorem contDiffOn_coeff_of_box {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) {sX sZ : ℕ}
    {f : Vec 2 → Vec 2 → (ℝ →L[ℝ] ℝ)} (hf : IsBoxSmoothOn Ω sX sZ f) {R : ℕ} (hRX : R ≤ sX)
    (hRZ : R ≤ sZ) :
    ContDiffOn ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => f p.1 p.2 1) (Ω ×ˢ univ) :=
  (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.comp_contDiffOn
    (IsBoxSmoothOn.contDiffOn_uncurry hΩ hf hRX hRZ)
end

/-! **Cut-off source edges for `LiftGenSetup`.** The source edges of a successor lift are fluxes of
the previous stage, cut by the admissibility indicator: they are regular only on the admissible
offsets `Ω`. The setup is therefore fed the cut-off edges `χ(lam⁻¹ Y) a(t, Y, z)` (`cutoffEdges`),
whose lifts (`liftEdges`, slow scale `lam`) agree with the true lifted edges where `χ = 1`
(`edgesAgreeOn_liftEdges_cutoff`) and are regular everywhere once the true ones are regular on
`Ω × ℝ²`.

`exists_cutoff_lift_data`: from a localized lift sequence of the family lift data (reserve
`R ≤ sX, sZ`, source edges `C^R` on `Ω`), cut-off lifts and cut-off edges such that the cut-off
data agree with the true data on a ball around `0`, the cut-off lifts agree with the true lifts
there and satisfy the local lift relation of the cut-off data there, and all of it is
`LiftRegular` of every order `R' ≤ R`. With `R = max N (2p) + Dm + 2` (F2′) these are the `loc`
and `reg` premises of `LiftGenSetup` with `edge A := cutoffEdges …`, and the regularity
`2a + Dm + 2` of the covariance letters. -/

section
/-- The cut-off of the coefficients of an edge family by a function of the slow offset. -/
def cutoffEdges {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} (χ : Vec 2 → ℝ) (e : ConstituentEdges Dm h) :
    ConstituentEdges Dm h :=
  fun v u d => (e v u d).map fun γ =>
    { γ with
      coeff := fun α t X z => χ X • γ.coeff α t X z
      periodic := fun α t X n z => by simp only [γ.periodic α t X n z] }

theorem edgesAgreeOn_liftEdges_cutoff {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} (c lam : ℝ)
    (χb : Vec 2 → ℝ) (e : ConstituentEdges Dm h) {B : Set (Vec 2)}
    (hχ : ∀ X ∈ B, χb (lam • X) = 1) :
    Uniqueness.EdgesAgreeOn B (liftEdges c lam e) (liftEdges c lam (cutoffEdges χb e)) := by
  intro v u d
  simp only [liftEdges, cutoffEdges, List.map_map]
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun γ _ => ⟨rfl, fun α t X hX z => by simp [hχ X hX]⟩

variable {ι : Type} [Fintype ι]

/-- **Cut-off lifts and cut-off edges for `LiftGenSetup`.** -/
theorem exists_cutoff_lift_data (D : OCData) (m : ℕ) (k : ℤ) {A : RealChain}
    (hA : A.WellSlotted) (ρ : ℝ) (hlam : ρ / D.eps (m - 1) ≠ 0) {Dm : ℕ}
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) {Ω : Set (Vec 2)} (hΩ : IsOpen Ω)
    (h0 : (0 : Vec 2) ∈ Ω) {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}
    (hC : IsLiftSequenceOn Ω (familyLiftData D m k A ρ edge) sX sZ t₀ t₁ N H Cc)
    {R : ℕ} (hsX : R ≤ sX) (hsZ : R ≤ sZ)
    (hedge : ∀ τ ∈ Icc t₀ t₁, ∀ (v u : ι) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ),
      γ ∈ (familyLiftData D m k A ρ edge).edge v u d → ∀ α c,
        ContDiffOn ℝ (R : WithTop ℕ∞)
          (fun p : Vec 2 × Vec 2 => γ.coeff α τ p.1 p.2 c) (Ω ×ˢ univ)) :
    ∃ r > 0, Metric.ball (0 : Vec 2) r ⊆ Ω ∧ ∃ (edge' : ConstituentEdges Dm (fun _ : ι => ℝ))
      (Cc' : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)),
      Uniqueness.DataAgreeOn (Metric.ball (0 : Vec 2) r) (familyLiftData D m k A ρ edge)
        (familyLiftData D m k A ρ edge') ∧
      (∀ hh n m (α : DerivativeWord2 m) t, ∀ X ∈ Metric.ball (0 : Vec 2) r,
        Cc' hh n m α t X = Cc hh n m α t X) ∧
      IsLiftLocal (familyLiftData D m k A ρ edge') (Metric.ball (0 : Vec 2) r) sZ t₀ t₁ N H Cc' ∧
      ∀ hh ≤ H, ∀ n R', R' ≤ R → ∀ τ ∈ Icc t₀ t₁, ∀ w : ι,
        LiftRegular (familyLiftData D m k A ρ edge') Cc' w τ hh n R' := by
  set lam := ρ / D.eps (m - 1) with hlamdef
  obtain ⟨r, hr, χ, hχ, hsupp, h1⟩ := exists_ball_cutoff hΩ h0
  have hBΩ : Metric.ball (0 : Vec 2) r ⊆ Ω := fun X hX =>
    hsupp (subset_tsupport χ (by rw [Function.mem_support, h1 X hX]; exact one_ne_zero))
  set χb : Vec 2 → ℝ := fun Y => χ (lam⁻¹ • Y) with hχb
  have hχbχ : ∀ X, χb (lam • X) = χ X := fun X => by
    simp only [hχb, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have hagree : Uniqueness.DataAgreeOn (Metric.ball (0 : Vec 2) r) (familyLiftData D m k A ρ edge)
      (familyLiftData D m k A ρ (cutoffEdges χb edge)) :=
    ⟨rfl, rfl, fun _ _ _ => rfl, edgesAgreeOn_liftEdges_cutoff _ lam χb edge
      fun X hX => by rw [hχbχ, h1 X hX]⟩
  refine ⟨r, hr, hBΩ, cutoffEdges χb edge, cutoffCoeff χ Cc, hagree,
    fun hh n m α t X hX => cutoffCoeff_eq h1 hh n m α t hX,
    IsLiftLocal.of_agree Metric.isOpen_ball subset_rfl hagree
      (fun hh n m α t X hX => (cutoffCoeff_eq h1 hh n m α t hX).symm)
      (IsLiftSequenceOn.toLocal hC hBΩ), fun hh hH n R' hR' τ hτ w => ?_⟩
  have hle : ((R' : ℕ) : WithTop ℕ∞) ≤ ((R : ℕ) : WithTop ℕ∞) := by exact_mod_cast hR'
  refine liftRegular_of D m k hA ρ (cutoffEdges χb edge) w τ hh n R'
    (fun hh' hh'' k' _ m' α v => ?_) (fun v u d γ hγ α c => ?_)
  · exact (contDiff_cutoffCoeff hΩ hχ hsupp (contDiffOn_coeff_of_box hΩ
      (hC.2.2.2.2.2.1 hh' (hh''.trans hH) k' m' α v w τ hτ).1 hsX hsZ)).of_le hle
  · -- `γ` is the lift of a cut-off base edge
    simp only [familyLiftData, liftEdges, cutoffEdges, List.map_map, List.mem_map,
      Function.comp_apply] at hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    have hmem : ({ γ₀ with
        coeff := fun α t X z => γ₀.coeff α (D.cellScaleSq m * t) (lam • X) z
        periodic := fun α t X => γ₀.periodic α (D.cellScaleSq m * t) (lam • X) } :
          Constituent d.1 ℝ ℝ) ∈ (familyLiftData D m k A ρ edge).edge v u d :=
      List.mem_map_of_mem hγ₀
    have hF := hedge τ hτ v u d _ hmem α c
    have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
      exact_mod_cast le_top
    have := contDiff_cutoff hΩ (hχ.of_le (htop _)) hsupp hF
    refine ContDiff.of_le ?_ hle
    convert this using 1
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, ← hlamdef, hχbχ]
end

end AVRegularity.Providers.GenSem
end
end
end

section
/-! **One step of the representation of the lift coefficients.** The setting
`LiftGenSetup` collects the hypotheses; `coeff_step` shows that, once the coefficients of all
earlier pairs `(hh', k)` are time-uniformly represented, the coefficient `Cc hh n m' I · X · v u 1`
is represented by `cellInvOf e_src`, where `e_src` represents the normalised cell source.

The identification: the represented source is parallel invariant, hence transverse;
so is the finite-past cell inverse `Cc hh n m' I · X · v u 1` (translation invariance and
uniqueness, `cellFieldInverse_par_invariant`); its transverse modes solve the mode equation from
zero, so it is the semantics of `cellInv (transPrim ·)` (`cellField_eq_cellInv_modes`;
no time-uniform mode bounds are needed). -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory
  AVRegularity.Providers.Transverse Set

namespace AVRegularity.Providers.GenSem

/-- The uniform representation environment of the lift of the slot `k` at level `m`, over the family
`𝒜` of base chains, the scale `ρ`, the per-chain offsets `U`, on the window `[t₀, t₁]` of lift
times. The index is `(A, τ)`: the physical time is `ℓ_m² τ` and the base chain is `A`. -/
def liftEnv (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (m : ℕ) (k : ℤ) (ρ : ℝ)
    (𝒜 : Set RealChain) (U : RealChain → Set (Vec 2)) (t₀ t₁ : ℝ) : UEnv (RealChain × ℝ) where
  E := ⟨D, bw, j₀, m, k, ⟨0, [], 0, []⟩, ρ, 0, 𝒮, ∅⟩
  time l := D.cellScaleSq m * l.2
  base l := l.1
  U l := U l.1
  W := {l | l.1 ∈ 𝒜 ∧ l.2 ∈ Icc t₀ t₁}

/-- The hypotheses of the representation of the lift coefficients: the lift sequences `Cc A` of
`familyLiftData D m k A ρ (edge A)` on `[t₀, t₁]` for every base chain `A ∈ 𝒜`, the uniform
representability of the aggregate of the (lifted) source edge coefficients, the regularity of the
lift data (`LiftRegular`). -/
structure LiftGenSetup {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ} (D : OCData) (bw : ℝ)
    (j₀ : ℕ) (𝒮 : SeedExports) (m : ℕ) (k : ℤ) (𝒜 : Set RealChain) (ρ : ℝ)
    (edge : RealChain → ConstituentEdges Dm (fun _ : ι => ℝ)) (U : RealChain → Set (Vec 2))
    (sX sZ : ℕ) (t₀ t₁ : ℝ) (N H : ℕ) (Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) :
    Prop where
  /-- The fast profile. -/
  hζ : IsFastProfile D.ζ
  /-- The scale is nonzero. -/
  hρ : ρ ≠ 0
  /-- The offsets are open. -/
  hU : ∀ A ∈ 𝒜, IsOpen (U A)
  /-- The slot is odd. -/
  hk : Odd k
  /-- The base chains are well slotted over the slot. -/
  hA : ∀ A ∈ 𝒜, A.WellSlotted ∧ A.slot = k
  /-- The cell time scale is positive. -/
  hc : 0 < D.cellScaleSq m
  /-- The window is nonempty. -/
  h01 : t₀ ≤ t₁
  /-- The window starts at the original start of the slot. -/
  hstart : D.cellScaleSq m * t₀ = D.slotStart m k
  /-- The normalisation of the drift. -/
  hη : Real.sqrt (D.kap m / D.kap (m - 1)) ≠ 0
  /-- The cell test fields are `C^{sZ}`, `sZ ≥ 1`. -/
  hsZ : 1 ≤ sZ
  /-- The lift relation at the offsets of `U A` (the coefficients of the setup may be
  cut-off copies of the localized lift sequences, which agree with them near `U A`). -/
  loc : ∀ A ∈ 𝒜, IsLiftLocal (familyLiftData D m k A ρ (edge A)) (U A) sZ t₀ t₁ N H (Cc A)
  /-- The aggregate `∑_γ (γ.map 1) * γ.coeff α τ X z k` of the (lifted) source edges is uniformly
  represented, on the window, over the family. -/
  edges : (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).EdgeURep (fun A => familyLiftData D m k A ρ (edge A))
  /-- The regularity of the lift data and coefficients. -/
  reg : ∀ A ∈ 𝒜, ∀ hh ≤ H, ∀ n, 1 ≤ n → n ≤ N → ∀ τ ∈ Icc t₀ t₁, ∀ w : ι,
    LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) w τ hh n (n + Dm + 2)

theorem isTransverse_of_invariant (p : ℤ) {f : Vec 2 → ℝ}
    (h : ∀ z (s : ℝ), f (z + s • basisVec (parIdx p)) = f z) :
    IsTransverse (transverseIndex p) f := by
  intro η
  have e : η = η (transverseIndex p) • basisVec (transverseIndex p) +
      η (parIdx p) • basisVec (parIdx p) := by
    have h1 := parIdx_ne_transverseIndex p
    funext i
    rcases UEnv.fin2_cases p i with rfl | rfl
    · simp [basisVec_apply, h1.symm]
    · simp [basisVec_apply, h1]
  conv_lhs => rw [e]
  exact h _ _

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ} {D : OCData} {bw : ℝ} {j₀ : ℕ}
  {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain} {ρ : ℝ}
  {edge : RealChain → ConstituentEdges Dm (fun _ : ι => ℝ)} {U : RealChain → Set (Vec 2)}
  {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ} {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}

namespace LiftGenSetup

theorem ok (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc) :
    (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).Ok :=
  ⟨hS.hζ, hS.hρ, fun l hl => hS.hU l.1 hl.1⟩

theorem metric_rep (_hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc) (a b : Fin 2) :
    (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURep
      (fun l X _ => (familyLiftData D m k l.1 ρ (edge l.1)).G l.2 X a b) :=
  ⟨_, (UEnv.urep_metric (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) a b).congr fun _ _ _ _ _ => rfl⟩

theorem drift_rep (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc) (c : Fin 2) :
    (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURep
      (fun l _ z => (familyLiftData D m k l.1 ρ (edge l.1)).v l.2 z c) :=
  UEnv.urep_pulseDrift (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) (fun l => l.2) (fun _ => rfl)
    hS.hc.ne' hS.hη c

/-- **The fixed-offset identification**: if the normalised cell source of the coefficient is
represented by a parallel-invariant denotation `f`, the coefficient is the semantics of
`cellInv (transPrim ·)` of `f` from zero at the start of the slot. -/
theorem coeff_eq_cellInv (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    {A : RealChain} (hA : A ∈ 𝒜)
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) {m' : ℕ} (hm : m' ≤ n)
    (I : DerivativeWord2 m') (v u : ι) {X : Vec 2} (hX : X ∈ U A) {f : GenSort.Sem .cell}
    (hf : ∀ τ ∈ Icc t₀ t₁, ∀ z, ((m'.factorial : ℝ))⁻¹ *
      liftCellSource (familyLiftData D m k A ρ (edge A)) (Cc A) (fun _ => monoField u X I) hh n τ X z v =
        f (D.cellScaleSq m * τ) (A.recenter D (ρ • X)) z)
    (hinv : ∀ τ ∈ Icc t₀ t₁, ∀ z (s : ℝ), f (D.cellScaleSq m * τ) (A.recenter D (ρ • X))
      (z + s • basisVec (parIdx k)) = f (D.cellScaleSq m * τ) (A.recenter D (ρ • X)) z) :
    ∀ τ ∈ Icc t₀ t₁, ∀ z, Cc A hh n m' I τ X z v u 1 =
      transverseInverseSem D m k
        (fun j => if j = transverseIndex k then transversePrimitiveSem k f
          else GenSort.ofTime .cell (TimeLetter.eval D (.const 0)))
        (D.slotStart m k) (GenSort.ofTime .cell (TimeLetter.eval D (.const 0)))
        (D.cellScaleSq m * τ) (A.recenter D (ρ • X)) z := by
  set Q := familyLiftData D m k A ρ (edge A) with hQ
  have hSeq : ∀ τ ∈ Icc t₀ t₁, ∀ z, ((m'.factorial : ℝ))⁻¹ *
      liftCellSource Q (Cc A) (fun _ => monoField u X I) hh n τ X z v =
      ((m'.factorial : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin m'), srcArr Q (Cc A) u hh n τ v m' (I ∘ σ) X z := by
    intro τ hτ z
    rw [liftCellSource_monoField Q (Cc A) u (hS.reg A hA hh hhH n hn1 hnN τ hτ u) X z v I (by omega)]
  have hcont : ∀ τ ∈ Icc t₀ t₁, Continuous (fun z => ((m'.factorial : ℝ))⁻¹ *
      liftCellSource Q (Cc A) (fun _ => monoField u X I) hh n τ X z v) := by
    intro τ hτ
    have e : (fun z => ((m'.factorial : ℝ))⁻¹ *
        liftCellSource Q (Cc A) (fun _ => monoField u X I) hh n τ X z v) =
        fun z => ((m'.factorial : ℝ))⁻¹ *
          ∑ σ : Equiv.Perm (Fin m'), srcArr Q (Cc A) u hh n τ v m' (I ∘ σ) X z :=
      funext (hSeq τ hτ)
    rw [e]
    exact continuous_const.mul (continuous_finsetSum _ fun σ _ =>
      continuous_srcArr_z Q (Cc A) u (hS.reg A hA hh hhH n hn1 hnN τ hτ) v m' (I ∘ σ) X)
  have hpar : ∀ τ ∈ Icc t₀ t₁, ∀ z (s : ℝ),
      ((m'.factorial : ℝ))⁻¹ * liftCellSource Q (Cc A) (fun _ => monoField u X I) hh n τ X
        (z + s • basisVec (parIdx k)) v =
      ((m'.factorial : ℝ))⁻¹ * liftCellSource Q (Cc A) (fun _ => monoField u X I) hh n τ X z v := by
    intro τ hτ z s
    rw [hf τ hτ, hf τ hτ]
    exact hinv τ hτ z s
  have htr : ∀ τ ∈ Icc t₀ t₁, IsTransverse (transverseIndex k) (fun z => ((m'.factorial : ℝ))⁻¹ *
      liftCellSource Q (Cc A) (fun _ => monoField u X I) hh n τ X z v) := fun τ hτ =>
    isTransverse_of_invariant k fun z s => hpar τ hτ z s
  obtain ⟨lo, hi, hlo, hq⟩ := familyLiftData_pos_window D hS.hζ m k A ρ (edge A) t₀ t₁ X
  obtain ⟨Mv, hMv⟩ := familyLiftData_v_bounded D hS.hζ m hS.hk A ρ (edge A)
  have hW := Uniqueness.windowData_of_elliptic (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo hi Mv
    (fun t => familyLiftData_symm D m k A ρ (edge A) t X 0 1) hlo hq (fun t _ z => hMv t z)
  have hC := liftCoeff_isCellFieldInverse_local Q hS.hsZ (hS.loc A hA) hhH hn1 hnN hX hm I v u
  have hCpar := cellFieldInverse_par_invariant hS.h01 hW (parIdx k)
    (fun t z s => ocPulseCellDrift_par m (D.kap m) hS.hk t z s)
    (fun t _ => ocPulseCellDrift_periodic m (D.kap m) hS.hk t) hpar hC
  have hCtr : ∀ τ ∈ Icc t₀ t₁, IsTransverse (transverseIndex k)
      (fun z => Cc A hh n m' I τ X z v u 1) := fun τ hτ =>
    isTransverse_of_invariant k fun z s => hCpar τ hτ z s
  intro τ hτ z
  have := cellField_eq_cellInv_modes D hS.hζ m k (A.recenter D (ρ • X)) hS.hc hS.hsZ
    (fun τ z => ((m'.factorial : ℝ))⁻¹ *
      liftCellSource Q (Cc A) (fun _ => monoField u X I) hh n τ X z v) f
    (fun τ hτ => funext fun z => (hf τ hτ z).symm) hcont htr
    (fun t => Matrix.of (Q.G t X)) Q.v (fun τ _ => by ext a b; rfl)
    (fun τ _ x => ocPulseCellDrift_transverse m (D.kap m) hS.hk τ x) _ hC hCtr
    (fun j => if j = transverseIndex k then transversePrimitiveSem k f
          else GenSort.ofTime .cell (TimeLetter.eval D (.const 0))) (ite_eq_left rfl) τ hτ z
  rw [this, ← hS.hstart]
  rfl

end LiftGenSetup

end AVRegularity.Providers.GenSem
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory Set
namespace AVRegularity.Providers.GenSem

/-! **The lift coefficients are `Gen`-representable.**

`LiftGenSetup.coeffRep`: by induction on `(hh, n)` every coefficient entry
`Cc A hh n m' I τ X z v u 1` (`A ∈ 𝒜`, `τ` in the window, `X` an admissible offset) is the semantics of one
scheduled, seed-provenanced cell expression, one expression for all base chains of the family and parallel invariant. For `1 ≤ n ≤ N`, `m' ≤ n` the
expression is `cellInvOf e_src`, the transverse inverse of the transverse primitive of the
expression `e_src` of the normalised cell source (`LiftGenSetup.coeff_eq_cellInv`). -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ} {D : OCData} {bw : ℝ} {j₀ : ℕ}
  {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain} {ρ : ℝ}
  {edge : RealChain → ConstituentEdges Dm (fun _ : ι => ℝ)} {U : RealChain → Set (Vec 2)}
  {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ} {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}

namespace LiftGenSetup

/-- **The step of the induction.** -/
theorem coeff_step (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N)
    (hbelow : (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).CoeffRepBelow Cc hh n) {m' : ℕ} (hm : m' ≤ n)
    (I : DerivativeWord2 m') (v u : ι) :
    ∃ e_src : Gen .cell m k,
      (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).URep (fun l X z => ((m'.factorial : ℝ))⁻¹ *
        liftCellSource (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1)
          (fun _ => monoField u X I) hh n l.2 X z v) e_src ∧
      (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).URep (fun l X z => Cc l.1 hh n m' I l.2 X z v u 1)
        (cellInvOf D e_src) := by
  obtain ⟨e_src, he⟩ := UEnv.isURep_cellSource hS.ok (fun A => familyLiftData D m k A ρ (edge A))
    Cc u hn1 (η := D.kap m / D.kap (m - 1)) (fun _ _ => rfl)
    hS.metric_rep hS.drift_rep hS.edges hbelow
    (fun l hl w => hS.reg l.1 hl.1 hh hhH n hn1 hnN l.2 hl.2 w) (by omega) I v
  refine ⟨e_src, he, ?_⟩
  obtain ⟨hsch, hfs, f, hd, hv, hinv⟩ := he
  have hval : ∀ l ∈ (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).W, ∀ X ∈ U l.1, ∀ z,
      Cc l.1 hh n m' I l.2 X z v u 1 =
        transverseInverseSem D m k
          (fun j => if j = transverseIndex k then transversePrimitiveSem k f
            else GenSort.ofTime .cell (TimeLetter.eval D (.const 0)))
          (D.slotStart m k) (GenSort.ofTime .cell (TimeLetter.eval D (.const 0)))
          (D.cellScaleSq m * l.2) (l.1.recenter D (ρ • X)) z := by
    intro l hl X hX z
    exact hS.coeff_eq_cellInv hl.1 hhH hn1 hnN hm I v u hX (f := f)
      (fun τ hτ z => hv (l.1, τ) ⟨hl.1, hτ⟩ X hX z)
      (fun τ hτ z s => (hv (l.1, τ) ⟨hl.1, hτ⟩ X hX _).symm.trans
        ((hinv (l.1, τ) ⟨hl.1, hτ⟩ X hX z s).trans (hv (l.1, τ) ⟨hl.1, hτ⟩ X hX z)))
      l.2 hl.2 z
  refine ⟨isScheduled_cellInvOf D hsch, fromSeed_cellInvOf D hfs, _,
    denotes_cellInvOf D _ _ hd, hval, fun l hl X hX z s => ?_⟩
  show Cc l.1 hh n m' I l.2 X (z + s • basisVec (parIdx k)) v u 1 = Cc l.1 hh n m' I l.2 X z v u 1
  rw [hval l hl X hX, hval l hl X hX]
  exact transverseInverseSem_phase D m k _ _ _ _ _ z s

/-- The order-zero coefficients. -/
theorem coeff_id (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc) {A : RealChain}
    (hA : A ∈ 𝒜) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁) (α : DerivativeWord2 0) {X : Vec 2} (hX : X ∈ U A)
    (z : Vec 2) (v u : ι) :
    Cc A 0 0 0 α τ X z v u 1 = if v = u then 1 else 0 := by
  have h := congrFun ((hS.loc A hA).init (fun _ => (Pi.single u (1 : ℝ) : ι → ℝ)) contDiff_const
    τ hτ X hX z) v
  simp only [liftApply, zero_add, Finset.sum_range_one] at h
  rw [Finset.sum_eq_single α (fun β _ hβ => absurd (Subsingleton.elim β α) hβ)
    (fun h' => absurd (Finset.mem_univ α) h')] at h
  have hod : orderedDerivative α (fun _ => (Pi.single u (1 : ℝ) : ι → ℝ)) =
      fun _ => Pi.single u 1 := by simp [orderedDerivative]
  rw [hod] at h
  rw [Finset.sum_eq_single u] at h
  · simpa [Pi.single_apply] using h
  · intro u' _ hu'
    simp [hu']
  · intro h'
    exact absurd (Finset.mem_univ u) h'

/-- **Every coefficient is uniformly represented.** -/
theorem coeffRep (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc) :
    ∀ hh, hh ≤ H → ∀ n m' (α : DerivativeWord2 m') (v u : ι),
      (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURep
        (fun l X z => Cc l.1 hh n m' α l.2 X z v u 1) := by
  intro hh
  induction hh using Nat.strong_induction_on with
  | _ hh ihh =>
  intro hhH n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro m' α v u
  set V := liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁ with hV
  have hzero : (∀ A ∈ 𝒜, ∀ τ ∈ Icc t₀ t₁, ∀ X ∈ U A, ∀ z, Cc A hh n m' α τ X z v u 1 = 0) →
      V.IsURep (fun l X z => Cc l.1 hh n m' α l.2 X z v u 1) := fun h =>
    (UEnv.isURep_const V 0).congr fun l hl X hX z => h l.1 hl.1 l.2 hl.2 X hX z
  have hbelow : V.CoeffRepBelow Cc hh n := fun hh' k' hk m'' α' v' u' => by
    rcases hk with hk | ⟨rfl, hk⟩
    · exact ihh hh' hk (by omega) k' m'' α' v' u'
    · exact ihn k' hk m'' α' v' u'
  by_cases hnN : N < n
  · exact hzero fun A hA τ _ X hX z => by
      rw [(hS.loc A hA).zeroN hh hhH n hnN m' α τ X hX z v u]; simp
  by_cases hn0 : n = 0
  · subst hn0
    by_cases hh0 : hh = 0
    · subst hh0
      by_cases hm0 : m' = 0
      · subst hm0
        exact (UEnv.isURep_const V (if v = u then 1 else 0)).congr fun l hl X hX z =>
          hS.coeff_id hl.1 hl.2 α hX z v u
      · exact hzero fun A hA τ _ X hX z => by
          rw [(hS.loc A hA).zeroM 0 hhH 0 m' (by omega) α τ X hX z v u]; simp
    · exact hzero fun A hA τ _ X hX z => by
        rw [(hS.loc A hA).zero0 hh (by omega) hhH m' α τ X hX z v u]; simp
  · by_cases hm : m' ≤ n
    · obtain ⟨e_src, -, hc⟩ := hS.coeff_step hhH (by omega) (by omega) hbelow hm α v u
      exact ⟨_, hc⟩
    · exact hzero fun A hA τ _ X hX z => by
        rw [(hS.loc A hA).zeroM hh hhH n m' (by omega) α τ X hX z v u]; simp

end LiftGenSetup

end AVRegularity.Providers.GenSem
end
end
