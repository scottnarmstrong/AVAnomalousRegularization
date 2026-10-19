-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Intermediate.KernelEnergy.KernelFluxBoundPlane
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
public import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarTorusH1Time
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
import AVRegularity.CycleReference.MeanEnhancementScale
import AVRegularity.CycleComparison.Assembly.OcData
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.EntryWeak.MolecularUlFluxNormBound
public import AVRegularity.EntryWeak.IndependentScaledDifferenceSegmentDerivativeJets
public import AVRegularity.CycleJoint.TransitionJetTermDerivative
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import AVRegularity.Construction.InitialValue.Cascade

section
section
/-! Literal matrix inverse and columns of the paired spanning equivalence. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem matrixContinuousLinearEquiv_symm_apply (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : IsUnit A.det) (x : Vec 2) :
    (matrixContinuousLinearEquiv A hA).symm x = Matrix.toLin' A⁻¹ x := by
  let := Matrix.invertibleOfIsUnitDet A hA
  change Matrix.toLin' (⅟A) x = Matrix.toLin' A⁻¹ x
  rw [Matrix.invOf_eq_nonsing_inv]

theorem matrixContinuousLinearEquiv_symm_map (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : IsUnit A.det) :
    (matrixContinuousLinearEquiv A hA).symm.toContinuousLinearMap =
      (Matrix.toLin' A⁻¹).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  exact matrixContinuousLinearEquiv_symm_apply A hA

theorem kernelSpan_first_column (S : KernelSpec) (t : ℝ)
    (hS : IsUnit (S.span t).det) :
    matrixContinuousLinearEquiv (S.span t) hS (basisVec 0) = S.H₁ t (basisVec 0) := by
  rw [matrixContinuousLinearEquiv_apply]
  ext a
  simp [Matrix.toLin'_apply, Matrix.mulVec, KernelSpec.span, basisVec]

theorem kernelSpan_second_column (S : KernelSpec) (t : ℝ)
    (hS : IsUnit (S.span t).det) :
    matrixContinuousLinearEquiv (S.span t) hS (basisVec 1) = S.H₂ t (basisVec 1) := by
  rw [matrixContinuousLinearEquiv_apply]
  ext a
  simp [Matrix.toLin'_apply, Matrix.mulVec, KernelSpec.span, basisVec]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Keep each original identity's inflated birth price before taking Schur sums. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_kernel_schur_entry_le_of_priced_identity_prices
    (G : GenStage D hr Dm bw j₀) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (ν ρ a b A : ℝ) (π : CompIn G.comps → ℝ) (n : ℕ) (c : ℕ → ℝ)
    (hν : 0 < ν)
    (hwidth : ∀ v u γ, 0 < (G.kernelOf P seedK freshK v u γ).width)
    (hc : ∀ j, j + 2 ≤ Dm → 0 ≤ c j)
    (hprice : ∀ v u γ,
      (∑ d : ↥(Finset.Icc 2 Dm),
        ((coefficientSeminorm ρ n a b (G.physCoeff v u γ d.1)).toReal * c (d.1 - 2)) /
          (ν * (G.kernelOf P seedK freshK v u γ).width ^ (d.1 - 2))) ≤
        A * (‖(G.fam.identity v u γ).map‖ * (G.fam.identity v u γ).record.size *
          constituentPrice (G.fam.identity v u γ).record))
    (v u : CompIn G.comps) :
    kernelSchurMatrix ν ρ π n Dm a b c
      (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1) v u ≤
        A * pricedRecordMajorant π (fun _ => 1) G.fam v u := by
  classical
  unfold kernelSchurMatrix pricedRecordMajorant
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_mul]
  rw [mul_left_comm A]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro γ _
  have hn : 0 ≤ ∑ d : ↥(Finset.Icc 2 Dm),
      ((coefficientSeminorm ρ n a b (G.physCoeff v u γ d.1)).toReal * c (d.1 - 2)) /
        (ν * (G.kernelOf P seedK freshK v u γ).width ^ (d.1 - 2)) := by
    apply Finset.sum_nonneg
    intro d _
    exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (hc _ (by have hd := Finset.mem_Icc.mp d.property; omega)))
      (mul_nonneg hν.le (pow_nonneg (hwidth v u γ).le _))
  exact (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_id_le (𝕜 := ℝ)) hn).trans
    (by simpa only [one_mul] using hprice v u γ)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Reuse the compiled order-consistency theorem for the literal native homogeneous system. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_truncate (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    (ν a b : ℝ) (bv : ℝ → Vec 2 → Vec 2) (k l : ℕ) (hkl : k ≤ l)
    (f : ∀ v : CompIn G.comps, TorusHk l (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk l (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (l + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (l + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv l a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k a b
      (fun v => truncateTorusHk hkl (f v)) (fun _ _ => 0) (fun _ _ => 0)
      (fun v t => truncateTorusHk hkl (U v t))
      (fun v t => truncateTorusHk (Nat.succ_le_succ hkl) (W v t))
      (fun v u γ t => truncateTorusHk (by omega : k + Dm - 1 ≤ l + Dm - 1) (Y v u γ t)) := by
  have h := Providers.kernel_solution_truncate_torus a b ν bv k l Dm hkl
    (fun v u γ d => G.physCoeff v u γ d.1)
    (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
    (G.sysS P seedK freshK φ₀ hφ₀) f (fun _ _ => 0) (fun _ _ => 0) U W Y hsol
  simpa only [GenStage.IsRegSolution, map_zero] using h

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The paired-column map is close to the identity when its two parent maps are. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem kernelSpan_toLin_first_column (S : KernelSpec) (t : ℝ) :
    Matrix.toLin' (S.span t) (basisVec 0) = S.H₁ t (basisVec 0) := by
  ext a
  simp [Matrix.toLin'_apply, Matrix.mulVec, KernelSpec.span, basisVec]

theorem kernelSpan_toLin_second_column (S : KernelSpec) (t : ℝ) :
    Matrix.toLin' (S.span t) (basisVec 1) = S.H₂ t (basisVec 1) := by
  ext a
  simp [Matrix.toLin'_apply, Matrix.mulVec, KernelSpec.span, basisVec]

theorem linear_map_basis_deviation_le (H : Vec 2 →L[ℝ] Vec 2) {η : ℝ}
    (hH : ‖H - 1‖ ≤ η) (i : Fin 2) : ‖H (basisVec i) - basisVec i‖ ≤ η := by
  have h := (H - 1).le_opNorm (basisVec i)
  have hi : ‖(basisVec i : Vec 2)‖ = 1 := by simp [basisVec, Pi.norm_single]
  have h' : ‖H (basisVec i) - basisVec i‖ ≤ ‖H - 1‖ := by
    simpa only [sub_apply, one_apply_eq_self, hi, mul_one] using h
  exact h'.trans hH

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! A pointwise lower norm estimate supplies both nonsingularity and the literal inverse bound. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem matrix_isUnit_and_inverse_norm_le_of_control (A : Matrix (Fin 2) (Fin 2) ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hcontrol : ∀ x : Vec 2, ‖x‖ ≤ C * ‖Matrix.toLin' A x‖) :
    IsUnit A.det ∧ ‖(Matrix.toLin' A⁻¹).toContinuousLinearMap‖ ≤ C := by
  have hk : (Matrix.toLin' A).ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply norm_eq_zero.mp
    have hh := hcontrol x
    rw [hx, norm_zero, mul_zero] at hh
    exact le_antisymm hh (norm_nonneg x)
  have hinj := LinearMap.ker_eq_bot.mp hk
  have hunit : IsUnit (Matrix.toLin' A) := (Module.End.isUnit_iff _).mpr
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.isUnit_toLin'_iff.mp hunit)
  refine ⟨hu, ?_⟩
  rw [← matrixContinuousLinearEquiv_symm_map A hu]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro y
  change ‖(matrixContinuousLinearEquiv A hu).symm y‖ ≤ C * ‖y‖
  have hh := hcontrol ((matrixContinuousLinearEquiv A hu).symm y)
  rw [← matrixContinuousLinearEquiv_apply A hu, ContinuousLinearEquiv.apply_symm_apply] at hh
  exact hh

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Positive identity prices and the original inflated record ledger give both kernel Schur sums. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_kernel_schur_bound_of_priced_identity_prices
    (G : GenStage D hr Dm bw j₀) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (ν ρ a b A Sbound : ℝ) (π : CompIn G.comps → ℝ) (n : ℕ) (c : ℕ → ℝ)
    (hν : 0 < ν)
    (hwidth : ∀ v u γ, 0 < (G.kernelOf P seedK freshK v u γ).width)
    (hc : ∀ j, j + 2 ≤ Dm → 0 ≤ c j)
    (hprice : ∀ v u γ,
      (∑ d : ↥(Finset.Icc 2 Dm),
        ((coefficientSeminorm ρ n a b (G.physCoeff v u γ d.1)).toReal * c (d.1 - 2)) /
          (ν * (G.kernelOf P seedK freshK v u γ).width ^ (d.1 - 2))) ≤
        A * (‖(G.fam.identity v u γ).map‖ * (G.fam.identity v u γ).record.size *
          constituentPrice (G.fam.identity v u γ).record))
    (hA : 0 ≤ A) (hrecord : SchurBound Sbound (pricedRecordMajorant π (fun _ => 1) G.fam)) :
    SchurBound (A * Sbound)
      (kernelSchurMatrix ν ρ π n Dm a b c
        (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
        (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
        (fun v u γ d => G.physCoeff v u γ d.1)) := by
  have he := native_kernel_schur_entry_le_of_priced_identity_prices G P seedK freshK
    ν ρ a b A π n c hν hwidth hc hprice
  constructor
  · intro v
    exact (Finset.sum_le_sum (fun u _ => he v u)).trans
      (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hrecord.1 v) hA)
  · intro u
    exact (Finset.sum_le_sum (fun v _ => he v u)).trans
      (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hrecord.2 u) hA)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Exact birth mass and marker factors, and their monotonicity in a readout fiber. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

theorem succComp_mass {q : ℝ} {Λ m : ℕ} (law : BirthLaw) (v : Comp)
    {t : List WordLetter} (ht : t ≠ []) :
    compMass q Λ law (succComp m v t) =
      (law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ (m - 1) ^ law.etaB) *
        compMass q Λ law v := by
  simp only [succComp, ht, ↓reduceDIte, compMass, List.map_cons, List.prod_cons]
  ring

theorem succComp_marker {q : ℝ} {Λ m : ℕ} (hm : 1 ≤ m) (law : BirthLaw)
    (v : Comp) (hold : ∀ e ∈ v.births, m ≤ e.scale)
    {t : List WordLetter} (ht : t ≠ []) :
    compMarker q Λ law (succComp m v t) =
      ocEpsilon q Λ (m - 1) ^ (-law.iota) * compMarker q Λ law v := by
  have hnew : m - 1 ∉ compBirthSet v := by
    intro h
    obtain ⟨e, he, hscale⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    have := hold e he
    omega
  simp only [succComp, ht, ↓reduceDIte, compMarker, compBirthSet,
    List.map_cons, List.toFinset_cons]
  exact Finset.prod_insert hnew

theorem succComp_mass_le {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (hcH : law.cH ≤ 1) (hη : 0 ≤ law.etaB)
    (v : Comp) (t : List WordLetter) :
    compMass q Λ law (succComp m v t) ≤ compMass q Λ law v := by
  by_cases ht : t = []
  · simp [succComp, ht]
  · rw [succComp_mass law v ht]
    have he := Scales.epsilon_basic (m := m - 1) hq hΛ
    have hpref : law.cH / (law.wordCount : ℝ) ≤ 1 := by
      apply (div_le_one₀ (by exact_mod_cast law.wordCount_pos)).mpr
      exact hcH.trans (by exact_mod_cast law.wordCount_pos)
    have hpref0 : 0 ≤ law.cH / (law.wordCount : ℝ) :=
      (div_pos law.cH_pos (by exact_mod_cast law.wordCount_pos)).le
    have hprice : law.cH / (law.wordCount : ℝ) *
        ocEpsilon q Λ (m - 1) ^ law.etaB ≤ 1 := by
      calc
        _ ≤ law.cH / (law.wordCount : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one he.1.le (by linarith [he.2]) hη) hpref0
        _ ≤ 1 := by simpa only [mul_one] using hpref
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hprice
      (Buffer.birth_compMass_pos hq hΛ law v).le

theorem succComp_marker_le {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hm : 1 ≤ m) (law : BirthLaw) (hiota : 0 ≤ law.iota)
    (v : Comp) (hold : ∀ e ∈ v.births, m ≤ e.scale) (t : List WordLetter) :
    compMarker q Λ law v ≤ compMarker q Λ law (succComp m v t) := by
  by_cases ht : t = []
  · simp [succComp, ht]
  · rw [succComp_marker hm law v hold ht]
    have he := Scales.epsilon_basic (m := m - 1) hq hΛ
    have hfactor := Real.one_le_rpow_of_pos_of_le_one_of_nonpos he.1
      (by linarith [he.2]) (neg_nonpos.mpr hiota)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor
      (Buffer.birth_compMarker_pos hq hΛ law v).le

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Small first-derivative deviations remain small under the two chart compositions. -/
@[expose] public section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem operator_norm_le_one_add_deviation (G : Vec 2 →L[ℝ] Vec 2) {η : ℝ}
    (hG : ‖G - 1‖ ≤ η) : ‖G‖ ≤ 1 + η := by
  calc
    ‖G‖ = ‖(G - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖G - 1‖ + ‖(1 : Vec 2 →L[ℝ] Vec 2)‖ := norm_add_le _ _
    _ ≤ η + 1 := add_le_add hG ContinuousLinearMap.norm_id_le
    _ = 1 + η := add_comm _ _

theorem operator_composition_deviation_le (G H : Vec 2 →L[ℝ] Vec 2) {η : ℝ}
    (hη : 0 ≤ η) (hG : ‖G - 1‖ ≤ η) (hH : ‖H - 1‖ ≤ η) :
    ‖G.comp H - 1‖ ≤ (1 + η) * η + η := by
  have he : G.comp H - 1 = G.comp (H - 1) + (G - 1) := by
    apply ContinuousLinearMap.ext
    intro x
    change G (H x) - x = G (H x - x) + (G x - x)
    rw [map_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖G.comp (H - 1)‖ + ‖G - 1‖ := norm_add_le _ _
    _ ≤ ‖G‖ * ‖H - 1‖ + η := add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) hG
    _ ≤ (1 + η) * η + η := add_le_add
      (mul_le_mul (operator_norm_le_one_add_deviation G hG) hH (norm_nonneg _)
        (by linarith)) le_rfl

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Covariance duality depends only on values and therefore transfers to compatible higher carriers. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem covImage_of_compatible_carriers {K K' L L' : ℕ}
    (hK : K ≤ K') (hL : L ≤ L') (P : (Vec 2 → E) → Vec 2 → E)
    (Z : TorusHk K E) (Z' : TorusHk K' E) (W : TorusHk L E) (W' : TorusHk L' E)
    (hZ : truncateTorusHk hK Z' = Z) (hW : truncateTorusHk hL W' = W)
    (hcov : IsCovImage P Z W) : IsCovImage P Z' W' := by
  subst Z
  subst W
  intro ψ hψ hp
  have ht := hcov ψ hψ hp
  change cellInner (CycleComparison.Coarse.tval W') ψ =
    cellInner (CycleComparison.Coarse.tval Z') (P ψ)
  change cellInner (CycleComparison.Coarse.tval (truncateTorusHk hL W')) ψ =
    cellInner (CycleComparison.Coarse.tval (truncateTorusHk hK Z')) (P ψ) at ht
  simpa only [CycleComparison.Coarse.tval_truncateTorusHk] using ht

theorem covImage_truncate_input {K L R : ℕ} (hKL : K ≤ L)
    (P : (Vec 2 → E) → Vec 2 → E) (Z : TorusHk L E) (W : TorusHk R E)
    (hW : IsCovImage P Z W) : IsCovImage P (truncateTorusHk hKL Z) W := by
  intro ψ hψ hp
  have hi := hW ψ hψ hp
  change cellInner (CycleComparison.Coarse.tval W) ψ =
    cellInner (CycleComparison.Coarse.tval Z) (P ψ) at hi
  change cellInner (CycleComparison.Coarse.tval W) ψ =
    cellInner (CycleComparison.Coarse.tval (truncateTorusHk hKL Z)) (P ψ)
  simpa only [CycleComparison.Coarse.tval_truncateTorusHk] using hi

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Every birth marker dominates the identity weight at the actual scales. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

theorem compMarker_one_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (hiota : 0 ≤ law.iota) (c : Comp) :
    1 ≤ compMarker q Λ law c := by
  unfold compMarker
  apply Finset.one_le_prod₀
  intro k _
  have he := Scales.epsilon_basic (m := k) hq hΛ
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos he.1
    (by linarith only [he.2]) (neg_nonpos.mpr hiota)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Every extended readout component has an incoming parent. Birth factors contract the
ordinary and marker-conjugated scalar readout coefficients. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

theorem readout_parent_mem {m : ℕ} (hm : 1 ≤ m) {A : Finset WordLetter}
    {J : ℕ} {S : Finset Comp} (hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale)
    {c : Comp} (hc : c ∈ succExtComps m A J S) : compParent m c ∈ S := by
  rcases Finset.mem_union.mp hc with hc | hc
  · rw [(InitialValue.compParent_eq_self hm (hold c hc)).1]
    exact hc
  · obtain ⟨⟨v, t⟩, hvt, rfl⟩ := Finset.mem_image.mp hc
    have hv := (Finset.mem_product.mp hvt).1
    rw [(parent_word_succComp hm v (hold v hv) t).1]
    exact hv

theorem readout_parent_mass_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (hcH : law.cH ≤ 1) (hη : 0 ≤ law.etaB) (m : ℕ) (c : Comp) :
    compMass q Λ law c ≤ compMass q Λ law (compParent m c) := by
  calc
    _ = compMass q Λ law (succComp m (compParent m c) (compWord m c)) := by
      rw [succComp_parent_word]
    _ ≤ _ := succComp_mass_le hq hΛ law hcH hη _ _

theorem readout_parent_marker_le {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hm : 1 ≤ m) (law : BirthLaw) (hiota : 0 ≤ law.iota)
    {A : Finset WordLetter} {J : ℕ} {S : Finset Comp}
    (hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale)
    {c : Comp} (hc : c ∈ succExtComps m A J S) :
    compMarker q Λ law (compParent m c) ≤ compMarker q Λ law c := by
  calc
    _ ≤ compMarker q Λ law (succComp m (compParent m c) (compWord m c)) :=
      succComp_marker_le hq hΛ hm law hiota _ (hold _ (readout_parent_mem hm hold hc)) _
    _ = _ := by rw [succComp_parent_word]

theorem readout_mass_conjugate_le_one {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (hcH : law.cH ≤ 1) (hη : 0 ≤ law.etaB) (m : ℕ) (c : Comp) :
    Real.sqrt (compMass q Λ law c / compMass q Λ law (compParent m c)) ≤ 1 := by
  apply (Real.sqrt_le_one).mpr
  exact (div_le_one₀ (Buffer.birth_compMass_pos hq hΛ law _)).mpr
    (readout_parent_mass_le hq hΛ law hcH hη m c)

theorem readout_coefficient_le_one {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    {η : ℝ} (hη : 0 ≤ η) (m : ℕ) (c : Comp) :
    ocEpsilon q Λ (m - 1) ^ (η * (compWord m c).length) ≤ 1 := by
  have he := Scales.epsilon_basic (m := m - 1) hq hΛ
  exact Real.rpow_le_one he.1.le he.2.1 (mul_nonneg hη (Nat.cast_nonneg _))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! The actual inverse-mass and marked diagonals give readout entries at most one. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

theorem inverse_mass_diagonal_ratio {π σ : ℝ} (hσ : 0 ≤ σ) (a b : ℝ) :
    (a * (Real.sqrt π)⁻¹) / (b * (Real.sqrt σ)⁻¹) =
      Real.sqrt (σ / π) * (a / b) := by
  rw [Real.sqrt_div hσ]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem readout_ordinary_entry_le_one {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (hcH : law.cH ≤ 1) (hηB : 0 ≤ law.etaB)
    {η : ℝ} (hη : 0 ≤ η) (m : ℕ) (c : Comp) :
    (Real.sqrt (compMass q Λ law (compParent m c)))⁻¹ /
        (Real.sqrt (compMass q Λ law c))⁻¹ *
      ocEpsilon q Λ (m - 1) ^ (η * (compWord m c).length) ≤ 1 := by
  have he : (Real.sqrt (compMass q Λ law (compParent m c)))⁻¹ /
        (Real.sqrt (compMass q Λ law c))⁻¹ =
      Real.sqrt (compMass q Λ law c / compMass q Λ law (compParent m c)) := by
    simpa only [one_mul, div_self (by norm_num : (1 : ℝ) ≠ 0), mul_one] using
      inverse_mass_diagonal_ratio (Buffer.birth_compMass_pos hq hΛ law c).le 1 1
  rw [he]
  exact (mul_le_mul (readout_mass_conjugate_le_one hq hΛ law hcH hηB m c)
    (readout_coefficient_le_one hq hΛ hη m c)
    (Real.rpow_nonneg (Scales.epsilon_basic (m := m - 1) hq hΛ).1.le _) zero_le_one).trans_eq
    (one_mul 1)

theorem readout_marked_entry_le_one {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hm : 1 ≤ m) (law : BirthLaw) (hcH : law.cH ≤ 1) (hηB : 0 ≤ law.etaB)
    (hiota : 0 ≤ law.iota) {η : ℝ} (hη : 0 ≤ η)
    {A : Finset WordLetter} {J : ℕ} {S : Finset Comp}
    (hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale)
    {c : Comp} (hc : c ∈ succExtComps m A J S) :
    (compMarker q Λ law (compParent m c) *
          (Real.sqrt (compMass q Λ law (compParent m c)))⁻¹) /
        (compMarker q Λ law c * (Real.sqrt (compMass q Λ law c))⁻¹) *
      ocEpsilon q Λ (m - 1) ^ (η * (compWord m c).length) ≤ 1 := by
  rw [inverse_mass_diagonal_ratio (Buffer.birth_compMass_pos hq hΛ law c).le]
  have hd : compMarker q Λ law (compParent m c) / compMarker q Λ law c ≤ 1 :=
    (div_le_one₀ (Buffer.birth_compMarker_pos hq hΛ law c)).mpr
      (readout_parent_marker_le hq hΛ hm law hiota hold hc)
  have hd0 : 0 ≤ compMarker q Λ law (compParent m c) / compMarker q Λ law c :=
    (div_pos (Buffer.birth_compMarker_pos hq hΛ law _) (Buffer.birth_compMarker_pos hq hΛ law _)).le
  have he : Real.sqrt (compMass q Λ law c / compMass q Λ law (compParent m c)) *
      (compMarker q Λ law (compParent m c) / compMarker q Λ law c) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul
      (readout_mass_conjugate_le_one hq hΛ law hcH hηB m c) hd hd0 zero_le_one
  simpa only [one_mul] using mul_le_mul he
    (readout_coefficient_le_one hq hΛ hη m c)
    (Real.rpow_nonneg (Scales.epsilon_basic (m := m - 1) hq hΛ).1.le _) zero_le_one

end AVRegularity.Construction.Preservation.FullLift
end
end

section
/-! Two transported long columns give a norm lower bound without paying their common size. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

theorem scaled_paired_column_norm_control
    (W G HH HV : Vec 2 →L[ℝ] Vec 2) (a : ℝ) (ha : 1 ≤ a)
    (hW₀ : W (basisVec 0) = a • G (HH (basisVec 0)))
    (hW₁ : W (basisVec 1) = a • G (HV (basisVec 1)))
    (hG : ‖G - 1‖ ≤ (1 / 16 : ℝ)) (hHH : ‖HH - 1‖ ≤ (1 / 16 : ℝ))
    (hHV : ‖HV - 1‖ ≤ (1 / 16 : ℝ)) (x : Vec 2) : ‖x‖ ≤ 2 * ‖W x‖ := by
  let U : Vec 2 →L[ℝ] Vec 2 := a⁻¹ • W
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hu₀ : U (basisVec 0) = G (HH (basisVec 0)) := by
    change a⁻¹ • W (basisVec 0) = _
    rw [hW₀, smul_smul, inv_mul_cancel₀ ha0.ne', one_smul]
  have hu₁ : U (basisVec 1) = G (HV (basisVec 1)) := by
    change a⁻¹ • W (basisVec 1) = _
    rw [hW₁, smul_smul, inv_mul_cancel₀ ha0.ne', one_smul]
  let δ : ℝ := (1 + 1 / 16) * (1 / 16) + 1 / 16
  have hδ : 0 ≤ δ := by norm_num [δ]
  have hu : ‖U - 1‖ ≤ 2 * δ := by
    apply AVenhance.timeIncrement_clm_norm_le_two_basis hδ
    · change ‖U (basisVec 0) - basisVec 0‖ ≤ δ
      rw [hu₀]
      exact linear_map_basis_deviation_le (G.comp HH)
        (operator_composition_deviation_le G HH (by norm_num) hG hHH) 0
    · change ‖U (basisVec 1) - basisVec 1‖ ≤ δ
      rw [hu₁]
      exact linear_map_basis_deviation_le (G.comp HV)
        (operator_composition_deviation_le G HV (by norm_num) hG hHV) 1
  have hhalf : ‖U - 1‖ ≤ (1 / 2 : ℝ) := hu.trans (by norm_num [δ])
  have he : ‖U x - x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := by
    have hh := (U - 1).le_opNorm x
    change ‖U x - x‖ ≤ ‖U - 1‖ * ‖x‖ at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hhalf (norm_nonneg x))
  have ht : ‖x‖ ≤ ‖U x‖ + ‖U x - x‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub' x (U x)
  have hl : ‖x‖ ≤ 2 * ‖U x‖ := by linarith
  have hUx : ‖U x‖ ≤ ‖W x‖ := by
    calc
      ‖U x‖ = a⁻¹ * ‖W x‖ := by
        change ‖a⁻¹ • W x‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ha0.le)]
      _ ≤ 1 * ‖W x‖ := mul_le_mul_of_nonneg_right ((inv_le_one₀ ha0).mpr ha) (norm_nonneg _)
      _ = ‖W x‖ := one_mul _
  exact hl.trans (mul_le_mul_of_nonneg_left hUx (by norm_num))

end AVRegularity.Construction.Preservation.FullLift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! A lift built with measurable window extensions solves the original literal recursion. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem windowEdges_liftSequence (Q : LiftOperatorData ι h D) (a b : ℝ)
    (sX sZ N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hc : IsLiftSequence {Q with edge := windowEdges a b Q.edge} sX sZ a b N H Cc) :
    IsLiftSequence Q sX sZ a b N H Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1,
    hc.2.2.2.2.2.1, ?_⟩
  intro hh hhh n hn hnN f hf X
  have hi := hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X
  apply CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
  intro t ht
  funext z
  exact (EntryWeakProofs.liftCellSource_edge_slow_open_congr isOpen_univ Q
    (windowEdges a b Q.edge) Cc (fun _ => f) hh n t
    (windowEdges_agree a b Q.edge t ht) X (Set.mem_univ X) z).symm

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Actual constituent coefficients inherit positive active-piece budgets without counting pieces. -/

open CycleJointProofs AVRegularity.Construction.Preservation.Buffer

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_constituentPhysical_positive_jet_budget
    {G : GenStage D hr Dm bw j₀} {M : ℕ} (hnat : G.IsNatural M)
    (a b : ℝ)
    (ν e E : ℝ) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (d n : ℕ) (ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (t : Set.Icc a b)
    (g : OddSlot → Vec 2 →
      ((PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root))))
    (hg : ∀ p y, g p y = nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t)
        (G.fam.identity v u γ).maxOrder
        (fun d' I => G.fam.dimFlux ν e E p (G.actual p) v u γ d' I t
          (streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) y t)
          (e⁻¹ • streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) y t)) (d - 1) A y a))
    (hgs : ∀ p, (t : ℝ) ∈ (G.fam.piece p).output → ContDiff ℝ (n : ℕ) (g p))
    (hjet : ∀ p, (t : ℝ) ∈ (G.fam.piece p).output → ∀ y,
      ρ ^ n * ‖iteratedFDeriv ℝ n (g p) y‖ ≤ B) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n
      (constituentPhysical G.fam ν e E G.actual v u γ d t) x‖ ≤ B := by
  let outputNormedGroup : NormedAddCommGroup
      ((PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) := inferInstance
  let outputNormedSpace : NormedSpace ℝ
      ((PiLp 2 (fun _ : DerivativeWord2 (d - 1) => hr u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => hr v.1.root))) := inferInstance
  let f := fun p y => G.fam.weight p t • g p y
  have he : constituentPhysical G.fam ν e E G.actual v u γ d t = fun y => ∑ᶠ p, f p y := by
    funext y
    unfold constituentPhysical
    apply finsum_congr
    intro p
    change G.fam.weight p t • (nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map _) = _
    rw [native_inverse_jacobian_eq_natural hnat p t, native_inverse_material_eq_flow hnat p t]
    rw [← hg p y]
  rw [he]
  have hz p (hout : (t : ℝ) ∉ (G.fam.piece p).output) : f p = fun _ => 0 := by
    funext y
    dsimp only [f]
    rw [G.fam.weight_zero p t hout]
    exact zero_smul ℝ (g p y)
  apply positive_piece_jet_assembly_total G.fam a b t t.property f n
    (fun p => by
      by_cases hout : (t : ℝ) ∈ (G.fam.piece p).output
      · exact (hgs p hout).const_smul _
      · rw [hz p hout]
        exact contDiff_const) _ ρ B hρ hB _ x
  · intro p y hout
    exact congrFun (hz p hout) y
  · intro p y
    by_cases hout : (t : ℝ) ∈ (G.fam.piece p).output
    · dsimp only [f]
      rw [iteratedFDeriv_const_smul_apply' (hgs p hout).contDiffAt]
      have hn := mul_le_mul_of_nonneg_left
        (norm_smul_le (G.fam.weight p t) (iteratedFDeriv ℝ n (g p) y)) (pow_nonneg hρ n)
      rw [Real.norm_eq_abs, abs_of_nonneg (G.fam.weight_nonneg p t)] at hn
      apply hn.trans
      have hh := mul_le_mul_of_nonneg_left (hjet p hout y) (G.fam.weight_nonneg p t)
      convert hh using 1; ring
    · rw [hz p hout, iteratedFDeriv_fun_zero, G.fam.weight_zero p t hout]
      simp only [Pi.zero_apply, norm_zero, mul_zero, zero_mul, le_refl]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! The actual fresh spanning inverse is uniformly bounded after a pre-data level threshold. -/

theorem uniform_fresh_spanning_inverse_bound
    (α s q : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
    ∀ b : ℕ, m₀ ≤ b + 1 → b + 1 ≤ D.term →
    ∀ S : KernelSpec, IsFreshAxes D b S.H₁ S.H₂ → ∀ t : ℝ,
      IsUnit (S.span t).det ∧ ‖(Matrix.toLin' (S.span t)⁻¹).toContinuousLinearMap‖ ≤ 2 := by
  obtain ⟨mS, hmS, hS⟩ := uniform_sampled_flow_derivative_deviation α s q hα₀ hα₁ hs₀ hs₁
    hq ζ hζ Λ hΛ (1 / 16) (by norm_num) (by norm_num)
  obtain ⟨mC, _, hC⟩ := uniform_quiet_margin_flow_derivative_deviation α s q hα₀ hα₁ hs₀ hs₁
    hq ζ hζ Λ hΛ (1 / 16) (by norm_num) (by norm_num)
  refine ⟨max mS mC, hmS.trans (le_max_left _ _), ?_⟩
  intro D hDα hDq hDΛ hDζ hΦ hband b hb hterm S haxes t
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hκ := CycleReference.bandChain_pos hΛD hζD hband hterm
  obtain ⟨l, ht⟩ := exists_fresh_quiet_margin D b hΛD t
  let s₀ := ((l : ℝ) + 1 / 2) * ocTauPP D.α D.q D.Λ (b + 1)
  obtain ⟨tH, tV, lH, lV, hsample, hcol⟩ :=
    fresh_axes_long_columns_on_quiet_margin D b hΛD hζD hκ S.H₁ S.H₂ haxes l
  have hcols := hcol t ht
  have hsampled := hS D hDα hDq hDΛ hΦ b ((le_max_left _ _).trans hb)
    s₀ tH tV lH lV hsample
  have ht' : |t - s₀| ≤ ocTauPP D.α D.q D.Λ (b + 1) := by
    have he : ((l : ℝ) + 3 / 2) * ocTauPP D.α D.q D.Λ (b + 1) =
        s₀ + ocTauPP D.α D.q D.Λ (b + 1) := by dsimp [s₀]; ring
    rw [he] at ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hcenter := hC D hDα hDq hDΛ hΦ b ((le_max_right _ _).trans hb) s₀ t ht' 0
  let aScale := Real.sqrt ((D.κ b)⁻¹ *
    ocRefFlux D.α D.q D.Λ D.ζ (b + 1) (D.κ (b + 1)) tH 0 0)
  have ha : 1 ≤ aScale := pulseSample_long_scale_ge_one D b hΛD hζD hband hterm
    s₀ tH tV lH lV hsample
  let W := (Matrix.toLin' (S.span t)).toContinuousLinearMap
  let G := fderiv ℝ (fun y => D.flowOf b t y s₀) 0
  let HH := sampledFlowDerivative D b s₀ tH lH
  let HV := sampledFlowDerivative D b s₀ tV lV
  have hW₀ : W (basisVec 0) = aScale • G (HH (basisVec 0)) :=
    (kernelSpan_toLin_first_column S t).trans hcols.1
  have hW₁ : W (basisVec 1) = aScale • G (HV (basisVec 1)) :=
    (kernelSpan_toLin_second_column S t).trans hcols.2
  exact matrix_isUnit_and_inverse_norm_le_of_control (S.span t) 2 (by norm_num)
    (scaled_paired_column_norm_control W G HH HV aScale ha hW₀ hW₁ hcenter hsampled.1 hsampled.2)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Piola transport keeps the original positive record prices after kernel normalization. -/

section
open AVRegularity.CycleJointProofs

theorem native_transport_kernel_price
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N Dγ Dmax Kmax n dout : ℕ)
    (hD : Dγ ≤ Dmax) (hkn : n ≤ Kmax) (hdout : 2 ≤ dout) (_hout : dout ≤ Dmax)
    (C E ρ ν e R r Csample : ℝ)
    (hC : 1 ≤ C) (hE : 0 < E) (hρ : 0 ≤ ρ) (hρE : ρ ≤ E)
    (hν : 0 < ν) (he : 0 ≤ e) (hR : 0 < R) (hr : 0 < r)
    (hRE : 3 ≤ Dγ → R ≤ E) (hCs : 0 ≤ Csample)
    (hn : n + Dγ ≤ N)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I i, ContDiff ℝ (n : ℕ) (fun x => B d I x i))
    (θ : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hθ : ∀ d I, 0 ≤ θ d I)
    (hBj : ∀ d ∈ Finset.Icc dout Dγ, ∀ I i j, j ≤ n → ∀ y,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B d I x i) y‖ ≤
        Csample * (ν * e ^ (d - 2)) * θ d I)
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Cmap : U →L[ℝ] V) (x : Vec 2) :
    (ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly (dout - 1) Cmap
      (fun a A => transportedCoeff K Dγ (fun d I => B d I y) (dout - 1) A y a)) x‖) /
        (ν * r ^ (dout - 2)) ≤
      ∑ _a : Fin 2, ∑ _A : DerivativeWord2 (dout - 1), ‖Cmap‖ *
        (∑ d ∈ Finset.Icc dout Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
          (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * C *
            (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dmax) * Csample *
              (θ d I * (e / R) ^ (d - 2) * max 1 ((R / r) ^ (Dγ - 2)))) := by
  have hd : dout - 1 + 1 = dout := by omega
  have hsub (d : ℕ) (h : d ∈ Finset.Icc dout Dγ) : d - 1 - (dout - 1) = d - dout := by
    have := (Finset.mem_Icc.mp h).1
    omega
  have hh := uniform_native_transport_assembly_jet_bound K hK N Dγ Dmax Kmax n
    (dout - 1) hD hkn C E ρ hC hE hρ hρE hn hKC B hB
    (fun d I => Csample * (ν * e ^ (d - 2)) * θ d I)
    (fun d I => mul_nonneg (mul_nonneg hCs (mul_nonneg hν.le (pow_nonneg he _))) (hθ d I))
    (by simpa only [hd] using hBj) Cmap x
  apply (div_le_div_of_nonneg_right hh (mul_nonneg hν.le (pow_nonneg hr.le _))).trans
  simp only [hd, Finset.sum_div, mul_div_assoc]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro A _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro d hdin
  apply Finset.sum_le_sum
  intro I _
  apply Finset.sum_le_sum
  intro i _
  rw [hsub d hdin]
  have hp := lowered_kernel_order_price_le_max_of_gap ν e E R r hν he hE hR hr
    dout d Dγ (fun hgap => hRE (by have := (Finset.mem_Icc.mp hdin).2; omega)) hdout (Finset.mem_Icc.mp hdin).1
      ((Finset.mem_Icc.mp hdin).1.trans (Finset.mem_Icc.mp hdin).2)
  have hc : 0 ≤ (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * C *
      (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dmax) * Csample * θ d I := by
    have hθd := hθ d I
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    positivity
  have ht := mul_le_mul_of_nonneg_left hp hc
  convert ht using 1 <;> ring
end

/-! The actual transported array kernel price is controlled by its original record. -/

section
open AVRegularity.CycleJointProofs

theorem native_transport_record_price
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N Dγ Dmax Kmax n dout : ℕ)
    (hD : Dγ ≤ Dmax) (hkn : n ≤ Kmax) (hdout : 2 ≤ dout) (hout : dout ≤ Dmax)
    (C E ρ ν e R r Csample : ℝ)
    (hC : 1 ≤ C) (hE : 0 < E) (hρ : 0 ≤ ρ) (hρE : ρ ≤ E)
    (hν : 0 < ν) (he : 0 ≤ e) (hR : 0 < R) (hr : 0 < r)
    (hRE : 3 ≤ Dγ → R ≤ E) (hCs : 0 ≤ Csample)
    (hn : n + Dγ ≤ N)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I i, ContDiff ℝ (n : ℕ) (fun x => B d I x i))
    (θ : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hθ : ∀ d I, 0 ≤ θ d I)
    (hBj : ∀ d ∈ Finset.Icc dout Dγ, ∀ I i j, j ≤ n → ∀ y,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B d I x i) y‖ ≤
        Csample * (ν * e ^ (d - 2)) * θ d I)
    (size : ℝ) (hsize : 0 ≤ size)
    (hledger : ∀ d, 2 ≤ d → d ≤ Dγ → (e / R) ^ (d - 2) * ∑ I, θ d I ≤ size)
    {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Cmap : U →L[ℝ] V) (x : Vec 2) :
    (ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly (dout - 1) Cmap
      (fun a A => transportedCoeff K Dγ (fun d I => B d I y) (dout - 1) A y a)) x‖) /
        (ν * r ^ (dout - 2)) ≤
      4 * (2 : ℝ) ^ Dmax * ‖Cmap‖ *
        (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * C *
          (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dmax) * Csample *
            max 1 ((R / r) ^ (Dγ - 2)) * (Dγ : ℝ) * size := by
  have hh := native_transport_kernel_price K hK N Dγ Dmax Kmax n dout
    hD hkn hdout hout C E ρ ν e R r Csample hC hE hρ hρE hν he hR hr hRE hCs
    hn hKC B hB θ hθ hBj Cmap x
  apply hh.trans
  apply positive_transport_record_budget e R (max 1 ((R / r) ^ (Dγ - 2))) _ Csample ‖Cmap‖ size
    (le_trans zero_le_one (le_max_left _ _)) _ hCs (norm_nonneg _) hsize
    dout Dγ Dmax hdout hout θ hledger
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  positivity
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! The native slot certificate gives exact transversality of every actual lift edge. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_lift_fiber_transverse (G : GenStage D hr Dm bw j₀)
    (hpar : G.IsSlotTransverse) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (p : OddSlot) (ρ : ℝ) :
    ∀ v u d, ∀ γ ∈ (familyLiftData D G.level p.1 (nativeChain G.level p.1) ρ
      (G.fam.fiber p (G.actual p))).edge v u d, ∀ α,
      IsTransverseOn (slotParallel p.1)
        (Set.Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
          ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level))
        (γ.coeff α) := by
  apply liftEdges_transverse
  · intro t ht
    exact EntryWeakProofs.weak_lift_clock_in_pulse_window D hΛ hζ hband G.level p.1 t ht
  · intro v u d γ hγ α t ht X z r
    obtain ⟨δ, _hd, he⟩ := fiber_coefficient_identity G.fam p (G.actual p) v u d γ hγ
    rw [he]
    exact hpar p (G.actual p) v u δ d.1 α t ht X z r

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

/-! Native context certificates give time measurability of the actual lift edge coefficients. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
  [∀ r, InnerProductSpace ℝ (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_lift_fiber_measurable (G : GenStage D hr Dm bw j₀)
    (k : InvConsts) (hcert : G.IsContextCertified k) (p : OddSlot) (ρ : ℝ)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) :
    ∀ v u d, ∀ γ ∈ (familyLiftData D G.level p.1 (nativeChain G.level p.1) ρ
      (G.fam.fiber p (G.actual p))).edge v u d, ∀ α X z,
      Measurable (fun t : Set.Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
        ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) =>
          γ.coeff α t X z) := by
  intro v u d γ hγ α X z
  obtain ⟨δ', hδ', rfl⟩ := List.mem_map.mp hγ
  obtain ⟨δ, _hd, he⟩ := fiber_coefficient_identity G.fam p (G.actual p) v u d δ' hδ'
  dsimp only
  rw [he]
  have hm := Buffer.contextCertified_flux_time_measurable_vec hcert p (G.actual p)
    v u δ d.1 α ((ρ / D.eps (G.level - 1)) • X) z
  let clock : Set.Icc (D.slotStart G.level p.1 / D.cellScaleSq G.level)
      ((((p.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) →
      ocPulseWindow D.α D.q D.Λ G.level p.1 := fun t =>
    ⟨D.cellScaleSq G.level * t.1,
      EntryWeakProofs.weak_lift_clock_in_pulse_window D hΛ hζ hband G.level p.1 t.1 t.2⟩
  exact hm.comp ((measurable_const.mul measurable_subtype_coe).subtype_mk : Measurable clock)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! Native metric and shear regularity instantiate the qualitative lift-setting fields. -/

open AVRegularity.EntryWeakProofs
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

theorem native_lift_metric_qualitative (D : OCData) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (ρ : ℝ) (edge : ConstituentEdges Dm h) :
    (∀ t X i j, (familyLiftData D m slot (nativeChain m slot) ρ edge).G t X i j =
      (familyLiftData D m slot (nativeChain m slot) ρ edge).G t X j i) ∧
    (∀ X i j, Measurable fun t =>
      (familyLiftData D m slot (nativeChain m slot) ρ edge).G t X i j) ∧
    (∀ t i j, ContDiff ℝ (⊤ : ℕ∞) fun X =>
      (familyLiftData D m slot (nativeChain m slot) ρ edge).G t X i j) := by
  exact ⟨familyLiftData_metric_symmetric D m slot (nativeChain m slot) ρ edge,
    familyLiftData_metric_measurable D hζ m slot (nativeChain m slot) rfl ρ edge,
    familyLiftData_metric_entry_smooth D m slot (nativeChain m slot) rfl ρ edge⟩

theorem native_lift_shear_qualitative (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (m : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm h) :
    (∀ t z, (familyLiftData D m slot A ρ edge).v t z =
      pulseShearProfile D.α D.q D.Λ m D.ζ (D.kap m) slot t
        (z (pulseParallel slot).rev) • basisVec (pulseParallel slot)) ∧
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (pulseShearProfile D.α D.q D.Λ m D.ζ (D.kap m) slot t)) ∧
    (∀ t, Function.Periodic (pulseShearProfile D.α D.q D.Λ m D.ζ (D.kap m) slot t) 1) ∧
    (∀ t, (∫ x in (0 : ℝ)..1, pulseShearProfile D.α D.q D.Λ m D.ζ (D.kap m) slot t x) = 0) ∧
    (∀ z, Measurable fun t => (familyLiftData D m slot A ρ edge).v t z) := by
  have hν := weakData_kap_pos D hΛ hζ hκ m
  refine ⟨normalizedPulseDrift_shear hΛ hν hslot,
    pulseShearProfile_contDiff D.α D.q D.Λ m D.ζ (D.kap m) slot,
    pulseShearProfile_periodic D.α D.q D.Λ m D.ζ (D.kap m) slot,
    pulseShearProfile_mean_zero D.α D.q D.Λ m D.ζ (D.kap m) slot, ?_⟩
  intro z
  exact ((normalizedPulseDrift_joint_continuous hΛ hν hζ hslot).comp
    (continuous_id.prodMk continuous_const)).measurable

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.FullLift

/-! Native lift metrics and actual torus-compatible source fibers share the physical slow lattice. -/

theorem native_familyLiftData_metric_shift {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}
    (D : OCData) (m : ℕ) (hm : 1 ≤ m) (slot : ℤ) {ρ : ℝ} (hρ : ρ ≠ 0)
    (edge : ConstituentEdges Dm h) (p : Fin 2 → ℤ) (s : ℝ) (X : Vec 2) :
    (familyLiftData D m slot (nativeChain m slot) ρ edge).G s (X + ρ⁻¹ • latticeShift p) =
      (familyLiftData D m slot (nativeChain m slot) ρ edge).G s X := by
  have hjac : jacMatrix (fun y => D.flowOf (m - 1) (D.cellScaleSq m * s) y
      (D.slotAnchor m slot)) (ρ • (X + ρ⁻¹ • latticeShift p)) =
      jacMatrix (fun y => D.flowOf (m - 1) (D.cellScaleSq m * s) y
        (D.slotAnchor m slot)) (ρ • X) := by
    rw [CycleComparison.Assembly.smul_add_inv_smul hρ]
    exact CycleReference.streamFlow_jacMatrix_spatial_periodic (D.hΦ (m - 1))
      (D.cellScaleSq m * s) (D.slotAnchor m slot) (ρ • X) p
  exact (EntryWeakProofs.native_familyLiftData_metric D m hm slot ρ edge s _).trans
    ((congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      fun i j => (M⁻¹ * Matrix.transpose M⁻¹) i j) hjac).trans
      (EntryWeakProofs.native_familyLiftData_metric D m hm slot ρ edge s X).symm)

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_familyLiftData_edge_coeff_shift (G : GenStage D hr Dm bw j₀)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (slot : OddSlot) {ρ : ℝ} (hρ : ρ ≠ 0) (p : Fin 2 → ℤ)
    (v u : CompIn G.comps) (d : Finset.Icc 2 Dm)
    (γ : Constituent d.1 (hr u.1.root) (hr v.1.root))
    (hγ : γ ∈ (familyLiftData D G.level slot.1 (nativeChain G.level slot.1) ρ
      (G.fam.fiber slot (G.actual slot))).edge v u d)
    (α : AVRegularity.Sobolev.DerivativeWord2 (d.1 - 1)) (t : ℝ) (X z : Vec 2) :
    γ.coeff α t (X + ρ⁻¹ • latticeShift p) z = γ.coeff α t X z := by
  exact CycleComparison.Assembly.liftEdges_fiber_coeff_shift hρ htorus
    (D.cellScaleSq G.level) slot p hγ α t X z

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.FullLift

/-! The physical diagonal pulse is periodic when its slow and fast lattices agree with integer shifts. -/

open CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem pulsePhysicalLift_static_periodic (c ρ e εc : ℝ) (N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (Φ Ψ : Vec 2 → Vec 2)
    (f : Vec 2 → ∀ i, h i) (t : ℝ) (hρ : ρ ≠ 0) {J : ℕ} (he : e⁻¹ = J)
    (hΦ : ∀ p Y, Φ (Y + latticeShift p) = Φ Y + latticeShift p)
    (hΨ : ∀ p Y, Ψ (Y + latticeShift p) = Ψ Y + latticeShift p)
    (hf : IsZ2Periodic f)
    (hslow : ∀ hh ≤ H, ∀ n ≤ N, ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ p X z v u,
      Cc hh n m α (c⁻¹ * t) (X + ρ⁻¹ • latticeShift p) z v u =
        Cc hh n m α (c⁻¹ * t) X z v u)
    (hfast : ∀ hh ≤ H, ∀ n ≤ N, ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ X v u,
      IsZ2Periodic (fun z => Cc hh n m α (c⁻¹ * t) X z v u)) :
    IsZ2Periodic (pulsePhysicalLift c ρ e εc N H Cc
      (fun _ => Φ) (fun _ => Ψ) (fun _ => f) t) := by
  intro p x
  have hinput (Y : Vec 2) : f (Φ (ρ • (Y + ρ⁻¹ • latticeShift p))) = f (Φ (ρ • Y)) := by
    rw [CycleComparison.Assembly.smul_add_inv_smul hρ, hΦ p, hf p]
  funext v
  rw [pulsePhysicalLift_static_expansion, pulsePhysicalLift_static_expansion,
    hΨ p, smul_add, smul_add, he, TorusCompatible.natCast_smul_latticeShift]
  refine Finset.sum_congr rfl fun hh hhh => ?_
  refine Finset.sum_congr rfl fun n hn => ?_
  have hhH : hh ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  apply congrArg (fun y : h v => εc ^ n • y)
  have hz := liftApply_periodic_of_coefficients n (Cc hh n) (fun _ Y => f (Φ (ρ • Y)))
    (c⁻¹ * t) (ρ⁻¹ • Ψ x + ρ⁻¹ • latticeShift p)
    (fun m hm α v u => hfast hh hhH n hnN m hm α _ v u)
    (fun i => (J : ℤ) * p i) ((J : ℝ) • Ψ x)
  have hX := liftApply_slow_translation_invariant n (Cc hh n) (fun _ Y => f (Φ (ρ • Y)))
    (c⁻¹ * t) (ρ⁻¹ • latticeShift p)
    (fun m hm α X z v u => hslow hh hhH n hnN m hm α p X z v u)
    hinput (ρ⁻¹ • Ψ x) ((J : ℝ) • Ψ x)
  exact congrFun (hz.trans hX) v

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! The compiled scheduled metric theorem gives global native ellipticity at one data-independent threshold. -/

section
open AVRegularity.EntryWeakProofs
theorem uniform_native_lift_ellipticity_all_carriers (α s q : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
      [∀ i, NormedSpace ℝ (h i)] (Dm : ℕ), ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ m, M + 1 ≤ m → ∀ slot : ℤ, Odd slot →
      ∀ (ρ : ℝ) (edge : ConstituentEdges Dm h),
      ∀ t ∈ Set.Icc (D.slotStart m slot / D.cellScaleSq m)
        ((((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m),
      ∀ X ξ : Vec 2,
        (3 / 4) * ∑ i, ξ i ^ 2 ≤
          ∑ i, ∑ j, (familyLiftData D m slot (nativeChain m slot) ρ edge).G t X i j * ξ i * ξ j ∧
        ∑ i, ∑ j, (familyLiftData D m slot (nativeChain m slot) ρ edge).G t X i j * ξ i * ξ j ≤
          (5 / 4) * ∑ i, ξ i ^ 2 := by
  obtain ⟨M, hM, hb⟩ := uniform_scheduled_weak_metric_eventually_elliptic
    α s q hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ 0
  refine ⟨M, hM, ?_⟩
  intro ι h _ _ Dm D hDα hDq hDΛ hDζ hseq hband m hm slot hslot ρ edge t ht X ξ
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hζ
  have hctx : (nativeChain m slot).ctxLevel = m := by
    simp only [nativeChain, RealChain.ctxLevel, RealChain.lastLevel, List.length_nil]
    omega
  exact hb D hDα hDq hDΛ hDζ hseq (nativeChain m slot) m slot (by change M ≤ m - 1; omega)
    (by simp [nativeChain]) hctx rfl (by simp [nativeChain, RealChain.slot])
    (by
      intro q hq
      have he : q = slot := by simpa only [nativeChain, List.mem_singleton] using hq
      exact he.symm ▸ hslot)
    (by intro k hk; simp only [nativeChain, List.length_singleton] at hk; omega)
    (D.cellScaleSq m * t) (weak_lift_clock_in_pulse_window D hΛD hζD hband m slot t ht) (ρ • X) ξ
end

/-! The physical diagonal is one explicit map from the two independent Pi coordinate blocks. -/

section
open EntryWeakProofs

def independentDiagonalMap (a b : ℝ) : Vec 2 →L[ℝ] Vec (2 + 2) :=
  ContinuousLinearMap.pi (Fin.addCases
    (fun i : Fin 2 => a • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ))
    (fun i : Fin 2 => b • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)))

theorem independentDiagonalMap_apply (a b : ℝ) (X : Vec 2) :
    independentDiagonalMap a b X = independentIntrinsicParameterPacking 2 (a • X) (b • X) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [independentDiagonalMap, independentIntrinsicParameterPacking,
      ContinuousLinearMap.pi_apply, smul_apply, ContinuousLinearMap.proj_apply,
      Pi.smul_apply, Fin.addCases_left, Fin.addCases_right]

theorem independentDiagonalMap_norm_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖independentDiagonalMap a b‖ ≤ max a b := by
  apply ContinuousLinearMap.opNorm_le_bound _ (ha.trans (le_max_left _ _))
  intro X
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (ha.trans (le_max_left _ _)) (norm_nonneg X))).2
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [independentDiagonalMap, ContinuousLinearMap.pi_apply, Fin.addCases_left,
      smul_apply, ContinuousLinearMap.proj_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm X j) ha).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg X))
  · simp only [independentDiagonalMap, ContinuousLinearMap.pi_apply, Fin.addCases_right,
      smul_apply, ContinuousLinearMap.proj_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm X j) hb).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg X))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem independent_diagonal_scaled_jet_bound (f : Vec (2 + 2) → F) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ∞) f) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hbound : ∀ j ≤ n, ∀ W, ‖iteratedFDeriv ℝ j f W‖ ≤ B j)
    (a b ρ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ : 0 ≤ ρ)
    (j : ℕ) (hj : j ≤ n) (X : Vec 2) :
    ρ ^ j * ‖iteratedFDeriv ℝ j
      (fun Y => f (independentIntrinsicParameterPacking 2 (a • Y) (b • Y))) X‖ ≤
        B j * (ρ * max a b) ^ j := by
  have hn := (linear_parameter_regular_and_jets f n hf (independentDiagonalMap a b) B hbound).2 j hj X
  have he : (f ∘ independentDiagonalMap a b) =
      (fun Y => f (independentIntrinsicParameterPacking 2 (a • Y) (b • Y))) := by
    funext Y
    rw [Function.comp_apply, independentDiagonalMap_apply]
  rw [he] at hn
  have hp := pow_le_pow_left₀ (norm_nonneg _) (independentDiagonalMap_norm_le ha hb) j
  have hh := mul_le_mul_of_nonneg_left
    (hn.trans (mul_le_mul_of_nonneg_left hp (hB j))) (pow_nonneg hρ j)
  exact hh.trans_eq (by rw [mul_pow]; ring)
end

end AVRegularity.Construction.Preservation.FullLift
end
end
