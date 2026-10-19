-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.JointSourceCongruence
public import AVRegularity.Proofs.GenSem.Jet.JetRepG

@[expose] public noncomputable section

section
open Homogenization AVRegularity
namespace AVRegularity.Providers.GenSem

/-! **D6a: Jacobian calculus of the chart maps.** The Jacobian matrix of a composition is the
product of the Jacobians; the Jacobian of the backward flow is the inverse of the Jacobian of the
forward flow at the image point; the inverse of a smooth matrix field with nonvanishing determinant
is smooth (adjugate formula). -/

theorem jacMatrix_comp {f g : Vec 2 → Vec 2} {x : Vec 2} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) :
    jacMatrix (f ∘ g) x = jacMatrix f (g x) * jacMatrix g x := by
  ext a b
  simp only [jacMatrix, Matrix.of_apply, Matrix.mul_apply, fderiv_comp x hf hg,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  conv_lhs => rw [show fderiv ℝ g x (basisVec b) = ∑ c : Fin 2, (fderiv ℝ g x (basisVec b) c) •
    basisVec c by
      funext a'
      simp [Finset.sum_apply, basisVec, Pi.single_apply]]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem jacMatrix_id (x : Vec 2) : jacMatrix (fun y => y) x = 1 := by
  ext a b
  simp only [jacMatrix, Matrix.of_apply, fderiv_fun_id, ContinuousLinearMap.id_apply, basisVec,
    Matrix.one_apply, Pi.single_apply]

/-- **The Jacobian of the backward flow** is the inverse of the forward Jacobian. -/
theorem jacMatrix_backward {g : ChainGeom} (hg : AVRegularity.Providers.GenSem.IsFlowGeom g)
    (hs : EntryWeakProofs.GeomSpatialSmooth g) (t s : ℝ) (Q : Vec 2) :
    jacMatrix (fun Q' => g.1 s Q' t) Q = (jacMatrix (fun y => g.1 t y s) (g.1 s Q t))⁻¹ := by
  have hφ : DifferentiableAt ℝ (fun Q' => g.1 s Q' t) Q :=
    ((hs s t).differentiable (by simp)) Q
  have hψ : DifferentiableAt ℝ (fun y => g.1 t y s) (g.1 s Q t) :=
    ((hs t s).differentiable (by simp)) _
  have hid : (fun y => g.1 t y s) ∘ (fun Q' => g.1 s Q' t) = fun y => y := by
    funext y; exact hg.inv t s y
  have h1 : jacMatrix (fun y => g.1 t y s) (g.1 s Q t) * jacMatrix (fun Q' => g.1 s Q' t) Q = 1 := by
    rw [← jacMatrix_comp hψ hφ, hid, jacMatrix_id]
  exact (Matrix.inv_eq_right_inv h1).symm

/-- The forward Jacobian of a flow geometry is invertible. -/
theorem isUnit_det_jac {g : ChainGeom} (hg : AVRegularity.Providers.GenSem.IsFlowGeom g)
    (hs : EntryWeakProofs.GeomSpatialSmooth g) (t s : ℝ) (y : Vec 2) :
    IsUnit (jacMatrix (fun y => g.1 t y s) y).det := by
  have hφ : DifferentiableAt ℝ (fun Q' => g.1 s Q' t) (g.1 t y s) :=
    ((hs s t).differentiable (by simp)) _
  have hψ : DifferentiableAt ℝ (fun y => g.1 t y s) (g.1 s (g.1 t y s) t) :=
    ((hs t s).differentiable (by simp)) _
  have hid : (fun y => g.1 t y s) ∘ (fun Q' => g.1 s Q' t) = fun y => y := by
    funext y; exact hg.inv t s y
  have h1 := jacMatrix_comp hψ hφ
  rw [hid, jacMatrix_id, hg.inv s t y] at h1
  exact Matrix.isUnit_det_of_right_inverse h1.symm

/-- The inverse of a smooth `2 × 2` matrix field with nonvanishing determinant is smooth. -/
theorem contDiff_matrix_inv {n : WithTop ℕ∞} {M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hM : ∀ a b, ContDiff ℝ n (fun y => M y a b)) (hdet : ∀ y, (M y).det ≠ 0) (a b : Fin 2) :
    ContDiff ℝ n (fun y => (M y)⁻¹ a b) := by
  have hd : ContDiff ℝ n (fun y => (M y).det) := by
    simp only [Matrix.det_fin_two]
    exact ((hM 0 0).mul (hM 1 1)).sub ((hM 0 1).mul (hM 1 0))
  have hinv : ContDiff ℝ n (fun y => ((M y).det)⁻¹) := hd.inv hdet
  have e : ∀ y, (M y)⁻¹ a b = ((M y).det)⁻¹ * (M y).adjugate a b := by
    intro y
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  simp_rw [e]
  refine hinv.mul ?_
  rw [show (fun y => (M y).adjugate a b) = fun y => (M y).adjugate a b from rfl]
  simp only [Matrix.adjugate_fin_two, Matrix.of_apply]
  fin_cases a <;> fin_cases b <;> simp [hM, (hM _ _).neg]

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Providers.GenSem

/-! **D6a: jets of the chart maps.** The family letters `famLetter L` (the mean over the internal
phase of the restriction of the geometric letter `L` of the own frame) denote the letters of the
last family. The centered map `𝒜_t = famMap` and its inverse `famMapInv` have represented jets of
every order at `0`: the derivative of `𝒜_t` at `w` is the Jacobian of the recentered family
(covariant), and the derivative of the inverse is the inverse Jacobian of the recentered family at
`𝒜_t⁻¹ x` (chain rule for jets). -/

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {p : ℤ}
  {W : Set (ℝ × RealChain)}

/-- The family letter of the geometric letter `L` (own frame). -/
def famLetter (i : ℕ) (p : ℤ) (L : GeoLetter) : Gen .fam i p :=
  Gen.mean (Gen.restrict (Gen.geo .own L))

theorem famLetter_rep (L : GeoLetter) :
    Gen.IsScheduled D (famLetter i p L) ∧ Gen.FromSeed 𝒮 (famLetter i p L) ∧
      ∃ f : GenSort.Sem .fam, Gen.Denotes D bw j₀ (famLetter i p L) f ∧
        ∀ t ch, f t ch = L.evalAt D ch t := by
  refine ⟨.mean (.restrict (.geoOwn L)), .mean (.restrict (.geo _ _)), _,
    .mean (.restrict (.geo _ _)), fun t ch => ?_⟩
  show ∫ η in AVenhance.unitCube, L.evalAt D ch t = _
  rw [setIntegral_const]
  have hvol : (volume AVenhance.unitCube).toReal = 1 := by
    simp [AVenhance.unitCube, volume_pi_pi]
  simp [Measure.real, hvol]

theorem contDiff_famMap (A : RealChain) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (A.famMap D t) := by
  have h := EntryWeakProofs.geomSpatialSmooth_geom D A t (A.geom D).2.2
  exact (h.comp (contDiff_const.add contDiff_id)).sub contDiff_const

theorem contDiff_famMapInv (A : RealChain) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (A.famMapInv D t) := by
  have h := EntryWeakProofs.geomSpatialSmooth_geom D A (A.geom D).2.2 t
  exact (h.comp (contDiff_const.add contDiff_id)).sub contDiff_const

theorem famMap_zero (A : RealChain) (t : ℝ) : A.famMap D t 0 = 0 := by
  simp [RealChain.famMap]

theorem famMapInv_zero (hζ : IsFastProfile D.ζ) (A : RealChain) (t : ℝ) : A.famMapInv D t 0 = 0 := by
  simp only [RealChain.famMapInv, add_zero]
  rw [(isFlowGeom_geom D hζ A).inv, sub_self]

/-- The derivative of the centered map is the Jacobian of the recentered family. -/
theorem dLabel_famMap (hζ : IsFastProfile D.ζ) (A : RealChain) (hA : A.WellSlotted) (t : ℝ)
    (b j : Fin 2) (w : Vec 2) :
    fderiv ℝ (fun y => A.famMap D t y b) w (basisVec j) = (A.recenter D w).famJac D t b j := by
  rw [famJac_recenter D hζ A hA w t]
  have hs := EntryWeakProofs.geomSpatialSmooth_geom D A t (A.geom D).2.2
  have e : (fun y => A.famMap D t y b) =
      fun y => (fun y' => (A.geom D).1 t ((A.geom D).2.1 + y') (A.geom D).2.2) y b -
        (A.geom D).1 t (A.geom D).2.1 (A.geom D).2.2 b := by
    funext y; simp [RealChain.famMap]
  rw [e, fderiv_sub_const]
  have hd : DifferentiableAt ℝ (fun y' => (A.geom D).1 t ((A.geom D).2.1 + y') (A.geom D).2.2) w :=
    ((hs.comp (contDiff_const.add contDiff_id)).differentiable (by simp)) w
  rw [fderiv_component hd b j]
  simp only [jacMatrix, Matrix.of_apply]
  set F : Vec 2 → Vec 2 := fun y => (A.geom D).1 t y (A.geom D).2.2
  show fderiv ℝ (fun y' => F ((A.geom D).2.1 + y')) w (basisVec j) b = _
  rw [fderiv_comp_add_left]

/-- **Jets of the centered map.** -/
theorem jetRep_famMap (hζ : IsFastProfile D.ζ) (hW : ∀ q ∈ W, q.2.WellSlotted) :
    ∀ (r : ℕ) (b : Fin 2), JetRep D bw j₀ 𝒮 i p W r (fun t A y => A.famMap D t y b)
  | 0, b => (IsFamRepOn.const 0).congr fun q _ => by
      show q.2.famMap D q.1 0 b = 0
      rw [famMap_zero]; rfl
  | r + 1, b => ⟨(IsFamRepOn.const 0).congr fun q _ => by
      show q.2.famMap D q.1 0 b = 0
      rw [famMap_zero]; rfl, fun j => by
      obtain ⟨hs, hf, f, hd, hv⟩ := famLetter_rep (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮)
        (i := i) (p := p) (.jac b j)
      exact jetRep_covariant hζ r hs hf hd fun q hq w => by
        simp only [dLabel]
        rw [dLabel_famMap hζ q.2 (hW q hq) q.1 b j w, hv]
        rfl⟩

/-- The entries of the Jacobian of a smooth map are smooth. -/
theorem contDiff_jacMatrix_entry {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => jacMatrix f y a b) := by
  simp only [jacMatrix, Matrix.of_apply]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (basisVec b)) :=
    (hf.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by norm_cast)).clm_apply contDiff_const
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) a).contDiff.comp h1

/-- The inverse Jacobian of the recentered family is smooth in the recentering offset. -/
theorem contDiff_famJacInv (hζ : IsFastProfile D.ζ) (A : RealChain) (hA : A.WellSlotted) (t : ℝ)
    (a b : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun w => ((A.recenter D w).famJac D t)⁻¹ a b) := by
  have hs := EntryWeakProofs.geomSpatialSmooth_geom D A t (A.geom D).2.2
  have e : (fun w => ((A.recenter D w).famJac D t)⁻¹ a b) =
      fun w => (jacMatrix (fun y => (A.geom D).1 t y (A.geom D).2.2) ((A.geom D).2.1 + w))⁻¹ a b := by
    funext w; rw [famJac_recenter D hζ A hA w t]
  rw [e]
  refine contDiff_matrix_inv (M := fun w =>
    jacMatrix (fun y => (A.geom D).1 t y (A.geom D).2.2) ((A.geom D).2.1 + w)) (fun a' b' =>
      (contDiff_jacMatrix_entry hs a' b').comp (contDiff_const.add contDiff_id)) (fun w => ?_) a b
  exact (isUnit_det_jac (isFlowGeom_geom D hζ A)
    (EntryWeakProofs.geomSpatialSmooth_geom D A) t (A.geom D).2.2 _).ne_zero

/-- The derivative of the inverse centered map is the inverse Jacobian of the recentered family at
the preimage. -/
theorem dLabel_famMapInv (hζ : IsFastProfile D.ζ) (A : RealChain) (hA : A.WellSlotted) (t : ℝ)
    (b j : Fin 2) (x : Vec 2) :
    fderiv ℝ (fun y => A.famMapInv D t y b) x (basisVec j) =
      ((A.recenter D (A.famMapInv D t x)).famJac D t)⁻¹ b j := by
  set g := A.geom D
  have hgF := isFlowGeom_geom D hζ A
  have hsm := EntryWeakProofs.geomSpatialSmooth_geom D A
  set P := g.1 t g.2.1 g.2.2
  have e : (fun y => A.famMapInv D t y b) =
      fun y => (fun Q => g.1 g.2.2 Q t) (P + y) b - g.2.1 b := by
    funext y; simp [RealChain.famMapInv, g, P]
  rw [e, fderiv_sub_const]
  have hd : DifferentiableAt ℝ (fun y => (fun Q => g.1 g.2.2 Q t) (P + y)) x :=
    (((hsm g.2.2 t).comp (contDiff_const.add contDiff_id)).differentiable (by simp)) x
  rw [fderiv_component hd b j]
  set F : Vec 2 → Vec 2 := fun Q => g.1 g.2.2 Q t
  show fderiv ℝ (fun y => F (P + y)) x (basisVec j) b = _
  rw [fderiv_comp_add_left]
  have hjac := jacMatrix_backward hgF hsm t g.2.2 (P + x)
  have h1 : fderiv ℝ F (P + x) (basisVec j) b = jacMatrix F (P + x) b j := rfl
  rw [h1, hjac, famJac_recenter D hζ A hA _ t]
  simp [RealChain.famMapInv, g, P]

/-- **Jets of the inverse centered map.** -/
theorem jetRep_famMapInv (hζ : IsFastProfile D.ζ) (hW : ∀ q ∈ W, q.2.WellSlotted) :
    ∀ (r : ℕ) (b : Fin 2), JetRep D bw j₀ 𝒮 i p W r (fun t A x => A.famMapInv D t x b)
  | 0, b => (IsFamRepOn.const 0).congr fun q _ => by
      show q.2.famMapInv D q.1 0 b = 0
      rw [famMapInv_zero hζ]; rfl
  | r + 1, b => ⟨(IsFamRepOn.const 0).congr fun q _ => by
      show q.2.famMapInv D q.1 0 b = 0
      rw [famMapInv_zero hζ]; rfl, fun j => by
      obtain ⟨hs, hf, f, hd, hv⟩ := famLetter_rep (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮)
        (i := i) (p := p) (.jacInv b j)
      have hG : JetRep D bw j₀ 𝒮 i p W r
          (fun t A w => ((A.recenter D w).famJac D t)⁻¹ b j) :=
        jetRep_covariant hζ r hs hf hd fun q _ w => by rw [hv]; rfl
      have hcomp := JetRep.comp (r := r) (g := fun t A w => ((A.recenter D w).famJac D t)⁻¹ b j)
        (Ψ := fun t A x => A.famMapInv D t x) (fun q _ => famMapInv_zero hζ q.2 q.1)
        (fun q hq => (contDiff_famJacInv hζ q.2 (hW q hq) q.1 b j).of_le (by exact_mod_cast le_top))
        (fun q _ => (contDiff_famMapInv q.2 q.1).of_le (by exact_mod_cast le_top)) hG
        (fun b' => jetRep_famMapInv hζ hW r b')
      refine hcomp.congr_germ fun q hq => Filter.Eventually.of_forall fun x => ?_
      simp only [dLabel]
      rw [dLabel_famMapInv hζ q.2 (hW q hq) q.1 b j x]⟩

end AVRegularity.Providers.GenSem
end
