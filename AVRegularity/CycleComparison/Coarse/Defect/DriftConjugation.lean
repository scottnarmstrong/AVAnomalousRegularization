-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.Fact.GradWord
public import AVRegularity.CycleComparison.Coarse.Defect.CovCommute
public import AVRegularity.Statements.Intermediate.CycleComparison.CovarianceMatrix

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! Pointwise smooth algebra for the covariance polynomial: the gradient field `∇χ` valued in
`ℝ² ⊗ E`, the drift derivative `b·∇χ`, smoothness and periodicity of iterates of `𝒞`, commutation
of `∇` with `𝒞`, `𝖯_p`, `𝖰_p`, the splitting of `𝖯_p`, and commutation of two covariance
operators. Smooth means `ContDiff ℝ (⊤ : ℕ∞)`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `b·∇χ` for a frozen-time drift field. -/
def driftDeriv (bt : Vec 2 → Vec 2) (χ : Vec 2 → E) : Vec 2 → E :=
  fun x => ∑ k : Fin 2, bt x k • fderiv ℝ χ x (basisVec k)

/-- `∇χ` as a field valued in `ℝ² ⊗ E`. -/
def gradField (χ : Vec 2 → E) : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) :=
  fun x => WithLp.toLp 2 fun k => fderiv ℝ χ x (basisVec k)

theorem gradField_apply (χ : Vec 2 → E) (x : Vec 2) (k : Fin 2) :
    gradField χ x k = partialOp k χ x := rfl

theorem driftDeriv_apply (bt : Vec 2 → Vec 2) (χ : Vec 2 → E) (x : Vec 2) :
    driftDeriv bt χ x = ∑ k : Fin 2, bt x k • partialOp k χ x := rfl

/-! ### Smoothness -/

theorem contDiff_partialOp_top {g : Vec 2 → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (partialOp i g) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_covOperator_top (Hc : Matrix (Fin 2) (Fin 2) ℝ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (AVRegularity.covOperator Hc f) := by
  rw [covOperator_eq]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.const_smul _
    (contDiff_partialOp_top (contDiff_partialOp_top hf j) i)

theorem contDiff_covIter_top (Hc : Matrix (Fin 2) (Fin 2) ℝ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∀ l : ℕ, ContDiff ℝ (⊤ : ℕ∞) ((AVRegularity.covOperator Hc)^[l] f)
  | 0 => hf
  | l + 1 => by
    rw [Function.iterate_succ_apply']
    exact contDiff_covOperator_top Hc (contDiff_covIter_top Hc hf l)

theorem contDiff_covPolyP_top (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (AVRegularity.covPolyP Hc p f) := by
  have : AVRegularity.covPolyP Hc p f = fun x => ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[l] f x := by
    funext x; simp [AVRegularity.covPolyP, Finset.sum_apply]
  rw [this]
  exact ContDiff.sum fun l _ => ContDiff.const_smul _ (contDiff_covIter_top Hc hf l)

theorem contDiff_covPolyQ_top (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (AVRegularity.covPolyQ Hc p f) := by
  have : AVRegularity.covPolyQ Hc p f = fun x => ∑ l ∈ Finset.range (p + 1),
      (((-1 : ℝ) ^ l / (l.factorial : ℝ))) • (AVRegularity.covOperator Hc)^[l] f x := by
    funext x; simp [AVRegularity.covPolyQ, Finset.sum_apply]
  rw [this]
  exact ContDiff.sum fun l _ => ContDiff.const_smul _ (contDiff_covIter_top Hc hf l)

theorem contDiff_gradField_top {χ : Vec 2 → E} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    ContDiff ℝ (⊤ : ℕ∞) (gradField χ) :=
  contDiff_piLp' 2 fun k => contDiff_partialOp_top hχ k

theorem contDiff_gradField_nat {n : ℕ} {χ : Vec 2 → E}
    (hχ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) χ) :
    ContDiff ℝ (n : WithTop ℕ∞) (gradField χ) :=
  contDiff_piLp' 2 fun k => contDiff_partialOp hχ k

theorem contDiff_driftDeriv_top {bt : Vec 2 → Vec 2} {χ : Vec 2 → E}
    (hb : ContDiff ℝ (⊤ : ℕ∞) bt) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    ContDiff ℝ (⊤ : ℕ∞) (driftDeriv bt χ) := by
  have : driftDeriv bt χ = fun x => ∑ k : Fin 2, bt x k • partialOp k χ x := rfl
  rw [this]
  exact ContDiff.sum fun k _ => (contDiff_pi.1 hb k).smul (contDiff_partialOp_top hχ k)

/-! ### Linear maps commute with the covariance operator -/

section Clm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem partialOp_clm (Φ : E →L[ℝ] F) {g : Vec 2 → E} (hg : Differentiable ℝ g) (j : Fin 2) :
    partialOp j (fun y => Φ (g y)) = fun y => Φ (partialOp j g y) := by
  funext x
  change fderiv ℝ (fun y => Φ (g y)) x (basisVec j) = _
  have h : HasFDerivAt (fun y => Φ (g y)) (Φ.comp (fderiv ℝ g x)) x :=
    Φ.hasFDerivAt.comp x (hg x).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem clm_covOperator (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Φ : E →L[ℝ] F) {f : Vec 2 → E}
    (hf : ContDiff ℝ 2 f) (x : Vec 2) :
    Φ (AVRegularity.covOperator Hc f x) = AVRegularity.covOperator Hc (fun y => Φ (f y)) x := by
  have h1 : ∀ j, ContDiff ℝ 1 (partialOp j f) := fun j => contDiff_partialOp (k := 1) hf j
  have hj : ∀ j, partialOp j (fun y => Φ (f y)) = fun y => Φ (partialOp j f y) := fun j =>
    partialOp_clm Φ (hf.differentiable (by norm_num)) j
  have hij : ∀ i j, partialOp i (fun y => Φ (partialOp j f y)) =
      fun y => Φ (partialOp i (partialOp j f) y) := fun i j =>
    partialOp_clm Φ ((h1 j).differentiable one_ne_zero) i
  rw [covOperator_eq, covOperator_eq]
  simp only [map_sum, map_smul, hj, hij]

end Clm

/-! ### Gradient commutation -/

theorem gradField_covOperator (Hc : Matrix (Fin 2) (Fin 2) ℝ) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ 3 χ) :
    gradField (AVRegularity.covOperator Hc χ) = AVRegularity.covOperator Hc (gradField χ) := by
  funext x
  ext k
  have h := clm_covOperator Hc (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k)
    (f := gradField χ) 
    (contDiff_gradField_nat (n := 2) (by exact_mod_cast hχ)) x
  have e : (fun y => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (gradField χ y)) = partialOp k χ := rfl
  rw [e] at h
  change partialOp k (AVRegularity.covOperator Hc χ) x = _
  rw [partialOp_covOperator Hc k hχ]
  exact h.symm

theorem contDiff_top_nat {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞) f :=
  hf.of_le (by exact_mod_cast le_top)

theorem clm_covIter (Hc : Matrix (Fin 2) (Fin 2) ℝ) {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (Φ : E →L[ℝ] F) {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∀ (l : ℕ) (x : Vec 2),
      Φ ((AVRegularity.covOperator Hc)^[l] f x) =
        (AVRegularity.covOperator Hc)^[l] (fun y => Φ (f y)) x
  | 0, _ => rfl
  | l + 1, x => by
    have e : (fun y => Φ ((AVRegularity.covOperator Hc)^[l] f y)) =
        (AVRegularity.covOperator Hc)^[l] (fun y => Φ (f y)) := funext (clm_covIter Hc Φ hf l)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      clm_covOperator Hc Φ (contDiff_top_nat (contDiff_covIter_top Hc hf l) 2), e]

theorem clm_covPolyP (Hc : Matrix (Fin 2) (Fin 2) ℝ) {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (Φ : E →L[ℝ] F) (p : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) :
    Φ (AVRegularity.covPolyP Hc p f x) = AVRegularity.covPolyP Hc p (fun y => Φ (f y)) x := by
  simp only [AVRegularity.covPolyP, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul,
    clm_covIter Hc Φ hf]

theorem gradField_covIter (Hc : Matrix (Fin 2) (Fin 2) ℝ) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    ∀ l : ℕ, gradField ((AVRegularity.covOperator Hc)^[l] χ) =
      (AVRegularity.covOperator Hc)^[l] (gradField χ)
  | 0 => rfl
  | l + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      gradField_covOperator Hc (contDiff_top_nat (contDiff_covIter_top Hc hχ l) 3),
      gradField_covIter Hc hχ l]

theorem gradField_covPolyP (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    gradField (AVRegularity.covPolyP Hc p χ) = AVRegularity.covPolyP Hc p (gradField χ) := by
  funext x
  ext k
  have h := clm_covPolyP Hc (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) p
    (f := gradField χ) (contDiff_gradField_top hχ) x
  have e : (fun y => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (gradField χ y)) = partialOp k χ := rfl
  rw [e] at h
  change partialOp k (AVRegularity.covPolyP Hc p χ) x = _
  rw [← (ConstCoefOp.covPolyP (E := E) Hc p).comm k χ (contDiff_top_nat hχ _)]
  exact h.symm

/-! ### Small algebra -/

theorem covPolyP_succ (Hc : Matrix (Fin 2) (Fin 2) ℝ) (q : ℕ) (ψ : Vec 2 → E) :
    AVRegularity.covPolyP Hc (q + 1) ψ = AVRegularity.covPolyP Hc q ψ +
      (((q + 1).factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[q + 1] ψ := by
  unfold AVRegularity.covPolyP
  rw [Finset.sum_range_succ _ (q + 1)]

theorem covPolyP_eq_sub_one (Hc : Matrix (Fin 2) (Fin 2) ℝ) {p : ℕ} (hp : 1 ≤ p)
    (ψ : Vec 2 → E) :
    AVRegularity.covPolyP Hc p ψ = AVRegularity.covPolyP Hc (p - 1) ψ +
      ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[p] ψ := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simpa using covPolyP_succ Hc q ψ

theorem partialOp_partialOp_covOperator (Hc : Matrix (Fin 2) (Fin 2) ℝ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) :
    partialOp i (partialOp j (AVRegularity.covOperator Hc f)) =
      AVRegularity.covOperator Hc (partialOp i (partialOp j f)) := by
  rw [partialOp_covOperator Hc j (contDiff_top_nat hf 3),
    partialOp_covOperator Hc i (contDiff_top_nat (contDiff_partialOp_top hf j) 3)]

theorem covOperator_comm (H H' : Matrix (Fin 2) (Fin 2) ℝ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    AVRegularity.covOperator H (AVRegularity.covOperator H' ψ) =
      AVRegularity.covOperator H' (AVRegularity.covOperator H ψ) := by
  have h2 : ∀ i j, ContDiff ℝ 2 (partialOp i (partialOp j ψ)) := fun i j =>
    contDiff_top_nat (contDiff_partialOp_top (contDiff_partialOp_top hψ j) i) 2
  have hs : AVRegularity.covOperator H ψ = fun y => ∑ i : Fin 2, ∑ j : Fin 2,
      H i j • partialOp i (partialOp j ψ) y := covOperator_eq H ψ
  funext x
  conv_lhs => rw [covOperator_eq H]
  simp only [partialOp_partialOp_covOperator H' hψ]
  rw [hs, covOperator_sum H' Finset.univ
    (fun i y => ∑ j : Fin 2, H i j • partialOp i (partialOp j ψ) y)
    (fun i _ => ContDiff.sum fun j _ => ContDiff.const_smul _ (h2 i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [covOperator_sum H' Finset.univ (fun j y => H i j • partialOp i (partialOp j ψ) y)
    (fun j _ => ContDiff.const_smul _ (h2 i j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [covOperator_smul H' _ (h2 i j)]

theorem covIter_covOperator_comm (H H' : Matrix (Fin 2) (Fin 2) ℝ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∀ l : ℕ, (AVRegularity.covOperator H)^[l] (AVRegularity.covOperator H' ψ) =
      AVRegularity.covOperator H' ((AVRegularity.covOperator H)^[l] ψ)
  | 0 => rfl
  | l + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      covIter_covOperator_comm H H' hψ l,
      covOperator_comm H H' (contDiff_covIter_top H hψ l)]

theorem covPolyP_covOperator_comm (H H' : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    AVRegularity.covPolyP H p (AVRegularity.covOperator H' ψ) =
      AVRegularity.covOperator H' (AVRegularity.covPolyP H p ψ) := by
  have h2 : ∀ l, ContDiff ℝ 2 ((AVRegularity.covOperator H)^[l] ψ) := fun l =>
    contDiff_top_nat (contDiff_covIter_top H hψ l) 2
  have hs : AVRegularity.covPolyP H p ψ = fun y => ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[l] ψ y := by
    funext y; simp [AVRegularity.covPolyP, Finset.sum_apply]
  funext x
  rw [hs, covOperator_sum H' _ _ (fun l _ => ContDiff.const_smul _ (h2 l))]
  simp only [AVRegularity.covPolyP, Finset.sum_apply, Pi.smul_apply,
    covIter_covOperator_comm H H' hψ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [covOperator_smul H' _ (h2 l)]

/-! ### Periodicity -/

theorem isZ2Periodic_partialOp {f : Vec 2 → E} (hf : Differentiable ℝ f)
    (hp : AVenhance.IsZ2Periodic f) (i : Fin 2) : AVenhance.IsZ2Periodic (partialOp i f) :=
  fun n x => congrArg (fun A => A (basisVec i)) (fderiv_isZ2Periodic hf hp n x)

theorem isZ2Periodic_covOperator (Hc : Matrix (Fin 2) (Fin 2) ℝ) {f : Vec 2 → E}
    (hf : ContDiff ℝ 2 f) (hp : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (AVRegularity.covOperator Hc f) := by
  have h1 : ∀ j, ContDiff ℝ 1 (partialOp j f) := fun j => contDiff_partialOp (k := 1) hf j
  have hj : ∀ j, AVenhance.IsZ2Periodic (partialOp j f) := fun j =>
    isZ2Periodic_partialOp (hf.differentiable (by norm_num)) hp j
  intro n x
  rw [covOperator_eq]
  simp only [isZ2Periodic_partialOp ((h1 _).differentiable one_ne_zero) (hj _) _ n x]

theorem isZ2Periodic_covIter (Hc : Matrix (Fin 2) (Fin 2) ℝ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    ∀ l : ℕ, AVenhance.IsZ2Periodic ((AVRegularity.covOperator Hc)^[l] f)
  | 0 => hp
  | l + 1 => by
    rw [Function.iterate_succ_apply']
    exact isZ2Periodic_covOperator Hc (contDiff_top_nat (contDiff_covIter_top Hc hf l) 2)
      (isZ2Periodic_covIter Hc hf hp l)

theorem isZ2Periodic_covPolyP (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (AVRegularity.covPolyP Hc p f) := by
  intro n x
  simp only [AVRegularity.covPolyP, Finset.sum_apply, Pi.smul_apply,
    isZ2Periodic_covIter Hc hf hp _ n x]

theorem isZ2Periodic_covPolyQ (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (AVRegularity.covPolyQ Hc p f) := by
  intro n x
  simp only [AVRegularity.covPolyQ, Finset.sum_apply, Pi.smul_apply,
    isZ2Periodic_covIter Hc hf hp _ n x]

theorem isZ2Periodic_gradField {χ : Vec 2 → E} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hp : AVenhance.IsZ2Periodic χ) : AVenhance.IsZ2Periodic (gradField χ) := by
  intro n x
  ext k
  exact isZ2Periodic_partialOp (hχ.differentiable (by simp)) hp k n x

theorem isZ2Periodic_driftDeriv {bt : Vec 2 → Vec 2} {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hbp : AVenhance.IsZ2Periodic bt)
    (hp : AVenhance.IsZ2Periodic ψ) : AVenhance.IsZ2Periodic (driftDeriv bt ψ) := by
  intro n x
  simp only [driftDeriv_apply, hbp n x, isZ2Periodic_partialOp (hψ.differentiable (by simp)) hp _ n x]
end

/-! The commutator of the covariance operator with the frozen-time drift.

For a symmetric `Hc`, a divergence-free drift `bt` and a smooth field `χ`,
`𝒞 (b·∇χ) - b·∇(𝒞χ) = 𝒥_H^*(∇χ)`, where `𝒥_H^* ψ = ∑_j ∂_j (∑_k 𝔑_{kj} ψ_k)` is
`commutatorAdjoint`. Both sides equal `∑ H_{ij} ∂_{ij} b_a ∂_a χ + 2 ∑ H_{ij} ∂_i b_a ∂_{ja} χ`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_top_nat_of {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Vec 2 → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) : ContDiff ℝ (n : WithTop ℕ∞) f :=
  hf.of_le (by exact_mod_cast le_top)

theorem partialOp_add_fun {f g : Vec 2 → E} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (j : Fin 2) :
    partialOp j (fun y => f y + g y) = fun y => partialOp j f y + partialOp j g y := by
  funext x
  have h : HasFDerivAt (fun y => f y + g y) (fderiv ℝ f x + fderiv ℝ g x) x :=
    (hf.differentiable one_ne_zero x).hasFDerivAt.add (hg.differentiable one_ne_zero x).hasFDerivAt
  change fderiv ℝ (fun y => f y + g y) x (basisVec j) = _
  rw [h.fderiv]
  rfl

theorem partialOp_smul_fun {β : Vec 2 → ℝ} {g : Vec 2 → E} (hβ : ContDiff ℝ 1 β)
    (hg : ContDiff ℝ 1 g) (j : Fin 2) :
    partialOp j (fun y => β y • g y) = fun y => partialOp j β y • g y + β y • partialOp j g y := by
  funext x
  have h : HasFDerivAt (fun y => β y • g y)
      (β x • fderiv ℝ g x + (fderiv ℝ β x).smulRight (g x)) x :=
    (hβ.differentiable one_ne_zero x).hasFDerivAt.smul (hg.differentiable one_ne_zero x).hasFDerivAt
  change fderiv ℝ (fun y => β y • g y) x (basisVec j) = _
  rw [h.fderiv]
  simp [partialOp_apply, add_comm]

/-- A constant times a product of a scalar and a vector field. -/
theorem partialOp_term {β : Vec 2 → ℝ} {g : Vec 2 → E} (c : ℝ) (hβ : ContDiff ℝ 1 β)
    (hg : ContDiff ℝ 1 g) (j : Fin 2) :
    partialOp j (fun y => c • (β y • g y)) =
      fun y => c • (partialOp j β y • g y + β y • partialOp j g y) := by
  rw [partialOp_smul j c (f := fun y => β y • g y) (hβ.smul hg), partialOp_smul_fun hβ hg]

theorem partialOp_sum2 (l : Fin 2) (F : Fin 2 → Fin 2 → Vec 2 → E)
    (hF : ∀ k m, ContDiff ℝ 1 (F k m)) :
    partialOp l (fun y => ∑ k, ∑ m, F k m y) = fun y => ∑ k, ∑ m, partialOp l (F k m) y := by
  rw [partialOp_sum l Finset.univ (fun k y => ∑ m, F k m y)
    (fun k _ => ContDiff.sum fun m _ => hF k m)]
  funext y
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [partialOp_sum l Finset.univ (F k) (fun m _ => hF k m)]

theorem fderiv_coord {bt : Vec 2 → Vec 2} (hb : ContDiff ℝ 1 bt) (x : Vec 2) (m k : Fin 2) :
    fderiv ℝ bt x (basisVec m) k = partialOp m (fun y => bt y k) x := by
  have hd : DifferentiableAt ℝ bt x := hb.differentiable one_ne_zero x
  have h := (hasFDerivAt_pi'.1 hd.hasFDerivAt k).fderiv
  rw [partialOp_apply, h]
  rfl

/-- The commutator adjoint of a frozen-time drift, with the matrix `𝔑` expanded. -/
theorem commutatorAdjoint_eq (b : ℝ → Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (x : Vec 2) :
    AVRegularity.commutatorAdjoint b Hc t ψ x = ∑ j : Fin 2, partialOp j
      (fun y => ∑ k : Fin 2, (∑ m : Fin 2, (fderiv ℝ (b t) y (basisVec m) k * Hc m j +
        Hc k m * fderiv ℝ (b t) y (basisVec m) j)) • ψ y k) x := rfl


theorem partialOp_term_add {β β' : Vec 2 → ℝ} {g : Vec 2 → E} (c c' : ℝ) (hβ : ContDiff ℝ 1 β)
    (hβ' : ContDiff ℝ 1 β') (hg : ContDiff ℝ 1 g) (j : Fin 2) :
    partialOp j (fun y => c • (β y • g y) + c' • (β' y • g y)) =
      fun y => c • (partialOp j β y • g y + β y • partialOp j g y) +
        c' • (partialOp j β' y • g y + β' y • partialOp j g y) := by
  rw [partialOp_add_fun (f := fun y => c • (β y • g y)) (g := fun y => c' • (β' y • g y))
    ((hβ.smul hg).const_smul c) ((hβ'.smul hg).const_smul c'),
    partialOp_term c hβ hg, partialOp_term c' hβ' hg]

/-- The pointwise identity for a frozen-time drift `bt`, with `𝒥_H^*` expanded. -/
theorem covOperator_driftDeriv_sub_aux (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, Hc i j = Hc j i) {bt : Vec 2 → Vec 2} (hb : ContDiff ℝ 3 bt)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ bt x (basisVec k) k = 0) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ 3 χ) (x : Vec 2) :
    AVRegularity.covOperator Hc (driftDeriv bt χ) x - driftDeriv bt (AVRegularity.covOperator Hc χ) x =
      ∑ j : Fin 2, partialOp j
      (fun y => ∑ k : Fin 2, (∑ m : Fin 2, (fderiv ℝ bt y (basisVec m) k * Hc m j +
        Hc k m * fderiv ℝ bt y (basisVec m) j)) • gradField χ y k) x := by
  have hb1 : ContDiff ℝ 1 bt := hb.of_le (by norm_num)
  have hβ3 : ∀ k, ContDiff ℝ 3 (fun y => bt y k) := fun k => contDiff_pi.1 hb k
  have hβ1 : ∀ k, ContDiff ℝ 1 (fun y => bt y k) := fun k => (hβ3 k).of_le (by norm_num)
  have hβ2' : ∀ k m, ContDiff ℝ 2 (partialOp m (fun y => bt y k)) := fun k m =>
    contDiff_partialOp (k := 2) (hβ3 k) m
  have hβ1' : ∀ k m, ContDiff ℝ 1 (partialOp m (fun y => bt y k)) := fun k m =>
    (hβ2' k m).of_le (by norm_num)
  have hχ2 : ∀ k, ContDiff ℝ 2 (partialOp k χ) := fun k => contDiff_partialOp (k := 2) hχ k
  have hχ1 : ∀ k, ContDiff ℝ 1 (partialOp k χ) := fun k => (hχ2 k).of_le (by norm_num)
  have hχ11 : ∀ j k, ContDiff ℝ 1 (partialOp j (partialOp k χ)) := fun j k =>
    contDiff_partialOp (k := 1) (hχ2 k) j
  have dd1 : ∀ j, partialOp j (driftDeriv bt χ) = fun y => ∑ k : Fin 2,
      (partialOp j (fun y => bt y k) y • partialOp k χ y +
        bt y k • partialOp j (partialOp k χ) y) := by
    intro j
    have e : driftDeriv bt χ = fun y => ∑ k : Fin 2, bt y k • partialOp k χ y := rfl
    rw [e, partialOp_sum j Finset.univ (fun k y => bt y k • partialOp k χ y)
      (fun k _ => (hβ1 k).smul (hχ1 k))]
    funext y
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [partialOp_smul_fun (β := fun y => bt y k) (hβ1 k) (hχ1 k)]
  have dd2 : ∀ i j, partialOp i (partialOp j (driftDeriv bt χ)) = fun y => ∑ k : Fin 2,
      ((partialOp i (partialOp j (fun y => bt y k)) y • partialOp k χ y +
          partialOp j (fun y => bt y k) y • partialOp i (partialOp k χ) y) +
        (partialOp i (fun y => bt y k) y • partialOp j (partialOp k χ) y +
          bt y k • partialOp i (partialOp j (partialOp k χ)) y)) := by
    intro i j
    rw [dd1 j, partialOp_sum i Finset.univ (fun k y => partialOp j (fun y => bt y k) y •
      partialOp k χ y + bt y k • partialOp j (partialOp k χ) y)
      (fun k _ => ((hβ1' k j).smul (hχ1 k)).add ((hβ1 k).smul (hχ11 j k)))]
    funext y
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [partialOp_add_fun (f := fun y => partialOp j (fun y => bt y k) y • partialOp k χ y)
      (g := fun y => bt y k • partialOp j (partialOp k χ) y)
      ((hβ1' k j).smul (hχ1 k)) ((hβ1 k).smul (hχ11 j k)),
      partialOp_smul_fun (β := partialOp j (fun y => bt y k)) (hβ1' k j) (hχ1 k),
      partialOp_smul_fun (β := fun y => bt y k) (hβ1 k) (hχ11 j k)]
  have hcβ : ∀ k, partialOp 1 (partialOp 0 (fun y => bt y k)) =
      partialOp 0 (partialOp 1 (fun y => bt y k)) := fun k =>
    partialOp_comm ((hβ3 k).of_le (by norm_num)) 1 0
  have hcχ : partialOp 1 (partialOp 0 χ) = partialOp 0 (partialOp 1 χ) :=
    partialOp_comm (hχ.of_le (by norm_num)) 1 0
  have hd0 : ∀ y, ∑ k : Fin 2, partialOp k (fun y => bt y k) y = 0 := fun y => by
    have := hdiv y
    simp only [fderiv_coord hb1] at this
    exact this
  have hdd : ∀ m, ∑ k : Fin 2, partialOp m (partialOp k (fun y => bt y k)) x = 0 := by
    intro m
    have h1 : (fun y => ∑ k : Fin 2, partialOp k (fun y => bt y k) y) = fun _ => 0 :=
      funext hd0
    have h2 := partialOp_sum m Finset.univ (fun k => partialOp k (fun y => bt y k))
      (fun k _ => hβ1' k k)
    rw [h1] at h2
    have h3 := congrFun h2 x
    have h4 : partialOp m (fun _ : Vec 2 => (0 : ℝ)) x = 0 := by simp [partialOp_apply]
    rw [h4] at h3
    exact h3.symm
  have e00 : partialOp 0 (partialOp 0 (fun y => bt y 0)) x =
      - partialOp 0 (partialOp 1 (fun y => bt y 1)) x := by
    have := hdd 0
    simp only [Fin.sum_univ_two] at this
    linarith
  have e11 : partialOp 1 (partialOp 1 (fun y => bt y 1)) x =
      - partialOp 0 (partialOp 1 (fun y => bt y 0)) x := by
    have := hdd 1
    simp only [Fin.sum_univ_two, hcβ] at this
    linarith
  have rhsf : ∀ j, (fun y => ∑ k : Fin 2, (∑ m : Fin 2, (fderiv ℝ bt y (basisVec m) k * Hc m j +
        Hc k m * fderiv ℝ bt y (basisVec m) j)) • gradField χ y k) =
      fun y => ∑ k : Fin 2, ∑ m : Fin 2,
        (Hc m j • (partialOp m (fun y => bt y k) y • partialOp k χ y) +
          Hc k m • (partialOp m (fun y => bt y j) y • partialOp k χ y)) := by
    intro j
    funext y
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [fderiv_coord hb1, gradField_apply]
    module
  have rhs : ∀ j, partialOp j (fun y => ∑ k : Fin 2, (∑ m : Fin 2,
      (fderiv ℝ bt y (basisVec m) k * Hc m j + Hc k m * fderiv ℝ bt y (basisVec m) j)) •
        gradField χ y k) x = ∑ k : Fin 2, ∑ m : Fin 2,
      (Hc m j • (partialOp j (partialOp m (fun y => bt y k)) x • partialOp k χ x +
          partialOp m (fun y => bt y k) x • partialOp j (partialOp k χ) x) +
        Hc k m • (partialOp j (partialOp m (fun y => bt y j)) x • partialOp k χ x +
          partialOp m (fun y => bt y j) x • partialOp j (partialOp k χ) x)) := by
    intro j
    rw [rhsf j, partialOp_sum2 j (fun k m y =>
      Hc m j • (partialOp m (fun y => bt y k) y • partialOp k χ y) +
        Hc k m • (partialOp m (fun y => bt y j) y • partialOp k χ y))
      (fun k m => (((hβ1' k m).smul (hχ1 k)).const_smul _).add
        (((hβ1' j m).smul (hχ1 k)).const_smul _))]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
    rw [partialOp_term_add (Hc m j) (Hc k m) (hβ1' k m) (hβ1' j m) (hχ1 k)]
  have hH10 := hH 1 0
  have hCχ : ∀ k, partialOp k (AVRegularity.covOperator Hc χ) =
      AVRegularity.covOperator Hc (partialOp k χ) := fun k => partialOp_covOperator Hc k hχ
  simp only [rhs, driftDeriv_apply, hCχ]
  simp only [covOperator_eq, dd2]
  simp only [Fin.sum_univ_two, hcβ, hcχ, e00, e11, hH10]
  module


/-- `𝒞(b·∇χ) - b·∇(𝒞χ) = 𝒥_H^*(∇χ)` for a symmetric covariance, a divergence-free smooth
drift `b t` and a smooth field `χ`. -/
theorem covOperator_driftDeriv_sub_of_contDiff_three (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, Hc i j = Hc j i) (b : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hb : ContDiff ℝ 3 (b t))
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (b t) x (basisVec k) k = 0) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ 3 χ) (x : Vec 2) :
    AVRegularity.covOperator Hc (driftDeriv (b t) χ) x -
        driftDeriv (b t) (AVRegularity.covOperator Hc χ) x =
      AVRegularity.commutatorAdjoint b Hc t (gradField χ) x := by
  rw [commutatorAdjoint_eq]
  exact covOperator_driftDeriv_sub_aux Hc hH hb hdiv hχ x

/-- Function form of the commutator identity for smooth data. -/
theorem covOperator_driftDeriv_sub (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, Hc i j = Hc j i) (b : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (b t))
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (b t) x (basisVec k) k = 0) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    AVRegularity.covOperator Hc (driftDeriv (b t) χ) -
        driftDeriv (b t) (AVRegularity.covOperator Hc χ) =
      AVRegularity.commutatorAdjoint b Hc t (gradField χ) := by
  funext x
  exact covOperator_driftDeriv_sub_of_contDiff_three Hc hH b t (contDiff_top_nat_of hb 3) hdiv
    (contDiff_top_nat hχ 3) x
end

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleComparison.Coarse

/-! The covariance polynomials as time-dependent test fields.

For a window `[t₀,t₁]` and a measurable, bounded matrix flux `Jm`, the fields
`(𝒞_{H(t)})^l ψ` and `𝖯_p(H(t)) ψ`, with `H(t) = covarianceMatrix Jm B t₀ t`, are time-dependent
test fields in the sense of `TimeTest`, with time derivatives `l 𝒞_{H'(t)} 𝒞_{H(t)}^{l-1} ψ`
and `𝒞_{H'(t)} 𝖯_{p-1}(H(t)) ψ`, where `H'(t) = Jm t - B I`. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem covOperator_eq_sum (H : Matrix (Fin 2) (Fin 2) ℝ) (f : Vec 2 → E) :
    AVRegularity.covOperator H f =
      fun x => ∑ m : Fin 2 × Fin 2, H m.1 m.2 • partialOp m.1 (partialOp m.2 f) x := by
  rw [covOperator_eq]
  funext x
  rw [Fintype.sum_prod_type]

theorem contDiff_covIter (H : Matrix (Fin 2) (Fin 2) ℝ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((AVRegularity.covOperator H)^[n] ψ) := by
  induction n with
  | zero => simpa using hψ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (smoothLinOp_covOperator H).smooth _ ih

/-- The time derivative matrix `Jm t - B I` of the covariance. -/
def covRate (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)

theorem covRate_apply (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B t : ℝ) (i j : Fin 2) :
    covRate Jm B t i j = Jm t i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  simp [covRate]

section Window

variable (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B t₀ t₁ : ℝ)

theorem covRate_integrableOn (hJ_meas : ∀ i j, Measurable fun t => Jm t i j)
    (hJ_bdd : ∃ M, ∀ t ∈ Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ M) (i j : Fin 2) :
    IntegrableOn (fun s => covRate Jm B s i j) (Ioc t₀ t₁) := by
  obtain ⟨M, hM⟩ := hJ_bdd
  have hmeas : Measurable fun s => covRate Jm B s i j := by
    simp only [covRate_apply]
    exact (hJ_meas i j).sub measurable_const
  refine Measure.integrableOn_of_bounded (M := M + |B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j|)
    (by simp) hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun s hs => ?_
  rw [covRate_apply, Real.norm_eq_abs]
  exact (abs_sub _ _).trans (add_le_add (hM s ⟨hs.1.le, hs.2⟩ i j) le_rfl)

theorem covarianceMatrix_apply_eq (t : ℝ) (ht : t ∈ Icc t₀ t₁) (i j : Fin 2) :
    covarianceMatrix Jm B t₀ t i j = covarianceMatrix Jm B t₀ t₀ i j +
      ∫ s in Ioc t₀ t, covRate Jm B s i j := by
  simp only [covarianceMatrix, Matrix.of_apply, covRate_apply, intervalIntegral.integral_same,
    zero_add]
  exact intervalIntegral.integral_of_le ht.1

end Window

variable (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B t₀ t₁ : ℝ)

/-- One step: from the test field of `𝒞^l ψ` to that of `𝒞^{l+1} ψ`. -/
theorem covIter_step (ht : t₀ ≤ t₁) (hrate : ∀ i j, IntegrableOn (fun s => covRate Jm B s i j)
      (Ioc t₀ t₁)) (Φ : TimeTest E t₀ t₁) :
    ∃ Φ' : TimeTest E t₀ t₁,
      (∀ t, Φ'.val t = AVRegularity.covOperator (covarianceMatrix Jm B t₀ t) (Φ.val t)) ∧
      (∀ t, Φ'.deriv t = fun x => AVRegularity.covOperator (covRate Jm B t) (Φ.val t) x +
        AVRegularity.covOperator (covarianceMatrix Jm B t₀ t) (Φ.deriv t) x) := by
  refine ⟨TimeTest.lincomb (κ := Fin 2 × Fin 2)
    (fun m t => covarianceMatrix Jm B t₀ t m.1 m.2) (fun m t => covRate Jm B t m.1 m.2) ht
    (fun m => hrate m.1 m.2) (fun m t htm => covarianceMatrix_apply_eq Jm B t₀ t₁ t htm m.1 m.2)
    (T := fun m f => partialOp m.1 (partialOp m.2 f))
    (fun m => smoothLinOp_partialOp_partialOp m.1 m.2) Φ, fun t => ?_, fun t => ?_⟩
  · rw [TimeTest.val_lincomb, covOperator_eq_sum]
  · rw [TimeTest.deriv_lincomb, covOperator_eq_sum, covOperator_eq_sum]
    funext x
    simp only [Finset.sum_add_distrib]

/-- The covariance iterates as time-dependent test fields. -/
theorem covIter_timeTest (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B t₀ t₁ : ℝ) (ht : t₀ ≤ t₁)
    (hJ_meas : ∀ i j, Measurable fun t => Jm t i j)
    (hJ_bdd : ∃ M, ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ M)
    (ψ : Vec 2 → E) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ) (l : ℕ) :
    ∃ Φ : TimeTest E t₀ t₁,
      (∀ t ∈ Set.Icc t₀ t₁, Φ.val t = (AVRegularity.covOperator (covarianceMatrix Jm B t₀ t))^[l] ψ) ∧
      (∀ t ∈ Set.Icc t₀ t₁, Φ.deriv t = fun x => (l : ℝ) • AVRegularity.covOperator
        (Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        ((AVRegularity.covOperator (covarianceMatrix Jm B t₀ t))^[l - 1] ψ) x) := by
  have hrate := covRate_integrableOn Jm B t₀ t₁ hJ_meas hJ_bdd
  induction l with
  | zero =>
    refine ⟨TimeTest.const ψ hψ hp, fun t _ => TimeTest.val_const ψ hψ hp t, fun t _ => ?_⟩
    rw [TimeTest.deriv_const]
    funext x
    simp
  | succ l ih =>
    obtain ⟨Φ, hv, hd⟩ := ih
    obtain ⟨Φ', hv', hd'⟩ := covIter_step Jm B t₀ t₁ ht hrate Φ
    refine ⟨Φ', fun t htm => ?_, fun t htm => ?_⟩
    · rw [hv', hv t htm, Function.iterate_succ_apply']
    · have hdJ : Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ) = covRate Jm B t := rfl
      rw [hd', hv t htm, hd t htm, hdJ]
      generalize covarianceMatrix Jm B t₀ t = H
      have hC : ∀ n, ContDiff ℝ (⊤ : ℕ∞) ((AVRegularity.covOperator H)^[n] ψ) :=
        contDiff_covIter H hψ
      have hs : ContDiff ℝ 2 (AVRegularity.covOperator (covRate Jm B t)
          ((AVRegularity.covOperator H)^[l - 1] ψ)) := by
        have := (smoothLinOp_covOperator (E := E) (covRate Jm B t)).smooth _ (hC (l - 1))
        exact_mod_cast contDiff_nat_of_top this 2
      rw [covOperator_smul H (l : ℝ) hs, ttCovOperator_comm H (covRate Jm B t) (hC (l - 1))]
      funext x
      cases l with
      | zero => simp
      | succ k =>
        have e : AVRegularity.covOperator H ((AVRegularity.covOperator H)^[k] ψ) =
            (AVRegularity.covOperator H)^[k + 1] ψ := (Function.iterate_succ_apply' _ k _).symm
        simp only [Nat.add_sub_cancel, e]
        push_cast
        module

/-- The covariance polynomials as time-dependent test fields. -/
theorem covPolyP_timeTest (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B t₀ t₁ : ℝ) (ht : t₀ ≤ t₁)
    (hJ_meas : ∀ i j, Measurable fun t => Jm t i j)
    (hJ_bdd : ∃ M, ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ M)
    (ψ : Vec 2 → E) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ)
    (p : ℕ) (hp1 : 1 ≤ p) :
    ∃ Φ : TimeTest E t₀ t₁,
      (∀ t ∈ Set.Icc t₀ t₁, Φ.val t = AVRegularity.covPolyP (covarianceMatrix Jm B t₀ t) p ψ) ∧
      (∀ t ∈ Set.Icc t₀ t₁, Φ.deriv t = AVRegularity.covOperator
        (Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ t) (p - 1) ψ)) := by
  choose Ψ hv hd using fun l : Fin (p + 1) =>
    covIter_timeTest Jm B t₀ t₁ ht hJ_meas hJ_bdd ψ hψ hp l
  refine ⟨TimeTest.sum (fun l : Fin (p + 1) => ((l.val.factorial : ℝ)⁻¹)) Ψ,
    fun t htm => ?_, fun t htm => ?_⟩
  · rw [TimeTest.val_sum]
    funext x
    simp only [hv _ t htm, AVRegularity.covPolyP, Finset.sum_apply, Pi.smul_apply]
    exact Fin.sum_univ_eq_sum_range (fun l => ((l.factorial : ℝ)⁻¹) •
      (AVRegularity.covOperator (covarianceMatrix Jm B t₀ t))^[l] ψ x) (p + 1)
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    set H := covarianceMatrix Jm B t₀ t with hH
    have hC : ∀ n, ContDiff ℝ (⊤ : ℕ∞) ((AVRegularity.covOperator H)^[n] ψ) :=
      contDiff_covIter H hψ
    have hq : AVRegularity.covPolyP H (q + 1 - 1) ψ =
        fun x => ∑ l ∈ Finset.range (q + 1), ((l.factorial : ℝ)⁻¹) •
          (AVRegularity.covOperator H)^[l] ψ x := by
      funext x
      simp [AVRegularity.covPolyP, Finset.sum_apply]
    rw [TimeTest.deriv_sum, hq]
    have h2 : ∀ l ∈ Finset.range (q + 1), ContDiff ℝ 2
        (fun x => ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[l] ψ x) := fun l _ =>
      ((contDiff_nat_of_top (hC l) 2).const_smul _)
    rw [covOperator_sum _ _ _ h2]
    funext x
    simp only [hd _ t htm]
    rw [Fin.sum_univ_eq_sum_range (fun l => ((l.factorial : ℝ)⁻¹) • (l : ℝ) •
      AVRegularity.covOperator (Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        ((AVRegularity.covOperator H)^[l - 1] ψ) x) (q + 1 + 1), Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_smul, smul_zero, add_zero]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [covOperator_smul _ _ (by exact_mod_cast contDiff_nat_of_top (hC l) 2)]
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    rw [smul_smul]
    congr 1
    field_simp

end AVRegularity.CycleComparison.Coarse
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! Telescoping of the commutator `[𝒞^l, b·∇]` and the covariance-polynomial form
`𝖯_p (b·∇ψ) - b·∇ 𝖯_p ψ = ∑_{l=1}^p (1/l!) ∑_{a<l} 𝒞^{l-1-a} 𝒥_H^* 𝒞^a ∇ψ`, which is the first
summand of `coarseFluxAdjoint` applied to `∇ψ`. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem covOperator_add (Hc : Matrix (Fin 2) (Fin 2) ℝ) {f g : Vec 2 → E}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    AVRegularity.covOperator Hc (fun y => f y + g y) =
      fun y => AVRegularity.covOperator Hc f y + AVRegularity.covOperator Hc g y := by
  have hj : ∀ j, partialOp j (fun y => f y + g y) =
      fun y => partialOp j f y + partialOp j g y := fun j =>
    partialOp_add_fun (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) j
  have hij : ∀ i j, partialOp i (fun y => partialOp j f y + partialOp j g y) =
      fun y => partialOp i (partialOp j f) y + partialOp i (partialOp j g) y := fun i j =>
    partialOp_add_fun (contDiff_partialOp (k := 1) hf j) (contDiff_partialOp (k := 1) hg j) i
  funext x
  rw [covOperator_eq, covOperator_eq, covOperator_eq]
  simp only [hj, hij, smul_add, Finset.sum_add_distrib]

omit [InnerProductSpace ℝ E] in
/-- Pi-valued finite sums are pointwise sums. -/
theorem finsum_fun_eq {ι : Type*} (s : Finset ι) (F : ι → Vec 2 → E) :
    (∑ a ∈ s, F a) = fun x => ∑ a ∈ s, F a x := by
  funext x; simp [Finset.sum_apply]

section Telescope

variable (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, Hc i j = Hc j i)
  (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) (b t))
  (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (b t) x (basisVec k) k = 0)

include hH hb hdiv in
theorem contDiff_commutatorAdjoint_covIter {ψ : Vec 2 → E} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (a : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (AVRegularity.commutatorAdjoint b Hc t
      (gradField ((AVRegularity.covOperator Hc)^[a] ψ))) := by
  have hχ := contDiff_covIter_top Hc hψ a
  rw [← covOperator_driftDeriv_sub Hc hH b t hb hdiv hχ]
  exact (contDiff_covOperator_top Hc (contDiff_driftDeriv_top hb hχ)).sub
    (contDiff_driftDeriv_top hb (contDiff_covOperator_top Hc hχ))

include hH hb hdiv in
/-- Telescoping: `𝒞^l (b·∇ψ) - b·∇ 𝒞^l ψ = ∑_{a<l} 𝒞^{l-1-a} 𝒥_H^* ∇𝒞^a ψ`. -/
theorem covIter_driftDeriv_sub {ψ : Vec 2 → E} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ∀ l : ℕ, (AVRegularity.covOperator Hc)^[l] (driftDeriv (b t) ψ) -
        driftDeriv (b t) ((AVRegularity.covOperator Hc)^[l] ψ) =
      ∑ a ∈ Finset.range l, (AVRegularity.covOperator Hc)^[l - 1 - a]
        (AVRegularity.commutatorAdjoint b Hc t (gradField ((AVRegularity.covOperator Hc)^[a] ψ)))
  | 0 => by simp
  | l + 1 => by
    have ih := covIter_driftDeriv_sub hψ l
    have hJs : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (AVRegularity.commutatorAdjoint b Hc t
        (gradField ((AVRegularity.covOperator Hc)^[a] ψ))) := fun a =>
      contDiff_commutatorAdjoint_covIter Hc hH b t hb hdiv hψ a
    have hF : ∀ a ∈ Finset.range l, ContDiff ℝ (⊤ : ℕ∞)
        ((AVRegularity.covOperator Hc)^[l - 1 - a] (AVRegularity.commutatorAdjoint b Hc t
          (gradField ((AVRegularity.covOperator Hc)^[a] ψ)))) := fun a _ =>
      contDiff_covIter_top Hc (hJs a) _
    have hS : ContDiff ℝ (⊤ : ℕ∞) (∑ a ∈ Finset.range l,
        (AVRegularity.covOperator Hc)^[l - 1 - a] (AVRegularity.commutatorAdjoint b Hc t
          (gradField ((AVRegularity.covOperator Hc)^[a] ψ)))) := by
      rw [finsum_fun_eq]
      exact ContDiff.sum fun a ha => hF a ha
    have hCl := contDiff_covIter_top Hc hψ l
    have h1 : (AVRegularity.covOperator Hc)^[l] (driftDeriv (b t) ψ) =
        (fun y => driftDeriv (b t) ((AVRegularity.covOperator Hc)^[l] ψ) y +
          (∑ a ∈ Finset.range l, (AVRegularity.covOperator Hc)^[l - 1 - a]
            (AVRegularity.commutatorAdjoint b Hc t
              (gradField ((AVRegularity.covOperator Hc)^[a] ψ)))) y) := by
      rw [← ih]; funext y; simp
    have h2 := covOperator_driftDeriv_sub Hc hH b t hb hdiv hCl
    have h3 : AVRegularity.covOperator Hc (∑ a ∈ Finset.range l,
        (AVRegularity.covOperator Hc)^[l - 1 - a] (AVRegularity.commutatorAdjoint b Hc t
          (gradField ((AVRegularity.covOperator Hc)^[a] ψ)))) =
        ∑ a ∈ Finset.range l, (AVRegularity.covOperator Hc)^[l + 1 - 1 - a]
          (AVRegularity.commutatorAdjoint b Hc t
            (gradField ((AVRegularity.covOperator Hc)^[a] ψ))) := by
      rw [finsum_fun_eq, covOperator_sum Hc _ _ (fun a ha => contDiff_top_nat (hF a ha) 2),
        finsum_fun_eq]
      funext x
      refine Finset.sum_congr rfl fun a ha => ?_
      have : l + 1 - 1 - a = (l - 1 - a) + 1 := by have := Finset.mem_range.mp ha; omega
      rw [this, Function.iterate_succ_apply']
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1,
      covOperator_add Hc (contDiff_top_nat (contDiff_driftDeriv_top hb hCl) 2)
        (contDiff_top_nat hS 2), h3]
    have e0 : l + 1 - 1 - l = 0 := by omega
    rw [Finset.sum_range_succ, e0]
    funext x
    have h2x := congrFun h2 x
    simp only [Pi.sub_apply, Pi.add_apply, Function.iterate_zero, id_eq] at h2x ⊢
    rw [← h2x]
    abel

end Telescope

theorem driftDeriv_covPolyP {bt : Vec 2 → Vec 2} (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    {ψ : Vec 2 → E} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    driftDeriv bt (AVRegularity.covPolyP Hc p ψ) = ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • driftDeriv bt ((AVRegularity.covOperator Hc)^[l] ψ) := by
  have hF : ∀ l, ContDiff ℝ 1 ((AVRegularity.covOperator Hc)^[l] ψ) := fun l =>
    contDiff_top_nat (contDiff_covIter_top Hc hψ l) 1
  have hs : AVRegularity.covPolyP Hc p ψ = fun y => ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[l] ψ y := by
    funext y; simp [AVRegularity.covPolyP, Finset.sum_apply]
  have hk : ∀ (k : Fin 2) (x : Vec 2), partialOp k (AVRegularity.covPolyP Hc p ψ) x =
      ∑ l ∈ Finset.range (p + 1), ((l.factorial : ℝ)⁻¹) •
        partialOp k ((AVRegularity.covOperator Hc)^[l] ψ) x := by
    intro k x
    rw [hs, partialOp_sum k _ (fun l y => ((l.factorial : ℝ)⁻¹) •
      (AVRegularity.covOperator Hc)^[l] ψ y) (fun l _ => (hF l).const_smul _)]
    exact Finset.sum_congr rfl fun l _ => by rw [partialOp_smul k _ (hF l)]
  funext x
  simp only [driftDeriv_apply, hk, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _

/-- The conjugation of `𝖯_p` by the drift: the first summand of `coarseFluxAdjoint` applied to
`∇ψ`. -/
theorem covPolyP_driftDeriv_sub (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, Hc i j = Hc j i)
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) (b t))
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (b t) x (basisVec k) k = 0) (p : ℕ)
    {ψ : Vec 2 → E} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    AVRegularity.covPolyP Hc p (driftDeriv (b t) ψ) - driftDeriv (b t) (AVRegularity.covPolyP Hc p ψ) =
      ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
        (AVRegularity.covOperator Hc)^[l - 1 - a] (AVRegularity.commutatorAdjoint b Hc t
          ((AVRegularity.covOperator Hc)^[a] (gradField ψ))) := by
  have h0 : ∀ (l : ℕ) (x : Vec 2),
      (AVRegularity.covOperator Hc)^[l] (driftDeriv (b t) ψ) x -
        driftDeriv (b t) ((AVRegularity.covOperator Hc)^[l] ψ) x =
      ∑ a ∈ Finset.range l, (AVRegularity.covOperator Hc)^[l - 1 - a]
        (AVRegularity.commutatorAdjoint b Hc t
          ((AVRegularity.covOperator Hc)^[a] (gradField ψ))) x := by
    intro l x
    have := congrFun (covIter_driftDeriv_sub Hc hH b t hb hdiv hψ l) x
    simp only [Pi.sub_apply, Finset.sum_apply, gradField_covIter Hc hψ] at this
    exact this
  funext x
  rw [driftDeriv_covPolyP Hc p hψ]
  simp only [Pi.sub_apply, AVRegularity.covPolyP, Finset.sum_apply, Pi.smul_apply]
  rw [← Finset.sum_sub_distrib]
  simp only [← smul_sub, h0]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have e : Finset.Ico (0 + 1) (p + 1) = Finset.Icc 1 p := by ext; simp
  simp [e]

end AVRegularity.CycleComparison.Coarse
end
