-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Local
public import AVRegularity.CycleComparison.Coarse.Defect.DriftConjugation
import AVRegularity.CycleComparison.Reconstruction.PiolaTested

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! The commutator of a divergence-free drift with the covariance operator and its iterates, in
divergence form `div (commFluxE b H ψ)`, at finite regularity. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One commutator step: `b·∇(𝒞ψ) = 𝒞(b·∇ψ) + div(𝒥_H ψ)`. -/
theorem drift_step (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, H i j = H j i)
    (b : Vec 2 → Vec 2) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ b x (basisVec k) k = 0) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ 3 ψ) (x : Vec 2) :
    driftDeriv b (AVRegularity.covOperator H ψ) x =
      AVRegularity.covOperator H (driftDeriv b ψ) x + divE (commFluxE b H ψ) x := by
  have key := covOperator_driftDeriv_sub_of_contDiff_three H hH (fun _ => b) 0
    (contDiff_top_nat_of hb 3) hdiv hψ x
  rw [commutatorAdjoint_eq] at key
  have hj : ∀ j : Fin 2, (fun y => commFluxE b H ψ y j) = fun y => -(∑ k : Fin 2,
      (∑ m : Fin 2, (fderiv ℝ b y (basisVec m) k * H m j +
        H k m * fderiv ℝ b y (basisVec m) j)) • partialOp k ψ y) := fun j => by
    funext y
    simp only [commFluxE]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, jacMatrix, Matrix.of_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hH m k, hH j m]
    ring
  have hd : divE (commFluxE b H ψ) x = -(∑ j : Fin 2, partialOp j (fun y => ∑ k : Fin 2,
      (∑ m : Fin 2, (fderiv ℝ b y (basisVec m) k * H m j +
        H k m * fderiv ℝ b y (basisVec m) j)) • partialOp k ψ y) x) := by
    unfold divE
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hj j, fderiv_fun_neg]
    rfl
  rw [hd]
  have key' : AVRegularity.covOperator H (driftDeriv b ψ) x - driftDeriv b (AVRegularity.covOperator H ψ) x =
      ∑ j : Fin 2, partialOp j (fun y => ∑ k : Fin 2,
        (∑ m : Fin 2, (fderiv ℝ b y (basisVec m) k * H m j +
          H k m * fderiv ℝ b y (basisVec m) j)) • partialOp k ψ y) x := key
  rw [← key']
  abel

theorem contDiff_driftDeriv {b : Vec 2 → Vec 2} (hb : ContDiff ℝ (⊤ : ℕ∞) b) {n : ℕ}
    {g : Vec 2 → E} (hg : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) g) :
    ContDiff ℝ (n : WithTop ℕ∞) (driftDeriv b g) := by
  have e : driftDeriv b g = fun x => ∑ k : Fin 2, b x k • partialOp k g x := rfl
  rw [e]
  refine ContDiff.sum fun k _ => ?_
  have hbk : ContDiff ℝ (n : WithTop ℕ∞) (fun x => b x k) :=
    ((contDiff_pi.1 hb k).of_le (by exact_mod_cast le_top))
  exact hbk.smul (contDiff_partialOp hg k)

/-- The commutator divergence is the difference `b·∇𝒞ψ - 𝒞(b·∇ψ)`. -/
theorem div_comm_eq (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, H i j = H j i)
    (b : Vec 2 → Vec 2) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ b x (basisVec k) k = 0) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ 3 ψ) :
    (fun x => divE (commFluxE b H ψ) x) = fun x => driftDeriv b (AVRegularity.covOperator H ψ) x -
      AVRegularity.covOperator H (driftDeriv b ψ) x := by
  funext x
  rw [drift_step H hH b hb hdiv hψ x]
  abel

theorem div_comm_contDiff (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, H i j = H j i)
    (b : Vec 2 → Vec 2) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ b x (basisVec k) k = 0) {ψ : Vec 2 → E} (r : ℕ)
    (hψ : ContDiff ℝ ((r + 3 : ℕ) : WithTop ℕ∞) ψ) :
    ContDiff ℝ (r : WithTop ℕ∞) (fun x => divE (commFluxE b H ψ) x) := by
  rw [div_comm_eq H hH b hb hdiv (hψ.of_le (by exact_mod_cast (by omega : 3 ≤ r + 3)))]
  have h1 : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (AVRegularity.covOperator H ψ) :=
    contDiff_covOperator H (by exact_mod_cast hψ)
  have h2 : ContDiff ℝ ((r + 2 : ℕ) : WithTop ℕ∞) (driftDeriv b ψ) :=
    contDiff_driftDeriv hb (by exact_mod_cast hψ)
  exact (contDiff_driftDeriv hb h1).sub (contDiff_covOperator H h2)

theorem drift_iter (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, H i j = H j i)
    (b : Vec 2 → Vec 2) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ b x (basisVec k) k = 0) {φ : Vec 2 → E} :
    ∀ l : ℕ, ContDiff ℝ ((l * 2 + 1 : ℕ) : WithTop ℕ∞) φ →
      driftDeriv b ((AVRegularity.covOperator H)^[l] φ) = fun x =>
        (AVRegularity.covOperator H)^[l] (driftDeriv b φ) x +
          ∑ a ∈ Finset.range l, (AVRegularity.covOperator H)^[a]
            (fun y => divE (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y) x
  | 0, _ => by funext x; simp
  | l + 1, hφ => by
    have hφ' : ContDiff ℝ ((l * 2 + 1 : ℕ) : WithTop ℕ∞) φ :=
      hφ.of_le (by exact_mod_cast (by omega : l * 2 + 1 ≤ (l + 1) * 2 + 1))
    have ih := drift_iter H hH b hb hdiv l hφ'
    have hχ : ContDiff ℝ 3 ((AVRegularity.covOperator H)^[l] φ) := by
      have := (ConstCoefOp.covIter (E := E) H l).reg 3 φ
        (hφ.of_le (by exact_mod_cast (by omega : 3 + l * 2 ≤ (l + 1) * 2 + 1)))
      exact_mod_cast this
    have hcc := ConstCoefOp.covOperator (E := E) H
    have hf2 : ContDiff ℝ 2 ((AVRegularity.covOperator H)^[l] (driftDeriv b φ)) := by
      have hD : ContDiff ℝ ((l * 2 + 2 : ℕ) : WithTop ℕ∞) (driftDeriv b φ) :=
        contDiff_driftDeriv hb (hφ.of_le (by exact_mod_cast (by omega : l * 2 + 2 + 1 ≤ (l + 1) * 2 + 1)))
      have := (ConstCoefOp.covIter (E := E) H l).reg 2 _ (by simpa [add_comm] using hD)
      exact_mod_cast this
    have hg2 : ∀ a ∈ Finset.range l, ContDiff ℝ 2 ((AVRegularity.covOperator H)^[a]
        (fun y => divE (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y)) := by
      intro a ha
      have ha' := Finset.mem_range.mp ha
      have hm : ContDiff ℝ (((2 + a * 2) + 3 : ℕ) : WithTop ℕ∞)
          ((AVRegularity.covOperator H)^[l - 1 - a] φ) := by
        have := (ConstCoefOp.covIter (E := E) H (l - 1 - a)).reg ((2 + a * 2) + 3) φ
          (hφ.of_le (by exact_mod_cast (by omega : (2 + a * 2) + 3 + (l - 1 - a) * 2 ≤ (l + 1) * 2 + 1)))
        exact_mod_cast this
      have hS := div_comm_contDiff H hH b hb hdiv (2 + a * 2) hm
      have := (ConstCoefOp.covIter (E := E) H a).reg 2 _ (by simpa [add_comm] using hS)
      exact_mod_cast this
    have e1 : driftDeriv b ((AVRegularity.covOperator H)^[l + 1] φ) = fun x =>
        AVRegularity.covOperator H (driftDeriv b ((AVRegularity.covOperator H)^[l] φ)) x +
          divE (commFluxE b H ((AVRegularity.covOperator H)^[l] φ)) x := by
      funext x
      rw [Function.iterate_succ_apply']
      exact drift_step H hH b hb hdiv hχ x
    rw [e1, ih]
    have hsum2 : ContDiff ℝ 2 (fun x => ∑ a ∈ Finset.range l, (AVRegularity.covOperator H)^[a]
        (fun y => divE (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y) x) :=
      ContDiff.sum hg2
    have hadd := cco_add hcc (f := (AVRegularity.covOperator H)^[l] (driftDeriv b φ))
      (g := fun x => ∑ a ∈ Finset.range l, (AVRegularity.covOperator H)^[a]
        (fun y => divE (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y) x)
      (by exact_mod_cast hf2) (by exact_mod_cast hsum2)
    have hsm := covOperator_sum H (Finset.range l) (fun a => (AVRegularity.covOperator H)^[a]
        (fun y => divE (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y)) hg2
    funext x
    rw [hadd]
    simp only
    rw [hsm, Finset.sum_range_succ', Function.iterate_succ_apply' (AVRegularity.covOperator H) l]
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
    have hidx : ∀ a : ℕ, l - 1 - a = l - (a + 1) := fun a => by omega
    simp only [Nat.add_sub_cancel, hidx, Nat.sub_zero]
    abel
end

/-! The commutator part of the temporal flux: `b·∇ P_p φ - P_p (b·∇ φ) = div Tcomm`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The commutator part of the temporal flux. -/
def Tcomm (b : Vec 2 → Vec 2) (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (φ : Vec 2 → E) :
    Vec 2 → Fin 2 → E := fun x =>
  ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
    (AVRegularity.covOperator H)^[a] (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) x

theorem sum_Icc_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (p : ℕ) :
    ∑ l ∈ Finset.Icc 1 p, f l = ∑ l ∈ Finset.range p, f (l + 1) := by
  induction p with
  | zero => simp
  | succ p ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem driftDeriv_comb {b : Vec 2 → Vec 2} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (g : ι → Vec 2 → E) (hg : ∀ i ∈ s, ContDiff ℝ 1 (g i)) (x : Vec 2) :
    driftDeriv b (fun y => ∑ i ∈ s, c i • g i y) x = ∑ i ∈ s, c i • driftDeriv b (g i) x := by
  have hc : ∀ i ∈ s, ContDiff ℝ 1 (fun y => c i • g i y) := fun i hi => (hg i hi).const_smul _
  have e : ∀ k : Fin 2, partialOp k (fun y => ∑ i ∈ s, c i • g i y) x =
      ∑ i ∈ s, c i • partialOp k (g i) x := fun k => by
    rw [partialOp_sum k s (fun i y => c i • g i y) hc]
    exact Finset.sum_congr rfl fun i hi => by rw [partialOp_smul k (c i) (hg i hi)]
  simp only [driftDeriv_apply, e, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm]

theorem cfl_contDiff {b : Vec 2 → Vec 2} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (H : Matrix (Fin 2) (Fin 2) ℝ) {r : ℕ} {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) ψ) (j : Fin 2) :
    ContDiff ℝ (r : WithTop ℕ∞) (fun y => commFluxE b H ψ y j) := by
  have hjac : ∀ i m : Fin 2, ContDiff ℝ (r : WithTop ℕ∞) (fun y => fderiv ℝ b y (basisVec m) i) :=
    fun i m => by
      have h1 : ContDiff ℝ (r : WithTop ℕ∞) (fderiv ℝ b) := hb.fderiv_right (by exact_mod_cast le_top)
      exact contDiff_pi.1 (h1.clm_apply contDiff_const) i
  simp only [commFluxE]
  refine (ContDiff.sum fun l _ => ?_).neg
  have hN : ContDiff ℝ (r : WithTop ℕ∞)
      (fun y => (jacMatrix b y * H + H * Matrix.transpose (jacMatrix b y)) j l) := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, jacMatrix, Matrix.of_apply]
    exact (ContDiff.sum fun m _ => (hjac j m).mul contDiff_const).add
      (ContDiff.sum fun m _ => contDiff_const.mul (hjac l m))
  exact hN.smul (contDiff_partialOp hψ l)

theorem divE_sum' {ι : Type*} (s : Finset ι) (F : ι → Vec 2 → Fin 2 → E)
    (hF : ∀ i ∈ s, ∀ j, ContDiff ℝ 1 (fun y => F i y j)) (x : Vec 2) :
    divE (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, divE (F i) x := by
  unfold divE
  have e : ∀ j : Fin 2, fderiv ℝ (fun y => (∑ i ∈ s, F i y) j) x (basisVec j) =
      ∑ i ∈ s, fderiv ℝ (fun y => F i y j) x (basisVec j) := fun j => by
    have := congrFun (partialOp_sum j s (fun i y => F i y j) (fun i hi => hF i hi j)) x
    simpa [Finset.sum_apply, partialOp_apply] using this
  simp only [e]
  rw [Finset.sum_comm]

theorem divE_smul (c : ℝ) (F : Vec 2 → Fin 2 → E) (hF : ∀ j, ContDiff ℝ 1 (fun y => F y j))
    (x : Vec 2) : divE (fun y => c • F y) x = c • divE F x := by
  unfold divE
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (partialOp_smul j c (hF j)) x
  simpa [partialOp_apply] using this

theorem divE_add' (F G : Vec 2 → Fin 2 → E) (hF : ∀ j, ContDiff ℝ 1 (fun y => F y j))
    (hG : ∀ j, ContDiff ℝ 1 (fun y => G y j)) (x : Vec 2) :
    divE (fun y => F y + G y) x = divE F x + divE G x := by
  unfold divE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (partialOp_add_fun (hF j) (hG j) j) x
  simpa [partialOp_apply] using this

theorem divE_sub (F G : Vec 2 → Fin 2 → E) (hF : ∀ j, ContDiff ℝ 1 (fun y => F y j))
    (hG : ∀ j, ContDiff ℝ 1 (fun y => G y j)) (x : Vec 2) :
    divE (fun y => F y - G y) x = divE F x - divE G x := by
  have e : (fun y => F y - G y) = fun y => F y + (-1 : ℝ) • G y := by
    funext y; simp [sub_eq_add_neg]
  rw [e, divE_add' F (fun y => (-1 : ℝ) • G y) hF (fun j => (hG j).const_smul (-1 : ℝ)) x,
    divE_smul (-1 : ℝ) G hG x]
  simp [sub_eq_add_neg]

theorem iter_comp {b : Vec 2 → Vec 2} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (a : ℕ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ ((a * 2 + 1 : ℕ) : WithTop ℕ∞) ψ) (y : Vec 2) (j : Fin 2) :
    (AVRegularity.covOperator H)^[a] (commFluxE b H ψ) y j =
      (AVRegularity.covOperator H)^[a] (fun y' => commFluxE b H ψ y' j) y := by
  have hF : ContDiff ℝ ((2 * a : ℕ) : ℕ∞) (commFluxE b H ψ) := by
    have : ∀ j, ContDiff ℝ ((a * 2 : ℕ) : WithTop ℕ∞) (fun y => commFluxE b H ψ y j) :=
      fun j => cfl_contDiff hb H hψ j
    have h2 : ContDiff ℝ ((a * 2 : ℕ) : WithTop ℕ∞) (commFluxE b H ψ) := contDiff_pi.2 this
    rw [mul_comm]; exact_mod_cast h2
  have := covProj_covIter H (ContinuousLinearMap.proj j : (Fin 2 → E) →L[ℝ] E) a hF y
  simpa using this

/-- The `a`-th covariance power of the commutator flux (a flux in `Fin 2 → E`) is `C¹` componentwise. -/
theorem iter_comp_contDiff {b : Vec 2 → Vec 2} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (a : ℕ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ ((a * 2 + 2 : ℕ) : WithTop ℕ∞) ψ) (j : Fin 2) :
    ContDiff ℝ 1 (fun y => (AVRegularity.covOperator H)^[a] (commFluxE b H ψ) y j) := by
  have hψ' : ContDiff ℝ ((a * 2 + 1 : ℕ) : WithTop ℕ∞) ψ :=
    hψ.of_le (by exact_mod_cast (by omega : a * 2 + 1 ≤ a * 2 + 2))
  simp only [iter_comp hb H a hψ']
  have h1 : ContDiff ℝ ((1 + a * 2 : ℕ) : WithTop ℕ∞) (fun y' => commFluxE b H ψ y' j) :=
    cfl_contDiff hb H (r := 1 + a * 2) (by
      refine hψ.of_le ?_
      exact_mod_cast (by omega : 1 + a * 2 + 1 ≤ a * 2 + 2)) j
  have := (ConstCoefOp.covIter (E := E) H a).reg 1 _ h1
  exact_mod_cast this

theorem divE_iter_comm {b : Vec 2 → Vec 2} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (a : ℕ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ ((a * 2 + 2 : ℕ) : WithTop ℕ∞) ψ) (x : Vec 2) :
    divE (fun y => (AVRegularity.covOperator H)^[a] (commFluxE b H ψ) y) x =
      (AVRegularity.covOperator H)^[a] (fun y => divE (commFluxE b H ψ) y) x := by
  have hψ' : ContDiff ℝ ((a * 2 + 1 : ℕ) : WithTop ℕ∞) ψ :=
    hψ.of_le (by exact_mod_cast (by omega : a * 2 + 1 ≤ a * 2 + 2))
  have hg : ∀ j, ContDiff ℝ ((a * 2 + 1 : ℕ) : WithTop ℕ∞) (fun y => commFluxE b H ψ y j) :=
    fun j => cfl_contDiff hb H hψ j
  have hd := ConstCoefOp.div (ConstCoefOp.covIter (E := E) H a) hg
    (f := fun y => divE (commFluxE b H ψ) y) (by funext y; rfl)
  rw [hd]
  unfold divE
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (fun y => (AVRegularity.covOperator H)^[a] (commFluxE b H ψ) y j) =
      (AVRegularity.covOperator H)^[a] (fun y' => commFluxE b H ψ y' j) :=
    funext fun y => iter_comp hb H a hψ' y j
  rw [e]
  rfl

theorem drift_poly (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, H i j = H j i)
    (b : Vec 2 → Vec 2) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ b x (basisVec k) k = 0) (p : ℕ) {φ : Vec 2 → E}
    (hφ : ContDiff ℝ ((p * 2 + 2 : ℕ) : WithTop ℕ∞) φ) (x : Vec 2) :
    driftDeriv b (AVRegularity.covPolyP H p φ) x -
        AVRegularity.covPolyP H p (driftDeriv b φ) x = divE (Tcomm b H p φ) x := by
  have hreg : ∀ l ∈ Finset.range (p + 1), ContDiff ℝ ((l * 2 + 1 : ℕ) : WithTop ℕ∞) φ :=
    fun l hl => hφ.of_le (by
      have := Finset.mem_range.mp hl
      exact_mod_cast (by omega : l * 2 + 1 ≤ p * 2 + 2))
  have hC1 : ∀ l ∈ Finset.range (p + 1), ContDiff ℝ 1 ((AVRegularity.covOperator H)^[l] φ) :=
    fun l hl => by
      have := (ConstCoefOp.covIter (E := E) H l).reg 1 φ (by
        simpa [add_comm] using hreg l hl)
      exact_mod_cast this
  have hP : AVRegularity.covPolyP H p φ = fun y => ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[l] φ y := by
    funext y; simp [AVRegularity.covPolyP, Finset.sum_apply]
  have hP' : AVRegularity.covPolyP H p (driftDeriv b φ) x = ∑ l ∈ Finset.range (p + 1),
      ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[l] (driftDeriv b φ) x := by
    simp [AVRegularity.covPolyP, Finset.sum_apply]
  rw [hP, driftDeriv_comb _ _ _ hC1 x, hP', ← Finset.sum_sub_distrib]
  -- the right side
  have hK : ∀ l ∈ Finset.range (p + 1), driftDeriv b ((AVRegularity.covOperator H)^[l] φ) x =
      (AVRegularity.covOperator H)^[l] (driftDeriv b φ) x + ∑ a ∈ Finset.range l,
        (AVRegularity.covOperator H)^[a]
          (fun y => divE (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y) x :=
    fun l hl => congrFun (drift_iter H hH b hb hdiv l (hreg l hl)) x
  have hL : ∑ l ∈ Finset.range (p + 1), (((l.factorial : ℝ)⁻¹) • driftDeriv b ((AVRegularity.covOperator H)^[l] φ) x -
      ((l.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[l] (driftDeriv b φ) x) =
      ∑ l ∈ Finset.range (p + 1), ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
        (AVRegularity.covOperator H)^[a]
          (fun y => divE (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y) x := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hK l hl, smul_add]; abel
  rw [hL]
  have hcomp : ∀ l ∈ Finset.Icc 1 p, ∀ a ∈ Finset.range l, ContDiff ℝ ((a * 2 + 2 : ℕ) : WithTop ℕ∞)
      ((AVRegularity.covOperator H)^[l - 1 - a] φ) := by
    intro l hl a ha
    have h1 := Finset.mem_Icc.mp hl
    have h2 := Finset.mem_range.mp ha
    have := (ConstCoefOp.covIter (E := E) H (l - 1 - a)).reg (a * 2 + 2) φ
      (hφ.of_le (by exact_mod_cast (by omega : a * 2 + 2 + (l - 1 - a) * 2 ≤ p * 2 + 2)))
    exact_mod_cast this
  unfold Tcomm
  have hdiv1 : ∀ l ∈ Finset.Icc 1 p, ∀ j, ContDiff ℝ 1 (fun y => (((l.factorial : ℝ)⁻¹) •
      ∑ a ∈ Finset.range l, (AVRegularity.covOperator H)^[a]
        (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y) j) := by
    intro l hl j
    simp only [Pi.smul_apply, Finset.sum_apply]
    exact (ContDiff.sum fun a ha => iter_comp_contDiff hb H a (hcomp l hl a ha) j).const_smul _
  have hdiv2 : ∀ l ∈ Finset.Icc 1 p, ∀ a ∈ Finset.range l, ∀ j, ContDiff ℝ 1
      (fun y => (AVRegularity.covOperator H)^[a]
        (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y j) :=
    fun l hl a ha j => iter_comp_contDiff hb H a (hcomp l hl a ha) j
  rw [divE_sum' (Finset.Icc 1 p) (fun l y => ((l.factorial : ℝ)⁻¹) •
    ∑ a ∈ Finset.range l, (AVRegularity.covOperator H)^[a]
      (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y) hdiv1 x]
  have hterm : ∀ l ∈ Finset.Icc 1 p, divE (fun y => ((l.factorial : ℝ)⁻¹) •
      ∑ a ∈ Finset.range l, (AVRegularity.covOperator H)^[a]
        (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y) x =
      ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l, (AVRegularity.covOperator H)^[a]
        (fun y => divE (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y) x := by
    intro l hl
    rw [divE_smul _ _ (fun j => by
      simp only [Finset.sum_apply]
      exact ContDiff.sum fun a ha => hdiv2 l hl a ha j) x]
    congr 1
    rw [divE_sum' (Finset.range l) (fun a y => (AVRegularity.covOperator H)^[a]
      (commFluxE b H ((AVRegularity.covOperator H)^[l - 1 - a] φ)) y)
      (fun a ha j => hdiv2 l hl a ha j) x]
    exact Finset.sum_congr rfl fun a ha => divE_iter_comm hb H a (hcomp l hl a ha) x
  rw [Finset.sum_congr rfl hterm, sum_Icc_range, Finset.sum_range_succ']
  simp only [Finset.range_zero, Finset.sum_empty, smul_zero, add_zero]

theorem Tcomm_contDiff (H : Matrix (Fin 2) (Fin 2) ℝ)
    (b : Vec 2 → Vec 2) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p : ℕ) {φ : Vec 2 → E}
    (hφ : ContDiff ℝ ((p * 2 + 2 : ℕ) : WithTop ℕ∞) φ) (j : Fin 2) :
    ContDiff ℝ 1 (fun y => Tcomm b H p φ y j) := by
  unfold Tcomm
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine ContDiff.sum fun l hl => ?_
  refine ContDiff.const_smul _ (ContDiff.sum fun a ha => ?_)
  have h1 := Finset.mem_Icc.mp hl
  have h2 := Finset.mem_range.mp ha
  have hc := (ConstCoefOp.covIter (E := E) H (l - 1 - a)).reg (a * 2 + 2) φ
    (hφ.of_le (by exact_mod_cast (by omega : a * 2 + 2 + (l - 1 - a) * 2 ≤ p * 2 + 2)))
  exact iter_comp_contDiff hb H a (by exact_mod_cast hc) j

/-- The flux `j ↦ ∑_l M j l ∂_l g`. -/
def FluxA (M : Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2 → E) : Vec 2 → Fin 2 → E :=
  fun y j => ∑ l : Fin 2, M j l • gradE g y l

theorem fluxA_contDiff (M : Matrix (Fin 2) (Fin 2) ℝ) {g : Vec 2 → E} {r : ℕ}
    (hg : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) g) (j : Fin 2) :
    ContDiff ℝ (r : WithTop ℕ∞) (fun y => FluxA M g y j) := by
  unfold FluxA
  exact ContDiff.sum fun l _ => (contDiff_const.smul (contDiff_partialOp hg l))

theorem divE_fluxA (M : Matrix (Fin 2) (Fin 2) ℝ) {g : Vec 2 → E}
    (hg : ContDiff ℝ 2 g) (x : Vec 2) :
    divE (FluxA M g) x = AVRegularity.covOperator M g x := by
  have h1 : ∀ l : Fin 2, ContDiff ℝ 1 (partialOp l g) := fun l => contDiff_partialOp (k := 1) hg l
  rw [covOperator_eq]
  unfold divE FluxA
  refine Finset.sum_congr rfl fun j _ => ?_
  show partialOp j (fun y => ∑ l : Fin 2, M j l • partialOp l g y) x = _
  rw [partialOp_sum j Finset.univ (fun l y => M j l • partialOp l g y)
    (fun l _ => (h1 l).const_smul _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [partialOp_smul j (M j l) (h1 l)]
end

/-! The pure spatial identity behind the temporal product formula, for one fixed time. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem covOperator_matrix_add (M N : Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2 → E) (x : Vec 2) :
    AVRegularity.covOperator (M + N) g x =
      AVRegularity.covOperator M g x + AVRegularity.covOperator N g x := by
  simp only [covOperator_eq, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem fluxA_smul_one (κ : ℝ) (g : Vec 2 → E) :
    FluxA (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) g = fun y j => κ • gradE g y j := by
  funext y j
  simp [FluxA, Matrix.one_apply]

theorem polyP_split (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (φ : Vec 2 → E) :
    AVRegularity.covPolyP H p φ = fun y => PolyLow H p φ y +
      ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[p] φ y := by
  funext y
  simp [AVRegularity.covPolyP, PolyLow, Finset.sum_apply, Finset.sum_range_succ]

theorem polyLow_contDiff (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {φ : Vec 2 → E}
    (hφ : ContDiff ℝ ((p * 2 + 2 : ℕ) : WithTop ℕ∞) φ) :
    ContDiff ℝ 2 (PolyLow H p φ) := by
  unfold PolyLow
  refine ContDiff.sum fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  have := (ConstCoefOp.covIter (E := E) H l).reg 2 φ
    (hφ.of_le (by exact_mod_cast (by omega : 2 + l * 2 ≤ p * 2 + 2)))
  exact (by exact_mod_cast this : ContDiff ℝ 2 _).const_smul _

theorem core (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : ∀ i j, H i j = H j i)
    (b : Vec 2 → Vec 2) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ b x (basisVec k) k = 0)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ) (p : ℕ) {φ ψ0 : Vec 2 → E}
    (hφ : ContDiff ℝ ((p * 2 + 2 : ℕ) : WithTop ℕ∞) φ)
    (hψ : ContDiff ℝ ((p * 2 : ℕ) : WithTop ℕ∞) ψ0) (x : Vec 2) (dR : E)
    (G Fsum lastF : Vec 2 → Fin 2 → E) (hG : ∀ j, ContDiff ℝ 1 (fun y => G y j))
    (hdR : dR = AVRegularity.covPolyP H p ψ0 x +
      AVRegularity.covOperator (R - κ • 1) (PolyLow H p φ) x)
    (hFs : ∀ y, Fsum y = Tcomm b H p φ y +
      FluxA R (AVRegularity.covPolyP H p φ) y - G y)
    (hlast : ∀ y, lastF y = FluxA (R - κ • 1)
      (fun y' => ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[p] φ y') y) :
    dR + driftDeriv b (AVRegularity.covPolyP H p φ) x - divE Fsum x =
      AVRegularity.covPolyP H p (fun y => ψ0 y + driftDeriv b φ y -
        divE (fun y' => κ • gradE φ y') y) x + divE G x - divE lastF x := by
  have hφ2 : ContDiff ℝ ((2 + 2 * p : ℕ) : WithTop ℕ∞) φ :=
    hφ.of_le (by exact_mod_cast (by omega : 2 + 2 * p ≤ p * 2 + 2))
  have hg2 : ContDiff ℝ 2 (AVRegularity.covPolyP H p φ) := by
    have := (ConstCoefOp.covPolyP (E := E) H p).reg 2 φ hφ2
    exact_mod_cast this
  have hφ2' : ContDiff ℝ 2 φ := hφ.of_le (by exact_mod_cast (by omega : 2 ≤ p * 2 + 2))
  have hgp2 : ContDiff ℝ 2 (fun y => ((p.factorial : ℝ)⁻¹) •
      (AVRegularity.covOperator H)^[p] φ y) := by
    have := (ConstCoefOp.covIter (E := E) H p).reg 2 φ
      (hφ.of_le (by exact_mod_cast (by omega : 2 + p * 2 ≤ p * 2 + 2)))
    exact (by exact_mod_cast this : ContDiff ℝ 2 _).const_smul _
  -- divergence of the flux sum
  have hT := Tcomm_contDiff H b hb p hφ
  have hA : ∀ j, ContDiff ℝ 1 (fun y => FluxA R (AVRegularity.covPolyP H p φ) y j) :=
    fun j => fluxA_contDiff R (r := 1) (by exact_mod_cast hg2) j
  have hTA : ∀ j, ContDiff ℝ 1 (fun y => (Tcomm b H p φ y +
      FluxA R (AVRegularity.covPolyP H p φ) y) j) := fun j => (hT j).add (hA j)
  have hdF : divE Fsum x = divE (Tcomm b H p φ) x +
      divE (FluxA R (AVRegularity.covPolyP H p φ)) x - divE G x := by
    have e : Fsum = fun y => (Tcomm b H p φ y +
        FluxA R (AVRegularity.covPolyP H p φ) y) - G y := funext hFs
    rw [e, divE_sub _ G hTA hG x, divE_add' _ _ hT hA x]
  have e2 := drift_poly H hH b hb hdiv p hφ x
  have e3 := divE_fluxA R hg2 x
  have e6 : divE lastF x = AVRegularity.covOperator (R - κ • 1) (fun y => ((p.factorial : ℝ)⁻¹) •
      (AVRegularity.covOperator H)^[p] φ y) x := by
    have : lastF = FluxA (R - κ • 1) (fun y' => ((p.factorial : ℝ)⁻¹) •
        (AVRegularity.covOperator H)^[p] φ y') := funext hlast
    rw [this]; exact divE_fluxA _ hgp2 x
  -- the polynomial applied to the coarse integrand
  have hQ : (fun y => divE (fun y' => κ • gradE φ y') y) =
      AVRegularity.covOperator (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) φ := by
    funext y
    have := divE_fluxA (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) hφ2' y
    rw [fluxA_smul_one] at this
    exact this
  have hPc := ConstCoefOp.covPolyP (E := E) H p
  have hD : ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) (driftDeriv b φ) :=
    contDiff_driftDeriv hb (n := 2 * p) (hφ.of_le (by exact_mod_cast (by omega : 2 * p + 1 ≤ p * 2 + 2)))
  have hQc : ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞)
      (AVRegularity.covOperator (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) φ) :=
    contDiff_covOperator _ (hφ.of_le (by exact_mod_cast (by omega : 2 * p + 2 ≤ p * 2 + 2)))
  have hψ' : ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) ψ0 := by
    rw [mul_comm]; exact hψ
  have hsplit : AVRegularity.covPolyP H p (fun y => ψ0 y + driftDeriv b φ y -
      divE (fun y' => κ • gradE φ y') y) x = AVRegularity.covPolyP H p ψ0 x +
      AVRegularity.covPolyP H p (driftDeriv b φ) x -
      AVRegularity.covOperator (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (AVRegularity.covPolyP H p φ) x := by
    have h1 : (fun y => ψ0 y + driftDeriv b φ y - divE (fun y' => κ • gradE φ y') y) =
        fun y => (ψ0 y + driftDeriv b φ y) - AVRegularity.covOperator
          (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) φ y := by
      funext y; rw [← hQ]
    rw [h1, congrFun (cco_sub hPc (hψ'.add hD) hQc) x,
      congrFun (cco_add hPc hψ' hD) x,
      congrFun (covPolyP_covOperator_comm' H (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) p hφ) x]
  rw [hsplit, hdF, e6, ← e2, e3, hdR]
  -- matrix and splitting algebra
  have hR : R = (R - κ • 1) + κ • 1 := by abel
  have hL := polyLow_contDiff H p hφ
  have hgsplit := congrFun (cco_add (ConstCoefOp.covOperator (E := E) (R - κ • 1)) hL hgp2) x
  have hgs : AVRegularity.covPolyP H p φ = fun y => PolyLow H p φ y +
      ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[p] φ y := polyP_split H p φ
  have hRg := covOperator_matrix_add (R - κ • 1) (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (AVRegularity.covPolyP H p φ) x
  rw [← hR] at hRg
  rw [hRg]
  have hg3 : AVRegularity.covOperator (R - κ • 1) (AVRegularity.covPolyP H p φ) x =
      AVRegularity.covOperator (R - κ • 1) (PolyLow H p φ) x + AVRegularity.covOperator (R - κ • 1)
        (fun y => ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator H)^[p] φ y) x := by
    rw [hgs]; exact hgsplit
  rw [hg3]
  abel
end

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Spatial step of `MacroWeakFromStrongStatement`: at one time, the strong macro equation
integrated against a periodic test gives the integrand of the weak identity (after integration
by parts of the two divergences on the unit cell). -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Periodic integration by parts for a divergence, as the vanishing of one integral. -/
theorem macroWeak_ibp_zero {F : Vec 2 → Fin 2 → E} (hF : ∀ k, ContDiff ℝ 1 (fun x => F x k))
    (hFp : ∀ k, AVenhance.IsZ2Periodic (fun x => F x k)) {φ : Vec 2 → E}
    (hφ : ContDiff ℝ 1 φ) (hφp : AVenhance.IsZ2Periodic φ) :
    ∫ x in AVenhance.unitCube, (inner ℝ (divE F x) (φ x) +
      ∑ k : Fin 2, inner ℝ (F x k) (gradE φ x k)) = 0 := by
  have h := cell_ibp_div hF hFp hφ hφp
  have hc1 : Continuous (fun x => inner ℝ (divE F x) (φ x)) :=
    (continuous_finsetSum _ fun k _ => cell_continuous_partial (hF k) k).inner hφ.continuous
  have hc2 : Continuous (fun x => ∑ k : Fin 2, inner ℝ (F x k) (gradE φ x k)) :=
    continuous_finsetSum _ fun k _ =>
      (hF k).continuous.inner (cell_continuous_partial hφ k)
  rw [integral_add (AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _ hc1)
    (AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _ hc2)]
  change (∫ x in AVenhance.unitCube, inner ℝ (∑ k : Fin 2, fderiv ℝ (fun y => F y k) x
    (basisVec k)) (φ x)) + _ = 0
  rw [h]
  simp [gradE]

/-- The spatial identity of the weak formulation at one time. -/
theorem macroWeak_spatial_identity (ν : ℝ) (b : Vec 2 → Vec 2) (a da : Vec 2 → E)
    (A B : Vec 2 → Fin 2 → E) (φ : Vec 2 → E)
    (ha : ContDiff ℝ 2 a) (hap : AVenhance.IsZ2Periodic a) (hda : Continuous da)
    (hA : ∀ k, ContDiff ℝ 1 (fun x => A x k)) (hAp : ∀ k, AVenhance.IsZ2Periodic (fun x => A x k))
    (hB : ∀ k, ContDiff ℝ 1 (fun x => B x k)) (hBp : ∀ k, AVenhance.IsZ2Periodic (fun x => B x k))
    (hφ : ContDiff ℝ 1 φ) (hφp : AVenhance.IsZ2Periodic φ)
    (hstrong : ∀ x, da x + ∑ j : Fin 2, b x j • gradE a x j -
      divE (fun y => ν • gradE a y + A y) x = divE B x) :
    (∫ x in AVenhance.unitCube, (-(∑ k : Fin 2, b x k * inner ℝ (gradE a x k) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (gradE a x k) (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (A x k + B x k) (gradE φ x k) + inner ℝ (0 : E) (φ x))) =
      ∫ x in AVenhance.unitCube, inner ℝ (da x) (φ x) := by
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hga : ∀ k, ContDiff ℝ 1 (fun x => gradE a x k) := fun k =>
    (ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hgap : ∀ k, AVenhance.IsZ2Periodic (fun x => gradE a x k) := fun k => by
    have hDp := fderiv_isZ2Periodic (ha.differentiable (by norm_num)) hap
    exact fun n x => congrArg (fun L => L (basisVec k)) (hDp n x)
  have hF1 : ∀ k, ContDiff ℝ 1 (fun x => (ν • gradE a x + A x) k) := fun k =>
    ((hga k).const_smul ν).add (hA k)
  have hF1p : ∀ k, AVenhance.IsZ2Periodic (fun x => (ν • gradE a x + A x) k) := fun k n x => by
    simp only [Pi.add_apply, Pi.smul_apply, hgap k n x, hAp k n x]
  have hT1 := macroWeak_ibp_zero hF1 hF1p hφ hφp
  have hT2 := macroWeak_ibp_zero hB hBp hφ hφp
  have hgφ : ∀ k, Continuous (fun x => gradE φ x k) := fun k => cell_continuous_partial hφ k
  have hga' : ∀ k, Continuous (fun x => gradE a x k) := fun k => (hga k).continuous
  have hc1 : Continuous (fun x => inner ℝ (divE (fun y => ν • gradE a y + A y) x) (φ x)) :=
    (continuous_finsetSum _ fun k _ => cell_continuous_partial (hF1 k) k).inner hφ.continuous
  have hc1' : Continuous (fun x => ∑ k : Fin 2,
      inner ℝ ((ν • gradE a x + A x) k) (gradE φ x k)) :=
    continuous_finsetSum _ fun k _ => (hF1 k).continuous.inner (hgφ k)
  have hc2 : Continuous (fun x => inner ℝ (divE B x) (φ x)) :=
    (continuous_finsetSum _ fun k _ => cell_continuous_partial (hB k) k).inner hφ.continuous
  have hc2' : Continuous (fun x => ∑ k : Fin 2, inner ℝ (B x k) (gradE φ x k)) :=
    continuous_finsetSum _ fun k _ => (hB k).continuous.inner (hgφ k)
  have hpt : ∀ x, (-(∑ k : Fin 2, b x k * inner ℝ (gradE a x k) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (gradE a x k) (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (A x k + B x k) (gradE φ x k) + inner ℝ (0 : E) (φ x)) =
      inner ℝ (da x) (φ x) -
        (inner ℝ (divE (fun y => ν • gradE a y + A y) x) (φ x) +
          ∑ k : Fin 2, inner ℝ ((ν • gradE a x + A x) k) (gradE φ x k)) -
        (inner ℝ (divE B x) (φ x) + ∑ k : Fin 2, inner ℝ (B x k) (gradE φ x k)) := by
    intro x
    have hd : da x = divE (fun y => ν • gradE a y + A y) x + divE B x -
        ∑ j : Fin 2, b x j • gradE a x j := by
      rw [← hstrong x]; abel
    rw [hd]
    simp only [inner_sub_left, inner_add_left, sum_inner, real_inner_smul_left, inner_zero_left,
      Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  simp only [hpt]
  have hi := AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable
  have I0 : Integrable (fun x => inner ℝ (da x) (φ x)) (volume.restrict AVenhance.unitCube) :=
      hi _ (hda.inner hφ.continuous)
  have I1 : Integrable (fun x => inner ℝ (divE (fun y => ν • gradE a y + A y) x) (φ x) +
        ∑ k : Fin 2, inner ℝ ((ν • gradE a x + A x) k) (gradE φ x k))
        (volume.restrict AVenhance.unitCube) := hi _ (hc1.add hc1')
  have I2 : Integrable (fun x => inner ℝ (divE B x) (φ x) +
        ∑ k : Fin 2, inner ℝ (B x k) (gradE φ x k)) (volume.restrict AVenhance.unitCube) :=
      hi _ (hc2.add hc2')
  have I01 : Integrable (fun x => inner ℝ (da x) (φ x) -
        (inner ℝ (divE (fun y => ν • gradE a y + A y) x) (φ x) +
        ∑ k : Fin 2, inner ℝ ((ν • gradE a x + A x) k) (gradE φ x k)))
        (volume.restrict AVenhance.unitCube) := I0.sub I1
  rw [integral_sub I01 I2, integral_sub I0 I1, hT1, hT2]
  ring

/-- The integrand of the weak identity is continuous. -/
theorem macroWeak_spatial_continuous (ν : ℝ) (b : Vec 2 → Vec 2) (a : Vec 2 → E)
    (A B : Vec 2 → Fin 2 → E) (φ : Vec 2 → E) (ha : ContDiff ℝ 1 a) (hb : Continuous b)
    (hA : ∀ k, Continuous (fun x => A x k)) (hB : ∀ k, Continuous (fun x => B x k))
    (hφ : ContDiff ℝ 1 φ) :
    Continuous (fun x => -(∑ k : Fin 2, b x k * inner ℝ (gradE a x k) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (gradE a x k) (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (A x k + B x k) (gradE φ x k) + inner ℝ (0 : E) (φ x)) := by
  have hga : ∀ k, Continuous (fun x => gradE a x k) := fun k => cell_continuous_partial ha k
  have hgφ : ∀ k, Continuous (fun x => gradE φ x k) := fun k => cell_continuous_partial hφ k
  have hbk : ∀ k, Continuous (fun x => b x k) := fun k => (continuous_apply k).comp hb
  refine ((((continuous_finsetSum _ fun k _ => (hbk k).mul ((hga k).inner hφ.continuous)).neg).sub
    (continuous_const.mul (continuous_finsetSum _ fun k _ => (hga k).inner (hgφ k)))).sub
    (continuous_finsetSum _ fun k _ => ((hA k).add (hB k)).inner (hgφ k))).add ?_
  exact continuous_const.inner hφ.continuous
end

/-! Spatial step of `ReadoutStrongEquationStatement`: at one time, the right side of the weak
identity integrates to the pairing of the classical operator
`R = div (ν ∇a + A) - b·∇a` with the test (periodic integration by parts), and `R` is continuous
and periodic. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The classical right-hand operator `div (ν ∇a + A) - b·∇a`. -/
def roStrR (ν : ℝ) (b : Vec 2 → Vec 2) (a : Vec 2 → E) (A : Vec 2 → Fin 2 → E) (x : Vec 2) : E :=
  divE (fun y => ν • gradE a y + A y) x - ∑ j : Fin 2, b x j • gradE a x j

theorem roStr_grad_contDiff {a : Vec 2 → E} (ha : ContDiff ℝ 2 a) (k : Fin 2) :
    ContDiff ℝ 1 (fun x => gradE a x k) :=
  (ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem roStr_grad_periodic {a : Vec 2 → E} (ha : ContDiff ℝ 2 a) (hap : AVenhance.IsZ2Periodic a)
    (k : Fin 2) : AVenhance.IsZ2Periodic (fun x => gradE a x k) := by
  have hDp := fderiv_isZ2Periodic (ha.differentiable (by norm_num)) hap
  exact fun n x => congrArg (fun L => L (basisVec k)) (hDp n x)

theorem roStr_R_continuous (ν : ℝ) {b : Vec 2 → Vec 2} {a : Vec 2 → E} {A : Vec 2 → Fin 2 → E}
    (ha : ContDiff ℝ 2 a) (hb : Continuous b) (hA : ∀ k, ContDiff ℝ 1 (fun x => A x k)) :
    Continuous (roStrR ν b a A) := by
  have hF : ∀ k, ContDiff ℝ 1 (fun x => (ν • gradE a x + A x) k) := fun k =>
    ((roStr_grad_contDiff ha k).const_smul ν).add (hA k)
  have hbk : ∀ k, Continuous (fun x => b x k) := fun k => (continuous_apply k).comp hb
  have hga : ∀ k, Continuous (fun x => gradE a x k) := fun k =>
    (roStr_grad_contDiff ha k).continuous
  unfold roStrR divE
  exact (continuous_finsetSum _ fun k _ => cell_continuous_partial (hF k) k).sub
    (continuous_finsetSum _ fun k _ => (hbk k).smul (hga k))

theorem roStr_R_periodic (ν : ℝ) {b : Vec 2 → Vec 2} {a : Vec 2 → E} {A : Vec 2 → Fin 2 → E}
    (ha : ContDiff ℝ 2 a) (hap : AVenhance.IsZ2Periodic a) (hbp : AVenhance.IsZ2Periodic b)
    (hA : ∀ k, ContDiff ℝ 1 (fun x => A x k)) (hAp : ∀ k, AVenhance.IsZ2Periodic (fun x => A x k)) :
    AVenhance.IsZ2Periodic (roStrR ν b a A) := by
  intro n x
  have hF : ∀ k, ContDiff ℝ 1 (fun x => (ν • gradE a x + A x) k) := fun k =>
    ((roStr_grad_contDiff ha k).const_smul ν).add (hA k)
  have hFp : ∀ k, AVenhance.IsZ2Periodic (fun x => (ν • gradE a x + A x) k) := fun k m y => by
    simp only [Pi.add_apply, Pi.smul_apply, roStr_grad_periodic ha hap k m y, hAp k m y]
  have hd : ∀ k, fderiv ℝ (fun y => (ν • gradE a y + A y) k) (x + AVenhance.latticeShift n)
      (basisVec k) = fderiv ℝ (fun y => (ν • gradE a y + A y) k) x (basisVec k) := fun k =>
    congrArg (fun L => L (basisVec k))
      (fderiv_isZ2Periodic ((hF k).differentiable one_ne_zero) (hFp k) n x)
  have hb : ∀ j, b (x + AVenhance.latticeShift n) j = b x j := fun j => by rw [hbp n x]
  have hg : ∀ j, gradE a (x + AVenhance.latticeShift n) j = gradE a x j := fun j =>
    roStr_grad_periodic ha hap j n x
  unfold roStrR divE
  simp only [hd, hb, hg]

/-- Periodic integration by parts at one time. -/
theorem roStr_spatial_identity (ν : ℝ) (b : Vec 2 → Vec 2) (a : Vec 2 → E)
    (A : Vec 2 → Fin 2 → E) (φ : Vec 2 → E)
    (ha : ContDiff ℝ 2 a) (hap : AVenhance.IsZ2Periodic a) (hb : Continuous b)
    (hA : ∀ k, ContDiff ℝ 1 (fun x => A x k)) (hAp : ∀ k, AVenhance.IsZ2Periodic (fun x => A x k))
    (hφ : ContDiff ℝ 1 φ) (hφp : AVenhance.IsZ2Periodic φ) :
    (∫ x in AVenhance.unitCube, (-(∑ k : Fin 2, b x k * inner ℝ (gradE a x k) (φ x))
        - ν * ∑ k : Fin 2, inner ℝ (gradE a x k) (gradE φ x k)
        - ∑ k : Fin 2, inner ℝ (A x k + (0 : E)) (gradE φ x k) + inner ℝ (0 : E) (φ x))) =
      ∫ x in AVenhance.unitCube, inner ℝ (roStrR ν b a A x) (φ x) := by
  have h := macroWeak_spatial_identity ν b a (roStrR ν b a A) A (fun _ _ => (0 : E)) φ ha hap
    (roStr_R_continuous ν ha hb hA) hA hAp (fun _ => contDiff_const) (fun _ _ _ => rfl) hφ hφp
    (fun x => by simp [roStrR, divE])
  simpa using h
end

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Weak-to-strong step of `ReadoutStrongEquationStatement`, for one component and one test:
the weak identity and the time primitive give `∫_{(tp,t]} G_φ = 0` for the pairing `G_φ` of the
defect `da - R` with `φ`. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The flux at one time as a plain function into `Fin 2 → E`. -/
def roStrFlux (A : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (s : ℝ) (y : Vec 2) : Fin 2 → E :=
  fun k => A s y k

/-- The defect `da - R` of the strong equation at time `s`. -/
def roStrDefect (ν : ℝ) (b : ℝ → Vec 2 → Vec 2) (a da : ℝ → Vec 2 → E)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (s : ℝ) (x : Vec 2) : E :=
  da s x - roStrR ν (b s) (a s) (roStrFlux A s) x

/-- The pairing of the defect with a test, integrated over the cell. -/
def roStrPairing (ν : ℝ) (b : ℝ → Vec 2 → Vec 2) (a da : ℝ → Vec 2 → E)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (φ : Vec 2 → E) (s : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube, inner ℝ (roStrDefect ν b a da A s x) (φ x)

/-- The classical regularity and time-primitive data used by the step. -/
structure RoStrData (tp tf ν : ℝ) (b : ℝ → Vec 2 → Vec 2) (a da : ℝ → Vec 2 → E)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) : Prop where
  ha : ∀ s ∈ Set.Icc tp tf, ContDiff ℝ 2 (a s)
  hap : ∀ s ∈ Set.Icc tp tf, AVenhance.IsZ2Periodic (a s)
  hdac : ∀ s ∈ Set.Icc tp tf, Continuous (da s)
  hdap : ∀ s ∈ Set.Icc tp tf, AVenhance.IsZ2Periodic (da s)
  hbc : ∀ s ∈ Set.Icc tp tf, Continuous (b s)
  hbp : ∀ s ∈ Set.Icc tp tf, AVenhance.IsZ2Periodic (b s)
  hAc : ∀ s ∈ Set.Icc tp tf, ∀ k, ContDiff ℝ 1 (fun x => A s x k)
  hAp : ∀ s ∈ Set.Icc tp tf, ∀ k, AVenhance.IsZ2Periodic (fun x => A s x k)
  hprim : ∀ x, ∀ s ∈ Set.Icc tp tf, a s x - a tp x = ∫ r in Set.Ioc tp s, da r x
  hmeas : Measurable (fun z : {z : ℝ × Vec 2 // z.1 ∈ Set.Icc tp tf} => da z.1.1 z.1.2)
  hB : ∃ B : ℝ → ℝ, IntegrableOn B (Set.Icc tp tf) ∧
    ∀ s ∈ Set.Icc tp tf, ∀ x ∈ AVenhance.unitCube, ‖da s x‖ ≤ B s

section
variable {tp tf ν : ℝ} {b : ℝ → Vec 2 → Vec 2} {a da : ℝ → Vec 2 → E}
  {A : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem roStr_defect_continuous (D : RoStrData tp tf ν b a da A)
    {s : ℝ} (hs : s ∈ Set.Icc tp tf) : Continuous (roStrDefect ν b a da A s) :=
  (D.hdac s hs).sub (roStr_R_continuous ν (D.ha s hs) (D.hbc s hs) (D.hAc s hs))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem roStr_defect_periodic (D : RoStrData tp tf ν b a da A)
    {s : ℝ} (hs : s ∈ Set.Icc tp tf) : AVenhance.IsZ2Periodic (roStrDefect ν b a da A s) :=
  fun n x => by
    have h := roStr_R_periodic ν (D.ha s hs) (D.hap s hs) (D.hbp s hs)
      (A := roStrFlux A s) (D.hAc s hs) (D.hAp s hs) n x
    unfold roStrDefect
    rw [D.hdap s hs n x, h]

end

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! For one component and one smooth periodic test: the weak identity, the time primitive of
`da` and periodic integration by parts give `∫_{(tp,t]} G_φ = 0`. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {tp tf ν : ℝ} {b : ℝ → Vec 2 → Vec 2} {a da : ℝ → Vec 2 → E}
  {A : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pairing of a continuous field with a continuous test is cell-integrable. -/
theorem roStr_inner_cell_integrable {f φ : Vec 2 → E} (hf : Continuous f) (hφ : Continuous φ) :
    Integrable (fun x => inner ℝ (f x) (φ x)) (volume.restrict AVenhance.unitCube) :=
  AVRegularity.CoupledEnergy.Galerkin.continuous_cell_integrable _ (hf.inner hφ)

theorem roStr_primitive_zero (D : RoStrData tp tf ν b a da A)
    (hweak : ∀ t ∈ Set.Icc tp tf, ∀ φ : Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) φ →
      AVenhance.IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν tp t b (a t) (a tp) φ
        (fun k x => gradE φ x k) (fun s k x => gradE (a s) x k) 0 A 0)
    {t : ℝ} (ht : t ∈ Set.Icc tp tf) {φ : Vec 2 → E}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφp : AVenhance.IsZ2Periodic φ) :
    IntegrableOn (roStrPairing ν b a da A φ) (Set.Ioc tp t) ∧
      ∫ s in Set.Ioc tp t, roStrPairing ν b a da A φ s = 0 := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hw := hweak t ht φ hφ hφp
  unfold CoupledWeakIdentity at hw
  obtain ⟨c1, c2, c3, c4, c5⟩ := hw
  have hsub : Set.Ioc tp t ⊆ Set.Icc tp tf := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  obtain ⟨-, hfub, hint⟩ := macroWeakTime tp tf t ht a da φ hφ1.continuous D.hprim D.hmeas D.hB
    c1 c2
  have hsp : ∀ s ∈ Set.Icc tp tf, ∫ x in AVenhance.unitCube,
      (-∑ k, b s x k * inner ℝ (gradE (a s) x k) (φ x) -
        ν * ∑ k, inner ℝ (gradE (a s) x k) (gradE φ x k) -
        ∑ k, inner ℝ (((0 : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) s x).ofLp k +
            (A s x).ofLp k)
          (gradE φ x k) + inner ℝ ((0 : ℝ → Vec 2 → E) s x) (φ x)) =
      ∫ x in AVenhance.unitCube, inner ℝ (roStrR ν (b s) (a s) (roStrFlux A s) x) (φ x) := by
    intro s hs
    have := roStr_spatial_identity ν (b s) (a s) (roStrFlux A s) φ (D.ha s hs) (D.hap s hs)
      (D.hbc s hs) (D.hAc s hs) (D.hAp s hs) hφ1 hφp
    simpa [roStrFlux] using this
  have hI2 : IntegrableOn (fun s => ∫ x in AVenhance.unitCube,
      inner ℝ (roStrR ν (b s) (a s) (roStrFlux A s) x) (φ x)) (Set.Ioc tp t) := by
    refine (integrableOn_congr_fun (fun s hs => ?_) measurableSet_Ioc).mp c4
    simpa using hsp s (hsub hs)
  have hpair : ∀ s ∈ Set.Icc tp tf, roStrPairing ν b a da A φ s =
      (∫ x in AVenhance.unitCube, inner ℝ (da s x) (φ x)) -
        ∫ x in AVenhance.unitCube, inner ℝ (roStrR ν (b s) (a s) (roStrFlux A s) x) (φ x) := by
    intro s hs
    unfold roStrPairing roStrDefect
    rw [← integral_sub (roStr_inner_cell_integrable (D.hdac s hs) hφ1.continuous)
      (roStr_inner_cell_integrable (roStr_R_continuous ν (A := roStrFlux A s) (D.ha s hs) (D.hbc s hs) (D.hAc s hs))
        hφ1.continuous)]
    simp only [inner_sub_left]
  have hcongr : Set.EqOn (roStrPairing ν b a da A φ) (fun s => (∫ x in AVenhance.unitCube,
      inner ℝ (da s x) (φ x)) - ∫ x in AVenhance.unitCube,
        inner ℝ (roStrR ν (b s) (a s) (roStrFlux A s) x) (φ x)) (Set.Ioc tp t) :=
    fun s hs => hpair s (hsub hs)
  refine ⟨(integrableOn_congr_fun hcongr measurableSet_Ioc).mpr (hint.sub hI2), ?_⟩
  have c5' : (∫ x in AVenhance.unitCube, inner ℝ (a t x) (φ x)) -
      (∫ x in AVenhance.unitCube, inner ℝ (a tp x) (φ x)) = ∫ s in Set.Ioc tp t,
        ∫ x in AVenhance.unitCube, inner ℝ (roStrR ν (b s) (a s) (roStrFlux A s) x) (φ x) :=
    c5.trans (setIntegral_congr_fun measurableSet_Ioc (fun s hs => by simpa using hsp s (hsub hs)))
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_sub hint hI2, ← hfub, c5', sub_self]

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-! Core of `ReadoutStrongEquationStatement` for one component: from the weak identity, the
defect `da - R` vanishes at every point for almost every time. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {tp tf ν : ℝ} {b : ℝ → Vec 2 → Vec 2} {a da : ℝ → Vec 2 → E}
  {A : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)}

theorem roStr_defect_ae_zero (hle : tp ≤ tf) (D : RoStrData tp tf ν b a da A)
    (hweak : ∀ t ∈ Set.Icc tp tf, ∀ φ : Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) φ →
      AVenhance.IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν tp t b (a t) (a tp) φ
        (fun k x => gradE φ x k) (fun s k x => gradE (a s) x k) 0 A 0) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)), ∀ x, roStrDefect ν b a da A s x = 0 := by
  obtain ⟨T, hT, hd⟩ := roStr_exists_countable_tests
  let e := stdOrthonormalBasis ℝ E
  have hall : ∀ n, ∀ i, ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)),
      roStrPairing ν b a da A (fun x => T n x • e i) s = 0 := by
    intro n i
    have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun x => T n x • e i) := (hT n).1.smul contDiff_const
    have hφp : AVenhance.IsZ2Periodic (fun x => T n x • e i) := fun m x => by
      simp only [(hT n).2 m x]
    have hI := (roStr_primitive_zero D hweak ⟨hle, le_rfl⟩ hφ hφp).1
    exact roStr_ae_zero_of_primitive_zero hle hI fun t ht =>
      (roStr_primitive_zero D hweak ht hφ hφp).2
  have hae := ae_all_iff.2 fun n => ae_all_iff.2 (hall n)
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with s hs hsI x
  have hcont := roStr_defect_continuous D hsI
  have hper := roStr_defect_periodic D hsI
  have hcoord : ∀ i, ∀ y, inner ℝ (roStrDefect ν b a da A s y) (e i) = 0 := by
    intro i
    refine roStr_zero_of_tests (hcont.inner continuous_const) (fun m y => ?_) ?_
    · simp only [hper m y]
    · refine roStr_pairing_zero_of_tests (hcont.inner continuous_const) T hT hd ?_
      intro n
      have := hs n i
      unfold roStrPairing at this
      rw [← this]
      congr 1
      funext y
      simp only [inner_smul_right, mul_comm]
  have hsum := e.sum_repr' (roStrDefect ν b a da A s x)
  rw [← hsum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [real_inner_comm, hcoord i x, zero_smul]

end AVRegularity.Construction.Preservation.Residual.CovarianceTransport
end
