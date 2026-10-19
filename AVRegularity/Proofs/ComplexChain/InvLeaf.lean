-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexChain.VelChild
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.RingTheory.PicardGroup

/-! **Certificates of the own-frame letters as functions of the Jacobian**. A scalar function
`Φ` of the complex Jacobian matrix, with real counterpart `φ`, that is holomorphic where
`det ≠ 0`, measurable, and bounded by `B m` on `1 + E` with rows of `ℓ¹` norm at most `m ≤ 1/2`
(`EntryFun Φ φ B`), gives a certified own-frame leaf over every slot (`ownLeafExt`,
`ownLeaf_isHolExtension`, `ownLeaf_ctxModeSup_le`): its extension on scheduled data and the
outer carrier is `Φ (F_t(0))` of the last family, it does not depend on the final phase, and its
zero mode is at most `B (K a_{i-1} (6/5) h_i)`.
Instances: the entries of `F⁻¹ − I` (`invSub_entryFun`) and of `𝒢 − I`, `𝒢 = F⁻¹F⁻ᵀ`
(`metricSub_entryFun`). -/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Homogenization AVenhance Metric
open scoped ENNReal

namespace AVRegularity.Providers.ComplexFlow

/-! ### Row bounds of the complex Jacobian -/

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]
variable {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ Λ T : ℝ}

/-- **The rows of `F_t(0) − I` are small.** -/
theorem rowSmall_jacC (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {t : ℝ} (ht : t ∈ W) :
    RowSmall (F.jacC P t - 1) (Λ * |t - F.anc|) := by
  have hc : F.ctr P ∈ ball (F.cur P F.anc) ϱ := by
    rw [h.cur_anc P hP]; exact mem_ball_self h.hϱ
  have hJ := h.jac P hP t ht F.anc h.anc_mem (F.ctr P) hc
  set L := fderiv ℂ (fun y => F.fl P t y F.anc) (F.ctr P)
  have e : ∀ a c, (F.jacC P t - 1) a c = ((L - ContinuousLinearMap.id ℂ CVec) (cbasis c)) a := by
    intro a c
    show L (cbasis c) a - (1 : Matrix (Fin 2) (Fin 2) ℂ) a c = _
    rw [sub_apply, ContinuousLinearMap.id_apply, Pi.sub_apply, Matrix.one_apply]
    congr 1
    unfold cbasis
    by_cases hac : a = c
    · subst hac; simp
    · simp [hac]
  have hrow : ∀ a, ‖(F.jacC P t - 1) a 0‖ + ‖(F.jacC P t - 1) a 1‖ ≤ Λ * |t - F.anc| := by
    intro a
    have := sum_norm_row_le (L - ContinuousLinearMap.id ℂ CVec) a
    rw [Fin.sum_univ_two] at this
    rw [e, e]
    exact this.trans hJ
  exact ⟨hrow 0, hrow 1⟩

/-- The window bound of the rows. -/
theorem row_bound_le_half (h : F.OK Ω W ϱ Λ T) {t : ℝ} (ht : t ∈ W) : Λ * |t - F.anc| ≤ 1 / 2 :=
  (mul_le_mul_of_nonneg_left (h.hT t ht F.anc h.anc_mem) h.hΛ).trans h.hΛT

end CFam

theorem RowSmall.mono {E : Matrix (Fin 2) (Fin 2) ℂ} {m m' : ℝ} (h : RowSmall E m) (hm : m ≤ m') :
    RowSmall E m' := ⟨h.row0.trans hm, h.row1.trans hm⟩

/-! ### Entry functions -/

/-- **A certifiable function of the Jacobian matrix**: `Φ` is holomorphic along holomorphic
matrix families with nonzero determinant, measurable, restricts to `φ` at real matrices, and is
bounded by `B m` on perturbations of the identity with rows at most `m ≤ 1/2`. -/
structure EntryFun (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
    (B : ℝ → ℝ) : Prop where
  hol : ∀ (n : ℕ) (U : Set (ChainParamsC n)) (M : ChainParamsC n → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ a c, DifferentiableOn ℂ (fun x => M x a c) U) → (∀ x ∈ U, (M x).det ≠ 0) →
      DifferentiableOn ℂ (fun x => Φ (M x)) U
  meas : Measurable Φ
  real : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, Φ (A.map fun r : ℝ => (r : ℂ)) = ((φ A : ℝ) : ℂ)
  bd : ∀ (E : Matrix (Fin 2) (Fin 2) ℂ) (m : ℝ), RowSmall E m → m ≤ 1 / 2 → ‖Φ (1 + E)‖ ≤ B m
  B_nonneg : ∀ m, 0 ≤ m → 0 ≤ B m

/-- The determinant of the complex Jacobian of a family is nonzero. -/
theorem CFam.det_jacC_ne_zero {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]
    {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ Λ T : ℝ} (h : F.OK Ω W ϱ Λ T) {P : Par}
    (hP : P ∈ Ω) {t : ℝ} (ht : t ∈ W) : (F.jacC P t).det ≠ 0 := by
  have hr := (CFam.rowSmall_jacC h hP ht).mono (CFam.row_bound_le_half h ht)
  have hd := norm_det_ge hr (by norm_num)
  rw [add_sub_cancel] at hd
  intro h0
  rw [h0, norm_zero] at hd
  norm_num at hd

open scoped Classical in
/-- **The extension of an own-frame leaf** `Φ(F_t(0))` over the slot `p` of level `i`. -/
def ownLeafExt (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ) :
    ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ :=
  fun dd n t x =>
    if GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2 then Φ ((chainFam D dd n).jacC x t)
    else 0

variable {D : OCData} {b CH Υ : ℝ} {j₀ : ℕ}

/-- An own-frame leaf does not depend on the final phase. -/
theorem ownLeafExt_shift (hΛ : 1 ≤ D.Λ) {i : ℕ} {p : ℤ} (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {dd : ChainData} {n : ℕ} (t : ℝ) (x : ChainParamsC n) (v : CVec) (hv : ∀ a', (v a').im = 0) :
    ownLeafExt D b j₀ i p Φ dd n t (x.1, x.2.1, x.2.2 + v) = ownLeafExt D b j₀ i p Φ dd n t x := by
  classical
  have hmem : ((x.1, x.2.1, x.2.2 + v) : ChainParamsC n) ∈ carrierC D b dd n 2 ↔
      x ∈ carrierC D b dd n 2 := by
    unfold carrierC
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Complex.add_im, hv, add_zero]
  have hjac : (chainFam D dd n).jacC (x.1, x.2.1, x.2.2 + v) t = (chainFam D dd n).jacC x t := by
    have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ).ne'
    have e : (chainFam D dd n).toGeom (x.1, x.2.1, x.2.2 + v) = (chainFam D dd n).toGeom x := by
      rw [chainFam_toGeom D hε, chainFam_toGeom D hε]
      rfl
    unfold CFam.jacC
    have e1 : (chainFam D dd n).fl (x.1, x.2.1, x.2.2 + v) = (chainFam D dd n).fl x :=
      congrArg Prod.fst e
    have e2 : (chainFam D dd n).ctr (x.1, x.2.1, x.2.2 + v) = (chainFam D dd n).ctr x :=
      congrArg (fun g : CGeom => g.2.1) e
    rw [e1, e2]
  unfold ownLeafExt
  rw [hmem, hjac]

/-- **The size of an own-frame leaf**, uniformly in the output time. -/
theorem norm_ownLeafExt_le (env : ChainEnv D b CH Υ j₀) (i : ℕ) (p : ℤ)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {B : ℝ → ℝ}
    (hΦ : EntryFun Φ φ B) (dd : ChainData) (n : ℕ) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) (x : ChainParamsC n) :
    ‖ownLeafExt D b j₀ i p Φ dd n t x‖ ≤
      B (chainK * ocA D.α D.q D.Λ (i - 1) * (6 / 5 * ocTauPP D.α D.q D.Λ i)) := by
  classical
  have hΛ1 := env.hΛ1
  have hm0 : 0 ≤ chainK * ocA D.α D.q D.Λ (i - 1) * (6 / 5 * ocTauPP D.α D.q D.Λ i) :=
    mul_nonneg (mul_nonneg (by rw [chainK_eq]; norm_num)
      (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _))
      (mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos hΛ1).le)
  by_cases hgx : GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2
  · have hO := env.chainFam_over hgx.1.1
    have htW := hgx.1.mem_slotWin hΛ1 ht
    simp only [ownLeafExt, hgx, and_self, ite_true]
    have hi : dd.baseLevel + n = i - 1 := by have := hgx.1.2.2; omega
    have hi' : i = dd.baseLevel + n + 1 := hgx.1.2.2.symm
    have hanc : (chainFam D dd n).anc = D.slotAnchor (dd.baseLevel + n + 1)
        (dd.slots.getLastD 0) := hO.anc
    have hst : |t - (chainFam D dd n).anc| ≤ 6 / 5 * ocTauPP D.α D.q D.Λ i := by
      rw [hanc]
      have := abs_sub_le_of_mem_slotWin D htW
        (anchor_mem_slotWin D hΛ1 (dd.baseLevel + n + 1) (dd.slots.getLastD 0))
      calc _ ≤ 6 / 5 * ocTauPP D.α D.q D.Λ (dd.baseLevel + n + 1) := this
        _ = 6 / 5 * ocTauPP D.α D.q D.Λ i := by rw [hgx.1.2.2]
    have hr := CFam.rowSmall_jacC hO.ok hgx.2 htW
    have hmle : chainK * ocA D.α D.q D.Λ (dd.baseLevel + n) * |t - (chainFam D dd n).anc| ≤
        chainK * ocA D.α D.q D.Λ (i - 1) * (6 / 5 * ocTauPP D.α D.q D.Λ i) := by
      rw [hi]
      exact mul_le_mul_of_nonneg_left hst (mul_nonneg (by rw [chainK_eq]; norm_num)
        (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _))
    have hhalf : chainK * ocA D.α D.q D.Λ (i - 1) * (6 / 5 * ocTauPP D.α D.q D.Λ i) ≤ 1 / 2 := by
      have := hO.ok.hΛT
      rw [← hi, hi']
      exact this
    have h1 := hΦ.bd _ _ (hr.mono hmle) hhalf
    rwa [add_sub_cancel] at h1
  · simp only [ownLeafExt, hgx, ite_false, norm_zero]
    exact hΦ.B_nonneg _ hm0

/-- An own-frame leaf is invariant under the child-phase translations. -/
theorem ownLeafExt_shiftChild (hΛ : 1 ≤ D.Λ) {i : ℕ} {p : ℤ} (Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    {dd : ChainData} {n : ℕ} (t : ℝ) (x : ChainParamsC n) (k : Fin n) {v : Vec 2}
    (hv : ∃ m : ℤ, v (transverseIndex (dd.slots.getD k 0)) = m) :
    ownLeafExt D b j₀ i p Φ dd n t (x.shiftChild k v) = ownLeafExt D b j₀ i p Φ dd n t x := by
  classical
  have hε : ∀ k, D.eps k ≠ 0 := fun k => (Construction.Stream.ocEpsilon_pos hΛ).ne'
  unfold ownLeafExt
  rw [mem_carrierC_shiftChild_iff, jacC_chainFam_shiftChild D hε dd x k hv]

/-- **An own-frame leaf has a holomorphic, time-measurable extension.** -/
theorem ownLeaf_isHolExtension (env : ChainEnv D b CH Υ j₀) (i : ℕ) (p : ℤ)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {B : ℝ → ℝ}
    (hΦ : EntryFun Φ φ B) :
    IsHolExtension D b j₀ i p (fun t ch _ => φ (ch.famJac D t)) (ownLeafExt D b j₀ i p Φ) := by
  classical
  have hΛ1 := env.hΛ1
  refine ⟨fun dd n t ht => ?_, ⟨fun dd n x => ?_, fun dd n t ht x _ =>
    ⟨fun v _ => ownLeafExt_shift hΛ1 Φ t x (fun a' => (v a' : ℂ)) (fun a' => by simp),
      fun k v hv => ownLeafExt_shiftChild hΛ1 Φ t x k hv⟩, fun dd n x hx =>
    ⟨_, (isOpen_carrierC D b dd n 2).mem_nhds hx, _, fun t ht y _ =>
      norm_ownLeafExt_le env i p hΦ dd n ht y⟩⟩, fun ch t ht ζ hch => ?_⟩
  · by_cases hg : GoodData D j₀ i p dd n
    · have hO := env.chainFam_over hg.1
      have htW := hg.mem_slotWin hΛ1 ht
      have hd := hΦ.hol n (carrierC D b dd n 2) (fun x => (chainFam D dd n).jacC x t)
        (fun a c => CFam.differentiableOn_jacC hO.ok htW a c)
        (fun x hx => CFam.det_jacC_ne_zero hO.ok hx htW)
      refine hd.congr fun x hx => ?_
      simp [ownLeafExt, hg, hx]
    · have : ownLeafExt D b j₀ i p Φ dd n t = fun _ => 0 := by
        funext x; simp [ownLeafExt, hg]
      rw [this]; exact differentiableOn_const 0
  · by_cases hgx : GoodData D j₀ i p dd n ∧ x ∈ carrierC D b dd n 2
    · have hO := env.chainFam_over hgx.1.1
      have hS : ocPulseWindow D.α D.q D.Λ i p ⊆
          slotWin D (dd.baseLevel + n + 1) (dd.slots.getLastD 0) := fun t ht =>
        hgx.1.mem_slotWin hΛ1 ht
      have hM : Measurable fun t : ocPulseWindow D.α D.q D.Λ i p => (chainFam D dd n).jacC x t :=
        measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun c =>
          CFam.measurable_jacC hO.ok hO.cont hgx.2 hS a c
      have e : (fun t : ocPulseWindow D.α D.q D.Λ i p => ownLeafExt D b j₀ i p Φ dd n t x) =
          fun t : ocPulseWindow D.α D.q D.Λ i p => Φ ((chainFam D dd n).jacC x t) := by
        funext t; simp [ownLeafExt, hgx]
      rw [e]; exact hΦ.meas.comp hM
    · have : (fun t : ocPulseWindow D.α D.q D.Λ i p => ownLeafExt D b j₀ i p Φ dd n t x) =
          fun _ => 0 := by
        funext t; simp [ownLeafExt, hgx]
      rw [this]; exact measurable_const
  · have hdd := chainOK_of_admissible hch
    have hg : GoodData D j₀ i p ch.data ch.children.length := ⟨hdd, hch.2.2.2.1, hch.1⟩
    have hx := GenSem.paramsC_mem_carrierC hΛ1 env.hb0 hch ζ
    simp only [ownLeafExt, hg, hx, and_self, ite_true]
    have hJ : (chainFam D ch.data ch.children.length).jacC (ch.paramsC ζ) t =
        (ch.famJac D t).map fun r : ℝ => (r : ℂ) := by
      ext a c
      rw [jacC_chainFam_real env hch ζ (ocPulseWindow_subset_slotWin hΛ1 i p ht) a c]
      rfl
    rw [hJ, hΦ.real]

/-- **The mode bound of an own-frame leaf.** -/
theorem ownLeaf_ctxModeSup_le (env : ChainEnv D b CH Υ j₀) (i : ℕ) (p : ℤ)
    {Φ : Matrix (Fin 2) (Fin 2) ℂ → ℂ} {φ : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {B : ℝ → ℝ}
    (hΦ : EntryFun Φ φ B) (mres : ℝ) (h : ℤ) :
    ctxModeSup D b j₀ i p (ownLeafExt D b j₀ i p Φ) mres h ≤
      if h = 0 then ENNReal.ofReal (B (chainK * ocA D.α D.q D.Λ (i - 1) *
        (6 / 5 * ocTauPP D.α D.q D.Λ i))) else 0 := by
  classical
  have hΛ1 := env.hΛ1
  have hm0 : 0 ≤ chainK * ocA D.α D.q D.Λ (i - 1) * (6 / 5 * ocTauPP D.α D.q D.Λ i) :=
    mul_nonneg (mul_nonneg (by rw [chainK_eq]; norm_num)
      (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _))
      (mul_nonneg (by norm_num) (Construction.Stream.ocTauPP_pos hΛ1).le)
  refine iSup_le fun dd => iSup_le fun n => iSup_le fun _ => iSup_le fun t => iSup_le fun ht =>
    iSup_le fun x => iSup_le fun _ => iSup_le fun hre => ?_
  rw [finalPhaseCoeff_of_invariant _ (fun s => ownLeafExt_shift hΛ1 Φ t x _ (fun a' => by
    split_ifs <;> simp))]
  split_ifs with h0
  · rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_ownLeafExt_le env i p hΦ dd n ht x)
  · simp

/-! ### Instances -/

theorem inv_map_ofReal (A : Matrix (Fin 2) (Fin 2) ℝ) (a c : Fin 2) :
    (A.map fun r : ℝ => (r : ℂ))⁻¹ a c = ((A⁻¹ a c : ℝ) : ℂ) := by
  rw [inv_apply_fin_two, inv_apply_fin_two, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two,
    Matrix.det_fin_two, Matrix.det_fin_two]
  fin_cases a <;> fin_cases c <;> simp [Matrix.map_apply]

/-- The entries of a holomorphic matrix family with nonzero determinant have holomorphic
inverses. -/
theorem differentiableOn_inv_apply {n : ℕ} {U : Set (ChainParamsC n)}
    {M : ChainParamsC n → Matrix (Fin 2) (Fin 2) ℂ}
    (hM : ∀ a c, DifferentiableOn ℂ (fun x => M x a c) U) (hd : ∀ x ∈ U, (M x).det ≠ 0)
    (a c : Fin 2) : DifferentiableOn ℂ (fun x => (M x)⁻¹ a c) U := by
  have hdet : DifferentiableOn ℂ (fun x => (M x).det) U := by
    simp_rw [Matrix.det_fin_two]
    exact ((hM 0 0).mul (hM 1 1)).sub ((hM 0 1).mul (hM 1 0))
  have hadj : DifferentiableOn ℂ (fun x => (M x).adjugate a c) U := by
    simp_rw [Matrix.adjugate_fin_two]
    fin_cases a <;> fin_cases c <;> simp
    · exact hM 1 1
    · exact hM 0 1
    · exact hM 1 0
    · exact hM 0 0
  simp_rw [inv_apply_fin_two]
  exact (hdet.inv hd).mul hadj

/-- **The entries of `F⁻¹ − I`.** -/
theorem invSub_entryFun (a c : Fin 2) :
    EntryFun (fun A => A⁻¹ a c - (if a = c then 1 else 0))
      (fun A => A⁻¹ a c - (if a = c then 1 else 0)) (fun m => m * (1 + m) / (1 - m) ^ 2) where
  hol := fun n U M hM hd => (differentiableOn_inv_apply hM hd a c).sub_const _
  meas := by
    have h1 : Measurable fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹ a c := by
      simp_rw [inv_apply_fin_two, Matrix.adjugate_fin_two, Matrix.det_fin_two]
      fin_cases a <;> fin_cases c <;> simp <;> fun_prop
    exact h1.sub_const _
  real := fun A => by rw [inv_map_ofReal]; split_ifs <;> simp
  bd := fun E m hE hm => norm_inv_sub_one_le hE (by linarith) a c
  B_nonneg := fun m hm => by
    by_cases h1 : m = 1
    · subst h1; simp
    · positivity

/-- The metric of a perturbed identity: `(1 + G)(1 + G)ᵀ − I` has entries at most `2g + 2g²`. -/
theorem norm_mul_transpose_sub_one_le {G : Matrix (Fin 2) (Fin 2) ℂ} {g : ℝ}
    (hG : ∀ i j, ‖G i j‖ ≤ g) (a c : Fin 2) :
    ‖((1 + G) * (1 + G).transpose) a c - (if a = c then 1 else 0)‖ ≤ 2 * g + 2 * g ^ 2 := by
  have hg : 0 ≤ g := (norm_nonneg _).trans (hG 0 0)
  have hp : ∀ i j k l, ‖G i j * G k l‖ ≤ g ^ 2 := fun i j k l => by
    rw [norm_mul, sq]; exact mul_le_mul (hG i j) (hG k l) (norm_nonneg _) hg
  fin_cases a <;> fin_cases c <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.one_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one, ↓reduceIte, zero_ne_one,
      one_ne_zero]
  · have e : (1 + G 0 0) * (1 + G 0 0) + (0 + G 0 1) * (0 + G 0 1) - 1 =
        G 0 0 + G 0 0 + (G 0 0 * G 0 0 + G 0 1 * G 0 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (by linarith [hG 0 0])) ((norm_add_le _ _).trans ?_)
    linarith [hp 0 0 0 0, hp 0 1 0 1]
  · have e : (1 + G 0 0) * (0 + G 1 0) + (0 + G 0 1) * (1 + G 1 1) - 0 =
        G 1 0 + G 0 1 + (G 0 0 * G 1 0 + G 0 1 * G 1 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (by linarith [hG 1 0, hG 0 1]))
      ((norm_add_le _ _).trans ?_)
    linarith [hp 0 0 1 0, hp 0 1 1 1]
  · have e : (0 + G 1 0) * (1 + G 0 0) + (1 + G 1 1) * (0 + G 0 1) - 0 =
        G 1 0 + G 0 1 + (G 1 0 * G 0 0 + G 1 1 * G 0 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (by linarith [hG 1 0, hG 0 1]))
      ((norm_add_le _ _).trans ?_)
    linarith [hp 1 0 0 0, hp 1 1 0 1]
  · have e : (0 + G 1 0) * (0 + G 1 0) + (1 + G 1 1) * (1 + G 1 1) - 1 =
        G 1 1 + G 1 1 + (G 1 0 * G 1 0 + G 1 1 * G 1 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (by linarith [hG 1 1])) ((norm_add_le _ _).trans ?_)
    linarith [hp 1 0 1 0, hp 1 1 1 1]

/-- The bound of the entries of `𝒢 − I` in terms of the rows of `F − I`. -/
def metricB (m : ℝ) : ℝ :=
  2 * (m * (1 + m) / (1 - m) ^ 2) + 2 * (m * (1 + m) / (1 - m) ^ 2) ^ 2

/-- **The entries of `𝒢 − I`, `𝒢 = F⁻¹F⁻ᵀ`.** -/
theorem metricSub_entryFun (a c : Fin 2) :
    EntryFun (fun A => (A⁻¹ * A⁻¹.transpose) a c - (if a = c then 1 else 0))
      (fun A => (A⁻¹ * A⁻¹.transpose) a c - (if a = c then 1 else 0)) metricB where
  hol := fun n U M hM hd => by
    have h : ∀ i j, DifferentiableOn ℂ (fun x => (M x)⁻¹ i j) U :=
      fun i j => differentiableOn_inv_apply hM hd i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    exact (((h a 0).mul (h c 0)).add ((h a 1).mul (h c 1))).sub_const _
  meas := by
    have h1 : ∀ i j, Measurable fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹ i j := by
      intro i j
      simp_rw [inv_apply_fin_two, Matrix.adjugate_fin_two, Matrix.det_fin_two]
      fin_cases i <;> fin_cases j <;> simp <;> fun_prop
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    exact ((((h1 a 0).mul (h1 c 0)).add ((h1 a 1).mul (h1 c 1)))).sub_const _
  real := fun A => by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, inv_map_ofReal]
    split_ifs <;> push_cast <;> ring
  bd := fun E m hE hm => by
    set G := (1 + E)⁻¹ - 1 with hG_def
    have hG : ∀ i j, ‖G i j‖ ≤ m * (1 + m) / (1 - m) ^ 2 := fun i j => by
      have := norm_inv_sub_one_le hE (by linarith) i j
      have e1 : G i j = (1 + E)⁻¹ i j - (if i = j then 1 else 0) := by
        rw [hG_def, Matrix.sub_apply, Matrix.one_apply]
      rw [e1]; exact this
    have e : (1 + E)⁻¹ = 1 + G := by rw [hG_def]; abel
    show ‖((1 + E)⁻¹ * ((1 + E)⁻¹).transpose) a c - (if a = c then 1 else 0)‖ ≤ metricB m
    rw [e]
    exact norm_mul_transpose_sub_one_le hG a c
  B_nonneg := fun m hm => by
    unfold metricB
    by_cases h1 : m = 1
    · subst h1; simp
    · positivity

end AVRegularity.Providers.ComplexFlow
