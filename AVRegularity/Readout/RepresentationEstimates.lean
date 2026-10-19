-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Readout.RepresentedSize
public import AVRegularity.Statements.Intermediate.Readout.IsRepresentationAt
public import AVRegularity.Statements.Intermediate.Readout.RepresentationValue
public import AVRegularity.Statements.Intermediate.Readout.HolderNorm

@[expose] public section

section
open Homogenization
namespace AVRegularity.Readout

/-! Algebraic lemmas for the iterated coordinate derivatives used by the readout lemma
`iteration_readout`. -/

variable {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup H'] [NormedSpace ℝ H']

/-- One coordinate directional derivative as an operator on fields. -/
noncomputable def along (v : Vec 2) (F : Vec 2 → H) : Vec 2 → H :=
  fun x => fderiv ℝ F x v

theorem along_contDiff {n : ℕ} (v : Vec 2) (F : Vec 2 → H)
    (hF : ContDiff ℝ (n + 1) F) : ContDiff ℝ n (along v F) := by
  have hpair : ContDiff ℝ n (fun x : Vec 2 => (x, v)) := by fun_prop
  have hjoint := hF.contDiff_fderiv_apply (m := n) le_rfl
  change ContDiff ℝ n (fun x => fderiv ℝ F x v)
  simpa [Function.comp_def] using hjoint.comp hpair

theorem along_add (v : Vec 2) (F G : Vec 2 → H)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) :
    along v (F + G) = along v F + along v G := by
  funext x
  simp [along, fderiv_add (hF x) (hG x)]

theorem along_comp (R : H →L[ℝ] H') (v : Vec 2) (F : Vec 2 → H)
    (hF : Differentiable ℝ F) :
    along v (fun x => R (F x)) = fun x => R (along v F x) := by
  funext x
  have hR : DifferentiableAt ℝ (R : H → H') (F x) := R.differentiableAt
  change (fderiv ℝ (R ∘ F) x) v = R ((fderiv ℝ F x) v)
  have hc := fderiv_comp x hR (hF x)
  rw [hc]
  simp [R.fderiv]

theorem along_contDiff_iterate {n m : ℕ} (v : Vec 2) (F : Vec 2 → H)
    (hF : ContDiff ℝ ((n + m : ℕ) : ℕ∞) F) :
    ContDiff ℝ n ((along v)^[m] F) := by
  induction m generalizing n F with
  | zero => simpa using hF
  | succ m ih =>
      have heq : n + (m + 1) = (n + 1) + m := by omega
      have hF' : ContDiff ℝ ((n + 1 + m : ℕ) : ℕ∞) F := by
        simpa only [Nat.cast_add, Nat.cast_one, heq] using hF
      have hmid : ContDiff ℝ (n + 1) ((along v)^[m] F) :=
        ih (n := n + 1) (F := F) hF'
      have hout := along_contDiff v ((along v)^[m] F) hmid
      have hs : ContDiff ℝ n ((along v)^[m + 1] F) := by
        simpa only [Function.iterate_succ_apply'] using hout
      simpa only [Function.iterate_succ_apply] using hs

theorem along_iterate_add {n m : ℕ} (v : Vec 2) (F G : Vec 2 → H)
    (hF : ContDiff ℝ ((n + m : ℕ) : ℕ∞) F) (hG : ContDiff ℝ ((n + m : ℕ) : ℕ∞) G) :
    ((along v)^[m] (F + G)) = ((along v)^[m] F) + ((along v)^[m] G) := by
  induction m generalizing n F G with
  | zero => simp
  | succ m ih =>
      have hF' : ContDiff ℝ (n + 1) ((along v)^[m] F) := by
        apply along_contDiff_iterate (n := n + 1) (m := m)
        have heq : n + (m + 1) = n + 1 + m := by omega
        simpa only [Nat.cast_add, Nat.cast_one, heq] using hF
      have hG' : ContDiff ℝ (n + 1) ((along v)^[m] G) := by
        apply along_contDiff_iterate (n := n + 1) (m := m)
        have heq : n + (m + 1) = n + 1 + m := by omega
        simpa only [Nat.cast_add, Nat.cast_one, heq] using hG
      have hFdiff : Differentiable ℝ ((along v)^[m] F) :=
        hF'.differentiable (by simp)
      have hGdiff : Differentiable ℝ ((along v)^[m] G) :=
        hG'.differentiable (by simp)
      simp only [Function.iterate_succ_apply']
      rw [ih (n := n + 1) (F := F) (G := G)
        (by
          have heq : n + (m + 1) = n + 1 + m := by omega
          simpa only [Nat.cast_add, Nat.cast_one, heq] using hF)
        (by
          have heq : n + (m + 1) = n + 1 + m := by omega
          simpa only [Nat.cast_add, Nat.cast_one, heq] using hG)]
      exact along_add v _ _ hFdiff hGdiff

theorem along_iterate_comp {K m : ℕ} (v : Vec 2) (R : H →L[ℝ] H')
    (hm : m ≤ K) (F : Vec 2 → H) (hF : ContDiff ℝ K F) :
    ((along v)^[m] (fun x => R (F x))) = fun x => R (((along v)^[m] F) x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hFmid : ContDiff ℝ 1 ((along v)^[m] F) := by
        apply along_contDiff_iterate (n := 1) (m := m)
        have hle : 1 + m ≤ K := by omega
        exact hF.of_le (by exact_mod_cast hle)
      rw [Function.iterate_succ_apply']
      rw [ih (by omega)]
      simpa only [Function.iterate_succ_apply'] using
        along_comp R v ((along v)^[m] F) (hFmid.differentiable (by simp))

theorem partialDerivative_add {K : ℕ} (α : Fin 2 → ℕ)
    (hα : α 0 + α 1 ≤ K) (F G : Vec 2 → H)
    (hF : ContDiff ℝ K F) (hG : ContDiff ℝ K G) :
    partialDerivative α (F + G) = partialDerivative α F + partialDerivative α G := by
  rw [show partialDerivative α (F + G) =
    ((along (basisVec 1))^[α 1]) (((along (basisVec 0))^[α 0]) (F + G)) by rfl]
  rw [show partialDerivative α F =
    ((along (basisVec 1))^[α 1]) (((along (basisVec 0))^[α 0]) F) by rfl]
  rw [show partialDerivative α G =
    ((along (basisVec 1))^[α 1]) (((along (basisVec 0))^[α 0]) G) by rfl]
  have h0 := along_iterate_add (n := α 1) (m := α 0) (basisVec 0) F G
  have h0F : ContDiff ℝ ((α 1 + α 0 : ℕ) : ℕ∞) F := by
    exact hF.of_le (by exact_mod_cast (Nat.add_comm (α 0) (α 1) ▸ hα))
  have h0G : ContDiff ℝ ((α 1 + α 0 : ℕ) : ℕ∞) G := by
    exact hG.of_le (by exact_mod_cast (Nat.add_comm (α 0) (α 1) ▸ hα))
  have hfirst := h0 h0F h0G
  have hFmid : ContDiff ℝ (α 1) (((along (basisVec 0))^[α 0]) F) := by
    apply along_contDiff_iterate (n := α 1) (m := α 0)
    exact h0F
  have hGmid : ContDiff ℝ (α 1) (((along (basisVec 0))^[α 0]) G) := by
    apply along_contDiff_iterate (n := α 1) (m := α 0)
    exact h0G
  have hsecond := along_iterate_add (n := 0) (m := α 1) (basisVec 1)
    (((along (basisVec 0))^[α 0]) F) (((along (basisVec 0))^[α 0]) G)
    (by simpa using hFmid) (by simpa using hGmid)
  rw [hfirst]
  exact hsecond

theorem partialDerivative_comp {K : ℕ} (α : Fin 2 → ℕ)
    (hα : α 0 + α 1 ≤ K) (R : H →L[ℝ] H') (F : Vec 2 → H)
    (hF : ContDiff ℝ K F) :
    partialDerivative α (fun x => R (F x)) = fun x => R (partialDerivative α F x) := by
  rw [show partialDerivative α (fun x => R (F x)) =
    ((along (basisVec 1))^[α 1]) (((along (basisVec 0))^[α 0]) (fun x => R (F x))) by rfl]
  rw [show partialDerivative α F =
    ((along (basisVec 1))^[α 1]) (((along (basisVec 0))^[α 0]) F) by rfl]
  have hα0K : α 0 ≤ K := by omega
  have hα1K : α 1 ≤ K - α 0 := by omega
  have h0 := along_iterate_comp (K := K) (m := α 0) (basisVec 0) R hα0K F hF
  let K₁ := K - α 0
  have hsum : K₁ + α 0 = K := by
    dsimp [K₁]
    omega
  have hFbase : ContDiff ℝ ((K₁ + α 0 : ℕ) : ℕ∞) F := by
    rw [hsum]
    exact hF
  have hFmid : ContDiff ℝ K₁ (((along (basisVec 0))^[α 0]) F) := by
    exact along_contDiff_iterate (n := K₁) (m := α 0) (basisVec 0) F hFbase
  have h1 := along_iterate_comp (K := K₁) (m := α 1) (basisVec 1) (R := R)
    hα1K (((along (basisVec 0))^[α 0]) F) hFmid
  rw [h0, h1]

end AVRegularity.Readout
end

section
open Homogenization
open scoped BigOperators
namespace AVRegularity.Readout

/-! Differential and periodic-geodesic estimates for the torus Hölder seminorm. -/

theorem pi_norm_le_vecEuclidean (v : Vec 2) :
    ‖v‖ ≤ Real.sqrt (vecNormSq v) := by
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  have hsq := sq_apply_le_vecNormSq v i
  have hroot := Real.sq_sqrt (vecNormSq_nonneg v)
  have habs : |v i| ≤ Real.sqrt (vecNormSq v) := by
    have habsSq : |v i| ^ 2 ≤ Real.sqrt (vecNormSq v) ^ 2 := by
      simpa [sq_abs] using hsq.trans_eq hroot.symm
    nlinarith [abs_nonneg (v i), Real.sqrt_nonneg (vecNormSq v)]
  simpa [Real.norm_eq_abs] using habs

theorem fderiv_opNorm_le_coordinate_sum {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : Vec 2 →L[ℝ] H) :
    ‖L‖ ≤ ‖L (basisVec 0)‖ + ‖L (basisVec 1)‖ := by
  apply (ContinuousLinearMap.opNorm_le_iff (by positivity)).2
  intro v
  have hv0 : ‖v 0‖ ≤ ‖v‖ := (pi_norm_le_iff_of_nonempty v).1 le_rfl 0
  have hv1 : ‖v 1‖ ≤ ‖v‖ := (pi_norm_le_iff_of_nonempty v).1 le_rfl 1
  have hvrepr : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  have hLv : L v = v 0 • L (basisVec 0) + v 1 • L (basisVec 1) := by
    calc
      L v = L (v 0 • basisVec 0 + v 1 • basisVec 1) := congrArg L hvrepr
      _ = v 0 • L (basisVec 0) + v 1 • L (basisVec 1) := by simp
  rw [hLv]
  calc
    ‖v 0 • L (basisVec 0) + v 1 • L (basisVec 1)‖ ≤
        ‖v 0 • L (basisVec 0)‖ + ‖v 1 • L (basisVec 1)‖ := norm_add_le _ _
    _ = ‖v 0‖ * ‖L (basisVec 0)‖ + ‖v 1‖ * ‖L (basisVec 1)‖ := by simp [norm_smul]
    _ ≤ ‖v‖ * ‖L (basisVec 0)‖ + ‖v‖ * ‖L (basisVec 1)‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hv0 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hv1 (norm_nonneg _))
    _ = (‖L (basisVec 0)‖ + ‖L (basisVec 1)‖) * ‖v‖ := by ring

theorem periodic_increment_le_torusDist {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (F : Vec 2 → H) (hF : ContDiff ℝ 1 F)
    (hper : AVenhance.IsZ2Periodic F) (B : ℝ) (hB : 0 ≤ B)
    (hderiv : ∀ x, ‖fderiv ℝ F x‖ ≤ B) (y z : Vec 2) :
    ‖F y - F z‖ ≤ B * torusDist y z := by
  have hshift : ∀ n : Fin 2 → ℤ,
      ‖F y - F z‖ ≤ B * Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) := by
    intro n
    have htranslate := hper n z
    have hmv := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => (hF.differentiable (by norm_num)) x)
      (fun x _ => hderiv x)
      (Set.mem_univ y) (Set.mem_univ (z + AVenhance.latticeShift n))
    have hnorm : ‖(z + AVenhance.latticeShift n) - y‖ ≤
        Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) := by
      have hvec : (z + AVenhance.latticeShift n) - y =
          -(y - z - AVenhance.latticeShift n) := by
        ext i
        simp [AVenhance.latticeShift]
        ring
      rw [hvec, norm_neg]
      exact pi_norm_le_vecEuclidean _
    calc
      ‖F y - F z‖ = ‖F y - F (z + AVenhance.latticeShift n)‖ := by rw [htranslate]
      _ = ‖F (z + AVenhance.latticeShift n) - F y‖ := norm_sub_rev _ _
      _ ≤ B * ‖(z + AVenhance.latticeShift n) - y‖ := hmv
      _ ≤ B * Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) :=
        mul_le_mul_of_nonneg_left hnorm hB
  by_cases hBpos : 0 < B
  · have hdiv : ‖F y - F z‖ / B ≤ torusDist y z := by
      unfold torusDist
      have hforall : ∀ n : Fin 2 → ℤ,
          ‖F y - F z‖ / B ≤ Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) := by
        intro n
        exact (div_le_iff₀ hBpos).2 (by simpa [mul_comm] using hshift n)
      exact le_ciInf hforall
    calc
      ‖F y - F z‖ = (‖F y - F z‖ / B) * B := by field_simp
      _ ≤ torusDist y z * B := mul_le_mul_of_nonneg_right hdiv hB
      _ = B * torusDist y z := by ring
  · have hBzero : B = 0 := le_antisymm (le_of_not_gt hBpos) hB
    have hzero : ‖F y - F z‖ = 0 := by
      have := hshift (fun _ => 0)
      simpa [hBzero] using this
    simp [hzero, hBzero]

end AVRegularity.Readout
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.Readout

/-! Supremum and profile seminorm inequalities for the readout lemma `iteration_readout`. -/

theorem supNorm_add_le {H : Type*} [NormedAddCommGroup H]
    (F G : Vec 2 → H) : supNorm (F + G) ≤ supNorm F + supNorm G := by
  unfold supNorm
  apply iSup_le
  intro x
  calc
    (‖F x + G x‖₊ : ℝ≥0∞) ≤ (‖F x‖₊ : ℝ≥0∞) + (‖G x‖₊ : ℝ≥0∞) := by
      exact_mod_cast nnnorm_add_le (F x) (G x)
    _ ≤ (⨆ y, (‖F y‖₊ : ℝ≥0∞)) + ⨆ y, (‖G y‖₊ : ℝ≥0∞) :=
      add_le_add (le_iSup_of_le x le_rfl) (le_iSup_of_le x le_rfl)

theorem supNorm_comp_le {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (R : H →L[ℝ] H') (F : Vec 2 → H) :
    supNorm (fun x => R (F x)) ≤ ENNReal.ofReal ‖R‖ * supNorm F := by
  unfold supNorm
  apply iSup_le
  intro x
  calc
    (‖R (F x)‖₊ : ℝ≥0∞) ≤ (‖R‖₊ : ℝ≥0∞) * (‖F x‖₊ : ℝ≥0∞) := by
      exact_mod_cast R.le_opNorm (F x)
    _ = ENNReal.ofReal ‖R‖ * (‖F x‖₊ : ℝ≥0∞) := by
      rw [← coe_nnnorm R, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal ‖R‖ * (⨆ y, (‖F y‖₊ : ℝ≥0∞)) := by
      exact mul_le_mul_right (α := ℝ≥0∞)
        (le_iSup (fun y : Vec 2 => (‖F y‖₊ : ℝ≥0∞)) x) (ENNReal.ofReal ‖R‖)

theorem profileSeminorm_add_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (lam : ℝ) (K : ℕ) (s : ℝ) (F G : Vec 2 → H)
    (hF : ContDiff ℝ K F) (hG : ContDiff ℝ K G) :
    profileSeminorm lam K s (F + G) ≤ profileSeminorm lam K s F + profileSeminorm lam K s G := by
  unfold profileSeminorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro α hα
  have horder : α 0 + α 1 ≤ K := by
    simp only [multiIndicesBetween, Finset.mem_filter] at hα
    exact hα.2.2
  rw [partialDerivative_add (K := K) α horder F G hF hG]
  calc
    _ ≤ ENNReal.ofReal (lam ^ ((↑(α 0 + α 1) : ℝ) - s) / multiIndexFactorial α) *
        (supNorm (partialDerivative α F) + supNorm (partialDerivative α G)) :=
      mul_le_mul_right (supNorm_add_le
        (partialDerivative α F) (partialDerivative α G)) _
    _ = _ := by rw [mul_add]

theorem profileSeminorm_scale_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {e E s : ℝ} {K : ℕ} (he : 0 < e) (heE : e ≤ E)
    (hs₁ : s < 1) (F : Vec 2 → H) :
    profileSeminorm e K s F ≤
      ENNReal.ofReal ((e / E) ^ (1 - s)) * profileSeminorm E K s F := by
  have hEpos : 0 < E := lt_of_lt_of_le he heE
  have hr0 : 0 ≤ e / E := (div_nonneg (le_of_lt he) (le_of_lt hEpos))
  have hr1 : e / E ≤ 1 := (div_le_one hEpos).2 heE
  have hfactor : 0 ≤ (e / E) ^ (1 - s) := Real.rpow_nonneg hr0 _
  unfold profileSeminorm
  calc
    (∑ α ∈ multiIndicesBetween 1 K,
        ENNReal.ofReal (e ^ ((↑(α 0 + α 1) : ℝ) - s) / multiIndexFactorial α) *
          supNorm (partialDerivative α F))
      ≤ ∑ α ∈ multiIndicesBetween 1 K,
        (ENNReal.ofReal ((e / E) ^ (1 - s)) *
          ENNReal.ofReal (E ^ ((↑(α 0 + α 1) : ℝ) - s) /
            multiIndexFactorial α)) * supNorm (partialDerivative α F) := by
        apply Finset.sum_le_sum
        intro α hα
        have horder : 1 ≤ α 0 + α 1 := by
          simp only [multiIndicesBetween, Finset.mem_filter] at hα
          exact hα.2.1
        have hj : (1 : ℝ) ≤ (↑(α 0 + α 1 : ℕ) : ℝ) := by exact_mod_cast horder
        let p : ℝ := (↑(α 0 + α 1 : ℕ) : ℝ) - s
        have hp : 1 - s ≤ p := by dsimp [p]; linarith
        have hpow : (e / E) ^ p ≤ (e / E) ^ (1 - s) :=
          Real.rpow_le_rpow_of_exponent_ge' hr0 hr1 (by linarith) hp
        have hbase : (e / E) * E = e := by field_simp
        have hepow : e ^ p = (e / E) ^ p * E ^ p := by
          calc
            e ^ p = ((e / E) * E) ^ p := by rw [hbase]
            _ = (e / E) ^ p * E ^ p := Real.mul_rpow hr0 (le_of_lt hEpos)
        have hfact : 0 < multiIndexFactorial α := by
          unfold multiIndexFactorial
          positivity
        have hcoef : e ^ p / multiIndexFactorial α ≤
            (e / E) ^ (1 - s) * (E ^ p / multiIndexFactorial α) := by
          rw [hepow]
          calc
            (e / E) ^ p * E ^ p / multiIndexFactorial α ≤
                (e / E) ^ (1 - s) * E ^ p / multiIndexFactorial α := by
              apply (div_le_div_iff_of_pos_right hfact).2
              exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (le_of_lt hEpos) p)
            _ = (e / E) ^ (1 - s) * (E ^ p / multiIndexFactorial α) := by
              rw [mul_div_assoc]
        have hcoefENN :
            ENNReal.ofReal (e ^ p / multiIndexFactorial α) ≤
              ENNReal.ofReal ((e / E) ^ (1 - s)) *
                ENNReal.ofReal (E ^ p / multiIndexFactorial α) := by
          calc
            _ ≤ ENNReal.ofReal ((e / E) ^ (1 - s) * (E ^ p / multiIndexFactorial α)) :=
              ENNReal.ofReal_mono hcoef
            _ = _ := ENNReal.ofReal_mul hfactor
        calc
          _ = supNorm (partialDerivative α F) *
              ENNReal.ofReal (e ^ p / multiIndexFactorial α) := by ac_rfl
          _ ≤ supNorm (partialDerivative α F) *
              (ENNReal.ofReal ((e / E) ^ (1 - s)) *
                ENNReal.ofReal (E ^ p / multiIndexFactorial α)) :=
            mul_le_mul_right hcoefENN (supNorm (partialDerivative α F))
          _ = _ := by ac_rfl
    _ = ENNReal.ofReal ((e / E) ^ (1 - s)) *
          (∑ α ∈ multiIndicesBetween 1 K,
            ENNReal.ofReal (E ^ ((↑(α 0 + α 1) : ℝ) - s) /
              multiIndexFactorial α) * supNorm (partialDerivative α F)) := by
        simp_rw [mul_assoc]
        rw [Finset.mul_sum]

theorem supNorm_list_sum_le {H : Type*} [NormedAddCommGroup H]
    (l : List (Vec 2 → H)) : supNorm l.sum ≤ (l.map supNorm).sum := by
  induction l with
  | nil => simp [supNorm]
  | cons F l ih =>
      simp only [List.sum_cons, List.map_cons, List.sum_cons]
      exact (supNorm_add_le F l.sum).trans (add_le_add le_rfl ih)

theorem list_sum_contDiff {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : ℕ) (l : List (Vec 2 → H))
    (hl : ∀ F ∈ l, ContDiff ℝ K F) : ContDiff ℝ K l.sum := by
  induction l with
  | nil =>
      change ContDiff ℝ K (fun _ : Vec 2 => (0 : H))
      exact contDiff_const
  | cons F l ih =>
      have hrest : ∀ G ∈ l, ContDiff ℝ K G := by
        intro G hG
        exact hl G (List.mem_cons_of_mem F hG)
      have hF : ContDiff ℝ K F := hl F (by simp)
      change ContDiff ℝ K (fun x => F x + l.sum x)
      exact hF.add (ih hrest)

theorem profileSeminorm_list_sum_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (lam : ℝ) (K : ℕ) (s : ℝ) (l : List (Vec 2 → H))
    (hl : ∀ F ∈ l, ContDiff ℝ K F) :
    profileSeminorm lam K s l.sum ≤ (l.map (profileSeminorm lam K s)).sum := by
  induction l with
  | nil =>
      have hiterZero : ∀ (D : (Vec 2 → H) → Vec 2 → H), D 0 = 0 →
          ∀ n : ℕ, D^[n] 0 = 0 := by
        intro D hD n
        induction n with
        | zero => rfl
        | succ n ih =>
            simp [Function.iterate_succ_apply', ih, hD]
      have hD0 : (fun G : Vec 2 → H => along (basisVec 0) G) 0 = 0 := by
        funext x
        simp [along]
      have hD1 : (fun G : Vec 2 → H => along (basisVec 1) G) 0 = 0 := by
        funext x
        simp [along]
      have hz (α : Fin 2 → ℕ) :
          partialDerivative α (fun _ : Vec 2 => (0 : H)) = fun _ => 0 := by
        rw [show partialDerivative α (fun _ : Vec 2 => (0 : H)) =
          ((fun G : Vec 2 → H => along (basisVec 1) G)^[α 1])
            (((fun G : Vec 2 → H => along (basisVec 0) G)^[α 0]) 0) by rfl]
        rw [hiterZero _ hD0 (α 0)]
        exact hiterZero _ hD1 (α 1)
      change profileSeminorm lam K s (fun _ : Vec 2 => (0 : H)) ≤ 0
      unfold profileSeminorm
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro α hα
      rw [hz α]
      simp [supNorm]
  | cons F l ih =>
      have hrest : ∀ G ∈ l, ContDiff ℝ K G := by
        intro G hG
        exact hl G (List.mem_cons_of_mem F hG)
      have hF : ContDiff ℝ K F := hl F (by simp)
      have hsum : ContDiff ℝ K l.sum := list_sum_contDiff K l hrest
      rw [List.sum_cons, List.map_cons, List.sum_cons]
      exact (profileSeminorm_add_le lam K s F l.sum hF hsum).trans
        (add_le_add le_rfl (ih hrest))

theorem profileSeminorm_le_label {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {e lam s : ℝ} {K : ℕ} (he : 0 < e) (helam : e ≤ lam)
    (hs₁ : s < 1) (F : Vec 2 → H) :
    profileSeminorm e K s F ≤ profileSeminorm lam K s F := by
  have hlampos : 0 < lam := lt_of_lt_of_le he helam
  have hr0 : 0 ≤ e / lam := div_nonneg (le_of_lt he) (le_of_lt hlampos)
  have hr1 : e / lam ≤ 1 := (div_le_one hlampos).2 helam
  have hpow : (e / lam) ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one hr0 hr1 (by linarith [hs₁])
  have hcoeff : ENNReal.ofReal ((e / lam) ^ (1 - s)) ≤ 1 := by
    calc
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_mono hpow
      _ = 1 := by simp
  calc
    profileSeminorm e K s F ≤
        ENNReal.ofReal ((e / lam) ^ (1 - s)) * profileSeminorm lam K s F :=
      profileSeminorm_scale_le he helam hs₁ F
    _ ≤ profileSeminorm lam K s F := by
      calc
        _ ≤ 1 * profileSeminorm lam K s F :=
          mul_le_mul_left (α := ℝ≥0∞) hcoeff (profileSeminorm lam K s F)
        _ = _ := one_mul _

theorem supNorm_le_profile_amplitude {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {lam s : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hs : 0 < s) (F : Vec 2 → H) :
    supNorm F ≤ ENNReal.ofReal (lam ^ (-s)) * supNorm F := by
  have hpow : 1 ≤ lam ^ (-s) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1 (by linarith)
  have hcoef : 1 ≤ ENNReal.ofReal (lam ^ (-s)) := by
    calc
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ _ := ENNReal.ofReal_mono hpow
  calc
    supNorm F = 1 * supNorm F := (one_mul _).symm
    _ ≤ ENNReal.ofReal (lam ^ (-s)) * supNorm F :=
      mul_le_mul_left (α := ℝ≥0∞) hcoef (supNorm F)

theorem profileCost_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {e lam s : ℝ} {K : ℕ} (he : 0 < e) (helam : e ≤ lam) (hlam : lam ≤ 1)
    (hs₀ : 0 < s) (hs₁ : s < 1) (F : Vec 2 → H) :
    supNorm F + profileSeminorm e K s F ≤ profileNorm lam K s F := by
  have h₁ := supNorm_le_profile_amplitude (lt_of_lt_of_le he helam) hlam hs₀ F
  have h₂ := profileSeminorm_le_label (K := K) he helam hs₁ F
  simpa [profileNorm] using add_le_add h₁ h₂

/-! Hölder readout bounds for a smooth periodic field and one profile. -/

def unitMultiIndex (i : Fin 2) : Fin 2 → ℕ := fun j => if j = i then 1 else 0

theorem partialDerivative_unit {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (i : Fin 2) (F : Vec 2 → H) :
    partialDerivative (unitMultiIndex i) F = along (basisVec i) F := by
  fin_cases i <;> funext x <;> simp [unitMultiIndex, partialDerivative, along]

theorem holderSeminorm_add_le {H : Type*} [NormedAddCommGroup H]
    {s : ℝ} (F G : Vec 2 → H) :
    holderSeminorm s (F + G) ≤ holderSeminorm s F + holderSeminorm s G := by
  unfold holderSeminorm
  apply iSup_le
  intro y
  apply iSup_le
  intro z
  apply iSup_le
  intro hdist
  have hdist0 : 0 < torusDist y z := lt_of_le_of_ne (le_ciInf (fun _ => Real.sqrt_nonneg _))
    (Ne.symm hdist)
  have hden : 0 < torusDist y z ^ s := Real.rpow_pos_of_pos hdist0 s
  have hnum : ‖(F + G) y - (F + G) z‖ ≤
      ‖F y - F z‖ + ‖G y - G z‖ := by
    simpa [Pi.add_apply, sub_add_sub_comm] using norm_add_le (F y - F z) (G y - G z)
  have hquot : ‖(F + G) y - (F + G) z‖ / torusDist y z ^ s ≤
      ‖F y - F z‖ / torusDist y z ^ s +
        ‖G y - G z‖ / torusDist y z ^ s := by
    calc
      _ ≤ (‖F y - F z‖ + ‖G y - G z‖) / torusDist y z ^ s :=
        div_le_div_of_nonneg_right hnum (le_of_lt hden)
      _ = _ := by rw [add_div]
  have hF : 0 ≤ ‖F y - F z‖ / torusDist y z ^ s := div_nonneg (norm_nonneg _) (le_of_lt hden)
  have hG : 0 ≤ ‖G y - G z‖ / torusDist y z ^ s := div_nonneg (norm_nonneg _) (le_of_lt hden)
  calc
    ENNReal.ofReal (‖(F + G) y - (F + G) z‖ / torusDist y z ^ s) ≤
      ENNReal.ofReal (‖F y - F z‖ / torusDist y z ^ s +
        ‖G y - G z‖ / torusDist y z ^ s) := ENNReal.ofReal_mono hquot
    _ = ENNReal.ofReal (‖F y - F z‖ / torusDist y z ^ s) +
        ENNReal.ofReal (‖G y - G z‖ / torusDist y z ^ s) := ENNReal.ofReal_add hF hG
    _ ≤ holderSeminorm s F + holderSeminorm s G :=
      add_le_add (le_iSup_of_le y (le_iSup_of_le z (le_iSup_of_le hdist le_rfl)))
        (le_iSup_of_le y (le_iSup_of_le z (le_iSup_of_le hdist le_rfl)))

theorem profile_holder_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {lam s : ℝ} (hlam : 0 < lam) (hs₀ : 0 < s) (hs₁ : s < 1)
    (F : Vec 2 → H) (hF : ContDiff ℝ 1 F) (hper : AVenhance.IsZ2Periodic F) :
    holderSeminorm s F ≤
      2 * (ENNReal.ofReal (lam ^ (-s)) * supNorm F) +
        ENNReal.ofReal (lam ^ (1 - s)) *
          (supNorm (along (basisVec 0) F) + supNorm (along (basisVec 1) F)) := by
  let A := supNorm F
  let D₀ := supNorm (along (basisVec 0) F)
  let D₁ := supNorm (along (basisVec 1) F)
  let cA := ENNReal.ofReal (lam ^ (-s))
  let cD := ENNReal.ofReal (lam ^ (1 - s))
  have hcA : cA ≠ 0 := by
    dsimp [cA]
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hlam _)).ne'
  have hcD : cD ≠ 0 := by
    dsimp [cD]
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hlam _)).ne'
  by_cases hA : A = ⊤
  · have htop : 2 * (cA * A) + cD * (D₀ + D₁) = ⊤ := by
      simp [hA, ENNReal.mul_top hcA]
    rw [show 2 * (ENNReal.ofReal (lam ^ (-s)) * supNorm F) +
        ENNReal.ofReal (lam ^ (1 - s)) *
          (supNorm (along (basisVec 0) F) + supNorm (along (basisVec 1) F)) = ⊤ by
      simpa [A, D₀, D₁, cA, cD] using htop]
    exact le_top
  · by_cases hD₀ : D₀ = ⊤
    · have htop : 2 * (cA * A) + cD * (D₀ + D₁) = ⊤ := by
        simp [hD₀, ENNReal.mul_top hcD]
      rw [show 2 * (ENNReal.ofReal (lam ^ (-s)) * supNorm F) +
          ENNReal.ofReal (lam ^ (1 - s)) *
            (supNorm (along (basisVec 0) F) + supNorm (along (basisVec 1) F)) = ⊤ by
        simpa [A, D₀, D₁, cA, cD] using htop]
      exact le_top
    · by_cases hD₁ : D₁ = ⊤
      · have htop : 2 * (cA * A) + cD * (D₀ + D₁) = ⊤ := by
          simp [hD₁, ENNReal.mul_top hcD]
        rw [show 2 * (ENNReal.ofReal (lam ^ (-s)) * supNorm F) +
            ENNReal.ofReal (lam ^ (1 - s)) *
              (supNorm (along (basisVec 0) F) + supNorm (along (basisVec 1) F)) = ⊤ by
          simpa [A, D₀, D₁, cA, cD] using htop]
        exact le_top
      · have hAreal : ∀ x, ‖F x‖ ≤ A.toReal := by
          intro x
          have hle : (‖F x‖₊ : ℝ≥0∞) ≤ A := by
            change (‖F x‖₊ : ℝ≥0∞) ≤ ⨆ y, (‖F y‖₊ : ℝ≥0∞)
            exact le_iSup (fun y : Vec 2 => (‖F y‖₊ : ℝ≥0∞)) x
          have := ENNReal.toReal_mono hA hle
          simpa using this
        have hD₀real : ∀ x, ‖along (basisVec 0) F x‖ ≤ D₀.toReal := by
          intro x
          have hle : (‖along (basisVec 0) F x‖₊ : ℝ≥0∞) ≤ D₀ := by
            change (‖along (basisVec 0) F x‖₊ : ℝ≥0∞) ≤
              ⨆ y, (‖along (basisVec 0) F y‖₊ : ℝ≥0∞)
            exact le_iSup (fun y : Vec 2 => (‖along (basisVec 0) F y‖₊ : ℝ≥0∞)) x
          have := ENNReal.toReal_mono hD₀ hle
          simpa using this
        have hD₁real : ∀ x, ‖along (basisVec 1) F x‖ ≤ D₁.toReal := by
          intro x
          have hle : (‖along (basisVec 1) F x‖₊ : ℝ≥0∞) ≤ D₁ := by
            change (‖along (basisVec 1) F x‖₊ : ℝ≥0∞) ≤
              ⨆ y, (‖along (basisVec 1) F y‖₊ : ℝ≥0∞)
            exact le_iSup (fun y : Vec 2 => (‖along (basisVec 1) F y‖₊ : ℝ≥0∞)) x
          have := ENNReal.toReal_mono hD₁ hle
          simpa using this
        have hA_nonneg : 0 ≤ A.toReal := ENNReal.toReal_nonneg
        have hD₀_nonneg : 0 ≤ D₀.toReal := ENNReal.toReal_nonneg
        have hD₁_nonneg : 0 ≤ D₁.toReal := ENNReal.toReal_nonneg
        let B : ℝ := D₀.toReal + D₁.toReal
        have hB : 0 ≤ B := by dsimp [B]; positivity
        have hderiv : ∀ x, ‖fderiv ℝ F x‖ ≤ B := by
          intro x
          calc
            ‖fderiv ℝ F x‖ ≤
                ‖fderiv ℝ F x (basisVec 0)‖ + ‖fderiv ℝ F x (basisVec 1)‖ :=
              fderiv_opNorm_le_coordinate_sum _
            _ = ‖along (basisVec 0) F x‖ + ‖along (basisVec 1) F x‖ := by
              rfl
            _ ≤ D₀.toReal + D₁.toReal := add_le_add (hD₀real x) (hD₁real x)
            _ = B := by rfl
        have hinc := periodic_increment_le_torusDist F hF hper B hB hderiv
        have hlam_neg_pos : 0 < lam ^ (-s) := Real.rpow_pos_of_pos hlam _
        have hlam_one_sub_pos : 0 < lam ^ (1 - s) := Real.rpow_pos_of_pos hlam _
        have hA_repr : ENNReal.ofReal A.toReal = A :=
          ENNReal.ofReal_toReal_eq_iff.mpr hA
        have hD₀_repr : ENNReal.ofReal D₀.toReal = D₀ :=
          ENNReal.ofReal_toReal_eq_iff.mpr hD₀
        have hD₁_repr : ENNReal.ofReal D₁.toReal = D₁ :=
          ENNReal.ofReal_toReal_eq_iff.mpr hD₁
        have hD_repr : ENNReal.ofReal B = D₀ + D₁ := by
          dsimp [B]
          rw [ENNReal.ofReal_add hD₀_nonneg hD₁_nonneg, hD₀_repr, hD₁_repr]
        have hcoefA : ENNReal.ofReal (2 * (A.toReal * lam ^ (-s))) =
            2 * (cA * A) := by
          rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
            ENNReal.ofReal_mul hA_nonneg, hA_repr]
          simp [cA, mul_assoc, mul_comm]
        have hcoefD : ENNReal.ofReal (B * lam ^ (1 - s)) = cD * (D₀ + D₁) := by
          rw [ENNReal.ofReal_mul hB, hD_repr]
          simp [cD, mul_comm]
        have hpoint : ∀ y z, torusDist y z ≠ 0 →
            ENNReal.ofReal (‖F y - F z‖ / torusDist y z ^ s) ≤
              2 * (cA * A) + cD * (D₀ + D₁) := by
          intro y z hdist
          have hdist0 : 0 < torusDist y z :=
            lt_of_le_of_ne (le_ciInf (fun _ => Real.sqrt_nonneg _)) (Ne.symm hdist)
          have hquot_nonneg : 0 ≤ ‖F y - F z‖ / torusDist y z ^ s :=
            div_nonneg (norm_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hdist0 s))
          by_cases hsmall : torusDist y z ≤ lam
          · have hsmall_bound :
                ‖F y - F z‖ / torusDist y z ^ s ≤ B * lam ^ (1 - s) := by
              have hlinear := hinc y z
              have hquot₁ : ‖F y - F z‖ / torusDist y z ^ s ≤
                  B * torusDist y z ^ (1 - s) := by
                calc
                  _ ≤ (B * torusDist y z) / torusDist y z ^ s :=
                    div_le_div_of_nonneg_right hlinear
                      (le_of_lt (Real.rpow_pos_of_pos hdist0 s))
                  _ = B * torusDist y z ^ (1 - s) := by
                    rw [Real.rpow_one_sub' (le_of_lt hdist0) (by linarith [hs₁])]
                    field_simp
              have hpow : torusDist y z ^ (1 - s) ≤ lam ^ (1 - s) :=
                Real.rpow_le_rpow (le_of_lt hdist0) hsmall (by linarith [hs₁])
              exact hquot₁.trans (mul_le_mul_of_nonneg_left hpow hB)
            calc
              _ ≤ ENNReal.ofReal (B * lam ^ (1 - s)) := ENNReal.ofReal_mono hsmall_bound
              _ = ENNReal.ofReal (B * lam ^ (1 - s)) + 0 := by simp
              _ ≤ ENNReal.ofReal (B * lam ^ (1 - s)) + 2 * (cA * A) := by
                calc
                  _ = ENNReal.ofReal (B * lam ^ (1 - s)) := by simp
                  _ ≤ _ := le_add_of_nonneg_right bot_le
              _ = 2 * (cA * A) + cD * (D₀ + D₁) := by
                rw [hcoefD]
                ac_rfl
          · have hlarge : lam ≤ torusDist y z := le_of_not_ge hsmall
            have hlarge_bound :
                ‖F y - F z‖ / torusDist y z ^ s ≤
                  2 * (A.toReal * lam ^ (-s)) := by
              have hnum : ‖F y - F z‖ ≤ 2 * A.toReal := by
                calc
                  ‖F y - F z‖ ≤ ‖F y‖ + ‖F z‖ := norm_sub_le _ _
                  _ ≤ A.toReal + A.toReal := add_le_add (hAreal y) (hAreal z)
                  _ = 2 * A.toReal := by ring
              have hpow : lam ^ s ≤ torusDist y z ^ s :=
                Real.rpow_le_rpow (le_of_lt hlam) hlarge (le_of_lt hs₀)
              calc
                _ ≤ (2 * A.toReal) / torusDist y z ^ s :=
                  div_le_div_of_nonneg_right hnum
                    (le_of_lt (Real.rpow_pos_of_pos (lt_of_lt_of_le hlam hlarge) s))
                _ ≤ (2 * A.toReal) / lam ^ s :=
                  div_le_div_of_nonneg_left (by positivity)
                    (Real.rpow_pos_of_pos hlam s) hpow
                _ = 2 * (A.toReal * lam ^ (-s)) := by
                  rw [Real.rpow_neg (le_of_lt hlam)]
                  field_simp
            calc
              _ ≤ ENNReal.ofReal (2 * (A.toReal * lam ^ (-s))) :=
                ENNReal.ofReal_mono hlarge_bound
              _ = 2 * (cA * A) := by
                exact hcoefA
              _ ≤ 2 * (cA * A) + cD * (D₀ + D₁) := le_self_add
        unfold holderSeminorm
        apply iSup_le
        intro y
        apply iSup_le
        intro z
        apply iSup_le
        intro hdist
        simpa [A, D₀, D₁, cA, cD] using hpoint y z hdist

theorem holderSeminorm_list_sum_le {H : Type*} [NormedAddCommGroup H]
    (s : ℝ) (l : List (Vec 2 → H)) :
    holderSeminorm s l.sum ≤ (l.map (holderSeminorm s)).sum := by
  induction l with
  | nil => simp [holderSeminorm]
  | cons F l ih =>
      rw [List.sum_cons, List.map_cons, List.sum_cons]
      exact (holderSeminorm_add_le F l.sum).trans (add_le_add le_rfl ih)

theorem profileSeminorm_coordinate_derivative_sum_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {lam s : ℝ} {K : ℕ} (hK : 1 ≤ K) (F : Vec 2 → H) :
    ENNReal.ofReal (lam ^ (1 - s)) * supNorm (along (basisVec 0) F) +
      ENNReal.ofReal (lam ^ (1 - s)) * supNorm (along (basisVec 1) F) ≤
        profileSeminorm lam K s F := by
  let u₀ := unitMultiIndex (0 : Fin 2)
  let u₁ := unitMultiIndex (1 : Fin 2)
  let S : Finset (Fin 2 → ℕ) := {u₀, u₁}
  have hu₀_mem : u₀ ∈ multiIndicesBetween 1 K := by
    exact (show unitMultiIndex (0 : Fin 2) ∈ multiIndicesBetween 1 K from by
      simp [multiIndicesBetween, unitMultiIndex, hK])
  have hu₁_mem : u₁ ∈ multiIndicesBetween 1 K := by
    exact (show unitMultiIndex (1 : Fin 2) ∈ multiIndicesBetween 1 K from by
      simp [multiIndicesBetween, unitMultiIndex, hK])
  have hu_ne : u₀ ≠ u₁ := by
    intro h
    have := congrFun h 0
    norm_num [u₀, u₁, unitMultiIndex] at this
  have hsub : S ⊆ multiIndicesBetween 1 K := by
    intro α hα
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl
    · exact hu₀_mem
    · exact hu₁_mem
  let term : (Fin 2 → ℕ) → ℝ≥0∞ := fun α =>
    ENNReal.ofReal (lam ^ (((α 0 + α 1 : ℕ) : ℝ) - s) /
      multiIndexFactorial α) * supNorm (partialDerivative α F)
  have htwo : term u₀ + term u₁ ≤
      ∑ α ∈ multiIndicesBetween 1 K, term α := by
    calc
      term u₀ + term u₁ = ∑ α ∈ S, term α := by
        simp [S, hu_ne, term]
      _ ≤ ∑ α ∈ multiIndicesBetween 1 K, term α :=
        Finset.sum_le_sum_of_subset hsub
  have hleft : term u₀ + term u₁ =
      ENNReal.ofReal (lam ^ (1 - s)) * supNorm (along (basisVec 0) F) +
        ENNReal.ofReal (lam ^ (1 - s)) * supNorm (along (basisVec 1) F) := by
    simp [term, u₀, u₁, partialDerivative_unit, unitMultiIndex, multiIndexFactorial]
  rw [← hleft]
  unfold profileSeminorm
  exact htwo

theorem profile_holder_cost {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {lam s : ℝ} {K : ℕ} (hK : 1 ≤ K) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hs₀ : 0 < s) (hs₁ : s < 1) (F : Vec 2 → H)
    (hF : ContDiff ℝ K F) (hper : AVenhance.IsZ2Periodic F) :
    supNorm F + holderSeminorm s F ≤ 3 * profileNorm lam K s F := by
  have hFone : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast hK)
  let amp := ENNReal.ofReal (lam ^ (-s)) * supNorm F
  have hholder := profile_holder_bound hlam hs₀ hs₁ F hFone hper
  have hderiv := profileSeminorm_coordinate_derivative_sum_le
    (lam := lam) (s := s) (F := F) hK
  have hsemi : holderSeminorm s F ≤ 2 * amp + profileSeminorm lam K s F := by
    calc
      holderSeminorm s F ≤ 2 * amp +
          ENNReal.ofReal (lam ^ (1 - s)) *
            (supNorm (along (basisVec 0) F) + supNorm (along (basisVec 1) F)) := by
        simpa [amp] using hholder
      _ ≤ 2 * amp + profileSeminorm lam K s F := by
        rw [mul_add]
        exact add_le_add_right hderiv (2 * amp)
  have hamp : supNorm F ≤ amp := by
    dsimp [amp]
    exact supNorm_le_profile_amplitude hlam hlam1 hs₀ F
  calc
    supNorm F + holderSeminorm s F ≤ supNorm F +
        (2 * amp + profileSeminorm lam K s F) := add_le_add_right hsemi (supNorm F)
    _ ≤ amp + (2 * amp + profileSeminorm lam K s F) :=
      add_le_add_left hamp _
    _ = 3 * amp + profileSeminorm lam K s F := by ring
    _ ≤ 3 * amp + 3 * profileSeminorm lam K s F := by
      exact add_le_add_right (by
        calc
          profileSeminorm lam K s F ≤
              profileSeminorm lam K s F + profileSeminorm lam K s F := le_self_add
          _ ≤ (profileSeminorm lam K s F + profileSeminorm lam K s F) +
              profileSeminorm lam K s F := le_add_of_nonneg_right bot_le
          _ = 3 * profileSeminorm lam K s F := by ring) _
    _ = 3 * (amp + profileSeminorm lam K s F) := by ring
    _ = 3 * profileNorm lam K s F := by simp [profileNorm, amp]

/-! Readout estimates for exact finite representations. -/

theorem list_eval_sum {H : Type*} [AddCommMonoid H] (l : List (Vec 2 → H))
    (x : Vec 2) : (l.map fun F => F x).sum = l.sum x := by
  induction l with
  | nil => rfl
  | cons F l ih => simp [ih]

theorem representation_profile_readout {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {s e : ℝ} {K : ℕ} (hs₀ : 0 < s) (hs₁ : s < 1)
    (r : Representation H) (hr : IsRepresentationAt e K r) :
    supNorm r.value + profileSeminorm e K s r.value ≤ representedSize s K e r := by
  rcases hr with ⟨he, he1, hbaseCD, hbasePer, hprofile⟩
  let gs : List (Vec 2 → H) := r.profiles.map Prod.fst
  have hvalue : r.value = r.base + gs.sum := by
    funext x
    change r.base x + (r.profiles.map fun p => p.1 x).sum =
      r.base x + gs.sum x
    rw [show r.profiles.map (fun p => p.1 x) = gs.map (fun G => G x) by
      simp [gs, List.map_map]]
    rw [list_eval_sum]
  have hgsCD : ∀ G ∈ gs, ContDiff ℝ K G := by
    intro G hG
    simp only [gs, List.mem_map] at hG
    rcases hG with ⟨p, hp, rfl⟩
    exact (hprofile p hp).1
  have hsumCD : ContDiff ℝ K gs.sum := list_sum_contDiff K gs hgsCD
  have hvalueCD : ContDiff ℝ K r.value := by
    rw [hvalue]
    exact hbaseCD.add hsumCD
  have hsup : supNorm r.value ≤ supNorm r.base + (gs.map supNorm).sum := by
    rw [hvalue]
    exact (supNorm_add_le r.base gs.sum).trans
      (add_le_add le_rfl (supNorm_list_sum_le gs))
  have hsemi : profileSeminorm e K s r.value ≤
      profileSeminorm e K s r.base + (gs.map (profileSeminorm e K s)).sum := by
    rw [hvalue]
    exact (profileSeminorm_add_le e K s r.base gs.sum hbaseCD hsumCD).trans
      (add_le_add le_rfl (profileSeminorm_list_sum_le e K s gs hgsCD))
  have hcost :
      (r.profiles.map fun p => supNorm p.1 + profileSeminorm e K s p.1).sum ≤
        (r.profiles.map fun p => profileNorm p.2 K s p.1).sum := by
    apply List.sum_le_sum
    intro p hp
    have hlabels := hprofile p hp
    exact profileCost_le he hlabels.2.2.1 hlabels.2.2.2 hs₀ hs₁ p.1
  have hcosts :
      (gs.map supNorm).sum + (gs.map (profileSeminorm e K s)).sum =
        (r.profiles.map fun p => supNorm p.1 + profileSeminorm e K s p.1).sum := by
    have haux (ps : List ((Vec 2 → H) × ℝ)) :
        (ps.map (fun p => supNorm p.1)).sum +
            (ps.map (fun p => profileSeminorm e K s p.1)).sum =
          (ps.map fun p => supNorm p.1 + profileSeminorm e K s p.1).sum := by
      induction ps with
      | nil => simp
      | cons p ps ih =>
          simp only [List.map_cons, List.sum_cons]
          calc
            supNorm p.1 + (ps.map fun p => supNorm p.1).sum +
                (profileSeminorm e K s p.1 +
                  (ps.map fun p => profileSeminorm e K s p.1).sum) =
              (supNorm p.1 + profileSeminorm e K s p.1) +
                ((ps.map fun p => supNorm p.1).sum +
                  (ps.map fun p => profileSeminorm e K s p.1).sum) := by ac_rfl
            _ = (supNorm p.1 + profileSeminorm e K s p.1) +
                (ps.map fun p => supNorm p.1 + profileSeminorm e K s p.1).sum := by rw [ih]
            _ = _ := by rfl
    change ((r.profiles.map Prod.fst).map supNorm).sum +
        ((r.profiles.map Prod.fst).map (profileSeminorm e K s)).sum = _
    simpa only [List.map_map, Function.comp_def] using haux r.profiles
  calc
    supNorm r.value + profileSeminorm e K s r.value
      ≤ (supNorm r.base + (gs.map supNorm).sum) +
          (profileSeminorm e K s r.base + (gs.map (profileSeminorm e K s)).sum) :=
        add_le_add hsup hsemi
    _ = (supNorm r.base + profileSeminorm e K s r.base) +
          ((gs.map supNorm).sum + (gs.map (profileSeminorm e K s)).sum) := by ac_rfl
    _ = (supNorm r.base + profileSeminorm e K s r.base) +
          (r.profiles.map fun p => supNorm p.1 + profileSeminorm e K s p.1).sum := by
        rw [hcosts]
    _ ≤ (supNorm r.base + profileSeminorm e K s r.base) +
          ((holderSeminorm s r.base) +
            (r.profiles.map fun p => profileNorm p.2 K s p.1).sum) := by
        calc
          (supNorm r.base + profileSeminorm e K s r.base) +
              (r.profiles.map fun p => supNorm p.1 + profileSeminorm e K s p.1).sum =
            (r.profiles.map fun p => supNorm p.1 + profileSeminorm e K s p.1).sum +
              (supNorm r.base + profileSeminorm e K s r.base) := by ac_rfl
          _ ≤ (holderSeminorm s r.base +
                (r.profiles.map fun p => profileNorm p.2 K s p.1).sum) +
              (supNorm r.base + profileSeminorm e K s r.base) := by
            exact add_le_add_left
              (hcost.trans (by
                calc
                  (r.profiles.map fun p => profileNorm p.2 K s p.1).sum =
                      0 + (r.profiles.map fun p => profileNorm p.2 K s p.1).sum := by simp
                  _ ≤ holderSeminorm s r.base +
                      (r.profiles.map fun p => profileNorm p.2 K s p.1).sum :=
                    add_le_add_left bot_le _)) _
          _ = (supNorm r.base + profileSeminorm e K s r.base) +
                (holderSeminorm s r.base +
                  (r.profiles.map fun p => profileNorm p.2 K s p.1).sum) := by ac_rfl
    _ = representedSize s K e r := by
      unfold representedSize
      ac_rfl

theorem representation_holder_readout {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {s e : ℝ} {K : ℕ} (hs₀ : 0 < s) (hs₁ : s < 1) (hK : 1 ≤ K)
    (r : Representation H) (hr : IsRepresentationAt e K r) :
    holderNorm s r.value ≤ 3 * representedSize s K e r := by
  rcases hr with ⟨he, _, _, _, hprofile⟩
  let gs : List (Vec 2 → H) := r.profiles.map Prod.fst
  have hvalue : r.value = r.base + gs.sum := by
    funext x
    change r.base x + (r.profiles.map fun p => p.1 x).sum = r.base x + gs.sum x
    rw [show r.profiles.map (fun p => p.1 x) = gs.map (fun G => G x) by
      simp [gs, List.map_map]]
    rw [list_eval_sum]
  have hgsCD : ∀ G ∈ gs, ContDiff ℝ K G := by
    intro G hG
    simp only [gs, List.mem_map] at hG
    rcases hG with ⟨p, hp, rfl⟩
    exact (hprofile p hp).1
  have hsumCD : ContDiff ℝ K gs.sum := list_sum_contDiff K gs hgsCD
  have hsup : supNorm r.value ≤ supNorm r.base + (gs.map supNorm).sum := by
    rw [hvalue]
    exact (supNorm_add_le r.base gs.sum).trans
      (add_le_add le_rfl (supNorm_list_sum_le gs))
  have hholder : holderSeminorm s r.value ≤
      holderSeminorm s r.base + (gs.map (holderSeminorm s)).sum := by
    rw [hvalue]
    exact (holderSeminorm_add_le r.base gs.sum).trans
      (add_le_add le_rfl (holderSeminorm_list_sum_le s gs))
  have hbase_base : supNorm r.base + holderSeminorm s r.base ≤
      supNorm r.base + profileSeminorm e K s r.base + holderSeminorm s r.base := by
    let b := supNorm r.base + profileSeminorm e K s r.base + holderSeminorm s r.base
    have hbase : supNorm r.base + holderSeminorm s r.base ≤ b := by
      dsimp [b]
      calc
        supNorm r.base + holderSeminorm s r.base ≤
            supNorm r.base + holderSeminorm s r.base + profileSeminorm e K s r.base :=
          le_add_of_nonneg_right bot_le
        _ = supNorm r.base + profileSeminorm e K s r.base +
            holderSeminorm s r.base := by ac_rfl
    simpa [b] using hbase
  have hbase_le : supNorm r.base + profileSeminorm e K s r.base +
      holderSeminorm s r.base ≤
      3 * (supNorm r.base + profileSeminorm e K s r.base +
        holderSeminorm s r.base) := by
    let b := supNorm r.base + profileSeminorm e K s r.base + holderSeminorm s r.base
    have hbmul : b ≤ 3 * b := by
      calc
        b ≤ b + b := le_self_add
        _ ≤ (b + b) + b := le_add_of_nonneg_right bot_le
        _ = 3 * b := by ring
    simpa [b] using hbmul
  have hprofiles :
      (r.profiles.map fun p => supNorm p.1 + holderSeminorm s p.1).sum ≤
        3 * (r.profiles.map fun p => profileNorm p.2 K s p.1).sum := by
    calc
      (r.profiles.map fun p => supNorm p.1 + holderSeminorm s p.1).sum ≤
          (r.profiles.map fun p => 3 * profileNorm p.2 K s p.1).sum := by
        apply List.sum_le_sum
        intro p hp
        rcases hprofile p hp with ⟨hCD, hper, helam, hlam⟩
        exact profile_holder_cost hK (lt_of_lt_of_le he helam) hlam hs₀ hs₁
          p.1 hCD hper
      _ = 3 * (r.profiles.map fun p => profileNorm p.2 K s p.1).sum := by
        induction r.profiles with
        | nil => simp
        | cons p ps ih =>
            simp only [List.map_cons, List.sum_cons]
            rw [ih, mul_add]
  have hprofiles_values :
      (gs.map supNorm).sum + (gs.map (holderSeminorm s)).sum =
        (r.profiles.map fun p => supNorm p.1 + holderSeminorm s p.1).sum := by
    have haux (ps : List ((Vec 2 → H) × ℝ)) :
        (ps.map (fun p => supNorm p.1)).sum +
            (ps.map (fun p => holderSeminorm s p.1)).sum =
          (ps.map fun p => supNorm p.1 + holderSeminorm s p.1).sum := by
      induction ps with
      | nil => simp
      | cons p ps ih =>
          simp only [List.map_cons, List.sum_cons]
          calc
            supNorm p.1 + (ps.map fun p => supNorm p.1).sum +
                (holderSeminorm s p.1 +
                  (ps.map fun p => holderSeminorm s p.1).sum) =
              (supNorm p.1 + holderSeminorm s p.1) +
                ((ps.map fun p => supNorm p.1).sum +
                  (ps.map fun p => holderSeminorm s p.1).sum) := by ac_rfl
            _ = (supNorm p.1 + holderSeminorm s p.1) +
                (ps.map fun p => supNorm p.1 + holderSeminorm s p.1).sum := by rw [ih]
            _ = _ := by rfl
    change ((r.profiles.map Prod.fst).map supNorm).sum +
      ((r.profiles.map Prod.fst).map (holderSeminorm s)).sum = _
    simpa only [List.map_map, Function.comp_def] using haux r.profiles
  have hprofiles_sum :
      (gs.map supNorm).sum + (gs.map (holderSeminorm s)).sum ≤
        3 * (r.profiles.map fun p => profileNorm p.2 K s p.1).sum := by
    rw [hprofiles_values]
    exact hprofiles
  calc
    holderNorm s r.value = supNorm r.value + holderSeminorm s r.value := rfl
    _ ≤ (supNorm r.base + (gs.map supNorm).sum) +
        (holderSeminorm s r.base + (gs.map (holderSeminorm s)).sum) :=
      add_le_add hsup hholder
    _ = (supNorm r.base + holderSeminorm s r.base) +
        ((gs.map supNorm).sum + (gs.map (holderSeminorm s)).sum) := by ac_rfl
    _ ≤ (supNorm r.base + profileSeminorm e K s r.base + holderSeminorm s r.base) +
        3 * (r.profiles.map fun p => profileNorm p.2 K s p.1).sum :=
      add_le_add hbase_base hprofiles_sum
    _ ≤ 3 * (supNorm r.base + profileSeminorm e K s r.base +
        holderSeminorm s r.base) +
          3 * (r.profiles.map fun p => profileNorm p.2 K s p.1).sum :=
      add_le_add_left hbase_le _
    _ = 3 * representedSize s K e r := by
      unfold representedSize
      ring

end AVRegularity.Readout
end
