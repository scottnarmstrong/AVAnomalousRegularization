-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
import AVRegularity.CycleComparison.Residual.TimeIntegration
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The lifts `liftApply n (Cc hh n) a` of a lift sequence are good fields (jointly smooth and
periodic), centred when `n ≥ 1` (or `hh ≥ 1`). -/

theorem contDiff_top_foldl_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List (Fin 2)) : ∀ {g : Vec 2 → E}, ContDiff ℝ (⊤ : ℕ∞) g →
      ContDiff ℝ (⊤ : ℕ∞) (l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g) := by
  induction l with
  | nil => intro g hg; exact hg
  | cons i l ih =>
    intro g hg
    refine ih ?_
    exact (contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const

theorem orderedDerivative_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (α : DerivativeWord2 m) {g : Vec 2 → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (orderedDerivative α g) :=
  contDiff_top_foldl_fderiv (List.ofFn α) hg

section Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_goodField (c : LiftCoeff ι h) (a₀ : Vec 2 → ∀ i, h i)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) (n r : ℕ) (t : ℝ)
    (hc : ∀ m α v u, IsBoxSmooth r r (fun X z => c m α t X z v u) ∧
      ∀ X, AVenhance.IsZ2Periodic (fun z => c m α t X z v u)) :
    GoodField r (liftApply n c (fun _ => a₀) t) := by
  refine GoodField.of_forall_apply (h := h) fun v => ?_
  simp only [liftApply]
  refine GoodField.sum _ fun m _ => GoodField.sum _ fun α _ => GoodField.sum _ fun u _ => ?_
  have hg : ContDiff ℝ (r : ℕ∞) (fun X => orderedDerivative α a₀ X u) :=
    ((contDiff_pi.mp (orderedDerivative_contDiff α ha) u)).of_le (by exact_mod_cast le_top)
  have hcd : ContDiff ℝ (r : ℕ∞) (Function.uncurry fun X z => c m α t X z v u) :=
    (hc m α v u).1.contDiff_uncurry le_rfl le_rfl
  refine ⟨hcd.clm_apply (hg.comp contDiff_fst), fun X n' x => ?_⟩
  exact congrArg (fun L => L (orderedDerivative α a₀ X u)) ((hc m α v u).2 X n' x)

theorem liftApply_eq_zero (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) (t : ℝ)
    (hc : ∀ m α X z v u, c m α t X z v u = 0) : liftApply n c a t = fun _ _ => 0 := by
  funext X z
  funext v
  simp [liftApply, hc]

end Lift

section LiftSeq
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  {D : ℕ}

theorem liftApply_goodField_of_seq (Q : LiftOperatorData ι h D) {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {r : ℕ}
    (hr : r ≤ sX) (hr' : r ≤ sZ) {hh : ℕ} (hhh : hh ≤ H) (n : ℕ) {a₀ : Vec 2 → ∀ i, h i}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    GoodField r (liftApply n (Cc hh n) (fun _ => a₀) t) := by
  obtain ⟨_, _, _, _, _, h6, _⟩ := hseq
  exact liftApply_goodField _ a₀ ha n r t fun m α v u =>
    ⟨((h6 hh hhh n m α v u t ht).1).mono hr hr', (h6 hh hhh n m α v u t ht).2⟩

theorem liftApply_centField_of_seq [∀ i, CompleteSpace (h i)] (Q : LiftOperatorData ι h D) {sX sZ : ℕ} {t₀ t₁ : ℝ}
    {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    {r : ℕ} (hr : r ≤ sX) (hr' : r ≤ sZ) {hh : ℕ} (hhh : hh ≤ H) {n : ℕ} (hn : 1 ≤ n ∨ 1 ≤ hh)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    CoefField True r (liftApply n (Cc hh n) (fun _ => a₀) t) := by
  have hgood := liftApply_goodField_of_seq Q hseq hr hr' hhh n ha ht
  by_cases hz : n = 0
  · subst hz
    have h2 : ∀ m α X z v u, Cc hh 0 m α t X z v u = 0 := by
      have := hseq.2.1 hh (by omega) hhh
      exact fun m α X z v u => this m α t X z v u
    rw [liftApply_eq_zero _ _ 0 t h2]
    exact CoefField.zero
  · refine ⟨hgood, fun _ X => ?_⟩
    by_cases hN : n ≤ N
    · exact liftApply_fieldCellMean_eq_zero Q sX sZ t₀ t₁ N H Cc hseq hh hhh n (by omega) hN a₀ ha t ht X
    · have h3 : ∀ m α X z v u, Cc hh n m α t X z v u = 0 := fun m α X z v u =>
        hseq.2.2.1 hh hhh n (by omega) m α t X z v u
      rw [liftApply_eq_zero _ _ n t h3]
      exact fieldCellMean_zero

end LiftSeq

end AVRegularity
end

section
open MeasureTheory Homogenization Filter Topology AVRegularity.Sobolev
namespace AVRegularity

/-! The source operator `𝒮_ε` is a polynomial in `ε` of degree at most `D` whose coefficients
are centred (resp. good) fields when the input field is, at a quiet time. Hence the Taylor
coefficients `𝒮_j` are centred, and vanish for `j > D`. -/

theorem EpsPoly.congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : Prop} {q r : ℕ}
    {Ψ Ψ' : ℝ → Vec 2 → Vec 2 → E} (h : ∀ ε X z, Ψ ε X z = Ψ' ε X z) (hΨ : EpsPoly c q r Ψ) :
    EpsPoly c q r Ψ' := by
  obtain ⟨P, hP, hz, he⟩ := hΨ
  exact ⟨P, hP, hz, fun ε X z => by rw [← h, he]⟩

section Source
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem sourceTerm_epsPoly {c : Prop} {d : ℕ} (hd : 2 ≤ d) (hdD : d ≤ D) (η t : ℝ) {u v : ι}
    (γ : Constituent d (h u) (h v)) (α : DerivativeWord2 (d - 1))
    (hquiet : ∀ X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ z, ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : CoefField c D Φ) (k : Fin 2) :
    EpsPoly c (D - 1) 1 (fun ε X z => (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u)) := by
  have hw : EpsPoly c (0 + (d - 1)) 1 (fun ε => dEpsWord η ε α Φ) :=
    EpsPoly.dEpsWord η α (EpsPoly.const (hΦ.mono (by omega)))
  have hw' : EpsPoly c (D - 1) 1 (fun ε => dEpsWord η ε α Φ) := hw.mono_deg (by omega)
  have hl := hw'.clm (γ.map.comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) u))
  have hg : ContDiff ℝ ((1 : ℕ) : ℕ∞) (fun X => γ.coeff α t X 0 k) :=
    contDiff_pi.mp (hsm 0) k
  refine EpsPoly.congr (fun ε X z => ?_) (hl.mulX hg)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [hquiet X z 0]


theorem sourceFlux_epsPoly {c : Prop} (edge : ConstituentEdges D h) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : CoefField c D Φ) (k : Fin 2) :
    EpsPoly c (D - 1) 1 (fun ε => sourceFlux edge η ε t Φ k) := by
  refine EpsPoly.of_forall_apply (ι := ι) (h := h) (Ψ := fun ε => sourceFlux edge η ε t Φ k) fun v => ?_
  simp only [sourceFlux]
  refine EpsPoly.sum _ fun u _ => EpsPoly.sum _ fun d _ => EpsPoly.list_sum _ fun γ hγ =>
    EpsPoly.sum _ fun α _ => ?_
  have hd := Finset.mem_Icc.mp d.2
  exact sourceTerm_epsPoly hd.1 hd.2 η t γ α (hquiet v u d γ hγ α) (hsm v u d γ hγ α) hΦ k


theorem sourceOp_epsPoly {c : Prop} (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : CoefField c D Φ) :
    EpsPoly c D 0 (fun ε => sourceOp edge η ε t Φ) := by
  have hk : ∀ k : Fin 2, EpsPoly c D 0 (fun ε => dEps η ε k (sourceFlux edge η ε t Φ k)) := fun k =>
    ((sourceFlux_epsPoly edge η t hquiet hsm hΦ k).dEps η k).mono_deg (by omega)
  have := EpsPoly.sum (Finset.univ : Finset (Fin 2))
    (Ψ := fun k ε => dEps η ε k (sourceFlux edge η ε t Φ k)) (fun k _ => hk k)
  exact this

theorem sourceCoeff_coefField {c : Prop} (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η t : ℝ)
    (hquiet : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : CoefField c D Φ) :
    ∃ S : ℕ → Vec 2 → Vec 2 → ∀ i, h i, (∀ j, CoefField c 0 (S j)) ∧
      (∀ j, D < j → ∀ X z, S j X z = 0) ∧ ∀ j X z, sourceCoeff edge η j t Φ X z = S j X z := by
  obtain ⟨P, hP, hz, he⟩ := sourceOp_epsPoly edge hD η t hquiet hsm hΦ
  refine ⟨P, hP, hz, fun j X z => ?_⟩
  have hf : (fun ε : ℝ => sourceOp edge η ε t Φ X z) =
      fun ε => ∑ i ∈ Finset.range (D + 1), ε ^ i • P i X z := funext fun ε => he ε X z
  simp only [sourceCoeff, hf, iteratedDeriv_epsPoly]
  by_cases hj : j ≤ D
  · simp [hj, Nat.factorial_ne_zero]
  · simp [hj, hz j (by omega)]

end Source

end AVRegularity
end
