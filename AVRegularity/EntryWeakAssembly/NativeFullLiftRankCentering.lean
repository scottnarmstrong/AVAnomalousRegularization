-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.ReadoutLinearLevel
import AVRegularity.EntryWeakAssembly.FirstMeanZero
import AVRegularity.CycleComparison.Lift.SettingLiftSourceBlockCoefficient
import AVRegularity.EntryWeakAssembly.NativeFamilyLiftUniqueness
import AVRegularity.Proofs.Torus.FirstSource
import AVRegularity.Proofs.GenSem.ChainMetric
import AVRegularity.Proofs.GenSem.LiftOn.Omega

section
section
/-! Primitive predecessor reserves give the literal mean action without a transverse setting. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem fullCellPredecessor_mean_action (S N : ℕ) (hD : 1 ≤ D) (hS : 2 * D + 4 ≤ S)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ) (hn : 2 ≤ n)
    (QG : ∀ i j, JointSourceReserve S (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve S (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (S + D + 2) (fun t z Y => Cc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve S (fun t z Y => γ.coeff α t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ t Y v u ξ,
        fieldCellMean (fun z => Cc p q m α t Y z v u ξ) = 0)
    (hperm : ∀ m, ∀ α : DerivativeWord2 m, ∀ σ : Equiv.Perm (Fin m),
      Cc hh (n - 1) m (α ∘ σ) = Cc hh (n - 1) m α)
    (hinit : ∀ (f : Vec 2 → ι → ℝ), ∀ t,
      liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y)
    (hcut : ∀ p q, N < q → Cc p q = 0)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (X z : Vec 2) :
    leftTermsApply (actualMeanLeftTerms Q Cc hh n t) f X z =
      liftMean Q Cc (fun _ => f) hh n t X := by
  have hp1 : hh < hh ∨ (hh = hh ∧ n - 1 < n) := Or.inr ⟨rfl, by omega⟩
  have hp2 : hh < hh ∨ (hh = hh ∧ n - 2 < n) := Or.inr ⟨rfl, by omega⟩
  have hG (i j) : ContDiff ℝ 1 (fun Y => Q.G t Y i j) :=
    (((QG i j).regular t).comp₂
      (show ContDiff ℝ (S : ℕ∞) (fun _ : Vec 2 => (0 : Vec 2)) from contDiff_const)
      contDiff_id).of_le (by exact_mod_cast (show 1 ≤ S by omega))
  have hw (k) : ContDiff ℝ 1 (fun y => Real.sqrt Q.η * Q.v t y k) := by
    have hvk : ContDiff ℝ 1 (fun y => Q.v t y k) :=
      ((Qv k).fast_contDiff t 0).of_le (by exact_mod_cast (show 1 ≤ S by omega))
    exact contDiff_const.mul hvk
  have hvp : AVenhance.IsZ2Periodic (Q.v t) := by
    intro k y
    funext i
    exact (Qv i).periodic t 0 k y
  have hΓ (v u d) (γ) (hγ : γ ∈ Q.edge v u d) (α) :
      IsBoxSmooth 1 1 (fun Y y => γ.coeff α t Y y) :=
    Weighted.isBoxSmooth_of_joint_contDiff 1 1 _
      (((Qedge v u d γ hγ α).goodField t).mono (by omega)).1
  have hΓg (v u d) (γ) (hγ : γ ∈ Q.edge v u d) (α) :
      GoodField 1 (fun Y y => γ.coeff α t Y y) :=
    ((Qedge v u d γ hγ α).goodField t).mono (by omega)
  have hg (hp : hh ≠ 0) (q : ℕ) : GoodField D
      (liftApply q (Cc (hh - 1) q) (fun _ => f) t) :=
    scalarLift_goodField D q _ f hf
      (fun m α v u => (Qc (hh - 1) q (Or.inl (by omega)) m α v u).mono (2 * D) (by omega)) t
  have hcl (p q : ℕ) (hq : N < q) : liftApply q (Cc p q) (fun _ => f) t = 0 := by
    have he := liftApply_of_coeff_zero q (Cc p q)
      (fun m α s Y y v u => by rw [hcut p q hq]; rfl) (fun _ => f)
    exact congrFun he t
  apply weakActualMean_leftTerms_apply Q hD N t hG hw hvp hΓ Cc hh n hn f hf X z
  · intro k m hm α v u
    let R := actualMeanCoefficientReserve S hD (by omega) Q Cc hh n hn m hm α v u k
      QG Qv Qc Qedge hmean (hperm m)
    apply realLinearMap_field_contDiff_of_value_one 1
    exact ((R.regular t).comp₂ contDiff_const contDiff_id).of_le
      (by exact_mod_cast (show 1 ≤ S by omega))
  · intro Y m hm α v u
    exact (scalarCoefficient_goodField (S + D + 2) m (Cc hh (n - 1)) α v u
      (Qc hh (n - 1) hp1 ⟨m, by omega⟩ α v u) t).continuous_slice Y
  · exact hinit f t
  · exact scalarLift_goodField 2 (n - 1) _ f hf
      (fun m α v u => (Qc hh (n - 1) hp1 m α v u).mono 4 (by omega)) t
  · intro hhq
    apply scalarLift_centField 2 (n - 2) _ f hf
      (fun m α v u => (Qc hh (n - 2) hp2 m α v u).mono 4 (by omega)) _ t
    apply hmean hh (n - 2) hp2
    rcases hhq with hn3 | hhpos
    · exact Or.inr (by omega)
    · exact Or.inl hhpos
  · intro hhpos j hj m hm α v u
    exact scalarCoefficient_boxSmooth (S + D + 2) j ((D - 1) - j) m (by omega)
      (Cc (hh - 1) (n - 1 - j)) α v u
      (Qc (hh - 1) (n - 1 - j) (Or.inl (by omega)) ⟨m, by omega⟩ α v u) t
  · exact hg
  · intro _ q hq
    exact hcl (hh - 1) q hq
  · intro hhpos k Y
    exact (weakSourceFlux_good_of_coefficients Q N t hΓg Cc (hh - 1) (n - 1) k f
      (hg hhpos) (hcl (hh - 1))).continuous_slice Y

end AVRegularity.WeakEntryProofs
end
end

section
/-! Primitive predecessor data identify the finite forcing with the actual full-cell source. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem fullCellSource_leftTerms_apply (S N : ℕ) (hD : 1 ≤ D) (hS : 2 * D + 4 ≤ S)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (hnS : n + 1 ≤ S)
    (QG : ∀ i j, JointSourceReserve S (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve S (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (S + D + 2) (fun t z Y => Cc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve S (fun t z Y => γ.coeff α t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ t Y v u ξ,
        fieldCellMean (fun z => Cc p q m α t Y z v u ξ) = 0)
    (hperm : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m, ∀ α : DerivativeWord2 m, ∀ σ : Equiv.Perm (Fin m),
        Cc p q m (α ∘ σ) = Cc p q m α)
    (hinit : ∀ p (f : Vec 2 → ι → ℝ), ∀ t,
      liftApply 0 (Cc p 0) (fun _ => f) t = fun Y _ => if p = 0 then f Y else 0)
    (hcut : ∀ p q, N < q → Cc p q = 0)
    (hvm : ∀ t k, (∫ z in AVenhance.unitCube, Q.v t z k) = 0)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z =
      liftCellSource Q Cc (fun _ => f) hh n t X z v := by
  have hpre (p q r s : ℕ) (hp : p ≤ hh) (hq : q ≤ n)
      (hrs : r < p ∨ (r = p ∧ s < q)) : r < hh ∨ (r = hh ∧ s < n) := by
    rcases hrs with hr | ⟨hrp, hs⟩
    · exact Or.inl (lt_of_lt_of_le hr hp)
    · subst r
      by_cases hlt : p < hh
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, by omega⟩
  have hi (g : Vec 2 → ι → ℝ) (s : ℝ) :
      liftApply 0 (Cc 0 0) (fun _ => g) s = fun Y _ => g Y := by
    simpa only [ite_true] using hinit 0 g s
  let RR := fun (p q : ℕ) (hp : p ≤ hh) (hq : q ≤ n) (hq2 : 2 ≤ q)
      (k : Fin 2) (m : ℕ) (hm : m ≤ q - 1) (α : DerivativeWord2 m) (v u : ι) =>
    actualMeanCoefficientReserve S hD (by omega) Q Cc p q hq2 m hm α v u k QG Qv
      (fun r s hrs => Qc r s (hpre p q r s hp hq hrs)) Qedge
      (fun r s hrs => hmean r s (hpre p q r s hp hq hrs))
      (hperm p (q - 1) (hpre p q p (q - 1) hp hq (Or.inr ⟨rfl, by omega⟩)) m)
  have hactual (p q : ℕ) (hp : p ≤ hh) (hq : q ≤ n) (hq2 : 2 ≤ q) (Y y : Vec 2) :
      leftTermsApply (actualMeanLeftTerms Q Cc p q t) f Y y =
        liftMean Q Cc (fun _ => f) p q t Y := by
    exact fullCellPredecessor_mean_action S N hD hS Q Cc p q hq2 QG Qv
      (fun r s hrs => Qc r s (hpre p q r s hp hq hrs)) Qedge
      (fun r s hrs => hmean r s (hpre p q r s hp hq hrs))
      (hperm p (q - 1) (hpre p q p (q - 1) hp hq (Or.inr ⟨rfl, by omega⟩))) hi hcut f hf t Y y
  have hG (i j) : ContDiff ℝ 1 (fun Y => Q.G t Y i j) :=
    (((QG i j).regular t).comp₂
      (show ContDiff ℝ (S : ℕ∞) (fun _ : Vec 2 => (0 : Vec 2)) from contDiff_const)
      contDiff_id).of_le (by exact_mod_cast (show 1 ≤ S by omega))
  have hΓ (v u d) (γ) (hγ : γ ∈ Q.edge v u d) (α) :
      IsBoxSmooth 1 1 (fun Y y => γ.coeff α t Y y) :=
    Weighted.isBoxSmooth_of_joint_contDiff 1 1 _
      (((Qedge v u d γ hγ α).goodField t).mono (by omega)).1
  have hΓD (v u d) (γ) (hγ : γ ∈ Q.edge v u d) (α) :
      IsBoxSmooth D D (fun Y y => γ.coeff α t Y y) :=
    Weighted.isBoxSmooth_of_joint_contDiff D D _
      (((Qedge v u d γ hγ α).goodField t).mono (by omega)).1
  have hg (hp : hh ≠ 0) (q : ℕ) : GoodField D
      (liftApply q (Cc (hh - 1) q) (fun _ => f) t) :=
    scalarLift_goodField D q _ f hf
      (fun m α v u => (Qc (hh - 1) q (Or.inl (by omega)) m α v u).mono (2 * D) (by omega)) t
  have hcl (p q : ℕ) (hq : N < q) : liftApply q (Cc p q) (fun _ => f) t = 0 := by
    have he := liftApply_of_coeff_zero q (Cc p q)
      (fun m α s Y y v u => by rw [hcut p q hq]; rfl) (fun _ => f)
    exact congrFun he t
  apply liftCellSource_leftTerms_apply_of_representations Cc hh n f hf t X z v
  · apply weakLiftA_leftTerms_apply_of_coefficients Q hD N t hG hΓ Cc hh n hn hnN f hf X z v
    · intro m hm α v u
      exact scalarCoefficient_boxSmooth (S + D + 2) 1 1 m (by omega) (Cc hh (n - 1)) α v u
        (Qc hh (n - 1) (Or.inr ⟨rfl, by omega⟩) ⟨m, by omega⟩ α v u) t
    · intro hn2 m hm α v u
      exact scalarCoefficient_boxSmooth (S + D + 2) 2 0 m (by omega) (Cc hh (n - 2)) α v u
        (Qc hh (n - 2) (Or.inr ⟨rfl, by omega⟩) ⟨m, by omega⟩ α v u) t
    · intro hhpos q m hm α v u
      exact scalarCoefficient_boxSmooth (S + D + 2) D D m (by omega) (Cc (hh - 1) q) α v u
        (Qc (hh - 1) q (Or.inl (by omega)) ⟨m, by omega⟩ α v u) t
    · exact hg
    · intro _ q hq
      exact hcl (hh - 1) q hq
  · intro Y
    apply recurrenceMeanLeftTerms_apply_of_finite_action Q Cc hh n hn f t Y z
    · intro hn1
      subst n
      by_cases hh0 : hh = 0
      · subst hh
        apply weakLiftMean_first_diagonal_zero Q t _ (hvm t) Cc f Y (hi f t)
        exact continuous_pi (fun i => (Qv i).fast_contDiff t 0 |>.continuous)
      · apply weakLiftMean_first_positive_zero Q hD t hΓD Cc f hf hh (by omega) Y
          (fun p => hinit p f t)
        · exact (hg hh0 1).1.comp₂ contDiff_const contDiff_id
        · exact (hg hh0 1).2 Y
    · intro hn2
      exact hactual hh n le_rfl le_rfl hn2 Y z
  · intro j hj p hp
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact actualMeanLeftTerms_box_of_reserves S j 0 (by omega) Q Cc p.2 (n - j)
      (RR p.2 (n - j) (by omega) (by omega) (by omega)) t
  · intro j hj p hp Y
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact hactual p.2 (n - j) (by omega) (by omega) (by omega) Y z

end AVRegularity.WeakEntryProofs
end
end

section
/-! Primitive predecessor data produce the exact forcing coefficient and its centering. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def fullCellSourceCoefficientReserve (H : ℕ) (hH : 1 ≤ H) (hD : 1 ≤ D)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (N hh n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (hroom : 2 * D + 4 ≤ H + n)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι)
    (QG : ∀ i j, JointSourceReserve (H + n + 1) (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve (H + n) (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (H + n + D + 2) (fun t z Y => Cc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve (H + n + 1) (fun t z Y => γ.coeff α t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ t Y v u ξ,
        fieldCellMean (fun z => Cc p q m α t Y z v u ξ) = 0)
    (hperm : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m, ∀ α : DerivativeWord2 m, ∀ σ : Equiv.Perm (Fin m),
        Cc p q m (α ∘ σ) = Cc p q m α)
    (hinit : ∀ p (f : Vec 2 → ι → ℝ), ∀ t,
      liftApply 0 (Cc p 0) (fun _ => f) t = fun Y _ => if p = 0 then f Y else 0)
    (hcut : ∀ p q, N < q → Cc p q = 0)
    (hvm : ∀ t k, (∫ z in AVenhance.unitCube, Q.v t z k) = 0) :
    JointSourceReserve H (fun t z Y => liftSourceBlockCoefficient Q Cc hh n m α t Y z v u 1) := by
  have hrep (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (X z : Vec 2) :
      leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z =
        liftCellSource Q Cc (fun _ => f) hh n t X z v := by
    exact fullCellSource_leftTerms_apply (H + n) N hD hroom Q Cc hh n hn hnN (by omega)
      (fun i j => (QG i j).mono (H + n) (by omega)) Qv Qc
      (fun v u d γ hγ α => (Qedge v u d γ hγ α).mono (H + n) (by omega))
      hmean hperm hinit hcut hvm f hf t X z v
  apply sourceCoefficientReserveOfRepresentation H Q Cc hh n hn m hm α v u hrep
  intro p
  exact normalizedFullCellSourceReserve H hH hD Q Cc hh n hn
    ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) v u QG Qv Qc Qedge

theorem fullCellSourceCoefficient_mean_zero (H : ℕ) (hH : 1 ≤ H) (hD : 1 ≤ D)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (N hh n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (hroom : 2 * D + 4 ≤ H + n)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι)
    (QG : ∀ i j, JointSourceReserve (H + n + 1) (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve (H + n) (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (H + n + D + 2) (fun t z Y => Cc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α,
      JointSourceReserve (H + n + 1) (fun t z Y => γ.coeff α t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ t Y v u ξ,
        fieldCellMean (fun z => Cc p q m α t Y z v u ξ) = 0)
    (hperm : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m, ∀ α : DerivativeWord2 m, ∀ σ : Equiv.Perm (Fin m),
        Cc p q m (α ∘ σ) = Cc p q m α)
    (hinit : ∀ p (f : Vec 2 → ι → ℝ), ∀ t,
      liftApply 0 (Cc p 0) (fun _ => f) t = fun Y _ => if p = 0 then f Y else 0)
    (hcut : ∀ p q, N < q → Cc p q = 0)
    (hvm : ∀ t k, (∫ z in AVenhance.unitCube, Q.v t z k) = 0) (t : ℝ) (Y : Vec 2) :
    fieldCellMean (fun z => liftSourceBlockCoefficient Q Cc hh n m α t Y z v u 1) = 0 := by
  have hrep (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (X z : Vec 2) :
      leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z =
        liftCellSource Q Cc (fun _ => f) hh n t X z v := by
    exact fullCellSource_leftTerms_apply (H + n) N hD hroom Q Cc hh n hn hnN (by omega)
      (fun i j => (QG i j).mono (H + n) (by omega)) Qv Qc
      (fun v u d γ hγ α => (Qedge v u d γ hγ α).mono (H + n) (by omega))
      hmean hperm hinit hcut hvm f hf t X z v
  apply sourceCoefficient_mean_zero H Q Cc hh n hn m hm α v u hrep
    (fun p => normalizedFullCellSourceReserve H hH hD Q Cc hh n hn
      ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) v u QG Qv Qc Qedge) _ t Y
  intro p t Y
  apply normalizedFullCellSource_mean_zero H hH hD Q Cc hh n hn
    ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ)) u QG Qv Qc Qedge _ t Y v
  intro r s hrs hs
  exact hmean r s hrs (Or.inr (by omega))

end AVRegularity.WeakEntryProofs
end
end

section
/-! Common actual coefficient cutoffs produce globally reserved centered full-cell sources. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem fullLiftLocalCutoff_source_reserve (H : ℕ) (hH : 1 ≤ H) (hD : 1 ≤ D)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (χ : Vec 2 → ℝ) (Ω : Set (Vec 2)) (hχ : tsupport χ ⊆ Ω)
    (a b : ℝ) (hab : a ≤ b) (N hh n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hroom : 2 * D + 4 ≤ H + n) (m : ℕ) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : ι)
    (QG : ∀ i j, JointSourceReserve (H + n + 1) (fun t _ Y => Q.G t Y i j))
    (Qv : ∀ i, JointSourceReserve (H + n) (fun t z _ => Q.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ l : Fin (q + 1), ∀ β : DerivativeWord2 l.val, ∀ v u,
      JointSourceReserve (H + n + D + 2)
        (fun t z Y => fullLiftLocalCutoff χ a b Cc p q l.val β t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ β,
      JointSourceReserve (H + n + 1) (fun t z Y => γ.coeff β t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ l ≤ q, ∀ β : DerivativeWord2 l, ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ v u ξ,
        fieldCellMean (fun z => Cc p q l β t Y z v u ξ) = 0)
    (hzero : ∀ p, p ≠ 0 → Cc p 0 = 0)
    (hperm : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ l, ∀ β : DerivativeWord2 l, ∀ σ : Equiv.Perm (Fin l),
        Cc p q l (β ∘ σ) = Cc p q l β)
    (hinit : ∀ p (f : Vec 2 → ι → ℝ), ∀ t,
      liftApply 0 (Cc p 0) (fun _ => f) t = fun Y _ => if p = 0 then f Y else 0)
    (hcut : ∀ p q, N < q → Cc p q = 0)
    (hvm : ∀ t k, (∫ z in AVenhance.unitCube, Q.v t z k) = 0) :
    let Dc := fullLiftLocalCutoff χ a b Cc
    Nonempty (JointSourceReserve H
      (fun t z Y => liftSourceBlockCoefficient Q Dc hh n m α t Y z v u 1)) ∧
    ∀ t Y, (∫ z in AVenhance.unitCube,
      liftSourceBlockCoefficient Q Dc hh n m α t Y z v u 1) = 0 := by
  let Dc := fullLiftLocalCutoff χ a b Cc
  have hmeanD (p q : ℕ) (hpq : p < hh ∨ (p = hh ∧ q < n))
      (hne : p ≠ 0 ∨ q ≠ 0) (l : ℕ) (hl : l ≤ q) (β : DerivativeWord2 l)
      (t : ℝ) (Y : Vec 2) (v u : ι) (ξ : ℝ) :
      fieldCellMean (fun z => Dc p q l β t Y z v u ξ) = 0 :=
    fullLiftLocalCutoff_rank_mean_zero χ a b hab Ω hχ Cc p q hne (hzero p)
      l β v u (fun t ht Y hY ξ => hmean p q hpq hne l hl β t ht Y hY v u ξ) t Y ξ
  have hpermD p q (hpq : p < hh ∨ (p = hh ∧ q < n)) l (β : DerivativeWord2 l) (σ : Equiv.Perm (Fin l)) :
      Dc p q l (β ∘ σ) = Dc p q l β :=
    fullLiftLocalCutoff_perm χ a b Cc p q l β σ (hperm p q hpq l β σ)
  have hinitD p (f : Vec 2 → ι → ℝ) t :
      liftApply 0 (Dc p 0) (fun _ => f) t = fun Y _ => if p = 0 then f Y else 0 := by
    change liftApply 0 (fullLiftLocalCutoff χ a b Cc p 0) (fun _ => f) t = _
    rw [fullLiftLocalCutoff_zero_degree]
    exact hinit p f t
  have hcutD p q (hq : N < q) : Dc p q = 0 :=
    fullLiftLocalCutoff_zero χ a b Cc p q (hcut p q hq)
  exact ⟨⟨fullCellSourceCoefficientReserve H hH hD Q Dc N hh n hn hnN hroom m hm α v u
      QG Qv Qc Qedge hmeanD hpermD hinitD hcutD hvm⟩,
    fullCellSourceCoefficient_mean_zero H hH hD Q Dc N hh n hn hnN hroom m hm α v u
      QG Qv Qc Qedge hmeanD hpermD hinitD hcutD hvm⟩

end AVRegularity.WeakEntryProofs
end
end

section
/-! Genuine reserved local models identify finite forcing with the literal full-cell source. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem fullCellSource_finite_action_of_local_model (S N : ℕ) (hD : 1 ≤ D) (hS : 2 * D + 4 ≤ S)
    (Q Q' : LiftOperatorData ι (fun _ => ℝ) D) (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc Dc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (hh n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (hnS : n + 1 ≤ S)
    (QG : ∀ i j, JointSourceReserve S (fun t _ Y => Q'.G t Y i j))
    (Qv : ∀ i, JointSourceReserve S (fun t z _ => Q'.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      JointSourceReserve (S + D + 2) (fun t z Y => Dc p q m.val α t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q'.edge v u d, ∀ α,
      JointSourceReserve S (fun t z Y => γ.coeff α t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ t Y v u ξ,
        fieldCellMean (fun z => Dc p q m α t Y z v u ξ) = 0)
    (hperm : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m, ∀ α : DerivativeWord2 m, ∀ σ : Equiv.Perm (Fin m),
        Dc p q m (α ∘ σ) = Dc p q m α)
    (hinit : ∀ p (f : Vec 2 → ι → ℝ), ∀ t,
      liftApply 0 (Dc p 0) (fun _ => f) t = fun Y _ => if p = 0 then f Y else 0)
    (hcut : ∀ p q, N < q → Dc p q = 0)
    (hvm : ∀ t k, (∫ z in AVenhance.unitCube, Q'.v t z k) = 0)
    (U : Set (Vec 2)) (hU : IsOpen U) (t : ℝ)
    (hG : ∀ X ∈ U, Q.G t X = Q'.G t X) (hΓ : SlowOpenEdgeEq U t Q.edge Q'.edge)
    (he : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ m ≤ q,
      ∀ α : DerivativeWord2 m, ∀ X ∈ U, ∀ z v u,
        Cc p q m α t X z v u = Dc p q m α t X z v u)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (X : Vec 2) (hX : X ∈ U) (z : Vec 2) (v : ι) :
    leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z =
      liftCellSource Q Cc (fun _ => f) hh n t X z v := by
  have hc : liftApply n (liftSourceBlockCoefficient Q Cc hh n) (fun _ => f) t X z v =
      liftApply n (liftSourceBlockCoefficient Q' Dc hh n) (fun _ => f) t X z v := by
    have hh := liftApply_slow_open_congr hU n t
      (liftSourceBlockCoefficient Q Cc hh n) (liftSourceBlockCoefficient Q' Dc hh n)
      (fun _ => f) (fun _ => f)
      (fun m _ α Y hY z v u =>
        fullCellSourceCoefficient_slow_local_primitive_congr U hU Q Q' hη hv Cc Dc
          hh n hn t hG hΓ he m α Y hY z v u)
      (fun _ _ => rfl) X hX z
    exact congrFun hh v
  calc
    leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f X z =
        liftApply n (liftSourceBlockCoefficient Q Cc hh n) (fun _ => f) t X z v :=
      (liftSourceBlockCoefficient_action Q Cc hh n hn f hf t X z v).symm
    _ = liftApply n (liftSourceBlockCoefficient Q' Dc hh n) (fun _ => f) t X z v := hc
    _ = leftTermsApply (liftCellSourceLeftTerms Q' Dc hh n t v) f X z :=
      liftSourceBlockCoefficient_action Q' Dc hh n hn f hf t X z v
    _ = liftCellSource Q' Dc (fun _ => f) hh n t X z v :=
      fullCellSource_leftTerms_apply S N hD hS Q' Dc hh n hn hnN hnS QG Qv Qc Qedge
        hmean hperm hinit hcut hvm f hf t X z v
    _ = liftCellSource Q Cc (fun _ => f) hh n t X z v :=
      (congrFun (fullCellSource_slow_local_primitive_congr hU Q Q' hη hv Cc Dc
        (fun _ => f) hh n hn t hG hΓ he X hX z) v).symm

end AVRegularity.WeakEntryProofs
end
end

section
/-! Common predecessor cutoffs identify the actual finite forcing on their unit germ. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem fullLiftLocalCutoff_finite_source_action (S : ℕ) (hD : 1 ≤ D) (hS : 2 * D + 4 ≤ S)
    (Q Q' : LiftOperatorData ι (fun _ => ℝ) D) (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (χ : Vec 2 → ℝ) (Ω : Set (Vec 2)) (hχ : tsupport χ ⊆ Ω)
    (a b : ℝ) (hab : a ≤ b) (N hh n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hnS : n + 1 ≤ S)
    (QG : ∀ i j, JointSourceReserve S (fun t _ Y => Q'.G t Y i j))
    (Qv : ∀ i, JointSourceReserve S (fun t z _ => Q'.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ l : Fin (q + 1), ∀ β : DerivativeWord2 l.val, ∀ v u,
      JointSourceReserve (S + D + 2)
        (fun t z Y => fullLiftLocalCutoff χ a b Cc p q l.val β t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q'.edge v u d, ∀ β,
      JointSourceReserve S (fun t z Y => γ.coeff β t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ l ≤ q, ∀ β : DerivativeWord2 l, ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ v u ξ,
        fieldCellMean (fun z => Cc p q l β t Y z v u ξ) = 0)
    (hzero : ∀ p, p ≠ 0 → Cc p 0 = 0)
    (hperm : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ l, ∀ β : DerivativeWord2 l, ∀ σ : Equiv.Perm (Fin l),
        Cc p q l (β ∘ σ) = Cc p q l β)
    (hinit : ∀ p (f : Vec 2 → ι → ℝ), ∀ t,
      liftApply 0 (Cc p 0) (fun _ => f) t = fun Y _ => if p = 0 then f Y else 0)
    (hcut : ∀ p q, N < q → Cc p q = 0)
    (hvm : ∀ t k, (∫ z in AVenhance.unitCube, Q'.v t z k) = 0)    (U : Set (Vec 2)) (hU : IsOpen U) (hone : ∀ Y ∈ U, χ Y = 1)
    (t : ℝ) (ht : t ∈ Icc a b)
    (hG : ∀ Y ∈ U, Q.G t Y = Q'.G t Y) (hΓ : SlowOpenEdgeEq U t Q.edge Q'.edge)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (Y : Vec 2) (hY : Y ∈ U) (z : Vec 2) (v : ι) :
    leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f Y z =
      liftCellSource Q Cc (fun _ => f) hh n t Y z v := by
  let Dc := fullLiftLocalCutoff χ a b Cc
  have hmeanD (p q : ℕ) (hpq : p < hh ∨ (p = hh ∧ q < n))
      (hne : p ≠ 0 ∨ q ≠ 0) (l : ℕ) (hl : l ≤ q) (β : DerivativeWord2 l)
      (t : ℝ) (Y : Vec 2) (v u : ι) (ξ : ℝ) :
      fieldCellMean (fun z => Dc p q l β t Y z v u ξ) = 0 :=
    fullLiftLocalCutoff_rank_mean_zero χ a b hab Ω hχ Cc p q hne (hzero p)
      l β v u (fun t ht Y hY ξ => hmean p q hpq hne l hl β t ht Y hY v u ξ) t Y ξ
  have hpermD p q (hpq : p < hh ∨ (p = hh ∧ q < n)) l (β : DerivativeWord2 l) (σ : Equiv.Perm (Fin l)) :
      Dc p q l (β ∘ σ) = Dc p q l β :=
    fullLiftLocalCutoff_perm χ a b Cc p q l β σ (hperm p q hpq l β σ)
  have hinitD p (f : Vec 2 → ι → ℝ) t :
      liftApply 0 (Dc p 0) (fun _ => f) t = fun Y _ => if p = 0 then f Y else 0 := by
    change liftApply 0 (fullLiftLocalCutoff χ a b Cc p 0) (fun _ => f) t = _
    rw [fullLiftLocalCutoff_zero_degree]
    exact hinit p f t
  have hcutD p q (hq : N < q) : Dc p q = 0 :=
    fullLiftLocalCutoff_zero χ a b Cc p q (hcut p q hq)
  exact fullCellSource_finite_action_of_local_model S N hD hS Q Q' hη hv Cc Dc
    hh n hn hnN hnS QG Qv Qc Qedge hmeanD hpermD hinitD hcutD hvm
    U hU t hG hΓ
    (fun p q _ l _ β X hX z v u =>
      (fullLiftLocalCutoff_copy χ a b Cc p q l β t ht X (hone X hX) z v u).symm)
    f hf Y hY z v

end AVRegularity.WeakEntryProofs
end
end

section
/-! A primitive local model and common predecessor cutoff reserve the literal full-cell source. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem fullLift_local_source_reserve (H : ℕ) (hH : 1 ≤ H) (hD : 1 ≤ D)
    (Q Q' : LiftOperatorData ι (fun _ => ℝ) D) (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (χ : Vec 2 → ℝ) (Ω U : Set (Vec 2)) (hχ : tsupport χ ⊆ Ω)
    (hU : IsOpen U) (hone : ∀ Y ∈ U, χ Y = 1)
    (a b : ℝ) (hab : a ≤ b) (N hh n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hroom : 2 * D + 4 ≤ H + n) (m : ℕ) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : ι)
    (QG : ∀ i j, JointSourceReserve (H + n + 1) (fun t _ Y => Q'.G t Y i j))
    (Qv : ∀ i, JointSourceReserve (H + n) (fun t z _ => Q'.v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ l : Fin (q + 1), ∀ β : DerivativeWord2 l.val, ∀ v u,
      JointSourceReserve (H + n + D + 2)
        (fun t z Y => fullLiftLocalCutoff χ a b Cc p q l.val β t Y z v u 1))
    (Qedge : ∀ v u d, ∀ γ ∈ Q'.edge v u d, ∀ β,
      JointSourceReserve (H + n + 1) (fun t z Y => γ.coeff β t Y z))
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ l ≤ q, ∀ β : DerivativeWord2 l, ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ v u ξ,
        fieldCellMean (fun z => Cc p q l β t Y z v u ξ) = 0)
    (hzero : ∀ p, p ≠ 0 → Cc p 0 = 0)
    (hperm : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ l, ∀ β : DerivativeWord2 l, ∀ σ : Equiv.Perm (Fin l),
        Cc p q l (β ∘ σ) = Cc p q l β)
    (hinit : ∀ p (f : Vec 2 → ι → ℝ), ∀ t,
      liftApply 0 (Cc p 0) (fun _ => f) t = fun Y _ => if p = 0 then f Y else 0)
    (hcut : ∀ p q, N < q → Cc p q = 0)
    (hvm : ∀ t k, (∫ z in AVenhance.unitCube, Q'.v t z k) = 0)
    (hG : ∀ t ∈ Icc a b, ∀ Y ∈ U, Q.G t Y = Q'.G t Y)
    (hΓ : ∀ t ∈ Icc a b, SlowOpenEdgeEq U t Q.edge Q'.edge) :
    ∃ g' : ℝ → Vec 2 → Vec 2 → ℝ,
      Nonempty (IndependentParameterSourceReserve H g') ∧
      (∀ t Y, (∫ z in AVenhance.unitCube, g' t z Y) = 0) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
        g' t z Y = weakLiftCoefficientForcing Q Cc hh n m α v u t z Y := by
  obtain ⟨⟨R⟩, hcenter⟩ := fullLiftLocalCutoff_source_reserve H hH hD Q' Cc χ Ω hχ
    a b hab N hh n hn hnN hroom m hm α v u QG Qv Qc Qedge
    hmean hzero hperm hinit hcut hvm
  refine ⟨_, ⟨independentReserveOfJoint R⟩, hcenter, ?_⟩
  intro t ht Y hYU z
  exact fullLiftLocalCutoff_source_germ U hU Q Q' hη hv Cc χ hone
    a b hh n hn t ht (hG t ht) (hΓ t ht) m α Y hYU z v u

end AVRegularity.WeakEntryProofs
end
end

section
/-! The completed inverse recurrence has the literal full-cell forcing on each local carrier germ. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem weakLiftInverseCoefficients_local_finite_source_action
    (S : ℕ) (hD : 1 ≤ D) (hS : 2 * D + 4 ≤ S)
    (a b : ℝ) (hab : a ≤ b) (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (Y₀ : Vec 2) (hYΩ : Y₀ ∈ Ω)
    (Q Q' : LiftOperatorData ι (fun _ => ℝ) D) (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (hnS : n + 1 ≤ S)
    (V : Set (Vec 2)) (hV : IsOpen V) (hYV : Y₀ ∈ V)
    (hG : ∀ t ∈ Icc a b, ∀ Y ∈ V, Q.G t Y = Q'.G t Y)
    (hΓ : ∀ t ∈ Icc a b, SlowOpenEdgeEq V t Q.edge Q'.edge)
    (QG : ∀ i j, JointSourceReserve S (fun t _ Y => Q'.G t Y i j))
    (Qv : ∀ i, JointSourceReserve S (fun t z _ => Q'.v t z i))
    (Qedge : ∀ v u d, ∀ γ ∈ Q'.edge v u d, ∀ β,
      JointSourceReserve S (fun t z Y => γ.coeff β t Y z))
    (hvm : ∀ t k, (∫ z in AVenhance.unitCube, Q'.v t z k) = 0)
    (hz : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u Y, Y ∈ Ω →
        ∀ z, weakLiftInverseCoefficients Q inv N p q m α a Y z v u 1 = 0)
    (hloc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u,
        ∃ (U : Set (Vec 2)) (f' : ℝ → Vec 2 → Vec 2 → ℝ),
          IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve (S + D + 2)
            (independentTimeWindowSource (Ioc a b) f')) ∧
          ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
            f' t z Y = weakLiftInverseCoefficients Q inv N p q m α t Y z v u 1)
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ l ≤ q, ∀ β : DerivativeWord2 l, ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ v u ξ,
        fieldCellMean (fun z => weakLiftInverseCoefficients Q inv N p q l β t Y z v u ξ) = 0)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (z : Vec 2) (v : ι) :
    leftTermsApply (liftCellSourceLeftTerms Q (weakLiftInverseCoefficients Q inv N) hh n t v) f Y₀ z =
      liftCellSource Q (weakLiftInverseCoefficients Q inv N) (fun _ => f) hh n t Y₀ z v := by
  obtain ⟨χ, hs, hone, ⟨Qc⟩⟩ := weakLiftInverseCoefficients_local_cutoff_reserve
    a b hab Ω hΩ Y₀ hYΩ Q inv N hh n hz hloc
  obtain ⟨W, hW, hYW, hWΩ, hχ⟩ := unit_cutoff_open_neighborhood χ Ω hΩ Y₀ hYΩ hone
  let U := W ∩ V
  have hzero p (hp : p ≠ 0) : weakLiftInverseCoefficients Q inv N p 0 = 0 := by
    funext l β t Y z v u
    exact weakLiftInverseCoefficients_positive_grade_zero Q inv N p (by omega) l β t Y z v u
  exact fullLiftLocalCutoff_finite_source_action S hD hS Q Q' hη hv
    (weakLiftInverseCoefficients Q inv N) χ Ω hs a b hab N hh n hn hnN hnS
    QG Qv Qc Qedge hmean hzero
    (fun p q _ l β σ => weakLiftInverseCoefficients_perm Q inv N p q l β σ)
    (weakLiftInverseCoefficients_initial_action Q inv N)
    (weakLiftInverseCoefficients_cutoff Q inv N) hvm U (hW.inter hV)
    (fun Y hY => hχ Y hY.1) t ht
    (fun Y hY => hG t ht Y hY.2) ((hΓ t ht).mono (fun _ hY => hY.2))
    f hf Y₀ ⟨hYW, hYV⟩ z v

end AVRegularity.WeakEntryProofs
end
end
end

section
section
/-! Local predecessor reserves produce the literal next forcing of the full inverse recurrence. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem weakLiftInverseCoefficients_local_source_production
    (H : ℕ) (hH : 1 ≤ H) (hD : 1 ≤ D)
    (a b : ℝ) (hab : a ≤ b) (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (Y₀ : Vec 2) (hYΩ : Y₀ ∈ Ω)
    (Q Q' : LiftOperatorData ι (fun _ => ℝ) D) (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    (inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (hroom : 2 * D + 4 ≤ H + n)
    (V : Set (Vec 2)) (hV : IsOpen V) (hYV : Y₀ ∈ V)
    (hG : ∀ t ∈ Icc a b, ∀ Y ∈ V, Q.G t Y = Q'.G t Y)
    (hΓ : ∀ t ∈ Icc a b, SlowOpenEdgeEq V t Q.edge Q'.edge)
    (QG : ∀ i j, JointSourceReserve (H + n + 1) (fun t _ Y => Q'.G t Y i j))
    (Qv : ∀ i, JointSourceReserve (H + n) (fun t z _ => Q'.v t z i))
    (Qedge : ∀ v u d, ∀ γ ∈ Q'.edge v u d, ∀ β,
      JointSourceReserve (H + n + 1) (fun t z Y => γ.coeff β t Y z))
    (hvm : ∀ t k, (∫ z in AVenhance.unitCube, Q'.v t z k) = 0)
    (hz : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u Y, Y ∈ Ω →
        ∀ z, weakLiftInverseCoefficients Q inv N p q m α a Y z v u 1 = 0)
    (hloc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u,
        ∃ (U : Set (Vec 2)) (f' : ℝ → Vec 2 → Vec 2 → ℝ),
          IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve (H + n + D + 2)
            (independentTimeWindowSource (Ioc a b) f')) ∧
          ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
            f' t z Y = weakLiftInverseCoefficients Q inv N p q m α t Y z v u 1)
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ l ≤ q, ∀ β : DerivativeWord2 l, ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ v u ξ,
        fieldCellMean (fun z => weakLiftInverseCoefficients Q inv N p q l β t Y z v u ξ) = 0)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι) :
    ∃ (U : Set (Vec 2)) (g' : ℝ → Vec 2 → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ U ⊆ Ω ∧ Nonempty (IndependentParameterSourceReserve H g') ∧
      (∀ t Y, (∫ z in AVenhance.unitCube, g' t z Y) = 0) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
        g' t z Y = weakLiftCoefficientForcing Q (weakLiftInverseCoefficients Q inv N)
          hh n m α v u t z Y := by
  obtain ⟨χ, hs, hone, ⟨Qc⟩⟩ := weakLiftInverseCoefficients_local_cutoff_reserve
    a b hab Ω hΩ Y₀ hYΩ Q inv N hh n hz hloc
  obtain ⟨W, hW, hYW, hWΩ, hχ⟩ := unit_cutoff_open_neighborhood χ Ω hΩ Y₀ hYΩ hone
  let U := W ∩ V
  have hzero p (hp : p ≠ 0) : weakLiftInverseCoefficients Q inv N p 0 = 0 := by
    funext l β t Y z v u
    exact weakLiftInverseCoefficients_positive_grade_zero Q inv N p (by omega) l β t Y z v u
  obtain ⟨g', hres, hcenter, he⟩ := fullLift_local_source_reserve H hH hD Q Q' hη hv
    (weakLiftInverseCoefficients Q inv N) χ Ω U hs (hW.inter hV)
    (fun Y hY => hχ Y hY.1) a b hab N hh n hn hnN hroom m hm α v u
    QG Qv Qc Qedge hmean hzero
    (fun p q _ l β σ => weakLiftInverseCoefficients_perm Q inv N p q l β σ)
    (weakLiftInverseCoefficients_initial_action Q inv N)
    (weakLiftInverseCoefficients_cutoff Q inv N) hvm
    (fun t ht Y hY => hG t ht Y hY.2)
    (fun t ht => (hΓ t ht).mono (fun _ hY => hY.2))
  exact ⟨U, g', hW.inter hV, ⟨hYW, hYV⟩, fun _ hY => hWΩ hY.1, hres, hcenter, he⟩

end AVRegularity.WeakEntryProofs
end
end

section
/-! Every positive native full-lift coefficient is literally zero off its solving window. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem nativeWindowResponseLinear_zero_off_window (D : OCData) (hζ : IsFastProfile D.ζ)
    (level : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) (Y : Vec 2) (g : ℝ → Vec 2 → ℝ)
    (t : ℝ) (ht : t ∉ Icc a b) :
    nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab Y g t = 0 :=
  windowResponseLinear_zero_off_window _ _ r hr a b hab _ g t ht

theorem native_full_lift_coefficient_zero_off_window (D : OCData) (hζ : IsFastProfile D.ζ)
    (level : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (r : ℕ) (hr : 1 ≤ r)
    (a b : ℝ) (hab : a ≤ b) (N hh n m : ℕ) (hn : 1 ≤ n)
    (α : DerivativeWord2 m) (t : ℝ) (ht : t ∉ Icc a b) (Y z : Vec 2) (v u : ι) :
    weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge)
      (fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab Y)
      N hh n m α t Y z v u = 0 := by
  by_cases hnN : n ≤ N
  · by_cases hm : m ≤ n
    · rw [weakLiftInverseCoefficients_eq_full_step _ _ N hh n hn hnN]
      simp only [weakLiftStepWithInverse, ite_eq_right (by omega : n ≠ 0), ite_eq_left hm]
      rw [nativeWindowResponseLinear_zero_off_window D hζ level slot hslot A ρ edge r hr
        a b hab Y _ t ht]
      exact zero_smul ℝ (ContinuousLinearMap.id ℝ ℝ)
    · exact weakLiftInverseCoefficients_above_order _ _ N hh n m (by omega) α t Y z v u
  · rw [weakLiftInverseCoefficients_cutoff _ _ N hh n (by omega)]
    rfl

end AVRegularity.WeakEntryProofs
end
end

section
/-! Uniqueness transfers the weak source coefficients between equivalent actual chain lifts. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open AVRegularity.Providers.Torus AVRegularity.Providers.GenSem
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D ScalarH Dm bw j₀}

/-- Precisely the geometric data read by an inherited path or a grade-zero eddy lift. -/
structure WeakChainLiftEquiv (G : GenStage D ScalarH Dm bw j₀) (k : ℤ)
    (A B : RealChain) (ρ : ℝ) : Prop where
  admissible : IsAdmissibleChain D bw j₀ G.level k A ↔ IsAdmissibleChain D bw j₀ G.level k B
  carrier : ladderOmega D bw j₀ G.level k A ρ = ladderOmega D bw j₀ G.level k B ρ
  eddyData : familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k A ρ (fun _ _ _ => []) =
    familyLiftData D G.level k B ρ (fun _ _ _ => [])
  pathData : ∀ h (π : StagePath G h) (hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k)
    (hB : IsAdmissibleChain D bw j₀ G.level k B ∧ Odd k),
    familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩) =
    familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hB.2⟩ ⟨B, hB.1⟩)

/-- The scalar eddy mean only reads the degree-zero-grade coefficients at its cell time. -/
theorem weakEddyFlux_coefficients_congr (D : OCData) (m : ℕ) (ρ : ℝ)
    (Q : LiftOperatorData (Fin 1) (fun _ => ℝ) Dm)
    (Cc Dc : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (n : ℕ) (t : ℝ)
    (h : ∀ l α X z v u, Cc 0 (n - 1) l α ((D.cellScaleSq m)⁻¹ * t) X z v u =
      Dc 0 (n - 1) l α ((D.cellScaleSq m)⁻¹ * t) X z v u) :
    weakEddyFlux D m ρ Q Cc n t = weakEddyFlux D m ρ Q Dc n t := by
  have ha (a : ℝ → Vec 2 → Fin 1 → ℝ) :
      liftApply (n - 1) (Cc 0 (n - 1)) a ((D.cellScaleSq m)⁻¹ * t) =
        liftApply (n - 1) (Dc 0 (n - 1)) a ((D.cellScaleSq m)⁻¹ * t) := by
    apply Uniqueness.liftApply_congr (ha := rfl)
    intro l _ α
    funext X z v u
    exact h l α X z v u
  unfold weakEddyFlux
  simp only [ha]

/-- The weak finer-source coefficients agree at every active finer-slot time. -/
theorem weak_source_fluxCoeff_chain_equiv (hζ : IsFastProfile D.ζ) (Mn : WeakMenu) (ρ : ℝ)
    (s : WeakSource G)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hLF : s.IsLiftFamily Mn.sX Mn.sZ Mn.N ρ Cc)
    (hDL : ∀ k A, Odd k → IsAdmissibleChain D bw j₀ G.level k A →
      IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k A ρ
        (fun _ _ _ => [])) Mn.sX Mn.sZ
        (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N 0 (Cc0 k A))
    (hτ : 0 < ocTau D.α D.q D.Λ G.level) (hcs : 0 ≤ D.cellScaleSq G.level)
    (k : ℤ) (t : ℝ) (hc : ocCutoff D.α D.q D.Λ G.level k t ≠ 0)
    (A B : RealChain) (hAB : WeakChainLiftEquiv G k A B ρ)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    fluxCoeff (s.fluxOp ρ Cc Cc0 k t A) d I 0 = fluxCoeff (s.fluxOp ρ Cc Cc0 k t B) d I 0 := by
  classical
  by_cases hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k
  · have hB : IsAdmissibleChain D bw j₀ G.level k B ∧ Odd k := ⟨hAB.admissible.mp hA.1, hA.2⟩
    have htime := mem_liftWindow_of_cutoff D hτ hcs hc
    have hab := liftWindow_le D hτ hcs k
    cases s with
    | inherited w h π n =>
      have hQ := hAB.pathData h π hA hB
      have hCa := hLF k A hA
      have hCb := hLF k B hB
      rw [← hAB.carrier, ← hQ] at hCb
      have hu := native_family_lift_coefficients_unique D hζ G.level k hA.2 A ρ _ _
        (isOpen_ladderOmega _ _ _ _ _ _ _) _ _ hab Mn.N h Mn.sX Mn.sZ Mn.sX Mn.sZ
        (Cc k A) (Cc k B) hCa hCb
      have hP : ∀ hh ≤ h, ∀ n' l α, ∀ X ∈ ladderOmega D bw j₀ G.level k A ρ,
          Cc k A hh n' l α ((D.cellScaleSq G.level)⁻¹ * t) X =
          Cc k B hh n' l α ((D.cellScaleSq G.level)⁻¹ * t) X := by
        intro hh hhh n' l α X hX
        funext z v u
        exact hu hh hhh n' l α _ htime X hX z v u
      simp only [WeakSource.fluxOp, dite_eq_left hA, dite_eq_left hB, ← hQ]
      unfold fluxCoeff
      apply congrArg (fun V : Vec 2 => ((d - 1).factorial : ℝ)⁻¹ • V)
      exact Uniqueness.pathMeanFlux_eq_of_agreeOn D G.level ρ _ _ _ n t
        (isOpen_ladderOmega _ _ _ _ _ _ _) hP _ 0
        (by rw [smul_zero]; exact zero_mem_ladderOmega hζ hA.1 ρ)
    | eddy v w n =>
      have hCa := Uniqueness.IsLiftSequence.toOn (hDL k A hA.2 hA.1) Set.univ
      have hCb := Uniqueness.IsLiftSequence.toOn (hDL k B hB.2 hB.1) Set.univ
      rw [← hAB.eddyData] at hCb
      have hu := native_family_lift_coefficients_unique D hζ G.level k hA.2 A ρ _ Set.univ
        isOpen_univ _ _ hab Mn.N 0 Mn.sX Mn.sZ Mn.sX Mn.sZ (Cc0 k A) (Cc0 k B) hCa hCb
      have hf := weakEddyFlux_coefficients_congr D G.level ρ
        (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k A ρ (fun _ _ _ => [])) (Cc0 k A) (Cc0 k B) n t
        (fun l α X z v u => hu 0 le_rfl (n - 1) l α _ htime X (Set.mem_univ _) z v u)
      simp only [WeakSource.fluxOp, dite_eq_left hA, dite_eq_left hB, ← hAB.eddyData, hf]
  · have hB : ¬ (IsAdmissibleChain D bw j₀ G.level k B ∧ Odd k) :=
      fun hb => hA ⟨hAB.admissible.mpr hb.1, hb.2⟩
    simp only [WeakSource.fluxOp, dite_eq_right hA, dite_eq_right hB]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Base lattice shifts and parallel phase shifts preserve the data of the actual weak lifts. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.Providers.Torus
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G : GenStage D ScalarH Dm bw j₀}

/-- Base shifts commute with all incoming path data and preserve the localized carrier. -/
theorem weakChainLiftEquiv_shiftBase (hG : G.IsShiftInvariant) (k : ℤ) (A : RealChain)
    (ρ : ℝ) (n : Fin 2 → ℤ) : WeakChainLiftEquiv G k A (A.shiftBase n) ρ := by
  refine ⟨(isAdmissibleChain_shiftBase _ _ _ _ _ _ _).symm,
    (ladderOmega_shiftBase D bw j₀ G.level k A ρ n).symm,
    (familyLiftData_shiftBase D G.level k A ρ _ n).symm, ?_⟩
  intro h π hA hB
  rw [pathEdges_shiftBase hG π ⟨k, hA.2⟩ ⟨A, hA.1⟩ ⟨A.shiftBase n, hB.1⟩ n rfl,
    familyLiftData_shiftBase]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Every actual weak passage preserves the full context-level torus law, by lift uniqueness. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization AVRegularity.Sobolev AVRegularity.Providers.Torus
variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G G' : GenStage D ScalarH Dm bw j₀}

/-- The slow-offset law follows from the exact recentering formula of any actual weak passage. -/
theorem weakPassage_slowOffset (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (hε : D.eps (G'.level - 1) ≠ 0) :
    ∀ (p : OddSlot) (c c' : StageCtx D bw j₀ G'.level p) (n : Fin 2 → ℤ), c.1.children = [] →
    c'.1 = c.1.shiftBase n → ∀ v u (γ : G'.fam.Γ v u) d (I : DerivativeWord2 (d - 1)) t X z,
      G'.fam.flux p c v u γ d I t (X + (D.eps (G'.level - 1))⁻¹ • AVenhance.latticeShift n) z =
        G'.fam.flux p c' v u γ d I t X z := by
  intro p c c' n h0 hc v u γ d I t X z
  have hrec : c.1.recenter D (D.eps (G'.level - 1) •
      (X + (D.eps (G'.level - 1))⁻¹ • AVenhance.latticeShift n)) =
      c'.1.recenter D (D.eps (G'.level - 1) • X) := by
    rw [smul_add, smul_inv_smul₀ hε, hc, RealChain.recenter_add_shiftBase D c.1 h0]
  by_cases hd : 2 ≤ d
  · obtain ⟨-, -, -, -, -, e, idx, Cc, Cc0, -, -, -, hall⟩ := hp
    rw [(hall v u γ).2.2 p c d I t _ z hd, (hall v u γ).2.2 p c' d I t X z hd, hrec]
  · rw [G'.fam.flux_zero p c v u γ d I (fun h => hd h.1),
      G'.fam.flux_zero p c' v u γ d I (fun h => hd h.1)]

/-- The base-shift law uses the same unique lifts at every time of nonzero finer cutoff. -/
theorem weakPassage_isShiftInvariant (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (hG : G.IsShiftInvariant)
    (hζ : IsFastProfile D.ζ) (hτ : 0 < ocTau D.α D.q D.Λ G.level)
    (hcs : 0 ≤ D.cellScaleSq G.level) (heps : ∀ i, 0 < D.eps i) :
    G'.IsShiftInvariant := by
  refine ⟨?_, weakPassage_slowOffset P Mn rW Din hp (heps _).ne'⟩
  intro p c c' n hc v u γ d I
  funext t X z
  by_cases hd : 2 ≤ d
  swap
  · rw [G'.fam.flux_zero p c' v u γ d I (fun h => hd h.1),
      G'.fam.flux_zero p c v u γ d I (fun h => hd h.1)]
  obtain ⟨-, -, -, -, -, e, idx, Cc, Cc0, hLF, hDL, -, hall⟩ := hp
  rw [(hall v u γ).2.2 p c' d I t X z hd, (hall v u γ).2.2 p c d I t X z hd,
    hc, recenter_shiftBase]
  let A := c.1.recenter D (D.eps (G'.level - 1) • X)
  by_cases hA : IsAdmissibleChain D bw j₀ G'.level p.1 A
  · have hA' : IsAdmissibleChain D bw j₀ G'.level p.1 (A.shiftBase n) := hA
    rw [ite_eq_left hA', ite_eq_left hA]
    apply transferAt_shiftBase D G.level p.1 _ _ _ t A z n d I
    intro k hk d' I'
    exact (weak_source_fluxCoeff_chain_equiv hζ Mn (D.eps (G.level - 1))
      (e v u γ).1 (Cc (e v u γ).1) Cc0 (hLF _) hDL hτ hcs k t hk _ _
      (weakChainLiftEquiv_shiftBase hG k (A.appendChild D k t z) _ n) d' I').symm
  · have hA' : ¬ IsAdmissibleChain D bw j₀ G'.level p.1 (A.shiftBase n) := hA
    rw [ite_eq_right hA', ite_eq_right hA]

end AVRegularity.WeakEntryProofs
end
end

section
/-! Local primitive models identify the literal finite native full-cell forcing. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_cell_finite_source_action
    (D : OCData) (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ)
    (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (S : ℕ) (hDm : 1 ≤ Dm) (hS : 2 * Dm + 4 ≤ S)
    (a b : ℝ) (hab : a ≤ b) (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (Y₀ : Vec 2) (hYΩ : Y₀ ∈ Ω)
    (inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (hnS : n + 1 ≤ S)
    (V : Set (Vec 2)) (hV : IsOpen V) (hYV : Y₀ ∈ V)
    (edge' : ConstituentEdges Dm (fun _ : ι => ℝ))
    (he : ∀ t ∈ Icc a b, SlowOpenEdgeEq V t
      (familyLiftData D level slot A ρ edge).edge edge')
    (Qedge : ∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
      JointSourceReserve S (fun t z Y => γ.coeff β t Y z))
    (hz : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u Y, Y ∈ Ω →
        ∀ z, weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge) inv N p q m α a Y z v u 1 = 0)
    (hloc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u,
        ∃ (U : Set (Vec 2)) (f' : ℝ → Vec 2 → Vec 2 → ℝ),
          IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve (S + Dm + 2)
            (independentTimeWindowSource (Ioc a b) f')) ∧
          ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
            f' t z Y = weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge) inv N p q m α t Y z v u 1)
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ l ≤ q, ∀ β : DerivativeWord2 l, ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ v u ξ,
        fieldCellMean (fun z => weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge) inv N p q l β t Y z v u ξ) = 0)
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Icc a b) (z : Vec 2) (v : ι) :
    let Q := familyLiftData D level slot A ρ edge
    let Cc := weakLiftInverseCoefficients Q inv N
    leftTermsApply (liftCellSourceLeftTerms Q Cc hh n t v) f Y₀ z =
      liftCellSource Q Cc (fun _ => f) hh n t Y₀ z v := by
  obtain ⟨Q', W, hW, hYW, hη, hv, hG, hΓ, ⟨QG⟩, ⟨Qv⟩, ⟨Qe⟩, hvm⟩ :=
    native_local_primitive_source_model D hζ hΛ level hν slot hslot A hl ρ edge
      a b hab S Y₀ V hV hYV edge' he Qedge
  exact weakLiftInverseCoefficients_local_finite_source_action S hDm hS a b hab Ω hΩ Y₀ hYΩ
    (familyLiftData D level slot A ρ edge) Q' hη hv inv N hh n hn hnN hnS
    W hW hYW hG hΓ QG Qv Qe hvm hz hloc hmean f hf t ht z v

end AVRegularity.WeakEntryProofs
end
end

section
/-! Arbitrary well-slotted native histories have locally reserved full-cell forcing at each rank. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_cell_source_local_reserve
    (D : OCData) (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ)
    (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (H : ℕ) (hH : 1 ≤ H) (hDm : 1 ≤ Dm)
    (a b : ℝ) (hab : a ≤ b) (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (Y₀ : Vec 2) (hYΩ : Y₀ ∈ Ω)
    (inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ) (N hh n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (hroom : 2 * Dm + 4 ≤ H + n)
    (V : Set (Vec 2)) (hV : IsOpen V) (hYV : Y₀ ∈ V)
    (edge' : ConstituentEdges Dm (fun _ : ι => ℝ))
    (he : ∀ t ∈ Icc a b, SlowOpenEdgeEq V t
      (familyLiftData D level slot A ρ edge).edge edge')
    (Qedge : ∀ v u d, ∀ γ ∈ edge' v u d, ∀ β,
      JointSourceReserve (H + n + 1) (fun t z Y => γ.coeff β t Y z))
    (hz : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u Y, Y ∈ Ω →
        ∀ z, weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge) inv N p q m α a Y z v u 1 = 0)
    (hloc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u,
        ∃ (U : Set (Vec 2)) (f' : ℝ → Vec 2 → Vec 2 → ℝ),
          IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve (H + n + Dm + 2)
            (independentTimeWindowSource (Ioc a b) f')) ∧
          ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
            f' t z Y = weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge) inv N p q m α t Y z v u 1)
    (hmean : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → p ≠ 0 ∨ q ≠ 0 →
      ∀ l ≤ q, ∀ β : DerivativeWord2 l, ∀ t ∈ Icc a b, ∀ Y ∈ Ω, ∀ v u ξ,
        fieldCellMean (fun z => weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge) inv N p q l β t Y z v u ξ) = 0)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι) :
    ∃ (U : Set (Vec 2)) (g' : ℝ → Vec 2 → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ U ⊆ Ω ∧ Nonempty (IndependentParameterSourceReserve H g') ∧
      (∀ t Y, (∫ z in AVenhance.unitCube, g' t z Y) = 0) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
        g' t z Y = weakLiftCoefficientForcing (familyLiftData D level slot A ρ edge)
          (weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge) inv N)
          hh n m α v u t z Y := by
  obtain ⟨Q', W, hW, hYW, hη, hv, hG, hΓ, ⟨QG⟩, ⟨Qv⟩, ⟨Qe⟩, hvm⟩ :=
    native_local_primitive_source_model D hζ hΛ level hν slot hslot A hl ρ edge
      a b hab (H + n + 1) Y₀ V hV hYV edge' he Qedge
  exact weakLiftInverseCoefficients_local_source_production H hH hDm a b hab Ω hΩ Y₀ hYΩ
    (familyLiftData D level slot A ρ edge) Q' hη hv inv N hh n hn hnN hroom
    W hW hYW hG hΓ QG (fun i => (Qv i).mono (H + n) (by omega)) Qe hvm
    hz hloc hmean m hm α v u

end AVRegularity.WeakEntryProofs
end
end

section
/-! A genuinely locally reserved full-cell forcing produces the next native coefficient rank. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm H : ℕ}

theorem native_full_lift_rank_response (D : OCData) (hζ : IsFastProfile D.ζ)
    (hΛ : 1 ≤ D.Λ) (level : ℕ) (hν : 0 < D.kap level) (slot : ℤ) (hslot : Odd slot)
    (A : RealChain) (hl : A.slots.length = A.children.length + 1)
    (ρ : ℝ) (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (a b : ℝ) (hab : a < b) (r : ℕ) (hr : 1 ≤ r)
    (R K : ℕ) (hrR : r ≤ R) (hH : R + (K + R) + 1 ≤ H)
    (hR : R + 2 ≤ H) (hK : R + 4 ≤ K)
    (N hh n m : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (v u : ι) (Ω : Set (Vec 2)) (hΩ : IsOpen Ω)
    (hsource : let Q := familyLiftData D level slot A ρ edge
      let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
      let Cc := weakLiftInverseCoefficients Q inv N
      ∀ Y₀ ∈ Ω, ∃ (U : Set (Vec 2)) (g' : ℝ → Vec 2 → Vec 2 → ℝ),
        IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve H g') ∧
        (∀ t Y, ∫ z in AVenhance.unitCube, g' t z Y = 0) ∧
        ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z,
          g' t z Y = weakLiftCoefficientForcing Q Cc hh n m α v u t z Y) :
    let Q := familyLiftData D level slot A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
    let Cc := weakLiftInverseCoefficients Q inv N
    let c := fun Y t z => Cc hh n m α t Y z v u 1
    (∀ Y ∈ Ω, IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v R a b 0
      (fun t z => weakLiftCoefficientForcing Q Cc hh n m α v u t z Y) (c Y)) ∧
    (∀ q, q ≤ R → ∀ t ∈ Icc a b,
      ContDiffOn ℝ (q : ℕ∞) (fun X : Vec 2 × Vec 2 => c X.1 t X.2) {X | X.1 ∈ Ω}) ∧
    ∀ Y₀ ∈ Ω, ∃ (U : Set (Vec 2)) (c' : Vec 2 → ℝ → Vec 2 → ℝ),
      IsOpen U ∧ Y₀ ∈ U ∧ U ⊆ Ω ∧ Nonempty (IndependentParameterSourceReserve R
        (independentTimeWindowSource (Ioc a b) (fun t z Y => c' Y t z))) ∧
      ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, c' Y t z = c Y t z := by
  dsimp only at hsource ⊢
  have he : (fun Y t z => weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge)
      (fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y)
      N hh n m α t Y z v u 1) =
      (fun Y t z => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y
        (fun s y => weakLiftCoefficientForcing (familyLiftData D level slot A ρ edge)
          (weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge)
            (fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y) N)
          hh n m α v u s y Y) t z) := by
    funext Y t z
    exact weakLiftInverseCoefficients_apply_one _ _ N hh n m hn hnN hm α t Y z v u
  simp_rw [show ∀ Y t z, weakLiftInverseCoefficients (familyLiftData D level slot A ρ edge)
      (fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab.le Y)
      N hh n m α t Y z v u 1 = _ from fun Y t z => congrFun (congrFun (congrFun he Y) t) z]
  exact native_window_response_on_local_reserve D hζ hΛ level hν slot hslot A hl ρ edge
    a b hab r hr R K hrR hH hR hK Ω hΩ hsource

end AVRegularity.WeakEntryProofs
end
end

section
/-! Solvable native full-cell ranks have exact zero initial traces and centered scalar blocks. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs
open Homogenization MeasureTheory Set AVRegularity.EntryWeakProofs
open AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Dm : ℕ}

theorem native_full_lift_rank_centering (D : OCData) (hζ : IsFastProfile D.ζ)
    (level : ℕ) (slot : ℤ) (hslot : Odd slot) (A : RealChain) (ρ : ℝ)
    (edge : ConstituentEdges Dm (fun _ : ι => ℝ))
    (r : ℕ) (hr : 1 ≤ r) (a b : ℝ) (hab : a ≤ b)
    (N hh n m : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (Y : Vec 2) (v u : ι)
    (hsolv : let Q := familyLiftData D level slot A ρ edge
      let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab Y
      let Cc := weakLiftInverseCoefficients Q inv N
      ∃ c, IsCellFieldInverse (fun t => Matrix.of (Q.G t Y)) Q.v r a b 0
        (fun t z => weakLiftCoefficientForcing Q Cc hh n m α v u t z Y) c) :
    let Q := familyLiftData D level slot A ρ edge
    let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab Y
    let Cc := weakLiftInverseCoefficients Q inv N
    (∀ z, Cc hh n m α a Y z v u 1 = 0) ∧
    (∀ t ξ, fieldCellMean (fun z => Cc hh n m α t Y z v u ξ) = 0) ∧
    ∀ t, AVenhance.IsZ2Periodic (fun z => Cc hh n m α t Y z v u 1) := by
  let Q := familyLiftData D level slot A ρ edge
  let inv : Vec 2 → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ := fun Y => nativeWindowResponseLinear D hζ level slot hslot A ρ edge r hr a b hab Y
  let Cc := weakLiftInverseCoefficients Q inv N
  let g := fun t z => weakLiftCoefficientForcing Q Cc hh n m α v u t z Y
  have he t z : Cc hh n m α t Y z v u 1 = inv Y g t z :=
    weakLiftInverseCoefficients_apply_one Q inv N hh n m hn hnN hm α t Y z v u
  have hz := nativeWindowResponseLinear_initial_zero D hζ level slot hslot A ρ edge
    r hr a b hab Y g hsolv
  have hmean := nativeWindowResponseLinear_mean_zero D hζ level slot hslot A ρ edge
    r hr a b hab Y g hsolv
  have hper := nativeWindowResponseLinear_periodic D hζ level slot hslot A ρ edge
    r hr a b hab Y g hsolv
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rw [he]
    exact congrFun hz z
  · intro t ξ
    have hscale : (fun z => Cc hh n m α t Y z v u ξ) =
        fun z => ξ • inv Y g t z := by
      funext z
      have hs := (Cc hh n m α t Y z v u).map_smul ξ (1 : ℝ)
      simpa only [smul_eq_mul, mul_one, he t z] using hs
    rw [hscale, fieldCellMean_smul]
    change ξ • (∫ z in AVenhance.unitCube, inv Y g t z) = 0
    rw [hmean t, smul_zero]
  · intro t
    convert hper t using 1
    funext z
    exact he t z

end AVRegularity.WeakEntryProofs
end
end
end
