-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.SourceParameterPeriodicity
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Native coefficient arrays extend beyond their stored carrier by the literal initial identity and zero positive coefficients. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d D N R sX sZ : ℕ} {a b : ℝ}

open scoped Classical in
def independentCarrierCoefficientExtension (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (P : Vec d) (hh n : ℕ) : LiftCoeff ι (fun _ => ℝ) :=
  if n = 0 then if hh = 0 then independentIdentityLiftCoeff else 0
  else if P ∈ V then c P hh n else 0

theorem independentCarrierCoefficientExtension_initial (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (P : Vec d)
    (f : ℝ → Vec 2 → ι → ℝ) (t : ℝ) (X z : Vec 2) :
    liftApply 0 (independentCarrierCoefficientExtension V c P 0 0) f t X z = f t X := by
  simp only [independentCarrierCoefficientExtension, ite_true]
  exact independentIdentityLiftCoeff_apply f t X z

theorem independentCarrierCoefficientExtension_copy (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (P : Vec d) (hP : P ∈ V)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (hc : IsLiftSequence Q sX sZ a b N R (c P)) (hh : ℕ) (hhh : hh ≤ R)
    (n m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) (v u : ι) :
    independentCarrierCoefficientExtension V c P hh n m α t X z v u = c P hh n m α t X z v u := by
  by_cases hn : n = 0
  · subst n
    by_cases hh0 : hh = 0
    · subst hh
      by_cases hm : m = 0
      · subst m
        apply ContinuousLinearMap.ext
        intro ξ
        have he := congrFun (hc.1 (fun _ => Pi.single u ξ) contDiff_const t ht X z) v
        rw [liftApply_constant_single 0 (c P 0 0) α t X z v u ξ] at he
        simpa only [independentCarrierCoefficientExtension, ite_true, independentIdentityLiftCoeff,
          blockIdentityEntry_apply] using he.symm
      · rw [hc.2.2.2.1 0 (Nat.zero_le _) 0 m (by omega) α t X z v u]
        simp only [independentCarrierCoefficientExtension, ite_true, independentIdentityLiftCoeff, ite_eq_right hm]
    · rw [hc.2.1 hh (by omega) hhh m α t X z v u]
      simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_right hh0, Pi.zero_apply]
  · simp only [independentCarrierCoefficientExtension, ite_eq_right hn, ite_eq_left hP]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Extending literal native coefficients preserves every algebraic initial, degree, order and symmetry clause. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d D N R sX sZ : ℕ} {a b : ℝ}

omit [Fintype ι] in
theorem independentCarrierCoefficientExtension_positive_zero_degree (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (P : Vec d)
    (hh : ℕ) (hhh : 1 ≤ hh) (m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    independentCarrierCoefficientExtension V c P hh 0 m α t X z v u = 0 := by
  simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_right (by omega : hh ≠ 0), Pi.zero_apply]

theorem independentCarrierCoefficientExtension_above_degree (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (Q : Vec d → LiftOperatorData ι (fun _ => ℝ) D)
    (hc : ∀ P ∈ V, IsLiftSequence (Q P) sX sZ a b N R (c P)) (P : Vec d)
    (hh n m : ℕ) (hhh : hh ≤ R) (hn : N < n) (α : DerivativeWord2 m)
    (t : ℝ) (X z : Vec 2) (v u : ι) :
    independentCarrierCoefficientExtension V c P hh n m α t X z v u = 0 := by
  have hn0 : n ≠ 0 := by omega
  by_cases hP : P ∈ V
  · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_left hP]
    exact (hc P hP).2.2.1 hh hhh n hn m α t X z v u
  · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_right hP, Pi.zero_apply]

theorem independentCarrierCoefficientExtension_above_order (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (Q : Vec d → LiftOperatorData ι (fun _ => ℝ) D)
    (hc : ∀ P ∈ V, IsLiftSequence (Q P) sX sZ a b N R (c P)) (P : Vec d)
    (hh n m : ℕ) (hhh : hh ≤ R) (hm : n < m) (α : DerivativeWord2 m)
    (t : ℝ) (X z : Vec 2) (v u : ι) :
    independentCarrierCoefficientExtension V c P hh n m α t X z v u = 0 := by
  by_cases hn0 : n = 0
  · subst n
    by_cases hh0 : hh = 0
    · simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_left hh0]
      exact independentIdentityLiftCoeff_above_order m hm α t X z v u
    · simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_right hh0, Pi.zero_apply]
  · by_cases hP : P ∈ V
    · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_left hP]
      exact (hc P hP).2.2.2.1 hh hhh n m hm α t X z v u
    · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_right hP, Pi.zero_apply]

theorem independentCarrierCoefficientExtension_perm (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (Q : Vec d → LiftOperatorData ι (fun _ => ℝ) D)
    (hc : ∀ P ∈ V, IsLiftSequence (Q P) sX sZ a b N R (c P)) (P : Vec d)
    (hh n m : ℕ) (hhh : hh ≤ R) (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    independentCarrierCoefficientExtension V c P hh n m (α ∘ σ) =
      independentCarrierCoefficientExtension V c P hh n m α := by
  by_cases hn0 : n = 0
  · subst n
    by_cases hh0 : hh = 0
    · simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_left hh0]
      exact independentIdentityLiftCoeff_perm m α σ
    · simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_right hh0, Pi.zero_apply]
  · by_cases hP : P ∈ V
    · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_left hP]
      exact (hc P hP).2.2.2.2.1 hh hhh n m α σ
    · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_right hP, Pi.zero_apply]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! The localized lift relation retains every global algebraic coefficient copy. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d D N R sX sZ : ℕ} {a b : ℝ}

theorem independentCarrierCoefficientExtension_copy_on (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (P : Vec d) (hP : P ∈ V)
    (Ω : Set (Vec 2)) (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (hc : IsLiftSequenceOn Ω Q sX sZ a b N R (c P)) (hh : ℕ) (hhh : hh ≤ R)
    (n m : ℕ) (α : DerivativeWord2 m) (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) (v u : ι) :
    independentCarrierCoefficientExtension V c P hh n m α t X z v u = c P hh n m α t X z v u := by
  by_cases hn : n = 0
  · subst n
    by_cases hh0 : hh = 0
    · subst hh
      by_cases hm : m = 0
      · subst m
        apply ContinuousLinearMap.ext
        intro ξ
        have he := congrFun (hc.1 (fun _ => Pi.single u ξ) contDiff_const t ht X z) v
        rw [liftApply_constant_single 0 (c P 0 0) α t X z v u ξ] at he
        simpa only [independentCarrierCoefficientExtension, ite_true, independentIdentityLiftCoeff,
          blockIdentityEntry_apply] using he.symm
      · rw [hc.2.2.2.1 0 (Nat.zero_le _) 0 m (by omega) α t X z v u]
        simp only [independentCarrierCoefficientExtension, ite_true, independentIdentityLiftCoeff, ite_eq_right hm]
    · rw [hc.2.1 hh (by omega) hhh m α t X z v u]
      simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_right hh0, Pi.zero_apply]
  · simp only [independentCarrierCoefficientExtension, ite_eq_right hn, ite_eq_left hP]

end AVRegularity.EntryWeakProofs
end
