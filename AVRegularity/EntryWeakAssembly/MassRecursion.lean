-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.EntryWeak.WeakReduction

/-! Exact mass and readout recursions for the weak response words. -/

@[expose] public section
namespace AVRegularity.WeakEntryProofs

@[simp] theorem weakMass_root (D : OCData) (N J r : ℕ) (η : ℝ) :
    weakMass D N J η ⟨r, []⟩ = 1 / 2 := by
  simp only [weakMass, List.map_nil, List.prod_nil, mul_one]

@[simp] theorem weakReadoutWeight_root (D : OCData) (r : ℕ) (η : ℝ) :
    weakReadoutWeight D η ⟨r, []⟩ = 1 := by
  simp only [weakReadoutWeight, List.map_nil, List.prod_nil]

theorem weakMass_succComp (D : OCData) (N J m : ℕ) (η : ℝ)
    (v : Comp) (w : List WordLetter) :
    weakMass D N J η (succComp m v w) =
      weakMass D N J η v * (weakCw N J * D.eps (m - 1) ^ (η / 2)) ^ w.length := by
  by_cases hw : w = []
  · subst w
    simp only [succComp, ↓reduceDIte, List.length_nil, pow_zero, mul_one]
  · simp only [succComp, hw, ↓reduceDIte, weakMass, List.map_cons, List.prod_cons]
    ring

end AVRegularity.WeakEntryProofs
