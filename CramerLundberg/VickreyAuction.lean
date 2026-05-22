import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Process.Stopping

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal BigOperators

open MeasureTheory

noncomputable section

/--
b = bid
m = maximum of others' bid
v = value
p = profit (or loss if negative)
-/
def p₁ (v m b : ℝ) := ite (b > m) (v - b) 0
def p₂ (v m b : ℝ) := ite (b > m) (v - m) 0
def p₃ (v m₀ m₁ b : ℝ) := ite (b > max m₀ m₁) (v - min m₀ m₁) 0

/-- The best bid in a sealed-bid second-price auction is your true value. -/
lemma vickrey (v m b : ℝ) : p₂ v m b ≤ p₂ v m v := by
    unfold p₂
    split_ifs
    all_goals try simp
    all_goals linarith



open NNReal

/-- In a sealed-bid first-price auction, there is no
winning strategy.
Can also prove there is no `f` when `m=0`?
-/
lemma vickrey₁ : ¬ ∃ f : ℝ≥0 → ℝ≥0,
    ∀ (v : ℝ≥0),
    ∀ m > 0,
    ∀ (b : ℝ≥0),
    p₁ v m b ≤
    p₁ v m (f v) := by
  unfold p₁
  push Not
  intro f
  by_cases H : ∃ v > 0, v ≤ f v
  · obtain ⟨v,hv⟩ := H
    use v
    use v / 2
    simp
    rw [if_pos (by
        calc v / 2 < v := by simp;tauto
             _ ≤ _ := by tauto)]
    constructor
    tauto
    use 2 * v / 3
    simp
    have : v.toReal > 0 := by refine coe_pos.mpr (by tauto)
    rw [if_pos (by linarith)]
    have : (f v).toReal > 0 := by refine coe_pos.mpr (by
        calc 0 < v := by tauto
             _ ≤ _ := by tauto)
    simp
    calc _ < v.toReal := by linarith
         _ ≤ _ := by refine coe_le_coe.mpr ?_;tauto
  push Not at H
  simp
  use 2
  by_cases H : f 2 = 0
  · rw [H]
    simp
    use 1/2
    constructor
    simp
    use 1
    rw [if_neg (by simp)]
    rw [if_pos (by simp;exact two_inv_lt_one)]
    simp
  use 1 * f 2 / 2
  have : (f 2).toReal > 0 := by simp;exact pos_of_ne_zero H
  constructor
  · linarith
  use 2 * f 2 / 3 -- we squeeze our bid in between `m` and `f v`
  simp
  rw [if_pos (by
    refine coe_lt_coe.mp ?_
    exact this)]
  rw [if_pos (by
    linarith)]
  linarith




/-- In a sealed-bid third-price auction, there is no
winning strategy.
-/
lemma vickrey' : ¬ ∃ f : ℝ≥0 → ℝ≥0, ∀ (v m₀ m₁ b : ℝ≥0),
    p₃ v m₀ m₁ b ≤
    p₃ v m₀ m₁ (f v) := by
    push Not
    intro f
    use 2, f 2, 1, 2 + f 2
    simp only [p₃, coe_one, gt_iff_lt, sup_lt_iff, lt_self_iff_false, one_lt_coe, false_and, ↓reduceIte,
      NNReal.coe_add, NNReal.coe_ofNat, lt_add_iff_pos_left, Nat.ofNat_pos, true_and]
    split_ifs with g
    · simp
    · exfalso
      revert g
      simp only [not_lt, imp_false, not_le]
      calc (1 : ℝ) < 2 := by linarith
           _ ≤ _ := by simp


/- If now `v` and `m` are uniform on `[0,1]`, in a first-bid auction we may choose
to bid `v/2`. Because given that `m≤v` that is `𝔼m`.
Then we prove the other player's `max 𝔼` profit is by using same strategy.
-/
