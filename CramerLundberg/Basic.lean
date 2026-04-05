import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi

/-!

# Cramér-Lundberg distribution

-/

open ProbabilityTheory
lemma h₀ (z) : ∫ (a : ℝ) in Set.Ici 0, z * Real.exp (-(z * a))
            =  ∫ (a : ℝ), exponentialPDFReal z a := by
        unfold exponentialPDFReal
          gammaPDFReal
        generalize Real.exp = f
        have (g : ℝ → ℝ) :
          ∫ (a : ℝ) in Set.Ici 0, g a = ∫ (a : ℝ), if 0 ≤ a then g a else 0 := by
          rw [← MeasureTheory.integral_indicator]
          · exact Real.ext_cauchy rfl
          · simp
        simp [this]

lemma g₀ (s r x : ℝ) : s * Real.exp (-(s * x)) * Real.exp (-(r * x))
                     = s * Real.exp (-((s+r) * x)) := by
  rw [mul_assoc]
  congr
  rw [← Real.exp_add]
  congr
  linarith

lemma h₂ (z : ℝ) (hz : 0 < z) :
    ∫ (y : ℝ), exponentialPDFReal z y = 1 := by
  have := @lintegral_exponentialPDF_eq_one z hz
  have h₁ : (1 : ℝ) = (1 : ENNReal).toReal := rfl
  rw [h₁]
  rw [← this]
  refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae ?_ ?_
  · rw [Filter.EventuallyLE, Filter.Eventually]
    exact Filter.univ_mem' <| exponentialPDFReal_nonneg hz
  unfold exponentialPDFReal
    gammaPDFReal
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  refine Measurable.aemeasurable ?_
  refine Measurable.ite measurableSet_Ici ?_ measurable_const
  · exact Measurable.mul measurable_const <|Measurable.exp
      <| Measurable.neg <| measurable_const_mul z


lemma first_loss_is_ruinous (r s : ℝ) (hs : 0 < s) (hr : 0 < r) :
    ∫ (y : ℝ) in Set.Ici 0, (∫ (x : ℝ) in Set.Iic y,
      exponentialPDFReal s y *
      exponentialPDFReal r x) = r / (r + s) := by
  simp_rw [MeasureTheory.integral_const_mul]
  have h₁ := @cdf_expMeasure_eq_integral r hr
  simp_rw [← h₁]
  simp_rw [@cdf_expMeasure_eq r hr]
  unfold exponentialPDFReal gammaPDFReal
  suffices (∫ (y : ℝ) in Set.Ici 0,
    if 0 ≤ y then s * Real.exp (-(s * y)) * (1 - Real.exp (-(r * y))) else 0) =
    r / (r + s) by
    rw [← this]
    congr
    ext y
    simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one, mul_ite,
      ite_mul, zero_mul, mul_zero, ite_eq_left_iff, not_le, right_eq_ite_iff, zero_eq_mul,
      mul_eq_zero, Real.exp_ne_zero, or_false]
    intro h₀ h₁
    linarith
  suffices (∫ (y : ℝ) in Set.Ici 0,
    s * Real.exp (-(s * y)) * (1 - Real.exp (-(r * y)))) = r / (r + s) by
    rw [← this]
    apply MeasureTheory.integral_congr_ae
    refine Set.EqOn.aeEq_restrict ?_ ?_
    · intro x hx
      simp only [ite_eq_left_iff, not_le, zero_eq_mul, mul_eq_zero, Real.exp_ne_zero, or_false]
      intro hx₀
      simp at hx
      linarith
    · simp
  simp_rw [mul_sub]
  simp only [mul_one]
  rw [MeasureTheory.integral_sub]
  · have : ∫ (a : ℝ) in Set.Ici 0, s * Real.exp (-(s * a)) = 1 := by
      rw [h₀]
      exact EReal.coe_eq_one.mp (congrArg Real.toEReal (h₂ s hs))
    rw [this]
    simp_rw [g₀]
    rw [MeasureTheory.integral_const_mul]
    have :          ∫ (x : ℝ) in Set.Ici 0, Real.exp (-((s + r) * x))
      = (1/(s+r)) * ∫ (x : ℝ) in Set.Ici 0, (s+r) * Real.exp (-((s + r) * x)) := by
        rw [MeasureTheory.integral_const_mul]
        field_simp
    rw [this]
    rw [h₀, h₂]
    · field_simp
      linarith
    · linarith
  · refine MeasureTheory.integrable_of_integral_eq_one ?_
    rw [h₀]
    rw [h₂]
    exact hs
  · simp_rw [g₀]
    have : (fun y ↦ s * Real.exp (-((s + r) * y)))
         = (fun _ => s / (s + r)) * (fun y ↦ (s + r) * Real.exp (-((s + r) * y))) := by
      ext y
      simp
      field_simp
    rw [this]
    refine MeasureTheory.Integrable.const_mul' ?_ _
    refine MeasureTheory.integrable_of_integral_eq_one ?_
    rw [h₀]
    rw [h₂]
    linarith

-- example (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
--     MeasureTheory.Measure.pi ![expMeasure r, expMeasure s]
--     {v | v 0 ≤ v 1} = some ⟨r / (r + s), by field_simp;linarith⟩ := by
--   -- rw [MeasureTheory.measure_eq_integral]
--   have := @first_loss_is_ruinous r s hs hr
--   simp_rw [← this]
--   simp
--   have (q : ℝ) : expMeasure q = MeasureTheory.volume.withDensity (exponentialPDF q) := by
--     rfl
--   repeat rw [this]
--   rw [MeasureTheory.Measure.withDensity]
--   unfold exponentialPDF
--   -- have := @MeasureTheory.integral_indicator

--   -- have := @lintegral_withDensity_eq_lintegral_mul
--   sorry
