import Mathlib.Probability.Distributions.Exponential

lemma h₀ (z) :
        ∫ (a : ℝ) in Set.Ici 0, z * Real.exp (-(z * a))
        =  ∫ (a : ℝ), ProbabilityTheory.exponentialPDFReal z a := by
        unfold ProbabilityTheory.exponentialPDFReal
          ProbabilityTheory.gammaPDFReal
        simp
        generalize Real.exp = f
        have (g : ℝ → ℝ) :
          ∫ (a : ℝ) in Set.Ici 0, g a = ∫ (a : ℝ), if 0 ≤ a then g a else 0 := by
          rw [← MeasureTheory.integral_indicator]
          exact Real.ext_cauchy rfl
          simp
        rw [this]

lemma h₂ (z : ℝ) (hz : 0 < z) : ∫ (y : ℝ), ProbabilityTheory.exponentialPDFReal z y = 1 := by
        have := @ProbabilityTheory.lintegral_exponentialPDF_eq_one z hz
        have h₁ : (1 : ℝ) = (1 : ENNReal).toReal := rfl
        rw [h₁]
        rw [← this]
        unfold ProbabilityTheory.exponentialPDF
        -- generalize ProbabilityTheory.exponentialPDFReal s = g
        refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae ?_ ?_
        rw [Filter.EventuallyLE]
        rw [Filter.Eventually]
        simp
        refine Filter.univ_mem' ?_
        simp
        intro a
        refine ProbabilityTheory.exponentialPDFReal_nonneg hz a
        unfold ProbabilityTheory.exponentialPDFReal
          ProbabilityTheory.gammaPDFReal
        simp
        refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
        refine Measurable.aemeasurable ?_
        refine Measurable.ite ?_ ?_ ?_
        exact measurableSet_Ici
        refine Measurable.mul ?_ ?_
        exact measurable_const
        refine Measurable.exp ?_
        refine Measurable.neg ?_
        exact measurable_const_mul z
        exact measurable_const


lemma first_loss_is_ruinous (r s : ℝ) (hs : 0 < s)
  (hr : 0 < r)
  :
    ∫ (y : ℝ) in Set.Ici 0,
      (∫ (x : ℝ) in Set.Iic y,
      ProbabilityTheory.exponentialPDFReal s y
      *
      ProbabilityTheory.exponentialPDFReal r x
      )
      = r / (r + s) := by
      suffices     ∫ (y : ℝ) in Set.Ici 0,
      ProbabilityTheory.exponentialPDFReal s y
      *
      (∫ (x : ℝ) in Set.Iic y,
      ProbabilityTheory.exponentialPDFReal r x
      )
      = r / (r + s) by
          rw [← this]
          congr
          ext x
          exact MeasureTheory.integral_const_mul _ _
      have h₁ := @ProbabilityTheory.cdf_expMeasure_eq_integral r hr
      simp_rw [← h₁]
      have := @ProbabilityTheory.cdf_expMeasure_eq r hr
      simp_rw [this]
      simp
      unfold ProbabilityTheory.exponentialPDFReal
        ProbabilityTheory.gammaPDFReal
      simp
      suffices (∫ (y : ℝ) in Set.Ici 0,
        if 0 ≤ y then s * Real.exp (-(s * y)) * (1 - Real.exp (-(r * y))) else 0) =
        r / (r + s) by
        rw [← this]
        congr
        ext y
        simp
        intro h₀ h₁
        linarith
      suffices (∫ (y : ℝ) in Set.Ici 0,
        s * Real.exp (-(s * y)) * (1 - Real.exp (-(r * y)))) =
        r / (r + s) by
        rw [← this]
        apply MeasureTheory.integral_congr_ae
        refine Set.EqOn.aeEq_restrict ?_ ?_
        intro x hx
        simp
        intro hx₀
        simp at hx
        linarith
        simp
      simp_rw [mul_sub]
      simp
      rw [MeasureTheory.integral_sub]
      have :
        ∫ (a : ℝ) in Set.Ici 0, s * Real.exp (-(s * a))
        =  1 := by
          rw [h₀]
          exact EReal.coe_eq_one.mp (congrArg Real.toEReal (h₂ s hs))
      rw [this]
      have (x : ℝ) :
         s * Real.exp (-(s * x)) * Real.exp (-(r * x))
         =
          s * Real.exp (-((s+r) * x))
          := by
            rw [mul_assoc]
            congr
            rw [← Real.exp_add]
            congr
            linarith
      simp_rw [this]
      have : ∫ (a : ℝ) in Set.Ici 0, s * Real.exp (-((s + r) * a))
       =
       s * ∫ (a : ℝ) in Set.Ici 0, Real.exp (-((s + r) * a))
       := by
        exact MeasureTheory.integral_const_mul s fun a ↦ Real.exp (-((s + r) * a))
      rw [this]
      have : ∫ (x : ℝ) in Set.Ici 0, Real.exp (-((s + r) * x))
        =
        (1/(s+r)) * ∫ (x : ℝ) in Set.Ici 0, (s+r) * Real.exp (-((s + r) * x))
        := by
          rw [MeasureTheory.integral_const_mul]
          field_simp
      rw [this]
      have :
        ∫ (x : ℝ) in Set.Ici 0, (s + r) * Real.exp (-((s + r) * x))
        = 1 := by
          rw [h₀]
          rw [h₂]
          linarith
      rw [this]
      field_simp
      linarith

      · refine MeasureTheory.integrable_of_integral_eq_one ?_
        rw [h₀]
        rw [h₂]
        exact hs
      ·
        have (x : ℝ) :
           s * Real.exp (-(s * x)) * Real.exp (-(r * x))
           =
            s * Real.exp (-((s + r) * x))
            := by
              rw [mul_assoc];congr
              rw [← Real.exp_add]
              congr
              linarith
        simp_rw [this]
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
#min_imports
